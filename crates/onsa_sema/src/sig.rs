//! Lowering of signatures (T2-3), after the names stage (`crate::names`:
//! the module tree, the item defs and scopes, the imports): every item's
//! signature, then the items flows generate.
//!
//! The stages, in the order of [`collect_and_lower`], each reading the
//! tables of the one before: the names stage, the types of the signatures
//! ([`Sema::lower_signatures`], here: every def in its order, a flow's
//! inputs and output by `flow_sig`), the items flows generate and `@param`
//! (`generated`), then the `use` of an item a flow does not generate
//! ([`Sema::fail_ungenerated`]). The parts are in a module each, an `impl` of
//! `Sema`: `types` (the types, also those written in a body), `flow_sig` and
//! `generated`.

use std::collections::{HashMap, HashSet};

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::FloatRange;
use onsa_syntax::ast::{
    Ast, Attr, AttrArg, Derives, EffectRow, ExprKind, GenericParam, Ident, ImplDecl, ItemKind, Lit, Mode, Param,
    ParamName, Path, TypeId, TypeKind, UnOp, Vis,
};
use onsa_syntax::foreign::{self, RowId};

use crate::def::*;
use crate::resolve::{Builtin, Entity, NameKind};
use crate::ty::*;
use crate::{Analysis, Module, Package, flatten};
mod decls;
mod flow_sig;
mod generated;
mod types;
mod wellformed;

use flow_sig::FlowHeading;

pub(crate) use decls::Decls;
pub(crate) use types::lower_type_in_body;
pub(crate) use wellformed::Pos;

pub(crate) struct Sema<'p> {
    pub(crate) a: &'p mut Analysis,
    pub(crate) flat: Vec<&'p Package>,
    /// Defs that already have a diagnostic, and its index in the
    /// diagnostics (P-01: one error per item, [`Sema::report`]).
    reported: HashMap<DefId, usize>,
    /// The `copy_bound` diagnostics reported (their index in the
    /// diagnostics), their type and whether the constraint is `Dup`: once
    /// every signature is lowered, the note names a field that does not meet
    /// it ([`Sema::name_non_copy_fields`], §4.6).
    kind_heads: Vec<(usize, DefId, bool)>,
    /// The places of the types written that name an alias, and the alias:
    /// its right side is judged at the alias (S-757, [`Sema::wellformed`]).
    alias_at: HashMap<(ModId, TypeId), DefId>,
    /// Whether a part of a type at its place holds a second-class type out
    /// of its place (E0710, [`Sema::wellformed`]).
    misfit: HashMap<(TyId, Pos, u8), bool>,
}

/// Lowering context for one item.
struct Cx<'p> {
    m: ModId,
    ast: &'p Ast,
    text: &'p str,
    /// Generic parameters in scope: the owner's (impl) first, then the item's.
    generics: Vec<GenericDef>,
    self_ty: Option<TyId>,
    def: DefId,
    /// How far the heading being lowered is seen (§15.1, S-665): a type
    /// named in it that reaches less far is an E0303. `None` out of a
    /// heading (a body, the type of an `impl`).
    reach: Option<Vis>,
    /// The local bindings and parameters the type sees, by name: values a
    /// path of it names first (§15.1, §4.5, S-729). Of a type of a body, the
    /// visible ones it names; in a heading, its parameters (S-741, S-733).
    locals: HashSet<String>,
}

impl Cx<'_> {
    /// Whether `name` is one of [`Self::locals`], a value (S-729).
    fn is_local(&self, name: &str) -> bool {
        self.locals.contains(name)
    }

    /// Whether a constant expression starts at one of [`Self::locals`]: a
    /// value, no constant (E0417, §4.5).
    fn local(&self) -> impl Fn(onsa_syntax::ast::ExprId) -> bool + '_ {
        |e| crate::constarg::path_of(self.ast, e).is_some_and(|p| self.is_local(&p.segments[0].name))
    }
}

pub(crate) fn collect_and_lower(pkg: &Package) -> Analysis {
    let mut a = Analysis::default();
    let mut s = Sema::new(&mut a, flatten(pkg));
    crate::names::collect_names(&mut s);
    let flows = s.lower_signatures();
    let pairs = s.lower_generated(&flows);
    s.a.known.ready = true;
    s.wellformed();
    s.check_generated(flows, pairs);
    s.fail_ungenerated();
    s.name_non_copy_fields();
    a
}

impl<'p> Sema<'p> {
    fn new(a: &'p mut Analysis, flat: Vec<&'p Package>) -> Self {
        Sema {
            a,
            flat,
            reported: HashMap::new(),
            kind_heads: Vec::new(),
            alias_at: HashMap::new(),
            misfit: HashMap::new(),
        }
    }

    pub(crate) fn module(&self, m: ModId) -> Option<&'p Module> {
        crate::names::module_of(&self.flat, &self.a.modules, m)
    }

    // ------------------------------------------------------------ diagnostics

    pub(crate) fn report(&mut self, def: DefId, d: Diagnostic) {
        self.keep(def, d);
    }

    /// The one diagnostic of `def`: the first in the order of a unit
    /// ([`Diagnostic::unit_order`], §18.1), whatever the order the stages
    /// find them in (a heading's narrow name before a name of a later
    /// parameter that is not found, S-698). Its index in the diagnostics
    /// when `d` is the one kept.
    fn keep(&mut self, def: DefId, d: Diagnostic) -> Option<usize> {
        let Some(&at) = self.reported.get(&def) else {
            self.reported.insert(def, self.a.diagnostics.len());
            self.a.diagnostics.push(d);
            return Some(self.a.diagnostics.len() - 1);
        };
        if d.unit_order() >= self.a.diagnostics[at].unit_order() {
            return None;
        }
        self.kind_heads.retain(|&(k, _, _)| k != at);
        self.a.diagnostics[at] = d;
        Some(at)
    }

    pub(crate) fn report_mod(&mut self, d: Diagnostic) {
        self.a.diagnostics.push(d);
    }

    /// E0200 for `feature` (S-224), with the details its phrase takes.
    pub(crate) fn unsupported(&mut self, def: DefId, span: Span, feature: Feature, details: &[&str]) {
        self.report(def, feature.diagnostic(Stage::Names, span, details));
    }

    // ------------------------------------------------------------ collection

    pub(crate) fn add_def(&mut self, def: Def) -> DefId {
        let module = def.item.and_then(|i| self.module(def.module).map(|m| (i, m)));
        let failed = module.and_then(|(i, m)| m.parsed.ast.item(i).failed);
        // The flow syntax outside a flow body (E0821 from W4-12): E0200, and
        // the def is not checked further (as a cut heading).
        let flow_syntax = match (failed, module) {
            (None, Some((i, m))) => crate::flow_syntax::first_form(&m.parsed, &m.text, i),
            _ => None,
        };
        self.a.defs.push(def);
        let id = DefId(self.a.defs.len() as u32 - 1);
        if let Some(f) = failed {
            self.a.failed.insert(id, f);
        }
        if let Some((span, form)) = flow_syntax {
            self.report(id, form.outside_flow(Stage::Names, span));
            self.a.failed.insert(id, onsa_syntax::ast::Failed::Heading);
        } else if let Some(span) =
            module.filter(|_| failed.is_none()).and_then(|(i, m)| crate::flow_syntax::first_mem(&m.parsed, i))
        {
            // `@mem` (§12.4) until W9-06: the same way.
            self.unsupported(id, span, Feature::MemStorage, &[]);
            self.a.failed.insert(id, onsa_syntax::ast::Failed::Heading);
        }
        id
    }

    // ------------------------------------------------------------ lowering

    /// The stage of the types of the signatures: the aliases and the
    /// constants in the order of the declarations (`decls`), then every def,
    /// in the order of the defs. The headings of the flows it lowered, for
    /// the next stage.
    fn lower_signatures(&mut self) -> Vec<FlowHeading> {
        self.order_declarations();
        let n = self.a.defs.len();
        let mut flows = Vec::new();
        for i in 0..n {
            let id = DefId(i as u32);
            // Lowered with their owner (impl / flow), or an E0200 (S-224).
            if self.a.defs[i].owner.is_some() || matches!(self.a.defs[i].kind, DefKind::Unsupported(_)) {
                continue;
            }
            let _scope = onsa_diag::internal::item_scope(self.a.defs[i].span);
            flows.extend(self.lower_def(id));
        }
        flows
    }

    /// The note of each `copy_bound` diagnostic that names the first field
    /// (or element of a variant) whose kind is not Copy (§4.6): the kinds are
    /// known once every signature and the items flows generate are lowered.
    /// A field whose kind is not known (a type parameter, an error) is not
    /// named.
    fn name_non_copy_fields(&mut self) {
        for (at, def, dup) in std::mem::take(&mut self.kind_heads) {
            let fields: Vec<(String, TyId, Span)> = match &self.a.def(def).kind {
                DefKind::Struct(s) => match &s.fields {
                    Fields::Named(fs) => fs.iter().map(|f| (format!("the field `{}`", f.name), f.ty, f.span)).collect(),
                    Fields::Opaque => Vec::new(),
                },
                DefKind::Enum(e) => e
                    .variants
                    .iter()
                    .flat_map(|v| v.fields.iter().map(move |&t| (format!("the variant `{}`", v.name), t, v.span)))
                    .collect(),
                _ => Vec::new(),
            };
            use crate::kind::Kind;
            // `Dup` is Copy or Shared: an Affine field does not meet it.
            let fails = |k: Kind| if dup { k == Kind::Affine } else { k != Kind::Copy };
            let shown = fields.into_iter().find(|(_, t, _)| crate::kind::kind_of(self.a, *t).is_some_and(fails));
            if let Some((what, _, span)) = shown {
                let (kind, name) = if dup { ("Affine", foreign::DUP) } else { ("not Copy", foreign::COPY) };
                let d = self.a.diagnostics[at].clone();
                self.a.diagnostics[at] = d.with_note(span, format!("{what} is {kind}, so the type is not {name}"));
            }
        }
    }

    fn cx_for(&self, id: DefId, extra: Vec<GenericDef>, self_ty: Option<TyId>) -> Option<Cx<'p>> {
        let def = &self.a.defs[id.0 as usize];
        let module = self.module(def.module)?;
        Some(Cx {
            m: def.module,
            ast: &module.parsed.ast,
            text: &module.text,
            generics: extra,
            self_ty,
            def: id,
            reach: Some(def.vis),
            locals: HashSet::new(),
        })
    }

    /// The signature of `id`; of a flow, its heading.
    fn lower_def(&mut self, id: DefId) -> Option<FlowHeading> {
        let def = &self.a.defs[id.0 as usize];
        let item_id = def.item?;
        let cx = self.cx_for(id, Vec::new(), None)?;
        match decls::item_kind(&cx.ast.item(item_id).kind) {
            ItemKind::Fn(f) => self.lower_fn(cx, id, f),
            ItemKind::Flow(f) => return self.lower_flow(cx, id, f),
            ItemKind::Struct(s) => {
                let mut cx = cx;
                cx.generics = self.lower_generics(&cx, &s.generics);
                self.member_clashes(id, "field", s.fields.iter().map(|f| &f.name));
                let derives = self.lower_derives(&cx, &s.derives);
                // A field has the visibility of its struct, narrowed by
                // `priv` alone (§15.1, S-35, S-672).
                // It is seen as far as it reaches (S-665).
                let inherited = self.a.def(id).vis;
                let mut fields = Vec::new();
                for f in &s.fields {
                    let vis = if f.vis == Vis::Priv { Vis::Priv } else { inherited };
                    cx.reach = Some(vis);
                    let ty = self.lower_type(&cx, f.ty);
                    fields.push(FieldDef { name: f.name.name.clone(), ty, vis, span: f.span });
                }
                let fields = Fields::Named(fields);
                if let DefKind::Struct(sd) = &mut self.a.defs[id.0 as usize].kind {
                    sd.generics = cx.generics;
                    sd.fields = fields;
                    sd.derives = derives;
                }
            }
            ItemKind::Enum(e) => {
                let mut cx = cx;
                cx.generics = self.lower_generics(&cx, &e.generics);
                self.member_clashes(id, "variant", e.variants.iter().map(|v| &v.name));
                let derives = self.lower_derives(&cx, &e.derives);
                let variants = e
                    .variants
                    .iter()
                    .map(|v| VariantDef {
                        name: v.name.name.clone(),
                        fields: v.fields.iter().map(|&t| self.lower_type(&cx, t)).collect(),
                        span: v.span,
                    })
                    .collect();
                if let DefKind::Enum(ed) = &mut self.a.defs[id.0 as usize].kind {
                    ed.generics = cx.generics;
                    ed.variants = variants;
                    ed.derives = derives;
                }
            }
            ItemKind::TypeAlias { .. } => {
                self.alias_ty(id);
            }
            // A constant is lowered in the order of the declarations.
            ItemKind::OpaqueType { .. } | ItemKind::Const(_) => {}
            ItemKind::Impl(i) => {
                if i.trait_.is_some() {
                    if let Some(dup) = i.trait_.as_ref().and_then(kind_constraint) {
                        self.copy_impl(&cx, item_id, i, dup);
                    }
                    return None;
                }
                let cx = self.impl_cx(cx, i);
                let aliased = self.alias_impl(&cx, i.self_ty);
                let self_ty = cx.self_ty.unwrap_or_else(|| self.a.types.error());
                let (fns, consts) = match &self.a.defs[id.0 as usize].kind {
                    DefKind::Impl(imp) => (imp.fns.clone(), imp.consts.clone()),
                    _ => unreachable!(),
                };
                if let DefKind::Impl(imp) = &mut self.a.defs[id.0 as usize].kind {
                    imp.generics = cx.generics.clone();
                    imp.self_ty = self_ty;
                }
                let (key_def, key_builtin) = self.member_key(id).unwrap_or((None, None));
                // The E0307 of an alias is the error of the heading.
                if !aliased {
                    self.impl_heading(&cx, i, self_ty, key_def.is_some() || key_builtin.is_some());
                }
                // A name the heading reads and the check does not (§18.1,
                // S-689): the members are checked, and read it too (an unknown
                // bound of their generics, an error type of `self`).
                let held = self.a.read_held.contains(&id);
                // The members are named before, with their E0304
                // (`Sema::name_members`), and a constant lowered in the order
                // of the declarations.
                for &sub in fns.iter().chain(&consts) {
                    if held {
                        self.a.read_held.insert(sub);
                    }
                    let sub_item = self.a.defs[sub.0 as usize].item.unwrap();
                    let reach = self.type_vis((key_def, key_builtin)).map(|t| self.member_reach(&cx, sub, t));
                    if let ItemKind::Fn(f) = &cx.ast.item(sub_item).kind {
                        self.lower_fn(Cx { def: sub, reach, ..cx_clone(&cx) }, sub, f);
                    }
                }
            }
            ItemKind::Test { .. } => {}
            _ => {}
        }
        None
    }

    /// The context of the members of the inherent `impl` `i` (its `cx`): its
    /// generics, and its type as `Self` (§2.2). Its heading has no
    /// visibility (§15.1).
    fn impl_cx(&mut self, cx: Cx<'p>, i: &ImplDecl) -> Cx<'p> {
        let mut cx = Cx { reach: None, ..cx };
        cx.generics = self.lower_generics(&cx, &i.generics);
        cx.self_ty = Some(self.lower_type(&cx, i.self_ty));
        cx
    }

    /// E0307 for the type `self_ty` of the inherent `impl` `i` written as it
    /// may not be (§6.3): with no name of a declaration (`keyed` false: a
    /// tuple, an array, `()`, a function type, a parameter; §4.4, R-320), or
    /// with type arguments other than the parameters of the `impl`, each
    /// once in any order (a concrete or compound type, one twice, one left
    /// out; §6.2, S-137), judged as written, of a target of the error type
    /// too. Arguments with an error of a name (its E0302, a name held, §18.1)
    /// are not judged; one of the types stage (an E0417, a length this version
    /// does not compute) is no parameter, and the E0307 of the names stage
    /// comes first.
    fn impl_heading(&mut self, cx: &Cx<'p>, i: &ImplDecl, self_ty: TyId, keyed: bool) {
        let target = cx.ast.ty(i.self_ty);
        let shown = one_line(&src(cx, target.span));
        let named = self.reported.get(&cx.def).is_some_and(|&at| self.a.diagnostics[at].stage != Stage::Types);
        let named = named || self.a.read_held.contains(&cx.def);
        // A scalar (`impl F32`) has no arguments.
        let (head, written): (_, &[TypeId]) = match &target.kind {
            TypeKind::Path { path, args } => (self.a.resolve_path(cx.m, path).ok(), args),
            _ => (None, &[]),
        };
        // An opaque type of `extern` is not judged.
        let opaque = matches!(head, Some(Entity::Def(d))
            if matches!(self.a.def(d).kind, DefKind::Unsupported(Declared::Type | Declared::Block)));
        // A target whose own count of arguments is not the declared one is
        // only its E0412 (§4.5, S-759 (2')): its arguments are not judged.
        let miscounted = head.and_then(|e| self.declared_params(e)).is_some_and(|p| p.len() != written.len());
        let types = &self.a.types;
        let failed = match types.get(self_ty) {
            Ty::Named(_, args) | Ty::Builtin(_, args) => args.iter().any(|&t| types.has_error(t)),
            t => matches!(t, Ty::Error),
        };
        if (named && failed) || opaque || miscounted {
            return;
        }
        // The parameter of the `impl` an argument is: its name alone (`T`, not `T[I32]`).
        let param = |a: TypeId| match &cx.ast.ty(a).kind {
            TypeKind::Path { path, args } if args.is_empty() && path.segments.len() == 1 => {
                cx.generics.iter().position(|g| g.name == path.segments[0].name)
            }
            _ => None,
        };
        let mut seen = vec![false; cx.generics.len()];
        let wrong = written.iter().position(|&a| param(a).is_none_or(|p| std::mem::replace(&mut seen[p], true)));
        let (span, what) = match (keyed, wrong, seen.iter().position(|s| !s)) {
            (false, ..) => (target.span, format!("`{shown}` is not the name of a type declaration")),
            (true, Some(k), _) => {
                let at = cx.ast.ty(written[k]).span;
                let twice = param(written[k]).is_some();
                let how = if twice { "is written twice" } else { "is not a parameter of the `impl`" };
                (at, format!("`{}` {how}", one_line(&src(cx, at))))
            }
            (true, None, Some(g)) => {
                let name = &cx.generics[g].name;
                (target.span, format!("the parameter `{name}` of the `impl` is not an argument of `{shown}`"))
            }
            (true, None, None) => return,
        };
        let rule = "the type of an `impl` is the name of its declaration, with the parameters of the `impl` as its arguments, each once (§4.4, §6.2)";
        let d = Diagnostic::new(Stage::Names, Code::E0307, span, what).with_found(src(cx, span)).with_rule(rule);
        self.report(cx.def, d);
    }

    /// `impl Copy for X` and `impl Dup for X` (E0020, `copy_impl`, §4.6,
    /// S-140), at the form (§18.1: from `impl` to its type). The candidate
    /// takes the whole `impl` out with its doc comments and attributes (the
    /// start of its unit, §18.1), and the note names a field of `X` that does
    /// not meet the constraint ([`Sema::name_non_copy_fields`]). No note when
    /// `X` names no struct or enum (its own error goes with the `impl`).
    fn copy_impl(&mut self, cx: &Cx<'p>, item: onsa_syntax::ast::ItemId, i: &ImplDecl, dup: bool) {
        let span = cx.ast.item(item).span;
        let units = self.module(cx.m).map(|m| &m.parsed.units);
        let unit = units.and_then(|us| us.of(span).map(|u| us.list[u].span.start));
        let fix = Fix::delete("remove the `impl`", Span { start: unit.unwrap_or(span.start), ..span });
        let form = Span { end: cx.ast.ty(i.self_ty).span.end, ..span };
        let Some(at) = self.keep(cx.def, foreign::report(RowId::CopyImpl, cx.text, form, vec![fix])) else { return };
        let TypeKind::Path { path, .. } = &cx.ast.ty(i.self_ty).kind else { return };
        if let Ok(Entity::Def(t)) = self.a.resolve_path(cx.m, path)
            && matches!(self.a.def(t).kind, DefKind::Struct(_) | DefKind::Enum(_))
        {
            self.kind_heads.push((at, t, dup));
        }
    }

    /// E0307 for an `impl` whose type `t` names a type alias (§4.4, S-91,
    /// R-105): the methods of a type are found by the name of its
    /// declaration. The candidate is the name of the type it stands for when
    /// that one is declared in the module, with no type arguments; the `impl`
    /// is lowered for that type all the same. An alias of the error type is
    /// an E0307 too, with no candidate: it stays when the alias is fixed, and
    /// is no use of the error type (§18.1, S-754). Whether `t` names an alias.
    fn alias_impl(&mut self, cx: &Cx<'p>, t: TypeId) -> bool {
        let TypeKind::Path { path, .. } = &cx.ast.ty(t).kind else { return false };
        let Ok(Entity::Def(d)) = self.a.resolve_path(cx.m, path) else { return false };
        if !matches!(self.a.def(d).kind, DefKind::Alias(_)) {
            return false;
        }
        let ty = self.alias_ty(d);
        let shown = src(cx, path.span);
        let mut diag = Diagnostic::new(
            Stage::Names,
            Code::E0307,
            path.span,
            format!("`{shown}` is a type alias; an `impl` names the type it stands for by its declaration (§4.4)"),
        )
        .with_found(shown);
        if let Ty::Named(orig, args) = self.a.types.get(ty)
            && args.is_empty()
            && let def = self.a.def(*orig)
            && def.module == cx.m
            && def.owner.is_none()
        {
            diag = diag.with_fix(Fix::replace(format!("write `{}`", def.name), path.span, def.name.clone()));
        }
        self.report(cx.def, diag);
        true
    }

    /// The associated items of the type of an `impl`: of a user type by its
    /// def, of a builtin type by its key; none for another type.
    fn assoc_table(&mut self, def: Option<DefId>, builtin: Option<TyId>) -> Option<&mut HashMap<String, DefId>> {
        match (def, builtin) {
            (Some(d), _) => Some(self.a.modules.assoc.entry(d).or_default()),
            (None, Some(t)) => Some(self.a.modules.assoc_builtin.entry(t).or_default()),
            _ => None,
        }
    }

    /// How far the member `sub` of an inherent `impl` of a type of `ty_vis`
    /// reaches: the narrower of its visibility and its type's (§15.1, S-665).
    /// A `pub` on it wider than the type is redundant (E0020, S-662).
    // The E0020, reported first, is the one error of the member; an E0303 of
    // a name in its heading comes once it is fixed (S-698).
    fn member_reach(&mut self, cx: &Cx<'p>, sub: DefId, ty_vis: Vis) -> Vis {
        let own = self.a.def(sub).vis;
        let at = self.a.def(sub).item.and_then(|i| cx.ast.item(i).vis_span);
        if let (Vis::Pub, Vis::Default | Vis::Priv, Some(at)) = (own, ty_vis, at) {
            let blanks =
                cx.text[at.end as usize..].len() - cx.text[at.end as usize..].trim_start_matches([' ', '\t']).len();
            let fix = Fix::delete("remove `pub`", Span { end: at.end + blanks as u32, ..at });
            self.report(sub, foreign::report(RowId::ImplMemberPub, cx.text, at, vec![fix]));
        }
        crate::resolve::narrower(own, ty_vis)
    }

    /// The type of the alias `id`, lowered once in the order of the
    /// declarations (`decls`), which lowers what it reads before it: an
    /// alias of a cycle is the error type (E0311), and a body reads the
    /// aliases lowered.
    fn alias_ty(&mut self, id: DefId) -> TyId {
        let DefKind::Alias(current) = self.a.defs[id.0 as usize].kind else { return self.a.types.error() };
        let at = Some(self.a.defs[id.0 as usize].name_span);
        match self.a.decls.lowered.insert(id, false) {
            Some(true) => {
                self.a.decls.lowered.insert(id, true);
                return current;
            }
            Some(false) => onsa_diag::internal::bug(at, "an alias read as it is lowered: a cycle not in the order"),
            None if self.flat.is_empty() => onsa_diag::internal::bug(at, "an alias the signatures did not lower"),
            None => {}
        }
        let ty = match (self.cx_for(id, Vec::new(), None), self.a.defs[id.0 as usize].item) {
            (Some(cx), Some(item)) => match &cx.ast.item(item).kind {
                ItemKind::TypeAlias { ty, .. } => self.lower_type(&cx, *ty),
                _ => self.a.types.error(),
            },
            _ => self.a.types.error(),
        };
        self.a.decls.lowered.insert(id, true);
        self.a.decls.aliases.push(id);
        if let DefKind::Alias(t) = &mut self.a.defs[id.0 as usize].kind {
            *t = ty;
        }
        ty
    }

    fn lower_generics(&mut self, cx: &Cx<'p>, gs: &[GenericParam]) -> Vec<GenericDef> {
        self.heading_clashes(cx.def, cx.m, gs, &cx.generics);
        let mut out = cx.generics.clone();
        // The names of the list, each seen in every bound of it.
        let listed: Vec<(&str, NameKind)> = gs
            .iter()
            .map(|g| (crate::names::param_name(g).name.as_str(), param_kind(g)))
            .chain(cx.generics.iter().map(|g| (g.name.as_str(), NameKind::of_generic(&g.kind))))
            .collect();
        for g in gs {
            let def = match g {
                GenericParam::Type { name, bounds } => {
                    let mut bs = Vec::new();
                    let mut dup = true;
                    let mut unknown = false;
                    // The path of a bound is resolved as any other (§15.1,
                    // R-278): a trait of the prelude, or a kind constraint; a
                    // user trait is an E0200 (S-719), a name of another kind
                    // an E0308 (S-713 (c)).
                    for b in bounds {
                        let n = b.path.segments.last().unwrap();
                        match heading_name(self.a, cx.m, &b.path, (&listed, &cx.locals), cx.self_ty) {
                            Ok((_, Some(Entity::Builtin(Builtin::Kind(Bound::Dup))))) if b.relaxed => dup = false,
                            Ok((_, Some(Entity::Builtin(Builtin::Kind(bound))))) => bs.push(bound),
                            // A trait this version does not take as a bound
                            // (E0200; with an E0308 in the unit, the first by
                            // its place, §18.1, S-731).
                            Ok((_, Some(Entity::Builtin(Builtin::Trait(i))))) => match TRAITS[i as usize].1 {
                                Some(bound) => bs.push(bound),
                                None => self.unsupported(cx.def, n.span, Feature::TraitBounds, &[]),
                            },
                            Ok((NameKind::Trait, _)) => self.unsupported(cx.def, n.span, Feature::TraitBounds, &[]),
                            // A bound with an error of its name is a part of the
                            // declaration not read (§18.1): unknown to its users, its
                            // implicit `Dup` too (S-768 (1)).
                            Ok((kind, _)) => {
                                let d = kind_error(&b.path, kind, "a trait or a kind constraint", b.path.span);
                                self.report(cx.def, d);
                                unknown = true;
                            }
                            // An unknown bound (§18.1, S-689).
                            Err(e) if self.a.unread_path(cx.def, cx.m, &b.path, &e) => unknown = true,
                            Err(e) => {
                                self.report(cx.def, e.into_diagnostic());
                                unknown = true;
                            }
                        }
                    }
                    let kind = GenericKind::Type { bounds: bs, dup, unknown };
                    GenericDef { name: name.name.clone(), span: name.span, kind }
                }
                GenericParam::Const { name, ty } => {
                    let t = self.lower_type(cx, *ty);
                    if !matches!(self.a.types.get(t), Ty::Int(IntKind::U32) | Ty::Error) {
                        self.report(
                            cx.def,
                            Feature::ConstGenericKinds
                                .diagnostic(Stage::Names, cx.ast.ty(*ty).span, &[])
                                .with_fix(Fix::replace("write `U32`", cx.ast.ty(*ty).span, "U32")),
                        );
                    }
                    GenericDef { name: name.name.clone(), span: name.span, kind: GenericKind::Const(t) }
                }
                GenericParam::Effect { name } => {
                    GenericDef { name: name.name.clone(), span: name.span, kind: GenericKind::Effect }
                }
            };
            out.push(def);
        }
        out
    }

    /// The traits at the head of a struct or an enum (§6.4): the closed list
    /// of the derivable ones ([`DERIVABLE`]); `Hash`, `Show` and `Ordinal` are
    /// E0200 in this version (S-13, W5-06), a kind constraint is `copy_bound`
    /// (§4.6) and any other name, or a path of more than one name (S-488),
    /// E0416. The diagnostics of the names stage go before the E0416 of the
    /// types stage (§18.1), whatever the order of the list. `None` when the
    /// list is not known (§18.1, S-460), or holds a name the names stage
    /// holds as an error.
    fn lower_derives(&mut self, cx: &Cx<'p>, derives: &Derives) -> Option<Vec<Derive>> {
        let Derives::Listed(paths) = derives else { return None };
        let mut out = Vec::new();
        let mut underivable = Vec::new();
        for (k, p) in paths.iter().enumerate() {
            let [n] = p.segments.as_slice() else {
                underivable.push(p);
                continue;
            };
            match (DERIVABLE.iter().find(|(name, _)| *name == n.name), kind_constraint(p)) {
                (Some((_, Some(d))), _) => out.push(*d),
                (Some((_, None)), _) => self.unsupported(cx.def, n.span, Feature::Derive, &[&n.name]),
                (None, Some(dup)) => {
                    let d = foreign::report(RowId::CopyBound, cx.text, p.span, vec![drop_derive(cx, paths, k)]);
                    if let Some(at) = self.keep(cx.def, d) {
                        self.kind_heads.push((at, cx.def, dup));
                    }
                }
                (None, None) => underivable.push(p),
            }
        }
        // A name held as an error: the list is not known (§18.1).
        let (held, underivable): (Vec<&Path>, _) =
            underivable.into_iter().partition(|p| self.a.record_if_held(cx.def, cx.m, p));
        for span in underivable.into_iter().map(|p| p.span) {
            let name = src(cx, span);
            let list: Vec<String> = DERIVABLE.iter().map(|(name, _)| format!("`{name}`")).collect();
            self.report(
                cx.def,
                Diagnostic::new(Stage::Types, Code::E0416, span, format!("`{name}` cannot be derived"))
                    .with_found(name)
                    .with_rule(foreign::DERIVE_RULE)
                    .with_rule(format!("the traits a type derives are {}", list.join(", "))),
            );
        }
        held.is_empty().then_some(out)
    }

    /// The effects of a row of a signature or a function type
    /// ([`read_effects`]): its errors are reported, and the lowering goes on.
    fn lower_effects(&mut self, cx: &Cx<'p>, row: Option<&EffectRow>) -> EffectSet {
        let (set, errors) = read_effects(self.a, cx.def, cx.m, (&cx.generics, cx.self_ty, &cx.locals), row);
        for d in errors {
            self.report(cx.def, d);
        }
        set
    }

    /// The parameters but `self`, whose mode the names stage has
    /// (`FnDef::self_mode`).
    fn lower_params(&mut self, cx: &Cx<'p>, params: &[Param], in_impl: bool) -> Vec<ParamSig> {
        let mut out = Vec::new();
        for (i, p) in params.iter().enumerate() {
            match &p.name {
                ParamName::SelfParam(span) => {
                    if i != 0 || !in_impl {
                        self.report(
                            cx.def,
                            Diagnostic::new(
                                Stage::Names,
                                Code::E0002,
                                *span,
                                "`self` must be the first parameter of a method",
                            ),
                        );
                    }
                }
                name => {
                    let n = match name {
                        ParamName::Ident(id) => id.name.clone(),
                        _ => "_".into(),
                    };
                    let ty = match p.ty {
                        Some(t) => self.lower_type(cx, t),
                        None => {
                            self.report(
                                cx.def,
                                Diagnostic::new(
                                    Stage::Names,
                                    Code::E0002,
                                    p.span,
                                    "parameter needs a type (only closures may omit it)",
                                ),
                            );
                            self.a.types.error()
                        }
                    };
                    out.push(ParamSig { name: n, mode: p.mode, ty, span: p.span });
                }
            }
        }
        out
    }

    fn lower_fn(&mut self, cx: Cx<'p>, id: DefId, f: &onsa_syntax::ast::FnDecl) {
        // A heading a syntax error cut (S-59): nothing of it is checked, and
        // its users see an error ([`Analysis::heading_failed`]).
        if self.a.heading_failed(id) {
            let error = self.a.types.error();
            if let DefKind::Fn(fd) = &mut self.a.defs[id.0 as usize].kind {
                fd.ret = error;
            }
            return;
        }
        let mut cx = cx;
        let in_impl = cx.self_ty.is_some();
        let consts = f.generics.iter().filter_map(|g| match g {
            GenericParam::Const { ty, .. } => Some(*ty),
            _ => None,
        });
        let types = f.params.iter().filter_map(|p| p.ty).chain(f.ret).chain(consts).collect();
        let bounds = f.generics.iter().flat_map(|g| match g {
            GenericParam::Type { bounds, .. } => &bounds[..],
            _ => &[],
        });
        let paths = f.effects.iter().flat_map(|r| &r.effects).chain(bounds.map(|b| &b.path)).collect();
        cx.locals = heading_locals(self.a, &cx, (&f.params, &f.generics, false), (types, paths));
        cx.generics = self.lower_generics(&cx, &f.generics);
        let params = self.lower_params(&cx, &f.params, in_impl);
        let ret = match f.ret {
            Some(t) => self.lower_type(&cx, t),
            None => self.a.types.unit(),
        };
        let effects = self.lower_effects(&cx, f.effects.as_ref());
        // §10 rule 1: an `rt` function cannot have `Alloc` in its effect row (E0902).
        if f.rt && effects.alloc {
            let span = f.effects.as_ref().map(|e| e.span).unwrap_or(f.name.span);
            self.report(
                id,
                Diagnostic::new(
                    Stage::Effects,
                    Code::E0902,
                    span,
                    "`rt fn` cannot have `Alloc` in its effect row (§10)",
                ),
            );
        }
        let target = self.a.defs[id.0 as usize].as_fn().is_some_and(|d| d.target);
        if f.body.is_none() && !target {
            self.report(id, Diagnostic::new(Stage::Names, Code::E0002, f.name.span, "function needs a body"));
        }
        if let DefKind::Fn(fd) = &mut self.a.defs[id.0 as usize].kind {
            fd.generics = cx.generics;
            fd.params = params;
            fd.ret = ret;
            fd.effects = effects;
        }
    }
}

fn cx_clone<'p>(cx: &Cx<'p>) -> Cx<'p> {
    Cx {
        m: cx.m,
        ast: cx.ast,
        text: cx.text,
        generics: cx.generics.clone(),
        self_ty: cx.self_ty,
        def: cx.def,
        reach: cx.reach,
        locals: cx.locals.clone(),
    }
}

/// The parameters `params` of a heading of the type, const and effect
/// parameters `generics` (and those of `cx`, of its `impl`), `self` of a
/// method too, of a flow (`flow`) or not: values its whole heading sees
/// (§5.1, S-741, S-733). One that is an E0304 ([`hides`], as the body
/// declares it) is none: its name names what it clashes with (§18.1, S-675).
/// A name of one at the head of a path of `types` (and of the constant
/// expressions in them) or of `paths` (bounds, the effect row) is a use of
/// it, which an E0320 renames (§2.3).
fn heading_locals(
    a: &Analysis,
    cx: &Cx<'_>,
    (params, generics, flow): (&[Param], &[GenericParam], bool),
    (types, paths): (Vec<TypeId>, Vec<&Path>),
) -> HashSet<String> {
    let mut seen: HashMap<&str, Span> = cx.generics.iter().map(|g| (g.name.as_str(), g.span)).collect();
    seen.extend(generics.iter().map(crate::names::param_name).map(|n| (n.name.as_str(), n.span)));
    let mut declared = HashMap::new();
    for p in params {
        let (name, span) = match &p.name {
            ParamName::Ident(i) => (i.name.as_str(), i.span),
            ParamName::SelfParam(s) if cx.self_ty.is_some() => ("self", *s),
            _ => continue,
        };
        let visible = seen.get(name).copied();
        seen.entry(name).or_insert(span);
        let ident = Ident { name: name.to_string(), span };
        if crate::names::hides(a, cx.m, &ident, visible, flow).is_none() {
            declared.insert(name, span);
        }
    }
    let mut names = Vec::new();
    types.into_iter().for_each(|t| crate::names::body::heads(cx.ast, t, &mut names));
    names.extend(paths.into_iter().filter_map(|p| p.segments.first()));
    for n in names {
        if let Some(&decl) = declared.get(n.name.as_str()) {
            a.note_use(decl, n.span);
        }
    }
    declared.into_keys().map(str::to_string).collect()
}

/// The derivable traits (§6.4, S-34), in the order of the spec: the closed
/// list, and what each is in this version (`None`: E0200, S-13, S-145). The
/// one list of their names.
const DERIVABLE: [(&str, Option<Derive>); 8] = [
    ("PartialEq", Some(Derive::PartialEq)),
    ("Eq", Some(Derive::Eq)),
    ("PartialOrd", Some(Derive::PartialOrd)),
    ("Ord", Some(Derive::Ord)),
    ("Hash", None),
    ("Show", None),
    ("Default", Some(Derive::Default)),
    ("Ordinal", None),
];

/// The candidate that takes the trait `k` of the head `paths` out (§4.6,
/// `copy_bound`): with the `+` before it, or after it when it is the first,
/// or with the `:` when it is the only one.
fn drop_derive(cx: &Cx<'_>, paths: &[onsa_syntax::ast::Path], k: usize) -> Fix {
    let p = paths[k].span;
    let span = if k > 0 {
        Span::new(p.file, paths[k - 1].span.end, p.end)
    } else if paths.len() > 1 {
        Span::new(p.file, p.start, paths[1].span.start)
    } else {
        // The `:` before the only trait (blanks may be between them).
        let before = cx.text[..p.start as usize].trim_end();
        let colon = before.strip_suffix(':').map_or(p.start, |b| b.len() as u32);
        Span::new(p.file, colon, p.end)
    };
    Fix::delete(format!("remove `{}`", &cx.text[p.start as usize..p.end as usize]), span)
}

/// The kind constraint `p` names (§4.6), by its spelling: whether it is
/// `Dup` (else `Copy`); none for another name or a path of more names. The
/// one judgment of `copy_bound` and `copy_impl` (`impl Copy for X` is no
/// trait implementation, S-140).
pub(crate) fn kind_constraint(p: &Path) -> Option<bool> {
    let [n] = p.segments.as_slice() else { return None };
    foreign::KIND_CONSTRAINTS.contains(&n.name.as_str()).then(|| n.name == foreign::DUP)
}

/// `s` on one line, for a message: line breaks and runs of blanks are one
/// space.
fn one_line(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn src(cx: &Cx<'_>, span: Span) -> String {
    cx.text[span.start as usize..span.end as usize].to_string()
}

/// The one reading of an effect row (§8.1, S-74, D-08), of a signature, of a
/// function type and of a closure: a single name of an effect variable of
/// `generics`, else a path as [`heading_name`] reads it (§15.1). `Alloc` (the
/// lang item) is read; another effect is an E0200 at its name, but in std,
/// which declares them (S-659); a name of another kind is an E0308 (S-713
/// (b)). A name not found is its E0302, with the `use` of the effect std
/// declares of that name as the candidate (S-659 (3)); a name the check does
/// not read is left out with no diagnostic (§18.1; read by `def`,
/// [`Analysis::unread_path`]). The errors go back to the caller, which
/// reports them.
// The effects read stay when a name held as an error is left out, as an
// unknown effect of an open row, and the check goes on (§18.1, S-691).
// A local it sees (`locals`, S-738) is a value, no effect.
pub(crate) fn read_effects(
    a: &mut Analysis,
    def: DefId,
    from: crate::ModId,
    (generics, self_ty, locals): (&[GenericDef], Option<TyId>, &HashSet<String>),
    row: Option<&EffectRow>,
) -> (EffectSet, Vec<Diagnostic>) {
    let mut set = EffectSet::default();
    let mut errors = Vec::new();
    let listed: Vec<(&str, NameKind)> =
        generics.iter().map(|g| (g.name.as_str(), NameKind::of_generic(&g.kind))).collect();
    for p in row.map_or(&[][..], |r| &r.effects[..]) {
        let n = p.segments.last().unwrap();
        let var = generics.iter().position(|g| g.name == n.name && matches!(g.kind, GenericKind::Effect));
        if let (1, Some(i)) = (p.segments.len(), var) {
            a.note_use(generics[i].span, n.span);
            set.vars.push(i as u32);
            continue;
        }
        match heading_name(a, from, p, (&listed, locals), self_ty) {
            Ok((_, Some(Entity::Def(d)))) if Some(d) == a.alloc => set.alloc = true,
            Ok((_, Some(Entity::Def(d))))
                if matches!(a.def(d).kind, DefKind::Effect { .. }) && a.modules.is_std(from) =>
            {
                set.other.push(n.name.clone());
            }
            // Another effect (of a user's `effect`, S-719, E0200); or a name
            // that is no effect (`uses {I32}`, `uses {T}`). With both in a
            // unit, the first by its place is reported (§18.1, S-731).
            Ok((kind, _)) => {
                errors.push(match kind {
                    NameKind::Effect => Feature::Effects.diagnostic(Stage::Names, n.span, &[&n.name]),
                    kind => kind_error(p, kind, "an effect", p.span),
                });
                set.other.push(n.name.clone());
            }
            Err(e) if a.unread_path(def, from, p, &e) => {}
            Err(e) => {
                let fix = match (&e, p.segments.as_slice()) {
                    (crate::ResolveError::NotFound { .. }, [_]) => {
                        a.modules.std_effect_use(from, &n.name, (&a.prelude, &a.defs, &a.builtin_key))
                    }
                    _ => None,
                };
                let d = e.into_diagnostic();
                errors.push(match fix {
                    Some(fix) => d.with_fix(fix),
                    None => d,
                });
            }
        }
    }
    (set, errors)
}

/// The kind of what the path `p` of a bound or an effect row names (§15.1),
/// and what it names but a parameter of the heading of `listed` (the names a
/// heading binds that are no item of a module, with their kinds, and the
/// values `locals` the place sees, [`Cx::locals`]) and an
/// associated name of a builtin type: through `Self` (`self_ty`) and the
/// aliases ([`Analysis::path_end`]). A parameter of a list has no members
/// (the E0302 of its head, as in a body), a local neither (its E0308).
fn heading_name(
    a: &Analysis,
    from: ModId,
    p: &Path,
    (listed, locals): (&[(&str, NameKind)], &HashSet<String>),
    self_ty: Option<TyId>,
) -> Result<(NameKind, Option<Entity>), crate::ResolveError> {
    let head = &p.segments[0];
    let local = locals.contains(&head.name).then_some(NameKind::Local);
    if let Some(kind) = local.or_else(|| listed.iter().find(|(n, _)| *n == head.name).map(|&(_, k)| k)) {
        return match &p.segments[1..] {
            [] => Ok((kind, None)),
            [next, ..] if kind == NameKind::Local => {
                Err(crate::ResolveError::NotANamespace { name: head.name.clone(), span: next.span, kind: Some(kind) })
            }
            _ => Err(crate::ResolveError::NotFound { name: head.name.clone(), span: head.span }),
        };
    }
    let end = a.path_end(from, p, self_ty)?;
    let entity = match end {
        crate::names::PathEnd::Entity(e) => Some(e),
        crate::names::PathEnd::Builtin { .. } => None,
    };
    Ok((end.kind(a, p.span), entity))
}

/// E0308 for the path `p` at `span`, of the kind `kind`, where `want` is
/// (§15.1): the one form of a signature.
fn kind_error(p: &Path, kind: NameKind, want: &'static str, span: Span) -> Diagnostic {
    let shown = p.segments.iter().map(|s| s.name.as_str()).collect::<Vec<_>>().join(".");
    crate::ResolveError::Kind { shown, span, kind, want }.into_diagnostic()
}

/// The kind of a parameter of a list of a heading (§15.1).
fn param_kind(g: &GenericParam) -> NameKind {
    match g {
        GenericParam::Type { .. } => NameKind::Type,
        GenericParam::Const { .. } => NameKind::ConstParam,
        GenericParam::Effect { .. } => NameKind::Effect,
    }
}
