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
//! `generated`; and of the lowering of a def, `heading` (the lists of
//! parameters with their bounds, the values a heading binds and the effect
//! rows), `derives` (the traits at the head of a struct or an enum) and
//! `impls` (an inherent `impl`, the heading of a trait `impl`, and `impl Copy`
//! and `impl Dup`).

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::timing::{Phase, phase};
use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::FloatRange;
use onsa_syntax::ast::{
    Ast, Attr, AttrArg, Derives, EffectRow, ExprKind, GenericParam, Ident, ImplDecl, ItemKind, Lit, Mode, Param,
    ParamName, Path, TypeId, TypeKind, UnOp, Vis,
};
use onsa_syntax::foreign::{self, RowId};

use crate::def::*;
use crate::names::body::clock_after;
use crate::resolve::{Builtin, Entity, NameKind};
use crate::ty::*;
use crate::{Analysis, Module, Package, flatten};
mod bound_list;
mod decls;
mod derives;
mod flow_sig;
mod generated;
mod heading;
mod impls;
#[cfg(test)]
mod tests;
mod types;
mod wellformed;

use flow_sig::FlowHeading;
use heading::{heading_locals, kind_error, local_member};

pub(crate) use decls::{Decls, item_kind};
pub(crate) use derives::kind_constraint;
pub(crate) use heading::read_effects;
pub(crate) use types::lower_type_in_body;
pub(crate) use wellformed::{Pos, no_kind_argument, second_class};

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
    /// A type of a flow body, whose constant expressions may hold what
    /// only a flow body holds (§11.1).
    flow: bool,
}

impl Cx<'_> {
    /// Whether `name` is one of [`Self::locals`], a value (S-729).
    fn is_local(&self, name: &str) -> bool {
        self.locals.contains(name)
    }

    /// The parameter in scope named `name`: its index in [`Self::generics`].
    fn param(&self, name: &str) -> Option<usize> {
        self.generics.iter().position(|g| g.name == name)
    }

    /// What a constant expression reads with ([`crate::constarg::expr`]).
    fn scope(&self) -> (&[GenericDef], Option<TyId>, bool) {
        (&self.generics, self.self_ty, self.flow)
    }

    /// Whether a constant expression starts at one of [`Self::locals`]: a
    /// value, no constant (E0417, §4.5).
    fn local(&self) -> impl Fn(onsa_syntax::ast::ExprId) -> bool + '_ {
        |e| crate::constarg::path_of(self.ast, e).is_some_and(|p| self.is_local(&p.segments[0].name))
    }
}

/// The names and the signatures of `pkg` on `a`, from its start: the
/// walks of the kinds learn nothing of the declarations of this run until
/// they are lowered (`walk::Known`).
pub(crate) fn collect_and_lower(pkg: &Package, mut a: Analysis) -> Result<Analysis, crate::base::Fallback> {
    a.known.ready = false;
    let mut s = Sema::new(&mut a, flatten(pkg));
    let names = phase(Phase::Names);
    crate::names::collect_names(&mut s);
    drop(names);
    let _signatures = phase(Phase::Signatures);
    let flows = s.lower_signatures()?;
    crate::prim::record(s.a);
    let pairs = s.lower_generated(&flows);
    s.a.known.ready = true;
    s.wellformed();
    s.check_generated(flows, pairs);
    s.fail_ungenerated();
    s.name_non_copy_fields();
    Ok(a)
}

impl<'p> Sema<'p> {
    fn new(a: &'p mut Analysis, flat: Vec<&'p Package>) -> Self {
        Sema {
            a,
            flat,
            reported: HashMap::default(),
            kind_heads: Vec::new(),
            alias_at: HashMap::default(),
            misfit: HashMap::default(),
        }
    }

    pub(crate) fn module(&self, m: ModId) -> Option<&'p Module> {
        self.a.modules.source(&self.flat, m)
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
        self.a.defs.push(def);
        let id = DefId(self.a.defs.len() as u32 - 1);
        if let Some(f) = failed {
            self.a.failed.insert(id, f);
        }
        if let Some(span) =
            module.filter(|_| failed.is_none()).and_then(|(i, m)| crate::flow_syntax::first_mem(&m.parsed, i))
        {
            // `@mem` (§12.4) until W9-06: E0200, and the def is not checked
            // further (as a cut heading).
            self.unsupported(id, span, Feature::MemStorage, &[]);
            self.a.failed.insert(id, onsa_syntax::ast::Failed::Heading);
        }
        id
    }

    // ------------------------------------------------------------ lowering

    /// The stage of the types of the signatures: the aliases and the
    /// constants in the order of the declarations (`decls`), then every def
    /// it runs on, in the order of the defs. The headings of the flows it
    /// lowered, for the next stage.
    fn lower_signatures(&mut self) -> Result<Vec<FlowHeading>, crate::base::Fallback> {
        self.order_declarations()?;
        let mut flows = Vec::new();
        for id in self.a.new_defs() {
            let def = self.a.def(id);
            // Lowered with their owner (impl / flow), or an E0200 (S-224).
            if def.owner.is_some() || matches!(def.kind, DefKind::Unsupported(_)) {
                continue;
            }
            let _scope = onsa_diag::internal::item_scope(def.span);
            flows.extend(self.lower_def(id));
        }
        Ok(flows)
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
            locals: HashSet::default(),
            flow: false,
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
            ItemKind::Impl(i) => self.lower_impl(cx, id, item_id, i),
            ItemKind::Test { .. } => {}
            _ => {}
        }
        None
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
                    // The clock of an input of a flow only (§11.3, S-368).
                    if let Some(c) = &p.clock {
                        self.report(cx.def, clock_after(cx.ast, cx.text, p.ty, c));
                    }
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
        if let Some(c) = &f.ret_clock {
            self.report(id, clock_after(cx.ast, cx.text, f.ret, c));
        }
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
        flow: cx.flow,
    }
}

/// `s` on one line, for a message: line breaks and runs of blanks are one
/// space.
fn one_line(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn src(cx: &Cx<'_>, span: Span) -> String {
    cx.text[span.start as usize..span.end as usize].to_string()
}
