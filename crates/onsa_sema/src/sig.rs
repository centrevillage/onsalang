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
    Ast, Attr, AttrArg, Derives, EffectRow, ExprKind, GenericParam, ItemKind, Lit, Mode, Param, ParamName, Path,
    TypeId, TypeKind, UnOp, Vis,
};
use onsa_syntax::foreign::{self, RowId};

use crate::def::*;
use crate::resolve::{Builtin, Entity};
use crate::ty::*;
use crate::{Analysis, Module, Package, flatten};
mod flow_sig;
mod generated;
mod types;

use flow_sig::FlowHeading;

pub(crate) use types::lower_type_in_body;

pub(crate) struct Sema<'p> {
    pub(crate) a: &'p mut Analysis,
    pub(crate) flat: Vec<&'p Package>,
    /// Defs that already have a diagnostic, and its index in the
    /// diagnostics (P-01: one error per item, [`Sema::report`]).
    reported: HashMap<DefId, usize>,
    /// Aliases being expanded (cycle guard).
    expanding: HashSet<DefId>,
    /// The `copy_bound` diagnostics reported (their index in the
    /// diagnostics), their type and whether the constraint is `Dup`: once
    /// every signature is lowered, the note names a field that does not meet
    /// it ([`Sema::name_non_copy_fields`], §4.6).
    kind_heads: Vec<(usize, DefId, bool)>,
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
}

pub(crate) fn collect_and_lower(pkg: &Package) -> Analysis {
    let mut a = Analysis::default();
    let mut s = Sema::new(&mut a, flatten(pkg));
    crate::names::collect_names(&mut s);
    let flows = s.lower_signatures();
    s.lower_generated(flows);
    s.fail_ungenerated();
    s.name_non_copy_fields();
    a
}

impl<'p> Sema<'p> {
    fn new(a: &'p mut Analysis, flat: Vec<&'p Package>) -> Self {
        Sema { a, flat, reported: HashMap::new(), expanding: HashSet::new(), kind_heads: Vec::new() }
    }

    pub(crate) fn module(&self, m: ModId) -> Option<&'p Module> {
        let info = self.a.modules.get(m);
        self.flat.get(info.pkg).and_then(|p| info.module.and_then(|i| p.modules.get(i)))
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

    /// The stage of the types of the signatures: every def, in the order of
    /// the defs. The headings of the flows it lowered, for the next stage.
    fn lower_signatures(&mut self) -> Vec<FlowHeading> {
        let n = self.a.defs.len();
        let mut flows = Vec::new();
        for i in 0..n {
            let id = DefId(i as u32);
            // Lowered with their owner (impl / flow), or an E0200 (S-224).
            if self.a.defs[i].owner.is_some() || matches!(self.a.defs[i].kind, DefKind::Unsupported) {
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
        })
    }

    /// The signature of `id`; of a flow, its heading.
    fn lower_def(&mut self, id: DefId) -> Option<FlowHeading> {
        let def = &self.a.defs[id.0 as usize];
        let item_id = def.item?;
        let cx = self.cx_for(id, Vec::new(), None)?;
        let item = cx.ast.item(item_id);
        let mut kind = &item.kind;
        if let ItemKind::Target(inner) = kind {
            kind = inner;
        }
        match kind {
            ItemKind::Fn(f) => self.lower_fn(cx, id, f),
            ItemKind::Flow(f) => return self.lower_flow(cx, id, f),
            ItemKind::Struct(s) => {
                let mut cx = cx;
                cx.generics = self.lower_generics(&cx, &s.generics);
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
            ItemKind::OpaqueType { .. } => {}
            ItemKind::Const(c) => {
                let ty = self.lower_type(&cx, c.ty);
                if let DefKind::Const(cd) = &mut self.a.defs[id.0 as usize].kind {
                    cd.ty = ty;
                }
            }
            ItemKind::Impl(i) => {
                if i.trait_.is_some() {
                    return None;
                }
                // The heading of an `impl` has no visibility (§15.1).
                let mut cx = Cx { reach: None, ..cx };
                cx.generics = self.lower_generics(&cx, &i.generics);
                let self_ty = self.lower_type(&cx, i.self_ty);
                let (fns, consts) = match &self.a.defs[id.0 as usize].kind {
                    DefKind::Impl(imp) => (imp.fns.clone(), imp.consts.clone()),
                    _ => unreachable!(),
                };
                if let DefKind::Impl(imp) = &mut self.a.defs[id.0 as usize].kind {
                    imp.generics = cx.generics.clone();
                    imp.self_ty = self_ty;
                }
                // Associated items are keyed by the type's def (or the builtin TyId).
                let key_def = match self.a.types.get(self_ty) {
                    Ty::Named(d, _) => Some(*d),
                    _ => None,
                };
                let key_builtin = match self.a.types.get(self_ty) {
                    Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char => Some(self_ty),
                    Ty::Builtin(b, _) => self.a.builtin_key.get(b).copied(),
                    _ => None,
                };
                if key_def.is_none() && key_builtin.is_none() && !matches!(self.a.types.get(self_ty), Ty::Error) {
                    let span = cx.ast.ty(i.self_ty).span;
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Names,
                            Code::E0302,
                            span,
                            "`impl` needs a struct, enum, or builtin type",
                        ),
                    );
                }
                // A name the heading reads and the check does not (§18.1,
                // S-689): the members are checked, and read it too (an unknown
                // bound of their generics, an error type of `self`).
                let held = self.a.read_held.contains(&id);
                for &sub in fns.iter().chain(&consts) {
                    if held {
                        self.a.read_held.insert(sub);
                    }
                    let sub_item = self.a.defs[sub.0 as usize].item.unwrap();
                    let ty_vis = key_def.map(|d| self.a.def(d).vis).or(key_builtin.map(|_| Vis::Pub));
                    let reach = ty_vis.map(|t| self.member_reach(&cx, sub, t));
                    let sub_cx =
                        Cx { generics: cx.generics.clone(), self_ty: Some(self_ty), def: sub, reach, ..cx_clone(&cx) };
                    match &cx.ast.item(sub_item).kind {
                        ItemKind::Fn(f) => self.lower_fn(sub_cx, sub, f),
                        ItemKind::Const(c) => {
                            let ty = self.lower_type(&sub_cx, c.ty);
                            if let DefKind::Const(cd) = &mut self.a.defs[sub.0 as usize].kind {
                                cd.ty = ty;
                            }
                        }
                        _ => {}
                    }
                    let name = self.a.defs[sub.0 as usize].name.clone();
                    let name_span = self.a.defs[sub.0 as usize].name_span;
                    let table = match (key_def, key_builtin) {
                        (Some(d), _) => self.a.modules.assoc.entry(d).or_default(),
                        (None, Some(t)) => self.a.modules.assoc_builtin.entry(t).or_default(),
                        _ => continue,
                    };
                    if let Some(prev) = table.get(&name) {
                        let prev_span = self.a.defs[prev.0 as usize].name_span;
                        self.report(
                            sub,
                            Diagnostic::new(
                                Stage::Names,
                                Code::E0304,
                                name_span,
                                format!("`{name}` is defined twice for this type"),
                            )
                            .with_note(prev_span, "first defined here"),
                        );
                    } else {
                        table.insert(name, sub);
                    }
                }
            }
            ItemKind::Test { .. } => {}
            _ => {}
        }
        None
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

    fn alias_ty(&mut self, id: DefId) -> TyId {
        let current = match &self.a.defs[id.0 as usize].kind {
            DefKind::Alias(t) => *t,
            _ => return self.a.types.error(),
        };
        if !matches!(self.a.types.get(current), Ty::Error) {
            return current;
        }
        if !self.expanding.insert(id) {
            let span = self.a.defs[id.0 as usize].name_span;
            self.report(id, Diagnostic::new(Stage::Names, Code::E0310, span, "type alias refers to itself"));
            return self.a.types.error();
        }
        let ty = match (self.cx_for(id, Vec::new(), None), self.a.defs[id.0 as usize].item) {
            (Some(cx), Some(item)) => match &cx.ast.item(item).kind {
                ItemKind::TypeAlias { ty, .. } => self.lower_type(&cx, *ty),
                _ => self.a.types.error(),
            },
            _ => self.a.types.error(),
        };
        self.expanding.remove(&id);
        if let DefKind::Alias(t) = &mut self.a.defs[id.0 as usize].kind {
            *t = ty;
        }
        ty
    }

    fn lower_generics(&mut self, cx: &Cx<'p>, gs: &[GenericParam]) -> Vec<GenericDef> {
        let mut out = cx.generics.clone();
        // The names of the list, each seen in every bound of it.
        let listed: Vec<&str> = gs
            .iter()
            .map(|g| match g {
                GenericParam::Type { name, .. } | GenericParam::Const { name, .. } | GenericParam::Effect { name } => {
                    name.name.as_str()
                }
            })
            .chain(cx.generics.iter().map(|g| g.name.as_str()))
            .collect();
        for g in gs {
            let def = match g {
                GenericParam::Type { name, bounds } => {
                    let mut bs = Vec::new();
                    let mut dup = true;
                    let mut unknown = false;
                    // The path of a bound is resolved as any other (§15.1,
                    // R-278): a trait of the prelude, or a kind constraint.
                    for b in bounds {
                        let n = b.path.segments.last().unwrap();
                        if heading_binds(&b.path, &listed, cx.self_ty.is_some()) {
                            self.unsupported(cx.def, n.span, Feature::TraitBounds, &[]);
                            continue;
                        }
                        match self.a.resolve_path(cx.m, &b.path) {
                            Ok(Entity::Builtin(Builtin::Kind(Bound::Dup))) if b.relaxed => dup = false,
                            Ok(Entity::Builtin(Builtin::Kind(bound))) => bs.push(bound),
                            Ok(Entity::Builtin(Builtin::Trait(i))) => match TRAITS[i as usize].1 {
                                Some(bound) => bs.push(bound),
                                None => self.unsupported(cx.def, n.span, Feature::TraitBounds, &[]),
                            },
                            // A name that is no trait (`T: I32`), or a user
                            // trait: the E0308 of the kinds of names is W4-04's
                            // (also for a parameter, above).
                            Ok(_) => self.unsupported(cx.def, n.span, Feature::TraitBounds, &[]),
                            // An unknown bound (§18.1, S-689).
                            Err(e) if self.a.unread_path(cx.def, cx.m, &b.path, &e) => unknown = true,
                            Err(e) => self.report(cx.def, e.into_diagnostic()),
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
            match DERIVABLE.iter().find(|(name, _)| *name == n.name) {
                Some((_, Some(d))) => out.push(*d),
                Some((_, None)) => self.unsupported(cx.def, n.span, Feature::Derive, &[&n.name]),
                None if foreign::KIND_CONSTRAINTS.contains(&n.name.as_str()) => {
                    let d = foreign::report(RowId::CopyBound, cx.text, p.span, vec![drop_derive(cx, paths, k)]);
                    if let Some(at) = self.keep(cx.def, d) {
                        self.kind_heads.push((at, cx.def, n.name == foreign::DUP));
                    }
                }
                None => underivable.push(p),
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
        let (set, errors) = read_effects(self.a, cx.def, cx.m, (&cx.generics, cx.self_ty.is_some()), row);
        for d in errors {
            self.report(cx.def, d);
        }
        set
    }

    fn lower_params(&mut self, cx: &Cx<'p>, params: &[Param], in_impl: bool) -> (Option<Mode>, Vec<ParamSig>) {
        let mut self_mode = None;
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
                    self_mode = Some(p.mode);
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
        (self_mode, out)
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
        cx.generics = self.lower_generics(&cx, &f.generics);
        let in_impl = cx.self_ty.is_some();
        let (self_mode, params) = self.lower_params(&cx, &f.params, in_impl);
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
            fd.self_mode = self_mode;
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
    }
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

fn src(cx: &Cx<'_>, span: Span) -> String {
    cx.text[span.start as usize..span.end as usize].to_string()
}

/// The one reading of an effect row (§8.1, S-74, D-08), of a signature, of a
/// function type and of a closure: a single name of an effect variable of
/// `generics`, else a path resolved as any other (§15.1). `Alloc` (the lang
/// item) is read; another effect is an E0200 at its name, but in std, which
/// declares them (S-659); so is a name of another kind, also a parameter of
/// `generics` or a `Self` that is seen (the bool, [`heading_binds`]). A name
/// not found is its E0302, with the `use` of the effect std declares of that
/// name as the candidate (S-659 (3)); a name
/// the check does not read is left out with no diagnostic (§18.1; read by
/// `def`, [`Analysis::unread_path`]). The errors go back to the caller,
/// which reports them.
// The effects read stay when a name held as an error is left out, as an
// unknown effect of an open row, and the check goes on (§18.1, S-691).
pub(crate) fn read_effects(
    a: &mut Analysis,
    def: DefId,
    from: crate::ModId,
    (generics, self_seen): (&[GenericDef], bool),
    row: Option<&EffectRow>,
) -> (EffectSet, Vec<Diagnostic>) {
    let mut set = EffectSet::default();
    let mut errors = Vec::new();
    let names: Vec<&str> = generics.iter().map(|g| g.name.as_str()).collect();
    for p in row.map_or(&[][..], |r| &r.effects[..]) {
        let n = p.segments.last().unwrap();
        let var = generics.iter().position(|g| g.name == n.name && matches!(g.kind, GenericKind::Effect));
        if let (1, Some(i)) = (p.segments.len(), var) {
            set.vars.push(i as u32);
            continue;
        }
        let found = if heading_binds(p, &names, self_seen) { None } else { Some(a.resolve_path(from, p)) };
        match found {
            Some(Ok(Entity::Def(d))) if Some(d) == a.alloc => set.alloc = true,
            Some(Ok(Entity::Def(d))) if matches!(a.def(d).kind, DefKind::Effect { .. }) && a.modules.is_std(from) => {
                set.other.push(n.name.clone());
            }
            // Another effect; or a name that is no effect (`uses {I32}`,
            // `uses {T}`), whose E0308 of the kinds of names is W4-04's.
            None | Some(Ok(_)) => {
                errors.push(Feature::Effects.diagnostic(Stage::Names, n.span, &[&n.name]));
                set.other.push(n.name.clone());
            }
            Some(Err(e)) if a.unread_path(def, from, p, &e) => {}
            Some(Err(e)) => {
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

/// Whether the head of `p` is a name a heading binds that is no item of a
/// module: one of `names` (the generic parameters seen), or `Self` where it
/// is seen (`self_seen`: in an `impl`, §2.2). It is found, so no E0302; in a
/// bound or an effect row it is a name of another kind (E0200 until the
/// E0308 of the kinds of names, W4-04).
fn heading_binds(p: &Path, names: &[&str], self_seen: bool) -> bool {
    let head = p.segments[0].name.as_str();
    names.contains(&head) || (self_seen && head == "Self")
}
