//! The well-formedness of the types written (R-37, R-135; §4.4, §4.5, §5.3).
//!
//! Once every signature and the items flows generate are lowered, and the
//! kinds are known, each type written is judged from its root, its place, by
//! the place and the head of each part: a second-class type (`Span`, a
//! generated `Out`) stands at an argument only (E0710), and a type argument
//! meets the requirements of its parameter (E0416: the element of `Buf` /
//! `Span`, the bounds and the implicit `Dup` of a declared type). The roots
//! are the fields, the parameters and the return types, the types of the
//! constants, the right sides of the aliases and the targets of the inherent
//! `impl`s; a type of a body is judged as it is lowered
//! (`lower_type_in_body`).
//!
//! The parts written are walked with the types lowered. An alias is judged
//! at its right side, before the types that name it: where it is named, its
//! parts meet the requirements already, and an alias with an error is the
//! error type (S-757). Its second-class parts are judged where it is named.

use super::*;
use crate::bounds::Bounds;
use crate::requirement::{Required, Requirement, first_unmet, unmet_error, unmet_rules};

/// The place of a root (§5.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Pos {
    /// An argument with its mode: of a function, a function type, an
    /// anonymous function.
    Arg(Mode),
    /// A type of a body (`let`, `var`, `as`): a borrow binding takes a
    /// `Span` (§5.4); the other second-class places of a body are the check
    /// of the modes'.
    Bind,
    /// A field, a return type (of an anonymous function too), a constant,
    /// the target of an `impl`.
    Other,
    /// The right side of an alias: its second-class parts are judged where
    /// it is named (S-757).
    Alias,
}

/// How deep a part is below its root: the root, the element of an array at
/// the root (the planar `[Span[T]; N]`, §5.3), or deeper.
const ROOT: u8 = 0;
const PLANAR: u8 = 1;
const INSIDE: u8 = 2;

/// The place of a type argument of a `?Escape` parameter (§4.5, S-927): a
/// `Span` or a planar array stands there, as at a borrow binding.
const LIFTED: (Pos, u8) = (Pos::Bind, ROOT);

/// The parts of the type `shape` at `at`, each at its place: the element of
/// an array at the root is planar, the parameters of a function type are
/// arguments, a type argument of a `?Escape` parameter is [`LIFTED`] (in the
/// right side of an alias, every part is of the alias).
fn places(a: &Analysis, shape: &Ty, at: (Pos, u8)) -> Vec<(TyId, (Pos, u8))> {
    let inner = if at.0 == Pos::Alias { (Pos::Alias, INSIDE) } else { (Pos::Other, INSIDE) };
    match shape {
        Ty::Array(e, _) if at.1 == ROOT => vec![(*e, (at.0, PLANAR))],
        Ty::Array(e, _) => vec![(*e, inner)],
        Ty::Named(d, ts) if at.0 != Pos::Alias => {
            let lifted = |k| a.def(*d).generics().get(k).is_some_and(GenericDef::lifts_escape);
            ts.iter().enumerate().map(|(k, &t)| (t, if lifted(k) { LIFTED } else { inner })).collect()
        }
        Ty::Tuple(ts) | Ty::Named(_, ts) | Ty::Builtin(_, ts) => ts.iter().map(|&t| (t, inner)).collect(),
        Ty::Fn(f) if at.0 == Pos::Alias => f.params.iter().map(|p| (p.1, inner)).chain([(f.ret, inner)]).collect(),
        Ty::Fn(f) => f.params.iter().map(|&(m, t)| (t, (Pos::Arg(m), ROOT))).chain([(f.ret, inner)]).collect(),
        _ => Vec::new(),
    }
}

/// The fields of a struct and the payloads of the variants of an enum: each
/// as written, as lowered, and its slot.
pub(super) fn payloads(item: &ItemKind, def: &DefKind) -> Vec<(TypeId, TyId, Slot)> {
    match (item, def) {
        (ItemKind::Struct(s), DefKind::Struct(StructDef { fields: Fields::Named(fs), .. })) => {
            s.fields.iter().zip(fs).enumerate().map(|(k, (f, l))| (f.ty, l.ty, Slot::Field(k))).collect()
        }
        (ItemKind::Enum(e), DefKind::Enum(ed)) => {
            let variants = e.variants.iter().zip(&ed.variants).enumerate();
            let fields =
                variants.flat_map(|(n, (v, l))| v.fields.iter().zip(&l.fields).enumerate().map(move |f| (n, f)));
            fields.map(|(n, (k, (&t, &l)))| (t, l, Slot::Variant(n, k))).collect()
        }
        _ => Vec::new(),
    }
}

/// Whether the head of `t` is second-class (§5.3): `Span`, a generated `Out`
/// (§11.6; `In` from W7-03), a `?Escape` type parameter in scope (§4.5). The
/// one place of the question.
pub(crate) fn second_class(under: &Bounds, t: TyId) -> bool {
    match under.a.types.get(t) {
        Ty::Builtin(BuiltinTy::Span, _) => true,
        Ty::Param(i) => under.generics.get(*i as usize).is_some_and(GenericDef::lifts_escape),
        Ty::Named(d, _) => matches!(&under.a.def(*d).kind, DefKind::Struct(s) if s.flow_ty == Some(FlowTy::Out)),
        _ => false,
    }
}

/// Whether the second-class `ty` stands in its place `at` (§5.3, §5.4):
/// an argument not `move` (S-758), the element of a planar one, a borrow
/// binding of a body. A `?Escape` type parameter stands where a `Span` does
/// (S-928).
fn fits(a: &Analysis, ty: TyId, at: (Pos, u8)) -> bool {
    let span = matches!(a.types.get(ty), Ty::Builtin(BuiltinTy::Span, _) | Ty::Param(_));
    match at {
        (Pos::Alias, _) => true,
        (Pos::Arg(m), ROOT) => m != Mode::Move,
        // S-770: a planar array is of `Span` elements only, as
        // §5.3 lists it (`[voice.Out; 2]` is an E0710).
        (Pos::Arg(m), PLANAR) => m != Mode::Move && span,
        (Pos::Bind, ROOT | PLANAR) => span,
        _ => false,
    }
}

/// Whether a second-class part of `ty` stands out of its place, `ty` at
/// `at`: what its E0710 is (a type is a graph of shared parts: each is
/// looked at once, `seen`).
fn holds(under: &Bounds, seen: &mut HashMap<(TyId, Pos, u8), bool>, ty: TyId, at: (Pos, u8)) -> bool {
    if let Some(&h) = seen.get(&(ty, at.0, at.1)) {
        return h;
    }
    let a = under.a;
    let parts = places(a, a.types.get(ty), at);
    let h = second_class(under, ty) && !fits(a, ty, at) || parts.into_iter().any(|(t, at)| holds(under, seen, t, at));
    seen.insert((ty, at.0, at.1), h);
    h
}

/// Whether the type argument `t`, written or decided by the inference, of a
/// parameter `?Escape` or not (`lifted`), stands out of its place: a parameter
/// with no mark takes no second-class type and none that holds one out of the
/// arguments of a function type, a type with no kind; a `?Escape` one takes
/// a `Span` and a planar array (§4.5, §4.6; S-766, S-771, S-862, S-927). The
/// one judgment of both.
pub(crate) fn no_kind_argument(under: &Bounds, t: TyId, lifted: bool) -> bool {
    holds(under, &mut HashMap::default(), t, if lifted { LIFTED } else { ARGUMENT })
}

/// The place of a type argument: inside another type.
const ARGUMENT: (Pos, u8) = (Pos::Other, INSIDE);

/// What [`Sema::required`] asks of an argument: the bound of the element of
/// a builtin type, or the requirements of the parameter `k` of a declared one.
#[derive(Clone)]
enum Want {
    Element(Bound, Required),
    Param(DefId, usize),
}

/// A part of a type as written: here at a place of the source, named by an
/// alias (read as its right side is, the error type where it has an error,
/// S-757), or else not written (`Self`, a part of those). The requirements
/// of a part not written here are judged where it is declared.
#[derive(Clone, Copy)]
enum Written {
    Here(TypeId),
    Alias(DefId),
    Elsewhere,
}

/// Where the type lowered of a root is kept ([`Sema::unread`]).
#[derive(Clone, Copy)]
pub(super) enum Slot {
    Field(usize),
    Variant(usize, usize),
    Param(usize),
    Ret,
    Const,
    Target,
    Input(usize),
    Out,
}

impl<'p> Sema<'p> {
    /// The stage (`collect_and_lower`): the aliases first, each after those
    /// its right side names, then the roots of every def.
    pub(super) fn wellformed(&mut self) {
        for d in std::mem::take(&mut self.a.decls.aliases) {
            self.wellformed_alias(d);
        }
        for d in self.a.new_defs() {
            self.wellformed_def(d);
        }
    }

    /// The right side of the alias `d`: with an error, the alias is the
    /// error type to the types that name it after (S-757).
    fn wellformed_alias(&mut self, d: DefId) {
        let (Some(cx), Some(item)) = (self.cx_for(d, Vec::new(), None), self.a.def(d).item) else { return };
        let (ItemKind::TypeAlias { ty, .. }, DefKind::Alias(lowered)) =
            (decls::item_kind(&cx.ast.item(item).kind), &self.a.def(d).kind)
        else {
            return;
        };
        let read = self.judge(&cx, *ty, *lowered, Pos::Alias).unwrap_or_else(|| self.a.types.error());
        if let DefKind::Alias(t) = &mut self.a.defs[d.0 as usize].kind {
            *t = read;
        }
    }

    /// The roots of the def `id`, under the generics in scope; the first
    /// with an error is the diagnostic of its unit.
    fn wellformed_def(&mut self, id: DefId) {
        let def = self.a.def(id);
        let Some(item) = def.item else { return };
        let generics = match (&def.kind, def.owner) {
            (DefKind::Const(_), Some(o)) => self.a.def(o).generics().to_vec(),
            _ => def.generics().to_vec(),
        };
        let Some(cx) = self.cx_for(id, generics, None) else { return };
        // S-861: std alone writes an `impl` of `Span[T]` and a `target fn`
        // that returns a `Span` (`slice`, §15.2): there a `Span` stands as
        // at an argument.
        let view = Pos::Arg(Mode::Borrow);
        let std = self.a.modules.is_std(self.a.def(id).module);
        let roots: Vec<(TypeId, TyId, Pos, Slot)> =
            match (decls::item_kind(&cx.ast.item(item).kind), &self.a.def(id).kind) {
                (kind @ (ItemKind::Struct(_) | ItemKind::Enum(_)), def) => {
                    payloads(kind, def).into_iter().map(|(t, l, slot)| (t, l, Pos::Other, slot)).collect()
                }
                // `self` is not lowered with the parameters (`lower_params`).
                (ItemKind::Fn(f), DefKind::Fn(fd)) => {
                    let params = f.params.iter().filter(|p| !matches!(p.name, ParamName::SelfParam(_)));
                    let roots = params.zip(&fd.params).enumerate();
                    let roots = roots.filter_map(|(k, (p, l))| Some((p.ty?, l.ty, Pos::Arg(p.mode), Slot::Param(k))));
                    let ret = if std && fd.target { view } else { Pos::Other };
                    roots.chain(f.ret.map(|t| (t, fd.ret, ret, Slot::Ret))).collect()
                }
                (ItemKind::Const(c), DefKind::Const(cd)) => vec![(c.ty, cd.ty, Pos::Other, Slot::Const)],
                // S-772: the types of the inputs and the output of a flow
                // are of its signature, none an argument (`Span[F32] at block` is an E0710).
                (ItemKind::Flow(f), DefKind::Flow(fd)) => {
                    let params = f.params.iter().filter(|p| !matches!(p.name, ParamName::SelfParam(_)));
                    let inputs = params.filter_map(|p| p.ty).zip(&fd.inputs).enumerate();
                    let inputs = inputs.map(|(k, (t, i))| (t, i.ty, Pos::Other, Slot::Input(k)));
                    inputs.chain([(f.ret, fd.out, Pos::Other, Slot::Out)]).collect()
                }
                // The target of an `impl` whose members are read (S-756): an error of it is of
                // the heading, the whole `impl` one unit (§18.1).
                // S-769: it is a place of a type, not an argument: `impl voice.Out` is an E0710.
                (ItemKind::Impl(i), DefKind::Impl(imp)) if crate::names::collect::reads_members(i) => {
                    vec![(i.self_ty, imp.self_ty, if std { view } else { Pos::Other }, Slot::Target)]
                }
                _ => Vec::new(),
            };
        for (t, ty, pos, slot) in roots {
            match self.judge(&cx, t, ty, pos) {
                None => {
                    // A field or a payload with an error is not read: the error type
                    // to its users (§18.1).
                    if matches!(slot, Slot::Field(_) | Slot::Variant(..)) {
                        let error = self.a.types.error();
                        self.unread(id, slot, error);
                    }
                    return;
                }
                Some(read) if read != ty => self.unread(id, slot, read),
                Some(_) => {}
            }
        }
    }

    /// The root `slot` of `id` names an alias with an error: it is read as
    /// `error`, that alias the error type in it, by the later stages (its
    /// body, S-757).
    fn unread(&mut self, id: DefId, slot: Slot, error: TyId) {
        // The fields an input of a flow gives its items (`Params`, `Config`,
        // made before, §11.6) are read as the input is.
        if let (DefKind::Flow(f), Slot::Input(k)) = (&self.a.def(id).kind, slot) {
            let (name, old) = (f.inputs[k].name.clone(), f.inputs[k].ty);
            for m in f.members.iter().map(|m| m.1).collect::<Vec<_>>() {
                if let DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }) =
                    &mut self.a.defs[m.0 as usize].kind
                {
                    fs.iter_mut().filter(|x| x.name == name && x.ty == old).for_each(|x| x.ty = error);
                }
            }
        }
        match (&mut self.a.defs[id.0 as usize].kind, slot) {
            (DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }), Slot::Field(k)) => {
                fs[k].ty = error;
                // The type of its default is the field's (§4.4).
                let default = fs[k].default;
                if let Some(DefKind::Const(c)) = default.map(|d| &mut self.a.defs[d.0 as usize].kind) {
                    c.ty = error;
                }
            }
            (DefKind::Enum(e), Slot::Variant(n, k)) => e.variants[n].fields[k] = error,
            (DefKind::Fn(f), Slot::Param(k)) => f.params[k].ty = error,
            (DefKind::Fn(f), Slot::Ret) => f.ret = error,
            (DefKind::Const(c), Slot::Const) => c.ty = error,
            (DefKind::Flow(f), Slot::Input(k)) => f.inputs[k].ty = error,
            (DefKind::Flow(f), Slot::Out) => f.out = error,
            // An alias in the heading of an `impl` is its E0307 (§18.1).
            _ => {}
        }
    }

    /// The type `t` written at a root of the place `pos`, lowered as `ty`:
    /// its first part out of its place or not meeting a requirement is a
    /// diagnostic of the unit `cx.def` (`None`). Else the type as read, with
    /// a part named by an alias with an error as the error type (S-757).
    pub(super) fn judge(&mut self, cx: &Cx<'p>, t: TypeId, ty: TyId, pos: Pos) -> Option<TyId> {
        let w = self.written(cx, t);
        self.part(cx, w, ty, (pos, ROOT), cx.ast.ty(t).span).map_err(|d| self.report(cx.def, d)).ok()
    }

    /// What the part written at `t` is ([`Written`]).
    fn written(&self, cx: &Cx<'p>, t: TypeId) -> Written {
        match self.alias_at.get(&(cx.m, t)) {
            Some(&d) => Written::Alias(d),
            None => Written::Here(t),
        }
    }

    /// The part `ty`, written as `w`, at the place `at`; `span`, where its
    /// nearest part written is. The type as read ([`Self::judge`]).
    fn part(&mut self, cx: &Cx<'p>, w: Written, ty: TyId, at: (Pos, u8), span: Span) -> Result<TyId, Diagnostic> {
        // A type of a cycle is read as the error type, its arguments judged (R-327).
        let cyclic = match w {
            Written::Here(t) => self.a.decls.cyclic_at.get(&(cx.m, t)).copied(),
            _ => None,
        };
        let (here, span, ty) = match w {
            Written::Here(t) => (Some(t), cx.ast.ty(t).span, cyclic.unwrap_or(ty)),
            // As the alias is read, after its own judgment ([`Self::wellformed`]).
            Written::Alias(d) => match self.a.def(d).kind {
                DefKind::Alias(read) if matches!(self.a.types.get(read), Ty::Error) => return Ok(read),
                DefKind::Alias(read) => (None, span, read),
                _ => (None, span, ty),
            },
            Written::Elsewhere => (None, span, ty),
        };
        // Where it is not written, only its second-class parts are judged.
        if here.is_none() && !self.holds(cx, ty, at) {
            return Ok(ty);
        }
        let kids = self.kids(cx, here, self.a.types.get(ty));
        self.parts(cx, (ty, at, span), (here.is_some(), kids), cyclic)
    }

    /// The type `ty` the type arguments `args` of an expression make with
    /// the name before them (§4.5), judged as a type written at the place of
    /// a part of a type, its parts the arguments ([`Self::judge`]).
    pub(super) fn judge_args(&mut self, cx: &Cx<'p>, args: &[TypeId], ty: TyId, span: Span) -> Option<TyId> {
        let kids = args.iter().map(|&t| self.written(cx, t)).collect();
        let r = self.parts(cx, (ty, ARGUMENT, span), (true, kids), None);
        r.map_err(|d| self.report(cx.def, d)).ok()
    }

    /// The part `ty` at `at` and `span` of [`Self::part`], with its parts as
    /// written (`kids`), here (`here`) or not.
    fn parts(
        &mut self,
        cx: &Cx<'p>,
        (ty, at, span): (TyId, (Pos, u8), Span),
        (here, kids): (bool, Vec<Written>),
        cyclic: Option<TyId>,
    ) -> Result<TyId, Diagnostic> {
        if second_class(&Bounds { a: self.a, generics: &cx.generics }, ty) && !fits(self.a, ty, at) {
            return Err(self.misplaced(cx, ty, at, span));
        }
        let shape = self.a.types.get(ty).clone();
        let parts = places(self.a, &shape, at);
        // The parts are read first (each, so that none is judged as lowered),
        // the requirements judged of them; its own error comes first, then the
        // first of its parts.
        let mut read = Vec::new();
        let mut first = Ok(());
        for ((t, at), &w) in parts.into_iter().zip(&kids) {
            let r = self.part(cx, w, t, at, span);
            read.push(*r.as_ref().unwrap_or(&t));
            first = first.and(r.map(drop));
        }
        if here {
            self.required(cx, &shape, &read, &kids, span)?;
        }
        first?;
        if cyclic.is_some() {
            return Ok(self.a.types.error());
        }
        // The same parts intern as the same type.
        let mut read = read.into_iter();
        let shape = match shape {
            Ty::Array(_, n) => Ty::Array(read.next().unwrap_or(ty), n),
            Ty::Tuple(_) => Ty::Tuple(read.collect()),
            Ty::Named(d, _) => Ty::Named(d, read.collect()),
            Ty::Builtin(b, _) => Ty::Builtin(b, read.collect()),
            Ty::Fn(mut f) => {
                f.params.iter_mut().for_each(|p| p.1 = read.next().unwrap_or(p.1));
                f.ret = read.next().unwrap_or(f.ret);
                Ty::Fn(f)
            }
            _ => return Ok(ty),
        };
        Ok(self.a.types.intern(shape))
    }

    /// [`holds`] under the generics of `cx`. The answers kept are of no
    /// scope: a scope with a `?Escape` parameter, which answers of its own
    /// `Ty::Param`, keeps none.
    fn holds(&mut self, cx: &Cx<'p>, ty: TyId, at: (Pos, u8)) -> bool {
        let under = Bounds { a: self.a, generics: &cx.generics };
        if cx.generics.iter().any(GenericDef::lifts_escape) {
            return holds(&under, &mut HashMap::default(), ty, at);
        }
        holds(&under, &mut self.misfit, ty, at)
    }

    /// The parts of the type `shape` as written at `here`, in the order of
    /// [`Self::part`]: not written where the forms do not match (`Self`, an
    /// alias, a part not written).
    fn kids(&self, cx: &Cx<'p>, here: Option<TypeId>, shape: &Ty) -> Vec<Written> {
        let count = match shape {
            Ty::Array(..) => 1,
            Ty::Tuple(ts) | Ty::Named(_, ts) | Ty::Builtin(_, ts) => ts.len(),
            Ty::Fn(f) => f.params.len() + 1,
            _ => 0,
        };
        let written: Option<Vec<Option<TypeId>>> = match (here.map(|t| &cx.ast.ty(t).kind), shape) {
            (Some(TypeKind::Array { elem, .. }), Ty::Array(..)) => Some(vec![Some(*elem)]),
            (Some(TypeKind::Tuple(ws)), Ty::Tuple(_))
            | (Some(TypeKind::Path { args: ws, .. }), Ty::Named(..) | Ty::Builtin(..)) => {
                Some(ws.iter().map(|&w| Some(w)).collect())
            }
            (Some(TypeKind::Fn { params, ret, .. }), Ty::Fn(_)) => {
                Some(params.iter().map(|p| Some(p.1)).chain([*ret]).collect())
            }
            _ => None,
        };
        match written.filter(|ws| ws.len() == count) {
            Some(ws) => ws.into_iter().map(|w| w.map_or(Written::Elsewhere, |t| self.written(cx, t))).collect(),
            None => vec![Written::Elsewhere; count],
        }
    }

    /// The E0710 of the second-class `ty` out of its place `at`.
    fn misplaced(&self, cx: &Cx<'p>, ty: TyId, at: (Pos, u8), span: Span) -> Diagnostic {
        let shown = self.shown(cx, ty);
        let moved = matches!(at.0, Pos::Arg(Mode::Move)) && fits(self.a, ty, (Pos::Arg(Mode::Borrow), at.1));
        let d = if moved {
            let msg =
                format!("`{shown}` is second-class, a view it does not own: a `move` parameter cannot take it (§5.3)");
            Diagnostic::new(Stage::Types, Code::E0710, span, msg).with_rule(
                "read it as `xs: Span[T]`, write it as `inout xs: Span[T]`, or own the elements as `move xs: Buf[T]`",
            )
        } else {
            let msg = format!(
                "`{shown}` is second-class: it is only the type of an argument, not of a field, a return value, a constant or a part of another type (§5.3)"
            );
            Diagnostic::new(Stage::Types, Code::E0710, span, msg)
        };
        d.with_found(src(cx, span))
    }

    /// The E0416 of the first argument of `shape`, written here, that does
    /// not meet the requirement of its parameter (§4.5): the element of
    /// `Buf` / `Span`, of `Array` / `Set` and the key and value of `Map`
    /// (S-767), the first unmet of the requirements of a parameter of a
    /// declared type, in the order of a use of a value (S-1013), judged
    /// under the generics in scope (an unknown bound is met, S-689).
    /// The arguments are judged as `read` ([`Self::part`]: an alias with an
    /// error in them, the error type, meets every requirement).
    fn required(
        &mut self,
        cx: &Cx<'p>,
        shape: &Ty,
        read: &[TyId],
        kids: &[Written],
        span: Span,
    ) -> Result<(), Diagnostic> {
        let (wants, args): (Vec<Want>, _) = match shape {
            &Ty::Builtin(b @ (BuiltinTy::Buf | BuiltinTy::Span), ref args) => {
                (vec![Want::Element(Bound::Copy, Required::BufElement(b))], args)
            }
            // The elements, keys and values of the Shared collections (S-767).
            Ty::Builtin(BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set, args) => {
                (vec![Want::Element(Bound::Dup, Required::SharedElement); args.len()], args)
            }
            Ty::Named(d, args) => ((0..self.a.def(*d).generics().len()).map(|k| Want::Param(*d, k)).collect(), args),
            _ => return Ok(()),
        };
        let at = places(self.a, shape, ARGUMENT);
        for ((want, ((&arg, &shown), w)), (_, place)) in wants.into_iter().zip(read.iter().zip(args).zip(kids)).zip(at)
        {
            // A second-class argument has no kind: its E0710 alone (§4.6, S-766).
            // S-771: so is an argument that holds one out of its place
            // (`C[(Span[F32], F32)]`, `N[[Span[F32]; 2]]`), not one at the
            // argument of a function type (`N[fn(Span[F32]) -> F32]`). A
            // `?Escape` parameter takes a `Span`, and judges its bounds (S-927).
            // That E0710 is the error of the part ([`Self::parts`]).
            let out = self.holds(cx, arg, place);
            let under = Bounds { a: self.a, generics: &cx.generics };
            let (b, what, declared) = match want {
                Want::Element(b, what) if !out && !under.meets(arg, b) => (b, what, None),
                Want::Param(d, k) => {
                    let g = &self.a.def(d).generics()[k];
                    let Some(Requirement::Bound(b)) = first_unmet(&under, g, arg, out) else { continue };
                    let owner = format!("`{}`", self.a.shown_name(d));
                    let std = self.a.modules.is_std(self.a.def(d).module);
                    (b, Required::Param { param: g.name.clone(), owner, std }, Some(g.span))
                }
                Want::Element(..) => continue,
            };
            let at = match w {
                Written::Here(t) => cx.ast.ty(*t).span,
                _ => span,
            };
            let shown = self.shown(cx, shown);
            let mut d = unmet_error(at, &what, &shown, b, &mut |t| self.shown(cx, t));
            if let (Some(decl), Required::Param { param, owner, .. }) = (declared, &what) {
                d = d.with_note(decl, format!("the parameter `{param}` of {owner} is declared here"));
            }
            let d = unmet_rules(self.a, arg, &shown, b).fold(d, Diagnostic::with_rule);
            return Err(d.with_found(src(cx, at)));
        }
        Ok(())
    }

    /// `ty` as the diagnostics show it, its parameters by their names.
    pub(super) fn shown(&self, cx: &Cx<'p>, ty: TyId) -> String {
        let param = |i: u32| cx.generics.get(i as usize).map_or_else(|| format!("<{i}>"), |g| g.name.clone());
        self.a.types.display(ty, &|d| self.a.shown_name(d), &param)
    }
}
