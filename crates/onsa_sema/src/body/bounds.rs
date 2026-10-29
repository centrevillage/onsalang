//! The bounds (§6.3): whether a type satisfies a bound, and which builtin
//! bound implies which. The judgments are of the types and the generics in
//! scope ([`Bounds`]), shared by the body and the well-formedness of the
//! types written (`sig::wellformed`, R-37).

use super::*;

/// The judgments of the bounds under the generics in scope `generics`.
pub(crate) struct Bounds<'b> {
    pub(crate) a: &'b Analysis,
    pub(crate) generics: &'b [GenericDef],
}

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ bounds

    /// The judgments of the bounds under the generics of the body.
    pub(crate) fn bounds(&self) -> Bounds<'_> {
        Bounds { a: self.a, generics: &self.generics }
    }

    pub(crate) fn traits_unknown(&self, t: TyId) -> bool {
        self.bounds().traits_unknown(t)
    }

    pub(crate) fn satisfies(&self, t: TyId, b: Bound) -> bool {
        self.bounds().satisfies(t, b)
    }
}

impl Bounds<'_> {
    fn ty(&self, t: TyId) -> Ty {
        self.a.types.get(t).clone()
    }

    /// Whether a decided type meets a requirement (the bounds of §6.3 and the
    /// kind constraints `Copy` / `Dup` of §4.6).
    pub(crate) fn meets(&self, t: TyId, b: Bound) -> bool {
        if self.satisfies(t, b) {
            return true;
        }
        // The kind of a user type that holds a type parameter of the body is not
        // computed (`kind_of` is `None`): such a constraint is not decided here and passes.
        // R-176 (W5-08): a `?Dup` parameter inside makes the type not `Dup`
        // (`tests/spec/negative/dup_maybe_dup_param.onsa`, in the pending list).
        if matches!(b, Bound::Dup | Bound::Copy) && !matches!(self.ty(t), Ty::Param(_)) && self.a.kind_of(t).is_none() {
            return true;
        }
        false
    }

    /// Whether the traits a (resolved) type meets are not known: the error
    /// type, or a type parameter with an unknown bound (§18.1, S-692 A1).
    /// Every check of whether it meets a trait keeps quiet then: the
    /// operators, the methods and the bounds of other functions.
    pub(crate) fn traits_unknown(&self, t: TyId) -> bool {
        match self.ty(t) {
            Ty::Error => true,
            Ty::Param(i) => {
                self.generics.get(i as usize).is_some_and(|g| matches!(g.kind, GenericKind::Type { unknown: true, .. }))
            }
            _ => false,
        }
    }

    /// Whether a (resolved) type satisfies a builtin bound (§6.3).
    pub(crate) fn satisfies(&self, t: TyId, b: Bound) -> bool {
        if self.traits_unknown(t) {
            return true;
        }
        let ty = self.ty(t);
        match (&ty, b) {
            (Ty::Param(i), _) => {
                let Some(g) = self.generics.get(*i as usize) else { return false };
                match &g.kind {
                    GenericKind::Type { bounds, dup, .. } => {
                        bounds.iter().any(|&have| implies(have, b)) || (b == Bound::Dup && *dup)
                    }
                    _ => false,
                }
            }
            (
                Ty::Int(_),
                Bound::Num
                | Bound::PartialEq
                | Bound::PartialOrd
                | Bound::Eq
                | Bound::Ord
                | Bound::Copy
                | Bound::Dup
                | Bound::Hash
                | Bound::Default
                | Bound::Show,
            ) => true,
            (
                Ty::Float(_),
                Bound::Num
                | Bound::Float
                | Bound::PartialEq
                | Bound::PartialOrd
                | Bound::Copy
                | Bound::Dup
                | Bound::Default
                | Bound::Show,
            ) => true,
            (
                Ty::Bool,
                Bound::PartialEq | Bound::Eq | Bound::Hash | Bound::Copy | Bound::Dup | Bound::Default | Bound::Show,
            ) => true,
            (
                Ty::Char,
                Bound::PartialEq
                | Bound::PartialOrd
                | Bound::Eq
                | Bound::Ord
                | Bound::Hash
                | Bound::Copy
                | Bound::Dup
                | Bound::Show,
            ) => true,
            (Ty::Unit, Bound::PartialEq | Bound::Eq | Bound::Copy | Bound::Dup | Bound::Default) => true,
            (
                Ty::Array(e, _),
                Bound::PartialEq
                | Bound::Eq
                | Bound::PartialOrd
                | Bound::Ord
                | Bound::Hash
                | Bound::Copy
                | Bound::Dup
                | Bound::Show
                | Bound::Default,
            ) => self.satisfies(*e, b),
            (
                Ty::Tuple(ts),
                Bound::PartialEq
                | Bound::Eq
                | Bound::PartialOrd
                | Bound::Ord
                | Bound::Hash
                | Bound::Copy
                | Bound::Dup
                | Bound::Show
                | Bound::Default,
            ) => ts.iter().all(|&x| self.satisfies(x, b)),
            (
                Ty::Builtin(BuiltinTy::Option | BuiltinTy::Result, args),
                Bound::PartialEq | Bound::Eq | Bound::Hash | Bound::Show | Bound::Copy | Bound::Dup,
            ) => args.iter().all(|&x| self.satisfies(x, b)),
            (
                Ty::Builtin(BuiltinTy::Str | BuiltinTy::Bytes, _),
                Bound::PartialEq
                | Bound::Eq
                | Bound::PartialOrd
                | Bound::Ord
                | Bound::Hash
                | Bound::Dup
                | Bound::Default,
            ) => true,
            (Ty::Builtin(BuiltinTy::Str, _), Bound::Show) => true,
            (Ty::Builtin(BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set, _), Bound::Dup) => true,
            (Ty::Builtin(BuiltinTy::Array, args), Bound::PartialEq | Bound::Eq) => {
                args.iter().all(|&x| self.satisfies(x, b))
            }
            // `Ptr[T]` is Copy (§4.1, R-322).
            (Ty::Fn(_) | Ty::Builtin(BuiltinTy::Ptr, _), Bound::Copy | Bound::Dup) => true,
            (Ty::Named(d, args), _) => {
                let def = self.a.def(*d);
                let derives = match &def.kind {
                    DefKind::Struct(s) => s.derives.as_deref(),
                    DefKind::Enum(e) => e.derives.as_deref(),
                    _ => Some(&[][..]),
                };
                // A list that is not known derives every trait (§18.1, S-460):
                // the uses that rely on it get no diagnostic.
                let derived = |d: crate::def::Derive| derives.is_none_or(|ds| ds.contains(&d));
                match b {
                    Bound::Copy => self.a.kind_of(t) == Some(Kind::Copy),
                    Bound::Dup => matches!(self.a.kind_of(t), Some(Kind::Copy | Kind::Shared)),
                    Bound::PartialEq => derived(crate::def::Derive::PartialEq) || derived(crate::def::Derive::Eq),
                    Bound::Eq => derived(crate::def::Derive::Eq),
                    Bound::PartialOrd => derived(crate::def::Derive::PartialOrd) || derived(crate::def::Derive::Ord),
                    Bound::Ord => derived(crate::def::Derive::Ord),
                    Bound::Default => derived(crate::def::Derive::Default),
                    // `Hash` and `Show` are E0200 in this version (W5-06): written,
                    // they are met (R-328).
                    Bound::Hash => derived(crate::def::Derive::Hash),
                    Bound::Show => derived(crate::def::Derive::Show),
                    _ => {
                        let _ = args;
                        false
                    }
                }
            }
            _ => false,
        }
    }
}

/// `have` implies `want` among the builtin bounds (§6.3): `Ord` ⇒ `PartialOrd`, `Eq`;
/// `Eq` ⇒ `PartialEq`; `Float` ⇒ `Num`; `Num` ⇒ `PartialEq`, `PartialOrd`, `Copy`.
pub(crate) fn implies(have: Bound, want: Bound) -> bool {
    if have == want {
        return true;
    }
    match have {
        Bound::Ord => matches!(want, Bound::PartialOrd | Bound::Eq | Bound::PartialEq),
        Bound::Eq => want == Bound::PartialEq,
        Bound::PartialOrd => want == Bound::PartialEq,
        Bound::Float => matches!(want, Bound::Num | Bound::PartialEq | Bound::PartialOrd | Bound::Copy | Bound::Dup),
        Bound::Num => matches!(want, Bound::PartialEq | Bound::PartialOrd | Bound::Copy | Bound::Dup),
        Bound::Copy => want == Bound::Dup,
        _ => false,
    }
}
