//! The bounds (§6.3): whether a type satisfies a bound. The judgments are of
//! the types and the generics in scope ([`Bounds`]), shared by the body and
//! the well-formedness of the types written (`sig::wellformed`, R-37); the
//! tables they read are [`crate::traits`].

use crate::def::{Bound, GenericDef, GenericKind};
use crate::traits::{Class, derive_of, implies};
use crate::ty::{BuiltinTy, Ty, TyId};
use crate::{Analysis, DefId, Kind};

/// The judgments of the bounds under the generics in scope `generics`.
pub(crate) struct Bounds<'b> {
    pub(crate) a: &'b Analysis,
    pub(crate) generics: &'b [GenericDef],
}

/// Whether the type parameter `g` satisfies `b`: by its bounds, and any `b`
/// when one of them is not known (§18.1).
pub(crate) fn param_holds(g: &GenericDef, b: Bound) -> bool {
    match &g.kind {
        GenericKind::Type { bounds, dup, unknown, .. } => {
            *unknown || bounds.iter().any(|&have| implies(have, b)) || (b == Bound::Dup && *dup)
        }
        _ => false,
    }
}

impl Bounds<'_> {
    fn ty(&self, t: TyId) -> Ty {
        self.a.types.get(t).clone()
    }

    /// The kind of `t` under the generics in scope (R-30, R-176): a type
    /// parameter by its bounds wherever `t` holds it.
    fn kind(&self, t: TyId) -> Option<Kind> {
        crate::kind::kind_in_body(self.a, t, self.generics)
    }

    /// Whether a decided type meets a requirement (the bounds of §6.3 and the
    /// kind constraints of §4.6). A type with no kind keeps a kind constraint
    /// quiet (§18.1: what it holds was not read, whose own error is reported;
    /// a second-class type has no kind, §4.6).
    pub(crate) fn meets(&self, t: TyId, b: Bound) -> bool {
        self.satisfies(t, b)
            || (b.is_kind_constraint() && !matches!(self.ty(t), Ty::Param(_)) && self.kind(t).is_none())
    }

    /// Whether the traits a (resolved) type meets are not known: of what is
    /// not known itself ([`Self::unknown`]), or of a type whose members and
    /// traits were not all read (§18.1, S-850). Every check of whether it
    /// meets a trait keeps quiet then: the operators, the methods and the
    /// bounds of other functions.
    pub(crate) fn traits_unknown(&self, t: TyId) -> bool {
        self.unknown(t)
            || matches!(self.a.types.get(t), Ty::Named(d, _) if self.a.modules.unread_members(*d, self.a.def(*d)))
    }

    /// The error type, or a type parameter with an unknown bound (§18.1,
    /// S-692 A1): nothing of it is known, its kind neither.
    fn unknown(&self, t: TyId) -> bool {
        match self.ty(t) {
            Ty::Error => true,
            Ty::Param(i) => {
                self.generics.get(i as usize).is_some_and(|g| matches!(g.kind, GenericKind::Type { unknown: true, .. }))
            }
            _ => false,
        }
    }

    /// Whether a (resolved) type satisfies a builtin bound (§6.3). The kind
    /// is of the structure, which no `impl` changes (§4.6, S-850).
    pub(crate) fn satisfies(&self, t: TyId, b: Bound) -> bool {
        let unknown = if b.is_kind_constraint() { self.unknown(t) } else { self.traits_unknown(t) };
        if unknown {
            return true;
        }
        let ty = self.ty(t);
        match (&ty, b) {
            (Ty::Param(i), _) => self.generics.get(*i as usize).is_some_and(|g| param_holds(g, b)),
            (Ty::Named(d, _), _) if self.a.modules.trait_impls.contains_key(&(b, *d)) => {
                self.impl_covers(self.a.modules.trait_impls[&(b, *d)], t)
            }
            (Ty::Named(d, args), _) => {
                let def = self.a.def(*d);
                let derives = def.derives();
                // A list that is not known derives every trait of the list of §6.4
                // (§18.1, S-460, S-774): the uses that rely on it get no diagnostic. A
                // generic type meets a derived trait only when its type arguments meet
                // it (§6.4, R-355). `Show` is E0200 in this version: written, it is met
                // (R-328).
                let of_args = || {
                    def.generics()
                        .iter()
                        .zip(args)
                        .all(|(g, &a)| !matches!(g.kind, GenericKind::Type { .. }) || self.satisfies(a, b))
                };
                match (b, derive_of(b)) {
                    (Bound::Copy | Bound::Dup, _) => self.kind_meets(t, b),
                    (_, Some(want)) => derives.is_none_or(|ds| ds.contains(&want) && of_args()),
                    _ => false,
                }
            }
            _ => self.of_table(t, &ty, b),
        }
    }

    /// Whether the `impl` `id` of a trait covers the instance `t` of its type
    /// (§6.2): the arguments of `t` meet the bounds of the parameters of the
    /// `impl` they stand at, in any order. A place that is no parameter is the
    /// error of the heading (E0307), not judged, nor is a type not read.
    fn impl_covers(&self, id: DefId, t: TyId) -> bool {
        let Some(imp) = self.a.def(id).as_impl() else { return true };
        let (Ty::Named(_, written), Ty::Named(_, args)) = (self.ty(imp.self_ty), self.ty(t)) else { return true };
        let param = |w: TyId| if let Ty::Param(k) = self.ty(w) { imp.generics.get(k as usize) } else { None };
        written.iter().zip(&args).all(|(&w, &arg)| match param(w).map(|g| &g.kind) {
            Some(GenericKind::Type { bounds, dup, unknown: false, .. }) => {
                bounds.iter().copied().chain(dup.then_some(Bound::Dup)).all(|b| self.meets(arg, b))
            }
            _ => true,
        })
    }

    /// Whether `t`, of a kind (§4.6), meets the kind constraint `b`.
    fn kind_meets(&self, t: TyId, b: Bound) -> bool {
        matches!((self.kind(t), b), (Some(Kind::Copy), _) | (Some(Kind::Shared), Bound::Dup))
    }

    /// Whether the type `t` (`ty`) of the table of §6.3 meets `b`: a trait of
    /// its row, with its parts for a tuple, `[T; N]` and `Array[T]`; a kind
    /// constraint by its kind (§6.3), which for a tuple and `[T; N]` is of
    /// their parts (§4.6), each asked so that an unknown one keeps quiet.
    fn of_table(&self, t: TyId, ty: &Ty, b: Bound) -> bool {
        let Some(class) = Class::of(ty) else { return false };
        let parts: &[TyId] = match ty {
            Ty::Array(e, _) => std::slice::from_ref(e),
            Ty::Tuple(ts) | Ty::Builtin(BuiltinTy::Array, ts) => ts,
            _ => &[],
        };
        let of_parts = || parts.iter().all(|&x| self.satisfies(x, b));
        match class {
            Class::Parts if b.is_kind_constraint() => of_parts(),
            _ if b.is_kind_constraint() => self.kind_meets(t, b),
            _ => class.implements(b) && of_parts(),
        }
    }
}
