//! The conversions with `as` (spec §3.3): the lossless widenings it
//! writes, and the conversion functions to suggest where it does not convert.
//! The functions are std's (`std/core/num.onsa`); a unit test checks the
//! names suggested against them (`prim_tests.rs`).

use crate::body::bounds::Bounds;
use crate::def::Bound;
use crate::prim::{ROUND_FROM, TRUNC_FROM, TRUNC_SAT_FROM};
use crate::ty::{FloatKind, Ty, TyId, Types};

/// Whether `from as to` is a lossless widening (§3.3). Both resolved scalars.
pub fn cast_allowed(types: &Types, from: TyId, to: TyId) -> bool {
    match (types.get(from), types.get(to)) {
        (Ty::Int(a), Ty::Int(b)) => {
            if a == b {
                return true;
            }
            match (a.signed(), b.signed()) {
                (true, true) | (false, false) => b.bits() > a.bits(),
                // unsigned -> wider signed is exact; signed -> unsigned never.
                (false, true) => b.bits() > a.bits(),
                (true, false) => false,
            }
        }
        (Ty::Float(a), Ty::Float(b)) => a == b || *b == FloatKind::F64,
        // Integers that fit the mantissa: F32 holds 24 bits, F64 holds 53.
        (Ty::Int(a), Ty::Float(FloatKind::F32)) => a.bits() <= 16,
        (Ty::Int(a), Ty::Float(FloatKind::F64)) => a.bits() <= 32,
        _ => false,
    }
}

/// What stands for a rejected `as` (§3.3).
#[derive(Debug, PartialEq, Eq)]
pub enum Instead {
    /// The functions of the target to suggest, one for each reading.
    Calls(&'static [&'static str]),
    /// An integer narrowing, whose `Option` no `as` gives: no candidate, a
    /// note of `narrow_from`.
    Narrowing,
    /// No function follows.
    Nothing,
}

/// The function a rejected `as` of a number or a type parameter `from`
/// to the number `to` reads as (§3.3): the one of a conversion to a float,
/// the two of a float to an integer. A bound of the source gives what it
/// can be, so the source meets the bound of the function (`AnyNum`, `Float`,
/// `Int`); a bound that is not known (§18.1, a failed `use`) gives nothing.
pub fn cast_instead(bounds: &Bounds, from: TyId, to: TyId) -> Instead {
    let source = |b| !bounds.traits_unknown(from) && bounds.satisfies(from, b);
    match bounds.a.types.get(to) {
        Ty::Float(_) if source(Bound::AnyNum) => Instead::Calls(&[ROUND_FROM]),
        Ty::Int(_) if source(Bound::Float) => Instead::Calls(&[TRUNC_SAT_FROM, TRUNC_FROM]),
        Ty::Int(_) if source(Bound::Int) => Instead::Narrowing,
        _ => Instead::Nothing,
    }
}
