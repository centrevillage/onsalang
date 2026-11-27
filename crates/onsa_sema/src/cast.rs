//! The conversions with `as` (spec §3.3): the lossless widenings it
//! writes, and the conversion functions to suggest where it does not convert.
//! The functions are std's (`std/core/num.onsa`); a unit test checks the
//! names suggested against them (`prim_tests.rs`).

use crate::bounds::Bounds;
use crate::def::Bound;
use crate::prim::{ROUND_FROM, Scalar, TRUNC_FROM, TRUNC_SAT_FROM};
use crate::ty::{FloatKind, TyId, Types};

/// Whether `from as to` is a lossless widening (§3.3). Both resolved scalars.
pub fn cast_allowed(types: &Types, from: TyId, to: TyId) -> bool {
    widens(Scalar::head(types.get(from)), Scalar::head(types.get(to)))
}

/// Whether `from as to` is a lossless widening (§3.3), of the kinds of the
/// types: sema's [`cast_allowed`] and the verifier of Core (V-03) ask it.
pub fn widens(from: Scalar, to: Scalar) -> bool {
    match (from, to) {
        (Scalar::Int(a), Scalar::Int(b)) => {
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
        (Scalar::Float(a), Scalar::Float(b)) => a == b || b == FloatKind::F64,
        // Integers that fit the mantissa: F32 holds 24 bits, F64 holds 53.
        (Scalar::Int(a), Scalar::Float(FloatKind::F32)) => a.bits() <= 16,
        (Scalar::Int(a), Scalar::Float(FloatKind::F64)) => a.bits() <= 32,
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
/// to a number or a type parameter `to` reads as (§3.3): the one of a
/// conversion to a float, the two of a float to an integer. A bound gives
/// what a type parameter can be, so the target has the function (`Float`,
/// `Int`) and the source meets its bound (`AnyNum`, `Float`, `Int`); a bound
/// that is not known (§18.1, a failed `use`) gives nothing.
pub fn cast_instead(bounds: &Bounds, from: TyId, to: TyId) -> Instead {
    let is = |t, b| !bounds.traits_unknown(t) && bounds.satisfies(t, b);
    if is(to, Bound::Float) && is(from, Bound::AnyNum) {
        Instead::Calls(&[ROUND_FROM])
    } else if is(to, Bound::Int) && is(from, Bound::Float) {
        Instead::Calls(&[TRUNC_SAT_FROM, TRUNC_FROM])
    } else if is(to, Bound::Int) && is(from, Bound::Int) {
        Instead::Narrowing
    } else {
        Instead::Nothing
    }
}
