//! The conversions with `as` (spec §3.3): the lossless widenings it
//! writes, and the conversion functions to suggest where it does not convert.
//! The functions are std's (`std/core/num.onsa`); a unit test checks the
//! names suggested against them (`prim_tests.rs`).

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

/// The conversion functions to call instead of a rejected `as` (§3.3): the
/// one reading of a conversion to a float, the two of a float to an integer,
/// and none of a narrowing, whose `Option` no `as` gives.
pub fn cast_suggestions(types: &Types, from: TyId, to: TyId) -> Vec<String> {
    match (types.get(from), types.get(to)) {
        (Ty::Int(_) | Ty::Float(_), Ty::Float(k)) => vec![format!("{}.round_from", k.name())],
        (Ty::Float(_), Ty::Int(k)) => vec![format!("{}.trunc_sat_from", k.name()), format!("{}.trunc_from", k.name())],
        _ => Vec::new(),
    }
}
