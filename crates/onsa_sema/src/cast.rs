//! The conversions with `as` (spec §3.3): the lossless widenings it
//! writes, and the conversion method to suggest where it does not convert.
//! The methods are std's (`std/core/num.onsa`); a unit test checks the
//! names suggested against them (`prim_tests.rs`). W5-14 decides the
//! suggestions.

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

/// The method to suggest instead of a rejected `as` (§3.3).
pub fn cast_suggestion(types: &Types, from: TyId, to: TyId) -> Option<String> {
    match (types.get(from), types.get(to)) {
        (Ty::Int(_), Ty::Int(b)) => Some(format!(".narrow_{}()", b.name().to_lowercase())),
        (Ty::Int(_), Ty::Float(FloatKind::F32)) | (Ty::Float(_), Ty::Float(FloatKind::F32)) => {
            Some(".round_f32()".into())
        }
        (Ty::Int(_), Ty::Float(FloatKind::F64)) => Some(".round_f64()".into()),
        (Ty::Float(_), Ty::Int(b)) => Some(format!(".trunc_{}()", b.name().to_lowercase())),
        _ => None,
    }
}
