//! Builtin methods, associated items and conversions of the builtin types
//! (spec §3.3, §4.1, §4.2, §5.3, S-09, S-12). Signatures only; the
//! interpreter and backends implement them (`onsa_core::prim`).

use crate::ty::{BuiltinTy, FloatKind, IntKind, Ty, TyId, Types};

/// A builtin method: parameter types (receiver excluded) and result.
#[derive(Debug, Clone)]
pub struct MethodSig {
    pub params: Vec<TyId>,
    pub ret: TyId,
    /// `inout self` (needs the `!` mark, §5.2).
    pub bang: bool,
}

const INTS: [IntKind; 8] =
    [IntKind::I8, IntKind::I16, IntKind::I32, IntKind::I64, IntKind::U8, IntKind::U16, IntKind::U32, IntKind::U64];

fn int_suffix(k: IntKind) -> &'static str {
    match k {
        IntKind::I8 => "i8",
        IntKind::I16 => "i16",
        IntKind::I32 => "i32",
        IntKind::I64 => "i64",
        IntKind::U8 => "u8",
        IntKind::U16 => "u16",
        IntKind::U32 => "u32",
        IntKind::U64 => "u64",
    }
}

/// Method `name` on a receiver of (resolved, non-variable) type `recv`.
pub fn method(types: &mut Types, recv: TyId, name: &str) -> Option<MethodSig> {
    let recv_ty = types.get(recv).clone();
    let u32 = types.int(IntKind::U32);
    let bool_ = types.bool();
    let sig = |params: Vec<TyId>, ret: TyId, bang: bool| Some(MethodSig { params, ret, bang });
    match recv_ty {
        Ty::Int(k) => {
            for t in INTS {
                if name == format!("narrow_{}", int_suffix(t)) {
                    let target = types.int(t);
                    let opt = types.builtin(BuiltinTy::Option, vec![target]);
                    return sig(vec![], opt, false);
                }
            }
            match name {
                "round_f32" => sig(vec![], types.float(FloatKind::F32), false),
                "round_f64" => sig(vec![], types.float(FloatKind::F64), false),
                "abs" if k.signed() => sig(vec![], recv, false),
                "checked_add" | "checked_sub" | "checked_mul" | "checked_div" => {
                    let opt = types.builtin(BuiltinTy::Option, vec![recv]);
                    sig(vec![recv], opt, false)
                }
                "div_euclid" | "rem_euclid" => sig(vec![recv], recv, false),
                "min" | "max" => sig(vec![recv], recv, false),
                _ => None,
            }
        }
        Ty::Float(k) => {
            for t in INTS {
                if name == format!("trunc_{}", int_suffix(t)) || name == format!("trunc_{}_sat", int_suffix(t)) {
                    let target = types.int(t);
                    return sig(vec![], target, false);
                }
            }
            match name {
                "round_f32" => sig(vec![], types.float(FloatKind::F32), false),
                "round_f64" => sig(vec![], types.float(FloatKind::F64), false),
                "to_bits" => {
                    let bits = types.int(if k == FloatKind::F32 { IntKind::U32 } else { IntKind::U64 });
                    sig(vec![], bits, false)
                }
                "abs" | "sqrt" | "floor" | "ceil" | "trunc" | "round" => sig(vec![], recv, false),
                "min" | "max" => sig(vec![recv], recv, false),
                "is_nan" | "is_finite" => sig(vec![], bool_, false),
                _ => None,
            }
        }
        // Sequences (§5.3, S-12): `[T; N]`, `Span[T]`, `Buf[T]`, and the Shared `Array[T]`.
        Ty::Array(elem, _) => seq_method(types, recv, elem, name),
        Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, args) => {
            seq_method(types, recv, args[0], name)
        }
        Ty::Builtin(BuiltinTy::Str, _) => {
            let str_ = types.builtin(BuiltinTy::Str, vec![]);
            match name {
                "len" => sig(vec![], u32, false),
                "is_empty" => sig(vec![], bool_, false),
                "substr" => sig(vec![u32, u32], str_, false),
                "get_substr" => {
                    let opt = types.builtin(BuiltinTy::Option, vec![str_]);
                    sig(vec![u32, u32], opt, false)
                }
                "find" => {
                    let opt = types.builtin(BuiltinTy::Option, vec![u32]);
                    sig(vec![str_], opt, false)
                }
                "is_char_boundary" => sig(vec![u32], bool_, false),
                _ => None,
            }
        }
        Ty::Builtin(BuiltinTy::Option, args) => match name {
            "unwrap" => sig(vec![], args[0], false),
            "is_some" | "is_none" => sig(vec![], bool_, false),
            "unwrap_or" => sig(vec![args[0]], args[0], false),
            _ => None,
        },
        Ty::Builtin(BuiltinTy::Result, args) => match name {
            "unwrap" => sig(vec![], args[0], false),
            "is_ok" | "is_err" => sig(vec![], bool_, false),
            _ => None,
        },
        _ => None,
    }
}

fn seq_method(types: &mut Types, recv: TyId, elem: TyId, name: &str) -> Option<MethodSig> {
    let _ = recv;
    let u32 = types.int(IntKind::U32);
    let bool_ = types.bool();
    let unit = types.unit();
    let span = types.builtin(BuiltinTy::Span, vec![elem]);
    let sig = |params: Vec<TyId>, ret: TyId, bang: bool| Some(MethodSig { params, ret, bang });
    match name {
        "len" => sig(vec![], u32, false),
        "is_empty" => sig(vec![], bool_, false),
        "slice" => sig(vec![u32, u32], span, false),
        "get" => {
            let opt = types.builtin(BuiltinTy::Option, vec![elem]);
            sig(vec![u32], opt, false)
        }
        "fill" => sig(vec![elem], unit, true),
        "add_from" | "copy_from" => sig(vec![span], unit, true),
        _ => None,
    }
}

/// Associated constant `Type.NAME` of a scalar type (`F32.PI`, `I32.MAX`).
pub fn assoc_const(types: &mut Types, scalar: TyId, name: &str) -> Option<TyId> {
    match types.get(scalar).clone() {
        Ty::Float(_) => matches!(name, "PI" | "MIN" | "MAX" | "EPSILON" | "INFINITY" | "NAN").then_some(scalar),
        Ty::Int(_) => matches!(name, "MIN" | "MAX" | "BITS")
            .then(|| if name == "BITS" { types.int(IntKind::U32) } else { scalar }),
        _ => None,
    }
}

/// Associated function `Type.name(...)` of a builtin type: `(params, ret)`.
/// `generic_arg` is the fresh type argument for `Buf.zeroed` (`T` from the
/// expected type).
pub fn assoc_fn(
    types: &mut Types,
    scalar: Option<TyId>,
    builtin: Option<BuiltinTy>,
    name: &str,
    generic_arg: TyId,
) -> Option<(Vec<TyId>, TyId)> {
    let u32 = types.int(IntKind::U32);
    match (scalar.map(|t| types.get(t).clone()), builtin, name) {
        (Some(Ty::Float(k)), _, "from_bits") => {
            let bits = types.int(if k == FloatKind::F32 { IntKind::U32 } else { IntKind::U64 });
            Some((vec![bits], scalar.unwrap()))
        }
        (_, Some(BuiltinTy::Buf), "zeroed") => {
            let buf = types.builtin(BuiltinTy::Buf, vec![generic_arg]);
            Some((vec![u32], buf))
        }
        _ => None,
    }
}

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
        (Ty::Int(_), Ty::Int(b)) => Some(format!(".narrow_{}()", int_suffix(*b))),
        (Ty::Int(_), Ty::Float(FloatKind::F32)) | (Ty::Float(_), Ty::Float(FloatKind::F32)) => {
            Some(".round_f32()".into())
        }
        (Ty::Int(_), Ty::Float(FloatKind::F64)) => Some(".round_f64()".into()),
        (Ty::Float(_), Ty::Int(b)) => Some(format!(".trunc_{}()", int_suffix(*b))),
        _ => None,
    }
}
