//! Builtin methods, associated items and conversions of the builtin types
//! (spec §3.3, §4.1, §4.2, §5.3, S-09, S-12). Signatures only; the
//! interpreter and backends implement them (`onsa_core::prim`).
//!
//! Every builtin method, associated constant and associated function is one
//! row of a table here ([`methods`], [`ASSOC_CONSTS`], [`ASSOC_FNS`]); the
//! lookups read the rows, so the names are written once, and [`names`] lists
//! them for the gate's check of hard-coded builtin names (Q-14, W1-02).
//! W5-02 moves these rows into std declarations (R-79).

use std::sync::OnceLock;

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

/// The receivers a builtin method is defined on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Recv {
    Int,
    /// Signed integers only.
    SignedInt,
    Float,
    /// `[T; N]`, `Span[T]`, `Buf[T]`, `Array[T]` (§5.3, S-12).
    Seq,
    Str,
    Option,
    Result,
}

/// A type in a method's signature, relative to the receiver.
#[derive(Debug, Clone, Copy)]
enum T {
    /// The receiver's type.
    Recv,
    /// The element of a sequence, the content of `Option` / `Result`.
    Inner,
    U32,
    Bool,
    Unit,
    Str,
    SpanOfInner,
    Int(IntKind),
    Float(FloatKind),
    /// `U32` for `F32`, `U64` for `F64` (`to_bits`).
    Bits,
    OptRecv,
    OptInner,
    OptStr,
    OptU32,
    OptInt(IntKind),
}

/// One builtin method.
struct Method {
    recv: Recv,
    name: String,
    params: &'static [T],
    ret: T,
    /// `inout self`.
    bang: bool,
}

/// Every builtin method.
fn methods() -> &'static [Method] {
    static TABLE: OnceLock<Vec<Method>> = OnceLock::new();
    TABLE.get_or_init(|| {
        let mut v = Vec::new();
        let mut add = |recv, name: &str, params: &'static [T], ret, bang| {
            v.push(Method { recv, name: name.to_string(), params, ret, bang })
        };
        // Integers (§3.3, §3.4).
        for t in INTS {
            add(Recv::Int, &format!("narrow_{}", int_suffix(t)), &[], T::OptInt(t), false);
        }
        add(Recv::Int, "round_f32", &[], T::Float(FloatKind::F32), false);
        add(Recv::Int, "round_f64", &[], T::Float(FloatKind::F64), false);
        add(Recv::SignedInt, "abs", &[], T::Recv, false);
        for name in ["checked_add", "checked_sub", "checked_mul", "checked_div"] {
            add(Recv::Int, name, &[T::Recv], T::OptRecv, false);
        }
        for name in ["div_euclid", "rem_euclid", "min", "max"] {
            add(Recv::Int, name, &[T::Recv], T::Recv, false);
        }
        // Floats (§3.3, S-09).
        for t in INTS {
            add(Recv::Float, &format!("trunc_{}", int_suffix(t)), &[], T::Int(t), false);
            add(Recv::Float, &format!("trunc_{}_sat", int_suffix(t)), &[], T::Int(t), false);
        }
        add(Recv::Float, "round_f32", &[], T::Float(FloatKind::F32), false);
        add(Recv::Float, "round_f64", &[], T::Float(FloatKind::F64), false);
        add(Recv::Float, "to_bits", &[], T::Bits, false);
        for name in ["abs", "sqrt", "floor", "ceil", "trunc", "round"] {
            add(Recv::Float, name, &[], T::Recv, false);
        }
        for name in ["min", "max"] {
            add(Recv::Float, name, &[T::Recv], T::Recv, false);
        }
        for name in ["is_nan", "is_finite"] {
            add(Recv::Float, name, &[], T::Bool, false);
        }
        // Sequences (§5.3, S-12).
        add(Recv::Seq, "len", &[], T::U32, false);
        add(Recv::Seq, "is_empty", &[], T::Bool, false);
        add(Recv::Seq, "slice", &[T::U32, T::U32], T::SpanOfInner, false);
        add(Recv::Seq, "get", &[T::U32], T::OptInner, false);
        add(Recv::Seq, "fill", &[T::Inner], T::Unit, true);
        add(Recv::Seq, "add_from", &[T::SpanOfInner], T::Unit, true);
        add(Recv::Seq, "copy_from", &[T::SpanOfInner], T::Unit, true);
        // Strings (§4.2).
        add(Recv::Str, "len", &[], T::U32, false);
        add(Recv::Str, "is_empty", &[], T::Bool, false);
        add(Recv::Str, "substr", &[T::U32, T::U32], T::Str, false);
        add(Recv::Str, "get_substr", &[T::U32, T::U32], T::OptStr, false);
        add(Recv::Str, "find", &[T::Str], T::OptU32, false);
        add(Recv::Str, "is_char_boundary", &[T::U32], T::Bool, false);
        // Option and Result (§4.1).
        add(Recv::Option, "unwrap", &[], T::Inner, false);
        add(Recv::Option, "is_some", &[], T::Bool, false);
        add(Recv::Option, "is_none", &[], T::Bool, false);
        add(Recv::Option, "unwrap_or", &[T::Inner], T::Inner, false);
        add(Recv::Result, "unwrap", &[], T::Inner, false);
        add(Recv::Result, "is_ok", &[], T::Bool, false);
        add(Recv::Result, "is_err", &[], T::Bool, false);
        v
    })
}

/// Method `name` on a receiver of (resolved, non-variable) type `recv`.
pub fn method(types: &mut Types, recv: TyId, name: &str) -> Option<MethodSig> {
    let recv_ty = types.get(recv).clone();
    let (families, inner): (&[Recv], Option<TyId>) = match &recv_ty {
        Ty::Int(k) if k.signed() => (&[Recv::Int, Recv::SignedInt], None),
        Ty::Int(_) => (&[Recv::Int], None),
        Ty::Float(_) => (&[Recv::Float], None),
        Ty::Array(elem, _) => (&[Recv::Seq], Some(*elem)),
        Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, args) => (&[Recv::Seq], Some(args[0])),
        Ty::Builtin(BuiltinTy::Str, _) => (&[Recv::Str], None),
        Ty::Builtin(BuiltinTy::Option, args) => (&[Recv::Option], Some(args[0])),
        Ty::Builtin(BuiltinTy::Result, args) => (&[Recv::Result], Some(args[0])),
        _ => return None,
    };
    let m = methods().iter().find(|m| families.contains(&m.recv) && m.name == name)?;
    let mut ty = |t: T| sig_ty(types, t, recv, &recv_ty, inner);
    let params = m.params.iter().map(|t| ty(*t)).collect::<Option<Vec<_>>>()?;
    let ret = ty(m.ret)?;
    Some(MethodSig { params, ret, bang: m.bang })
}

fn sig_ty(types: &mut Types, t: T, recv: TyId, recv_ty: &Ty, inner: Option<TyId>) -> Option<TyId> {
    Some(match t {
        T::Recv => recv,
        T::Inner => inner?,
        T::U32 => types.int(IntKind::U32),
        T::Bool => types.bool(),
        T::Unit => types.unit(),
        T::Str => types.builtin(BuiltinTy::Str, vec![]),
        T::SpanOfInner => types.builtin(BuiltinTy::Span, vec![inner?]),
        T::Int(k) => types.int(k),
        T::Float(k) => types.float(k),
        T::Bits => types.int(if matches!(recv_ty, Ty::Float(FloatKind::F32)) { IntKind::U32 } else { IntKind::U64 }),
        T::OptRecv => types.builtin(BuiltinTy::Option, vec![recv]),
        T::OptInner => types.builtin(BuiltinTy::Option, vec![inner?]),
        T::OptStr => {
            let s = types.builtin(BuiltinTy::Str, vec![]);
            types.builtin(BuiltinTy::Option, vec![s])
        }
        T::OptU32 => {
            let u = types.int(IntKind::U32);
            types.builtin(BuiltinTy::Option, vec![u])
        }
        T::OptInt(k) => {
            let i = types.int(k);
            types.builtin(BuiltinTy::Option, vec![i])
        }
    })
}

/// The type of an associated constant.
#[derive(Debug, Clone, Copy)]
enum ConstTy {
    /// The scalar itself.
    Scalar,
    U32,
}

/// Associated constants `Type.NAME` of the scalar types (§6.3, §6.6).
const ASSOC_CONSTS: &[(Recv, &str, ConstTy)] = &[
    (Recv::Float, "PI", ConstTy::Scalar),
    (Recv::Float, "MIN", ConstTy::Scalar),
    (Recv::Float, "MAX", ConstTy::Scalar),
    (Recv::Float, "EPSILON", ConstTy::Scalar),
    (Recv::Float, "INFINITY", ConstTy::Scalar),
    (Recv::Float, "NAN", ConstTy::Scalar),
    (Recv::Int, "MIN", ConstTy::Scalar),
    (Recv::Int, "MAX", ConstTy::Scalar),
    (Recv::Int, "BITS", ConstTy::U32),
];

/// Associated constant `Type.NAME` of a scalar type (`F32.PI`, `I32.MAX`).
pub fn assoc_const(types: &mut Types, scalar: TyId, name: &str) -> Option<TyId> {
    let family = match types.get(scalar) {
        Ty::Float(_) => Recv::Float,
        Ty::Int(_) => Recv::Int,
        _ => return None,
    };
    let (_, _, ty) = ASSOC_CONSTS.iter().find(|(r, n, _)| *r == family && *n == name)?;
    Some(match ty {
        ConstTy::Scalar => scalar,
        ConstTy::U32 => types.int(IntKind::U32),
    })
}

/// The owner and the signature of an associated function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AssocFn {
    /// `F32.from_bits(u)`: the bits (`U32` / `U64`) to the float.
    FromBits,
    /// `Buf.zeroed(n)`: a `Buf[T]` of `n` zero elements.
    Zeroed,
}

/// Associated functions `Type.name(...)` of the builtin types.
const ASSOC_FNS: &[(&str, AssocFn)] = &[("from_bits", AssocFn::FromBits), ("zeroed", AssocFn::Zeroed)];

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
    let (_, f) = ASSOC_FNS.iter().find(|(n, _)| *n == name)?;
    match (scalar.map(|t| types.get(t).clone()), builtin, f) {
        (Some(Ty::Float(k)), _, AssocFn::FromBits) => {
            let bits = types.int(if k == FloatKind::F32 { IntKind::U32 } else { IntKind::U64 });
            Some((vec![bits], scalar.unwrap()))
        }
        (_, Some(BuiltinTy::Buf), AssocFn::Zeroed) => {
            let buf = types.builtin(BuiltinTy::Buf, vec![generic_arg]);
            Some((vec![u32], buf))
        }
        _ => None,
    }
}

/// The names of every builtin method, associated constant and associated
/// function, sorted and without duplicates (for the gate, Q-14).
pub fn names() -> Vec<String> {
    let mut v: Vec<String> = methods().iter().map(|m| m.name.clone()).collect();
    v.extend(ASSOC_CONSTS.iter().map(|(_, n, _)| n.to_string()));
    v.extend(ASSOC_FNS.iter().map(|(n, _)| n.to_string()));
    v.sort();
    v.dedup();
    v
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_list_every_row() {
        let n = names();
        for x in ["narrow_u8", "trunc_i64_sat", "to_bits", "len", "fill", "unwrap", "is_err", "PI", "BITS", "zeroed"] {
            assert!(n.iter().any(|y| y == x), "{x} not in {n:?}");
        }
        let mut sorted = n.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(n, sorted);
    }

    #[test]
    fn every_row_resolves_on_its_receiver() {
        let mut types = Types::default();
        let i32 = types.int(IntKind::I32);
        let u8 = types.int(IntKind::U8);
        let f32 = types.float(FloatKind::F32);
        let f64 = types.float(FloatKind::F64);
        let buf = types.builtin(BuiltinTy::Buf, vec![f32]);
        let s = types.builtin(BuiltinTy::Str, vec![]);
        let opt = types.builtin(BuiltinTy::Option, vec![f32]);
        let res = types.builtin(BuiltinTy::Result, vec![f32, s]);
        for m in methods() {
            let recv = match m.recv {
                Recv::Int | Recv::SignedInt => i32,
                Recv::Float => f32,
                Recv::Seq => buf,
                Recv::Str => s,
                Recv::Option => opt,
                Recv::Result => res,
            };
            assert!(method(&mut types, recv, &m.name).is_some(), "{}", m.name);
        }
        // `abs` is for signed integers only; `to_bits` follows the width
        assert!(method(&mut types, u8, "abs").is_none());
        let b32 = method(&mut types, f32, "to_bits").unwrap().ret;
        let b64 = method(&mut types, f64, "to_bits").unwrap().ret;
        assert!(matches!(types.get(b32), Ty::Int(IntKind::U32)));
        assert!(matches!(types.get(b64), Ty::Int(IntKind::U64)));
        assert!(method(&mut types, s, "fill").is_none());
        let bits = assoc_const(&mut types, i32, "BITS").unwrap();
        assert!(matches!(types.get(bits), Ty::Int(IntKind::U32)));
        assert_eq!(assoc_const(&mut types, f32, "PI"), Some(f32));
        assert_eq!(assoc_const(&mut types, i32, "PI"), None);
        assert!(assoc_fn(&mut types, Some(f64), None, "from_bits", f32).is_some());
        assert!(assoc_fn(&mut types, None, Some(BuiltinTy::Buf), "zeroed", f32).is_some());
        assert!(assoc_fn(&mut types, Some(i32), None, "from_bits", f32).is_none());
    }
}
