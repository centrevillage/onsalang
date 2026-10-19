//! The rules of the numbers (spec §3.3, §3.4, S-25) and the checks of the
//! types of values (R-92 (1)).

use onsa_core::prim::MathFn;
use onsa_core::{BinOp, CmpOp, FloatKind, IntKind, Overflow, Ty, UnOp};
use onsa_diag::Span;

use crate::value::{self, Value, clamp_int, in_range, int_value, wrap_int};
use crate::{Interp, R, internal, panic};

impl<'m> Interp<'m> {
    // ------------------------------------------------------------ numerics

    pub(super) fn unary(&self, op: UnOp, v: Value, span: Span) -> R<Value> {
        Ok(match (op, v) {
            (UnOp::Neg, Value::F32(x)) => Value::F32(-x),
            (UnOp::Neg, Value::F64(x)) => Value::F64(-x),
            (UnOp::Neg, v) => {
                let k = int_kind_of(&v, span);
                let i = int_of(&v, k, span);
                let r = -i;
                if !in_range(k, r) {
                    return panic(span, format!("integer overflow in `-{i}`"));
                }
                int_value(k, r)
            }
            (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
            (UnOp::Not, v) => {
                let k = int_kind_of(&v, span);
                let i = int_of(&v, k, span);
                int_value(k, wrap_int(k, !i))
            }
        })
    }

    /// Off the way down a recursion through an operand (R-05).
    #[inline(never)]
    pub(super) fn binary(&self, op: BinOp, overflow: Overflow, a: Value, b: Value, span: Span) -> R<Value> {
        match (&a, &b) {
            (Value::F32(x), Value::F32(y)) => {
                let (x, y) = (*x, *y);
                return Ok(Value::F32(match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => internal(span, "bit operation on a float"),
                }));
            }
            (Value::F64(x), Value::F64(y)) => {
                let (x, y) = (*x, *y);
                return Ok(Value::F64(match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => internal(span, "bit operation on a float"),
                }));
            }
            (Value::Bool(x), Value::Bool(y)) => {
                return Ok(Value::Bool(match op {
                    BinOp::BitAnd => *x & *y,
                    BinOp::BitOr => *x | *y,
                    BinOp::BitXor => *x ^ *y,
                    _ => internal(span, "arithmetic on Bool"),
                }));
            }
            _ => {}
        }
        let k = int_kind_of(&a, span);
        let x = int_of(&a, k, span);
        // The amount of a shift is a `U32` (spec §3.4); the other operators
        // take two operands of one type.
        let y = match op {
            BinOp::Shl | BinOp::Shr => int_of(&b, IntKind::U32, span),
            _ => int_of(&b, k, span),
        };
        let bits = k.bits() as i128;
        let r = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => return arith(op, overflow, k, x, y, span),
            BinOp::Div => {
                if y == 0 {
                    return panic(span, "division by zero");
                }
                let q = x / y;
                if !in_range(k, q) {
                    return panic(span, format!("integer overflow in `{x} / {y}`"));
                }
                q
            }
            // `MIN % -1` is 0 (spec §3.4, R-19): only a zero divisor panics.
            BinOp::Rem => {
                if y == 0 {
                    return panic(span, "division by zero");
                }
                x % y
            }
            BinOp::BitAnd => x & y,
            BinOp::BitOr => x | y,
            BinOp::BitXor => x ^ y,
            BinOp::Shl | BinOp::Shr => {
                if y >= bits {
                    return panic(span, format!("shift amount {y} is not below the bit width {bits}"));
                }
                if op == BinOp::Shl { wrap_int(k, x << y) } else { x >> y }
            }
        };
        Ok(int_value(k, r))
    }

    pub(super) fn compare(&self, op: CmpOp, a: &Value, b: &Value, span: Span) -> R<bool> {
        use std::cmp::Ordering;
        let ord: Option<Ordering> = match (a, b) {
            (Value::F32(x), Value::F32(y)) => x.partial_cmp(y),
            (Value::F64(x), Value::F64(y)) => x.partial_cmp(y),
            (Value::Bool(x), Value::Bool(y)) => Some(x.cmp(y)),
            (Value::Char(x), Value::Char(y)) => Some(x.cmp(y)),
            (Value::Unit, Value::Unit) => Some(Ordering::Equal),
            _ => {
                let k = int_kind_of(a, span);
                Some(int_of(a, k, span).cmp(&int_of(b, k, span)))
            }
        };
        Ok(match (op, ord) {
            (CmpOp::Eq, o) => o == Some(Ordering::Equal),
            (CmpOp::Ne, o) => o != Some(Ordering::Equal),
            (CmpOp::Lt, o) => o == Some(Ordering::Less),
            (CmpOp::Le, o) => matches!(o, Some(Ordering::Less | Ordering::Equal)),
            (CmpOp::Gt, o) => o == Some(Ordering::Greater),
            (CmpOp::Ge, o) => matches!(o, Some(Ordering::Greater | Ordering::Equal)),
        })
    }

    /// Lossless widening (§3.3) of `v`, of type `from`, to `to`. The value
    /// has the type the operand declares (R-92 (1)).
    pub(super) fn cast(&self, v: Value, from: &Ty, to: &Ty, span: Span) -> R<Value> {
        Ok(match (from, to) {
            (Ty::Float(fk), Ty::Float(k)) => {
                // Exact: an `F32` is exact as an `f64`, and back.
                let x = float_of(&v, *fk, span);
                match (fk, k) {
                    (FloatKind::F32, FloatKind::F32) => Value::F32(x as f32),
                    (_, FloatKind::F64) => Value::F64(x),
                    (FloatKind::F64, FloatKind::F32) => {
                        internal(span, "the cast of an `F64` to `F32` loses information")
                    }
                }
            }
            (Ty::Int(fk), Ty::Float(k)) => {
                let i = int_of(&v, *fk, span);
                match k {
                    FloatKind::F32 => Value::F32(i as f32),
                    FloatKind::F64 => Value::F64(i as f64),
                }
            }
            (Ty::Int(fk), Ty::Int(k)) => match int_of(&v, *fk, span) {
                i if in_range(*k, i) => int_value(*k, i),
                i => internal(span, format!("the cast of {i} to `{}` loses information", k.name())),
            },
            _ => internal(span, "a cast that is not a widening of numbers"),
        })
    }
}

/// `x + y`, `x - y`, `x * y` on integers of kind `k` (spec §3.4, R-04). The
/// exact result when `i128` holds it, which it does for every sum and
/// difference of 64-bit values and every product but one of two `U64`s above
/// 2^127; such a product is beyond every type, and positive.
fn arith(op: BinOp, overflow: Overflow, k: IntKind, x: i128, y: i128, span: Span) -> R<Value> {
    let (exact, wrapped, sym) = match op {
        BinOp::Add => (x.checked_add(y), x.wrapping_add(y), "+"),
        BinOp::Sub => (x.checked_sub(y), x.wrapping_sub(y), "-"),
        BinOp::Mul => (x.checked_mul(y), x.wrapping_mul(y), "*"),
        _ => internal(span, "not an arithmetic operator"),
    };
    let r = match (overflow, exact) {
        // Modulo 2^128, so modulo 2^(bit width) too.
        (Overflow::Wrap, _) => wrap_int(k, wrapped),
        (Overflow::Sat, Some(r)) => clamp_int(k, r),
        (Overflow::Sat, None) => {
            let (lo, hi) = value::int_range(k);
            if (x < 0) != (y < 0) { lo } else { hi }
        }
        (Overflow::Checked, Some(r)) if in_range(k, r) => r,
        (Overflow::Checked, _) => {
            return panic(span, format!("integer overflow in `{x} {sym} {y}` ({})", k.name()));
        }
    };
    Ok(int_value(k, r))
}

/// `trunc_<type>()` and `trunc_<type>_sat()` of `x` (spec §3.3, §3.4): toward
/// zero; out of range or NaN is a panic, or the bound and 0 for `_sat`. The
/// range is `lo <= t < above`, with `above` the power of two just past the
/// type's maximum: both exact as `f64`, where the maximum of a 64-bit type is
/// not (R-19).
pub(super) fn trunc_to_int(x: f64, from: FloatKind, to: IntKind, sat: bool, span: Span) -> R<i128> {
    let (lo, hi) = value::int_range(to);
    let above = (hi + 1) as f64;
    if x.is_nan() {
        return if sat { Ok(0) } else { panic(span, "conversion of NaN to an integer") };
    }
    let t = x.trunc();
    if t < lo as f64 || t >= above {
        return if sat {
            Ok(if t < lo as f64 { lo } else { hi })
        } else {
            // The value in the `Show` form of its own type (`spec/tools.md` §4):
            // an `F32` widened to `f64` is exact, and goes back exactly.
            let shown = value::show(&match from {
                FloatKind::F32 => Value::F32(x as f32),
                FloatKind::F64 => Value::F64(x),
            });
            panic(span, format!("{shown} is out of range for {}", to.name()))
        };
    }
    Ok(t as i128)
}

/// A value of the wrong type where Core's types promise another (R-92 (1)):
/// the interpreter never reads it as 0 or `false`, it is an internal error
/// (the Core verifier missed it, S-67).
#[cold]
#[inline(never)]
#[track_caller]
pub(super) fn mismatch(span: Span, expected: &str, got: &Value) -> ! {
    internal(span, format!("{expected} expected, found {}", value_kind(got)))
}

/// The kind of a value, for the message of [`mismatch`].
fn value_kind(v: &Value) -> String {
    match v {
        Value::F32(_) => "an `F32`".into(),
        Value::F64(_) => "an `F64`".into(),
        Value::Bool(_) => "a `Bool`".into(),
        Value::Char(_) => "a `Char`".into(),
        Value::Unit => "`()`".into(),
        Value::Array(_) => "an array".into(),
        Value::Tuple(_) => "a tuple".into(),
        Value::Struct(_) => "a struct".into(),
        Value::Enum { .. } => "an enum".into(),
        Value::Span(_) => "a `Span`".into(),
        Value::Buf(_) => "a `Buf`".into(),
        Value::Fn(_) => "a function".into(),
        v => match v.int_kind() {
            Some(k) => format!("an integer of `{}`", k.name()),
            None => "a value".into(),
        },
    }
}

/// The checks of the types of values (R-92 (1)): the one place the
/// interpreter compares a value with the type Core gives it. Each stops with
/// [`mismatch`], at its caller (`#[track_caller]`).
///
/// The kind of the integer `v`.
#[track_caller]
pub(super) fn int_kind_of(v: &Value, span: Span) -> IntKind {
    // A `match`, not a closure: `#[track_caller]` does not pass through one.
    match v.int_kind() {
        Some(k) => k,
        None => mismatch(span, "an integer", v),
    }
}

/// The `Bool` in `v`.
#[track_caller]
pub(super) fn bool_of(v: &Value, span: Span) -> bool {
    match v {
        Value::Bool(b) => *b,
        _ => mismatch(span, "a `Bool`", v),
    }
}

/// The integer of kind `k` in `v` (R-92 (1)).
#[track_caller]
pub(super) fn int_of(v: &Value, k: IntKind, span: Span) -> i128 {
    match (v.int_kind(), v.to_i128()) {
        (Some(vk), Some(i)) if vk == k => i,
        _ => mismatch(span, &format!("an integer of `{}`", k.name()), v),
    }
}

/// The float of kind `k` in `v`, as `f64` (exact for `F32`) (R-92 (1)).
#[track_caller]
pub(super) fn float_of(v: &Value, k: FloatKind, span: Span) -> f64 {
    match (v, k) {
        (Value::F32(x), FloatKind::F32) => *x as f64,
        (Value::F64(x), FloatKind::F64) => *x,
        _ => mismatch(span, &format!("an `{}`", k.name()), v),
    }
}

pub(super) fn some(v: Value) -> Value {
    Value::Enum { tag: 1, fields: vec![v] }
}

pub(super) fn none() -> Value {
    Value::Enum { tag: 0, fields: Vec::new() }
}

/// Round half to even (S-25).
fn round_even_f32(x: f32) -> f32 {
    x.round_ties_even()
}

fn round_even_f64(x: f64) -> f64 {
    x.round_ties_even()
}

/// `min` / `max` with NaN propagation and signed zeros ordered (S-25).
fn min_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        return f64::NAN;
    }
    if a == 0.0 && b == 0.0 {
        return if a.is_sign_negative() || b.is_sign_negative() { -0.0 } else { 0.0 };
    }
    if a < b { a } else { b }
}

fn max_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        return f64::NAN;
    }
    if a == 0.0 && b == 0.0 {
        return if a.is_sign_negative() && b.is_sign_negative() { -0.0 } else { 0.0 };
    }
    if a > b { a } else { b }
}

pub(super) fn math_f32(mf: MathFn, x: f32, y: f32) -> f32 {
    match mf {
        MathFn::Exp => x.exp(),
        MathFn::Exp2 => x.exp2(),
        MathFn::Log => x.ln(),
        MathFn::Log2 => x.log2(),
        MathFn::Sin => x.sin(),
        MathFn::Cos => x.cos(),
        MathFn::Tan => x.tan(),
        MathFn::Tanh => x.tanh(),
        MathFn::Pow => x.powf(y),
        MathFn::Sqrt => x.sqrt(),
        MathFn::Floor => x.floor(),
        MathFn::Ceil => x.ceil(),
        MathFn::Trunc => x.trunc(),
        MathFn::Round => round_even_f32(x),
        MathFn::Abs => x.abs(),
        MathFn::Min => min_f64(x as f64, y as f64) as f32,
        MathFn::Max => max_f64(x as f64, y as f64) as f32,
        MathFn::Fmod => x % y,
    }
}

pub(super) fn math_f64(mf: MathFn, x: f64, y: f64) -> f64 {
    match mf {
        MathFn::Exp => x.exp(),
        MathFn::Exp2 => x.exp2(),
        MathFn::Log => x.ln(),
        MathFn::Log2 => x.log2(),
        MathFn::Sin => x.sin(),
        MathFn::Cos => x.cos(),
        MathFn::Tan => x.tan(),
        MathFn::Tanh => x.tanh(),
        MathFn::Pow => x.powf(y),
        MathFn::Sqrt => x.sqrt(),
        MathFn::Floor => x.floor(),
        MathFn::Ceil => x.ceil(),
        MathFn::Trunc => x.trunc(),
        MathFn::Round => round_even_f64(x),
        MathFn::Abs => x.abs(),
        MathFn::Min => min_f64(x, y),
        MathFn::Max => max_f64(x, y),
        MathFn::Fmod => x % y,
    }
}
