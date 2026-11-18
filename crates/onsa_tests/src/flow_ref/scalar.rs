//! The operators of §3.4 on the integers and floats of the evaluator, and `as`
//! (§3.3). An integer is computed exactly in an `i128` and then checked against
//! the range of its kind; a float is the host's `f32` or `f64`, whose `+ - * /`
//! round to nearest even, `%` is `fmod` and comparisons are IEEE (§3.4). A panic
//! (§9.2) is a value of [`Fault`], not a Rust panic.
//!
//! The checked methods (`checked_add`, ...) are these operators with the panic
//! turned into `None`; the conversions with a panic or an `Option`
//! (`trunc_from`, `narrow_from`, ...) and `std.math` are left to the host of the
//! evaluator's functions.

use super::value::{IntKind, Scalar, Value};

/// Why an operation panics (§9.2, the kinds of `tests/vectors/FORMAT.md`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PanicKind {
    /// The result does not fit the type (`-a` of `MIN`, `MIN / -1`).
    Overflow,
    DivZero,
    /// The amount of a shift is the bit width or more.
    Shift,
    /// An index out of the array (§9.2).
    Bounds,
    /// A call nested deeper than the limit of §12.5 (128).
    Depth,
    /// `panic(msg)` (§9.2).
    Explicit,
    /// A column of a `sample` input is not as long as the call (§11.6).
    Length,
    /// A function the interpreter ran for the host of the evaluator panicked: its kind and its message are the
    /// interpreter's, and only that it panicked is compared (W7-19).
    Host,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    Panic(PanicKind),
    /// The operands do not agree: the check of types rules the program out.
    Internal(&'static str),
    /// A form that this version of the evaluator does not take, or a table of the checker that is not whole.
    Unavailable(&'static str),
}

fn fail(kind: PanicKind) -> Result<Value, Fault> {
    Err(Fault::Panic(kind))
}

fn internal<T>(what: &'static str) -> Result<T, Fault> {
    Err(Fault::Internal(what))
}

/// The binary operators (the traits of §3.2): `+ - * / %`, `+% -% *%`, `+| -| *|`,
/// `div_euclid`, `rem_euclid`, `& | ^`, `<< >>` and the comparisons.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bin {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    WAdd,
    WSub,
    WMul,
    SAdd,
    SSub,
    SMul,
    DivEuclid,
    RemEuclid,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Un {
    Neg,
    Not,
}

/// `x + y` and the like on `f32` and `f64`: one rounding for each operation, no
/// fusing and no reassociation (§3.4). `%` of Rust is `fmod`: the exact remainder
/// with the sign of `x`, NaN for a zero `y` or an infinite `x`, and `x` for a
/// finite `x` and an infinite `y`.
macro_rules! float_binary {
    ($op:expr, $x:expr, $y:expr, $v:ident) => {
        match $op {
            Bin::Add => Ok(Value::$v($x + $y)),
            Bin::Sub => Ok(Value::$v($x - $y)),
            Bin::Mul => Ok(Value::$v($x * $y)),
            Bin::Div => Ok(Value::$v($x / $y)),
            Bin::Rem => Ok(Value::$v($x % $y)),
            op => compare(op, $x, $y),
        }
    };
}

pub fn binary(op: Bin, a: &Value, b: &Value) -> Result<Value, Fault> {
    match (a, b) {
        (Value::Int(k, x, _), Value::Int(IntKind::U32, n, _)) if matches!(op, Bin::Shl | Bin::Shr) => {
            shift(op, *k, *x, *n)
        }
        (Value::Int(k, x, _), Value::Int(l, y, _)) if k == l => int_binary(op, *k, *x, *y),
        (Value::F32(x), Value::F32(y)) => float_binary!(op, x, y, F32),
        (Value::F64(x), Value::F64(y)) => float_binary!(op, x, y, F64),
        // `Bool` and `()` have `==` and `!=` only (§6.3).
        (Value::Bool(x), Value::Bool(y)) if matches!(op, Bin::Eq | Bin::Ne) => compare(op, x, y),
        (Value::Char(x), Value::Char(y)) => compare(op, x, y),
        (Value::Unit, Value::Unit) if matches!(op, Bin::Eq | Bin::Ne) => compare(op, &(), &()),
        _ => internal("the operands of an operator do not agree"),
    }
}

/// The comparisons of two scalars. For a float they are IEEE: a NaN is not equal
/// to anything, itself included, and has no order; `-0.0 == 0.0`.
fn compare<T: PartialOrd>(op: Bin, x: &T, y: &T) -> Result<Value, Fault> {
    Ok(Value::Bool(match op {
        Bin::Eq => x == y,
        Bin::Ne => x != y,
        Bin::Lt => x < y,
        Bin::Le => x <= y,
        Bin::Gt => x > y,
        Bin::Ge => x >= y,
        _ => return internal("an operator that the type does not have"),
    }))
}

/// `v` as a value of `k`, modulo 2^bits (the two's complement wrap).
fn wrap(k: IntKind, v: i128) -> i128 {
    let m = 1i128 << k.bits();
    let r = v.rem_euclid(m);
    if r > k.range().1 { r - m } else { r }
}

fn int_binary(op: Bin, k: IntKind, x: i128, y: i128) -> Result<Value, Fault> {
    let int = |v: i128| Ok(Value::int(k, v));
    let (lo, hi) = k.range();
    let fit = |v: i128| if (lo..=hi).contains(&v) { int(v) } else { fail(PanicKind::Overflow) };
    // The product of two 64-bit values can leave the `i128`: then it is out of every range.
    let product = x.checked_mul(y);
    match op {
        Bin::Add => fit(x + y),
        Bin::Sub => fit(x - y),
        Bin::Mul => product.map_or_else(|| fail(PanicKind::Overflow), fit),
        Bin::Div | Bin::Rem | Bin::DivEuclid | Bin::RemEuclid if y == 0 => fail(PanicKind::DivZero),
        Bin::Div => fit(x / y),
        Bin::Rem => int(x % y),
        Bin::DivEuclid => fit(x.div_euclid(y)),
        Bin::RemEuclid => int(x.rem_euclid(y)),
        Bin::WAdd => int(wrap(k, x + y)),
        Bin::WSub => int(wrap(k, x - y)),
        Bin::WMul => int(wrap(k, x.wrapping_mul(y))),
        Bin::SAdd => int((x + y).clamp(lo, hi)),
        Bin::SSub => int((x - y).clamp(lo, hi)),
        // The product leaves the `i128` only for two `U64`, whose product is positive: it saturates upward.
        Bin::SMul => int(product.map_or(hi, |p| p.clamp(lo, hi))),
        Bin::And => int(x & y),
        Bin::Or => int(x | y),
        Bin::Xor => int(x ^ y),
        Bin::Shl | Bin::Shr => internal("the amount of a shift is a U32"),
        op => compare(op, &x, &y),
    }
}

/// `x << n` drops the bits that leave the type; `x >> n` fills with the sign of a
/// signed `x` and with 0 for an unsigned one. `n` of the bit width or more panics.
fn shift(op: Bin, k: IntKind, x: i128, n: i128) -> Result<Value, Fault> {
    if n >= i128::from(k.bits()) {
        return fail(PanicKind::Shift);
    }
    Ok(Value::int(k, if op == Bin::Shl { wrap(k, x << n) } else { x >> n }))
}

pub fn unary(op: Un, a: &Value) -> Result<Value, Fault> {
    match (op, a) {
        (Un::Neg, Value::F32(x)) => Ok(Value::F32(-x)),
        (Un::Neg, Value::F64(x)) => Ok(Value::F64(-x)),
        (Un::Neg, Value::Int(k, _, _)) if !k.signed() => internal("`-` of an unsigned integer is E0401"),
        (Un::Neg, Value::Int(k, x, _)) if *x == k.range().0 => fail(PanicKind::Overflow),
        (Un::Neg, Value::Int(k, x, _)) => Ok(Value::int(*k, -x)),
        // `!x` is `-x - 1`: the same bits flipped in the type, signed or not.
        (Un::Not, Value::Int(k, x, _)) => Ok(Value::int(*k, wrap(*k, !x))),
        (Un::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
        _ => internal("an operator that the type does not have"),
    }
}

/// `v as to` (§3.3): only the conversions that lose no information. The value
/// does not change.
pub fn cast(to: Scalar, v: &Value) -> Result<Value, Fault> {
    match (to, v) {
        (Scalar::Int(t), Value::Int(k, x, _)) if lossless_int(*k, t) => Ok(Value::int(t, *x)),
        (Scalar::F32, Value::Int(k, x, _)) if k.bits() <= 16 => Ok(Value::F32(*x as f32)),
        (Scalar::F64, Value::Int(k, x, _)) if k.bits() <= 32 => Ok(Value::F64(*x as f64)),
        (Scalar::F64, Value::F32(x)) => Ok(Value::F64(f64::from(*x))),
        (Scalar::F32, Value::F32(_)) | (Scalar::F64, Value::F64(_)) => Ok(v.clone()),
        _ => internal("`as` of a conversion that loses information is E0411"),
    }
}

/// The same sign and at least the width, or an unsigned type into a wider signed one.
fn lossless_int(from: IntKind, to: IntKind) -> bool {
    if from.signed() == to.signed() { to.bits() >= from.bits() } else { !from.signed() && to.bits() > from.bits() }
}
