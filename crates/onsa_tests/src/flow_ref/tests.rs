//! The tests of the values and the arithmetic of the evaluator (W7-01 U2).
//!
//! Two sources, neither of them the interpreter (Q-02 (a)):
//! - the `edge` rows of `tests/vectors/` (the data is a source of the spec's side,
//!   `tests/vectors/FORMAT.md`), for the operators and `as` the evaluator has;
//! - values worked out by hand from §3.3, §3.4 and §6.3, for what the rows of
//!   `edge` leave out or say less sharply (each with the rule that gives it).

use std::collections::BTreeMap;

use super::scalar::{Bin, Fault, PanicKind, Un, binary, cast, unary};
use super::value::{IntKind, Scalar, Shape, Value};
use crate::case::repo_root;
use crate::vectors::data::{Data, Expect};

fn scalar_of(ty: &str) -> Option<Scalar> {
    Some(match ty {
        "I8" => Scalar::Int(IntKind::I8),
        "I16" => Scalar::Int(IntKind::I16),
        "I32" => Scalar::Int(IntKind::I32),
        "I64" => Scalar::Int(IntKind::I64),
        "U8" => Scalar::Int(IntKind::U8),
        "U16" => Scalar::Int(IntKind::U16),
        "U32" => Scalar::Int(IntKind::U32),
        "U64" => Scalar::Int(IntKind::U64),
        "F32" => Scalar::F32,
        "F64" => Scalar::F64,
        "Bool" => Scalar::Bool,
        _ => return None,
    })
}

/// A value as `tests/vectors/FORMAT.md` writes it: decimal, the hex bits of a float, `true`.
fn parse(ty: Scalar, text: &str) -> Value {
    let hex = |digits: usize| {
        let h = text.strip_prefix("0x").unwrap_or_else(|| panic!("`{text}`: a float is written in hex bits"));
        assert_eq!(h.len(), digits, "`{text}`");
        u64::from_str_radix(h, 16).unwrap_or_else(|e| panic!("`{text}`: {e}"))
    };
    match ty {
        Scalar::Int(k) => Value::Int(k, text.parse().unwrap_or_else(|e| panic!("`{text}`: {e}"))),
        Scalar::F32 => Value::F32(f32::from_bits(hex(8) as u32)),
        Scalar::F64 => Value::F64(f64::from_bits(hex(16))),
        Scalar::Bool => Value::Bool(text == "true"),
        Scalar::Char | Scalar::Unit => panic!("the vectors have no such value"),
    }
}

/// What a row asks of the evaluator, by the name of its operation (`i32.add` is `add`).
enum Plan {
    Bin(Bin),
    Un(Un),
    As(Scalar),
}

fn plan(name: &str) -> Option<Plan> {
    // A checked method is the operator with its panic turned into `None` (§3.4).
    let operator = name.strip_prefix("checked_").unwrap_or(name);
    Some(Plan::Bin(match operator {
        "add" => Bin::Add,
        "sub" => Bin::Sub,
        "mul" => Bin::Mul,
        "div" => Bin::Div,
        "rem" => Bin::Rem,
        "wadd" => Bin::WAdd,
        "wsub" => Bin::WSub,
        "wmul" => Bin::WMul,
        "sadd" => Bin::SAdd,
        "ssub" => Bin::SSub,
        "smul" => Bin::SMul,
        "div_euclid" => Bin::DivEuclid,
        "rem_euclid" => Bin::RemEuclid,
        "and" => Bin::And,
        "or" => Bin::Or,
        "xor" => Bin::Xor,
        "shl" => Bin::Shl,
        "shr" => Bin::Shr,
        "eq" => Bin::Eq,
        "ne" => Bin::Ne,
        "lt" => Bin::Lt,
        "le" => Bin::Le,
        "gt" => Bin::Gt,
        "ge" => Bin::Ge,
        "neg" => return Some(Plan::Un(Un::Neg)),
        "not" => return Some(Plan::Un(Un::Not)),
        _ => return Some(Plan::As(scalar_of(&name.strip_prefix("as_")?.to_uppercase())?)),
    }))
}

/// The operations of the rows that are not the evaluator's: `std.math` and the
/// conversions with a panic or an `Option` (the host of the functions), the
/// associated constants that are literals, and the expression forms of §3.4, which
/// are the expressions of U3. Any other operation without a plan fails the test.
fn not_the_evaluators(name: &str) -> bool {
    ["narrow_", "trunc_", "round_", "expr_", "vdelay_"].iter().any(|p| name.starts_with(p))
        || [
            "min",
            "max",
            "abs",
            "sqrt",
            "floor",
            "ceil",
            "trunc",
            "round",
            "is_nan",
            "is_finite",
            "to_bits",
            "from_bits",
            "PI",
            "MAX",
            "EPSILON",
            "INFINITY",
            "NAN",
            "ONE",
        ]
        .contains(&name)
}

fn judge(expect: &Expect, ret: Scalar, got: &Result<Value, Fault>) -> Result<(), String> {
    match (expect, got) {
        (Expect::Value(t) | Expect::Some(t), Ok(v)) if v.same(&parse(ret, t)) => Ok(()),
        (Expect::Nan, Ok(Value::F32(x))) if x.is_nan() => Ok(()),
        (Expect::Nan, Ok(Value::F64(x))) if x.is_nan() => Ok(()),
        (Expect::None, Err(Fault::Panic(_))) => Ok(()),
        (Expect::Panic(kind), Err(Fault::Panic(p))) => match (kind.as_str(), p) {
            ("overflow", PanicKind::Overflow) | ("div-zero", PanicKind::DivZero) | ("shift", PanicKind::Shift) => {
                Ok(())
            }
            _ => Err(format!("panics with {p:?}, expected `{kind}`")),
        },
        _ => Err(format!("got {got:?}, expected `{}`", expect.text())),
    }
}

/// The type of the operation, from its name `i32.add`, as the evaluator's scalar.
fn type_of(op_id: &str) -> Scalar {
    scalar_of(&op_id.split_once('.').expect("an operation is `<type>.<name>`").0.to_uppercase()).expect("a scalar type")
}

#[test]
fn the_edge_rows_of_the_vectors() {
    let data = Data::load(&repo_root()).unwrap_or_else(|e| panic!("the vectors do not load: {e:?}"));
    let mut failures = Vec::new();
    let mut checked: BTreeMap<String, usize> = BTreeMap::new();
    let mut skipped: BTreeMap<String, usize> = BTreeMap::new();
    for row in data.rows.iter().filter(|r| r.stage == "edge") {
        let op = &data.ops[row.op];
        let (ty, name) = op.id.split_once('.').expect("an operation is `<type>.<name>`");
        let own = type_of(&op.id);
        let ret = scalar_of(op.ret.trim_start_matches("Option[").trim_end_matches(']'))
            .unwrap_or_else(|| panic!("{}: result `{}`", op.id, op.ret));
        let args: Vec<Value> =
            op.args.iter().zip(&row.args).filter_map(|(t, a)| Some(parse(scalar_of(t)?, a))).collect();
        let got = match (plan(name), name) {
            (Some(Plan::Bin(b)), _) => binary(b, &args[0], &args[1]),
            (Some(Plan::Un(u)), _) => unary(u, &args[0]),
            (Some(Plan::As(to)), _) => cast(to, &args[0]),
            // The constants of an integer type, from its kind: `MIN`, `MAX`, `BITS` (a `U32`), `ZERO` is its default.
            (None, "MIN" | "MAX" | "BITS" | "ZERO") if matches!(own, Scalar::Int(_)) => {
                let Scalar::Int(k) = own else { unreachable!() };
                Ok(match name {
                    "MIN" => Value::Int(k, k.min()),
                    "MAX" => Value::Int(k, k.max()),
                    "BITS" => Value::Int(IntKind::U32, i128::from(k.bits())),
                    _ => own.default_value().expect("an integer has a default"),
                })
            }
            (None, "ZERO") => Ok(own.default_value().expect("a float has a default")),
            (None, _) if not_the_evaluators(name) => {
                *skipped.entry(format!("{ty}.{name}")).or_default() += 1;
                continue;
            }
            (None, _) => {
                failures.push(format!("{}: no plan for `{}` and not in the list of the skipped", row.at(), op.id));
                continue;
            }
        };
        *checked.entry(op.id.clone()).or_default() += 1;
        if let Err(why) = judge(&row.expect, ret, &got) {
            failures.push(format!("{} {} {}: {why}", row.at(), op.id, row.args.join(" ")));
        }
    }
    assert!(
        failures.is_empty(),
        "{} rows differ, the first: {:#?}",
        failures.len(),
        &failures[..failures.len().min(20)]
    );
    // Something ran for every type: every integer type has its operators, every float its own.
    for ty in ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"] {
        let n = checked.keys().filter(|k| k.starts_with(&format!("{ty}."))).count();
        assert!(n >= 30, "{ty}: only {n} operations ran");
    }
    for ty in ["f32", "f64"] {
        let n = checked.keys().filter(|k| k.starts_with(&format!("{ty}."))).count();
        assert!(n >= 10, "{ty}: only {n} operations ran");
    }
    eprintln!(
        "edge rows checked: {} in {} operations; skipped (not the evaluator's): {} in {} operations",
        checked.values().sum::<usize>(),
        checked.len(),
        skipped.values().sum::<usize>(),
        skipped.len()
    );
}

// What `edge` leaves out or says less sharply, by hand from the spec.

fn int(k: IntKind, v: i128) -> Value {
    Value::Int(k, v)
}

fn f32b(bits: u32) -> Value {
    Value::F32(f32::from_bits(bits))
}

const NEG0: u32 = 0x8000_0000;
const INF: u32 = 0x7f80_0000;

/// A hand-worked case: the operation, its operands, and the value (`Ok`) or the panic (`Err`).
type Case = (Bin, Value, Value, Result<Value, PanicKind>);

fn check(cases: &[Case]) {
    for (op, a, b, want) in cases {
        let got = binary(*op, a, b);
        let ok = match (&got, want) {
            (Ok(g), Ok(w)) => g.same(w),
            (Err(Fault::Panic(g)), Err(w)) => g == w,
            _ => false,
        };
        assert!(ok, "{op:?} {a:?} {b:?}: got {got:?}, want {want:?}");
    }
}

#[test]
fn float_remainder_is_fmod_with_the_sign_of_the_dividend() {
    // §3.4: `a % b` is `a - b * trunc(a / b)` unrounded, the sign of `a`; NaN for a zero `b` or an infinite
    // `a`; `a` for a finite `a` and an infinite `b`, `-0.0` kept.
    let f = Value::F32;
    check(&[
        (Bin::Rem, f(5.5), f(2.0), Ok(f(1.5))),
        (Bin::Rem, f(-5.5), f(2.0), Ok(f(-1.5))),
        (Bin::Rem, f(5.5), f(-2.0), Ok(f(1.5))),
        (Bin::Rem, f(-5.5), f(-2.0), Ok(f(-1.5))),
        // The exact remainder is 0 and keeps the sign of `a`.
        (Bin::Rem, f(-4.0), f(2.0), Ok(f32b(NEG0))),
        (Bin::Rem, f(4.0), f(-2.0), Ok(f(0.0))),
        (Bin::Rem, f(1.0), f(0.0), Ok(f(f32::NAN))),
        (Bin::Rem, f32b(INF), f(2.0), Ok(f(f32::NAN))),
        (Bin::Rem, f(3.0), f32b(INF), Ok(f(3.0))),
        (Bin::Rem, f(-3.0), f32b(INF), Ok(f(-3.0))),
        (Bin::Rem, f32b(NEG0), f32b(INF), Ok(f32b(NEG0))),
        // `0.3` is 0x3e99999a and `0.1` is 0x3dcccccd: the quotient is 3 and the remainder
        // 0.3 - 3 * 0.1 = 2^-27 exactly (0x32000000), where a rounded `a / b` could give 0.1.
        (Bin::Rem, f(0.3), f(0.1), Ok(f32b(0x3200_0000))),
    ]);
    // The same in F64: `7.5 % -2.0 = 1.5`, `-7.5 % 2.0 = -1.5`.
    let d = Value::F64;
    check(&[(Bin::Rem, d(7.5), d(-2.0), Ok(d(1.5))), (Bin::Rem, d(-7.5), d(2.0), Ok(d(-1.5)))]);
}

#[test]
fn float_zeros_have_their_signs() {
    // §3.4: a sum that is exactly 0 is `-0.0` only when both operands are `-0.0`; `a - b` is `a + (-b)`;
    // the sign of a product and of a quotient is the xor of the signs, even for a zero or an infinity;
    // a non-zero result that rounds to 0 keeps its sign.
    let f = Value::F32;
    let (nz, pz) = (f32b(NEG0), f(0.0));
    check(&[
        (Bin::Add, nz.clone(), nz.clone(), Ok(nz.clone())),
        (Bin::Add, nz.clone(), pz.clone(), Ok(pz.clone())),
        (Bin::Add, pz.clone(), nz.clone(), Ok(pz.clone())),
        (Bin::Add, f(1.0), f(-1.0), Ok(pz.clone())),
        (Bin::Sub, nz.clone(), pz.clone(), Ok(nz.clone())),
        (Bin::Sub, pz.clone(), pz.clone(), Ok(pz.clone())),
        (Bin::Sub, nz.clone(), nz.clone(), Ok(pz.clone())),
        (Bin::Sub, f(1.0), f(1.0), Ok(pz.clone())),
        (Bin::Mul, nz.clone(), f(1.0), Ok(nz.clone())),
        (Bin::Mul, f(-1.0), pz.clone(), Ok(nz.clone())),
        (Bin::Mul, nz.clone(), f(-1.0), Ok(pz.clone())),
        (Bin::Div, pz.clone(), f(-1.0), Ok(nz.clone())),
        // 1e-30 is 0x0da24260 and its square, 1e-60, is below the smallest subnormal.
        (Bin::Mul, f32b(0x0da2_4260), f32b(0x8da2_4260), Ok(nz.clone())),
        (Bin::Mul, f32b(0x0da2_4260), f32b(0x0da2_4260), Ok(pz.clone())),
        (Bin::Div, f(1.0), pz.clone(), Ok(f32b(INF))),
        (Bin::Div, f(-1.0), pz.clone(), Ok(f32b(INF | NEG0))),
        (Bin::Div, f(1.0), nz.clone(), Ok(f32b(INF | NEG0))),
        (Bin::Div, pz.clone(), pz.clone(), Ok(f(f32::NAN))),
        (Bin::Mul, nz.clone(), f32b(INF), Ok(f(f32::NAN))),
        (Bin::Sub, f32b(INF), f32b(INF), Ok(f(f32::NAN))),
        (Bin::Add, f32b(0x7f7f_ffff), f32b(0x7f7f_ffff), Ok(f32b(INF))),
    ]);
}

#[test]
fn float_operations_round_once_to_nearest_even() {
    // 2^24 + 1 is half way between 2^24 and 2^24 + 2: the even one is 2^24; 2^24 + 3 is half way between
    // 2^24 + 2 and 2^24 + 4 (mantissas 2^23 + 1 and 2^23 + 2): the even one is 2^24 + 4.
    let f = Value::F32;
    check(&[
        (Bin::Add, f(16777216.0), f(1.0), Ok(f(16777216.0))),
        (Bin::Add, f(16777216.0), f(3.0), Ok(f(16777220.0))),
        // 1 / 3 rounds to 0x3eaaaaab, the nearest to the third (an F64 `1.0 / 3.0` is not a F32).
        (Bin::Div, f(1.0), f(3.0), Ok(f32b(0x3eaa_aaab))),
        // 1.1 is 0x3f8ccccd; its square is 1.2100000... which rounds to 0x3f9ae148.
        (Bin::Mul, f32b(0x3f8c_cccd), f32b(0x3f8c_cccd), Ok(f32b(0x3f9a_e148))),
    ]);
}

#[test]
fn float_comparisons_are_ieee() {
    // §3.4: NaN is equal to nothing, itself included, and has no order, so only `!=` is true; `-0.0 == 0.0`.
    let (nan, one, nz, pz) = (Value::F32(f32::NAN), Value::F32(1.0), f32b(NEG0), Value::F32(0.0));
    let t = |b: bool| Ok(Value::Bool(b));
    let nan64 = Value::F64(f64::NAN);
    check(&[
        (Bin::Eq, nan.clone(), nan.clone(), t(false)),
        (Bin::Ne, nan.clone(), nan.clone(), t(true)),
        (Bin::Lt, nan.clone(), one.clone(), t(false)),
        (Bin::Le, nan.clone(), one.clone(), t(false)),
        (Bin::Gt, one.clone(), nan.clone(), t(false)),
        (Bin::Ge, one.clone(), nan.clone(), t(false)),
        (Bin::Ne, one.clone(), nan.clone(), t(true)),
        (Bin::Eq, nz.clone(), pz.clone(), t(true)),
        (Bin::Lt, nz.clone(), pz.clone(), t(false)),
        (Bin::Le, nz, pz, t(true)),
        (Bin::Lt, one, f32b(INF), t(true)),
        (Bin::Eq, nan64.clone(), nan64, t(false)),
    ]);
}

#[test]
fn float_negation_flips_the_sign() {
    let neg = |v: Value| unary(Un::Neg, &v).expect("a float negates");
    assert!(neg(Value::F32(0.0)).same(&f32b(NEG0)));
    assert!(neg(f32b(NEG0)).same(&Value::F32(0.0)));
    assert!(neg(f32b(INF)).same(&f32b(INF | NEG0)));
    assert!(neg(Value::F32(f32::NAN)).same(&Value::F32(f32::NAN)));
    assert!(neg(Value::F64(0.0)).same(&Value::F64(-0.0)));
}

#[test]
fn integer_saturation_and_wrap_at_the_ends() {
    use IntKind::*;
    let n = int;
    check(&[
        (Bin::SAdd, n(I8, 127), n(I8, 1), Ok(n(I8, 127))),
        (Bin::SSub, n(I8, -128), n(I8, 1), Ok(n(I8, -128))),
        (Bin::SMul, n(I8, 100), n(I8, 2), Ok(n(I8, 127))),
        (Bin::SMul, n(I8, -100), n(I8, 2), Ok(n(I8, -128))),
        (Bin::SMul, n(I8, -128), n(I8, -1), Ok(n(I8, 127))),
        (Bin::SAdd, n(U8, 200), n(U8, 100), Ok(n(U8, 255))),
        (Bin::SSub, n(U8, 0), n(U8, 1), Ok(n(U8, 0))),
        // A 64-bit product leaves the `i64` range by far: it is saturated by its sign.
        (Bin::SMul, n(U64, u64::MAX.into()), n(U64, u64::MAX.into()), Ok(n(U64, u64::MAX.into()))),
        (Bin::SMul, n(I64, i64::MIN.into()), n(I64, i64::MIN.into()), Ok(n(I64, i64::MAX.into()))),
        (Bin::SMul, n(I64, i64::MIN.into()), n(I64, i64::MAX.into()), Ok(n(I64, i64::MIN.into()))),
        (Bin::WAdd, n(I8, 127), n(I8, 1), Ok(n(I8, -128))),
        (Bin::WSub, n(I8, -128), n(I8, 1), Ok(n(I8, 127))),
        (Bin::WSub, n(U8, 0), n(U8, 1), Ok(n(U8, 255))),
        (Bin::WAdd, n(U32, u32::MAX.into()), n(U32, 1), Ok(n(U32, 0))),
        // (2^64 - 1)^2 = 2^128 - 2^65 + 1, which is 1 modulo 2^64.
        (Bin::WMul, n(U64, u64::MAX.into()), n(U64, u64::MAX.into()), Ok(n(U64, 1))),
        (Bin::WMul, n(I64, i64::MIN.into()), n(I64, -1), Ok(n(I64, i64::MIN.into()))),
        (Bin::WMul, n(I8, 16), n(I8, 8), Ok(n(I8, -128))),
    ]);
}

#[test]
fn integer_overflow_and_zero_division_panic() {
    use IntKind::*;
    use PanicKind::{DivZero, Overflow};
    let n = int;
    check(&[
        (Bin::Sub, n(U8, 0), n(U8, 1), Err(Overflow)),
        (Bin::Add, n(I8, 127), n(I8, 1), Err(Overflow)),
        // The product of two `u64` does not even fit 127 bits.
        (Bin::Mul, n(U64, u64::MAX.into()), n(U64, u64::MAX.into()), Err(Overflow)),
        (Bin::Mul, n(I64, i64::MIN.into()), n(I64, -1), Err(Overflow)),
        (Bin::Div, n(I64, i64::MIN.into()), n(I64, -1), Err(Overflow)),
        (Bin::DivEuclid, n(I8, -128), n(I8, -1), Err(Overflow)),
        // §3.4: `MIN % -1` and `MIN.rem_euclid(-1)` are 0 and do not panic.
        (Bin::Rem, n(I64, i64::MIN.into()), n(I64, -1), Ok(n(I64, 0))),
        (Bin::RemEuclid, n(I8, -128), n(I8, -1), Ok(n(I8, 0))),
        (Bin::Div, n(I32, 1), n(I32, 0), Err(DivZero)),
        (Bin::Rem, n(I32, 1), n(I32, 0), Err(DivZero)),
        (Bin::DivEuclid, n(U8, 1), n(U8, 0), Err(DivZero)),
        (Bin::RemEuclid, n(U8, 1), n(U8, 0), Err(DivZero)),
        // Division truncates toward zero and `%` has the sign of the dividend.
        (Bin::Div, n(I32, -7), n(I32, 2), Ok(n(I32, -3))),
        (Bin::Rem, n(I32, -7), n(I32, 2), Ok(n(I32, -1))),
        (Bin::Rem, n(I32, 7), n(I32, -2), Ok(n(I32, 1))),
        // `0 <= r < |b|` and `a == q * b + r`: -7 = -4 * 2 + 1, 7 = -3 * -2 + 1, -7 = 4 * -2 + 1.
        (Bin::DivEuclid, n(I32, -7), n(I32, 2), Ok(n(I32, -4))),
        (Bin::RemEuclid, n(I32, -7), n(I32, 2), Ok(n(I32, 1))),
        (Bin::DivEuclid, n(I32, 7), n(I32, -2), Ok(n(I32, -3))),
        (Bin::RemEuclid, n(I32, 7), n(I32, -2), Ok(n(I32, 1))),
        (Bin::DivEuclid, n(I32, -7), n(I32, -2), Ok(n(I32, 4))),
        (Bin::RemEuclid, n(I32, -7), n(I32, -2), Ok(n(I32, 1))),
    ]);
}

#[test]
fn shifts_and_bit_operations() {
    use IntKind::*;
    use PanicKind::Shift;
    let (n, u) = (int, |v: i128| int(U32, v));
    check(&[
        // `>>` fills with the sign of a signed type and with 0 for an unsigned one.
        (Bin::Shr, n(I8, -128), u(7), Ok(n(I8, -1))),
        (Bin::Shr, n(I8, -1), u(1), Ok(n(I8, -1))),
        (Bin::Shr, n(U8, 255), u(7), Ok(n(U8, 1))),
        // `<<` drops the bits that leave the type: 0b0100_0000 << 1 is 0b1000_0000.
        (Bin::Shl, n(I8, 64), u(1), Ok(n(I8, -128))),
        (Bin::Shl, n(I8, 127), u(7), Ok(n(I8, -128))),
        (Bin::Shl, n(I64, 1), u(63), Ok(n(I64, i64::MIN.into()))),
        (Bin::Shl, n(U64, 1), u(63), Ok(n(U64, 1 << 63))),
        (Bin::Shl, n(U64, u64::MAX.into()), u(63), Ok(n(U64, 1 << 63))),
        // The amount of the bit width or more panics, whatever the value.
        (Bin::Shl, n(I8, 0), u(8), Err(Shift)),
        (Bin::Shr, n(U32, 0), u(32), Err(Shift)),
        (Bin::Shl, n(I64, 1), u(64), Err(Shift)),
        (Bin::Shr, n(U64, 1), u(u32::MAX.into()), Err(Shift)),
        // The bits of a negative number are those of its two's complement: -16 is 0xF0.
        (Bin::And, n(I8, -16), n(I8, 0x7f), Ok(n(I8, 0x70))),
        (Bin::Or, n(I8, -16), n(I8, 15), Ok(n(I8, -1))),
        (Bin::Xor, n(I8, -1), n(I8, 1), Ok(n(I8, -2))),
        (Bin::Gt, n(U64, u64::MAX.into()), n(U64, 0), Ok(Value::Bool(true))),
        (Bin::Lt, n(I8, -1), n(I8, 0), Ok(Value::Bool(true))),
    ]);
}

#[test]
fn unary_operators() {
    use IntKind::*;
    let un = |op, v: Value| unary(op, &v);
    assert!(un(Un::Not, int(U8, 0)).unwrap().same(&int(U8, 255)));
    assert!(un(Un::Not, int(U8, 255)).unwrap().same(&int(U8, 0)));
    assert!(un(Un::Not, int(I8, 0)).unwrap().same(&int(I8, -1)));
    assert!(un(Un::Not, int(I8, -128)).unwrap().same(&int(I8, 127)));
    assert!(un(Un::Not, Value::Bool(true)).unwrap().same(&Value::Bool(false)));
    assert!(un(Un::Neg, int(I32, 0)).unwrap().same(&int(I32, 0)));
    assert!(un(Un::Neg, int(I8, 127)).unwrap().same(&int(I8, -127)));
    assert_eq!(un(Un::Neg, int(I8, -128)).unwrap_err(), Fault::Panic(PanicKind::Overflow));
    // §3.4: no `-` on an unsigned integer (E0401), so the evaluator is never given one.
    assert!(matches!(un(Un::Neg, int(U8, 0)), Err(Fault::Internal(_))));
}

#[test]
fn as_converts_only_without_losing_information() {
    use IntKind::*;
    let c = |to, v: Value| cast(to, &v);
    let (i, f) = (Scalar::Int, Scalar::F32);
    // §3.3: the same sign into a type as wide, an unsigned into a wider signed, F32 into F64,
    // I8 I16 U8 U16 into F32, and I8..I32 U8..U32 into F64; the value does not change.
    assert!(c(i(I64), int(I8, -5)).unwrap().same(&int(I64, -5)));
    assert!(c(i(I16), int(U8, 200)).unwrap().same(&int(I16, 200)));
    assert!(c(i(I64), int(U32, 4294967295)).unwrap().same(&int(I64, 4294967295)));
    assert!(c(i(U64), int(U64, 7)).unwrap().same(&int(U64, 7)));
    assert!(c(Scalar::F64, int(I32, -2147483648)).unwrap().same(&Value::F64(-2147483648.0)));
    assert!(c(f, int(U16, 65535)).unwrap().same(&Value::F32(65535.0)));
    assert!(c(f, int(I16, -32768)).unwrap().same(&Value::F32(-32768.0)));
    assert!(c(f, int(I8, 0)).unwrap().same(&Value::F32(0.0)), "an integer 0 is +0.0");
    assert!(c(Scalar::F64, Value::F32(-0.0)).unwrap().same(&Value::F64(-0.0)), "the sign of a zero is kept");
    assert!(c(Scalar::F64, Value::F32(f32::NAN)).unwrap().same(&Value::F64(f64::NAN)));
    assert!(c(Scalar::F64, f32b(INF)).unwrap().same(&Value::F64(f64::INFINITY)));
    assert!(c(f, Value::F32(1.5)).unwrap().same(&Value::F32(1.5)));
    // Everything else is `narrow_from`, `trunc_from` or `round_from` (E0411): not given to the evaluator.
    for (to, v) in [
        (i(I32), int(I64, 1)),
        (i(U32), int(I32, 1)),
        (i(I32), int(U32, 1)),
        (i(U64), int(I64, 1)),
        (i(I64), int(U64, 1)),
        (f, int(I32, 1)),
        (f, int(U32, 1)),
        (Scalar::F64, int(I64, 1)),
        (Scalar::F64, int(U64, 1)),
        (f, Value::F64(1.0)),
        (i(I32), Value::F32(1.0)),
    ] {
        assert!(matches!(cast(to, &v), Err(Fault::Internal(_))), "{v:?} as {to:?}");
    }
}

#[test]
fn operands_that_do_not_agree_are_internal_errors_not_panics() {
    use IntKind::*;
    // The check of types rules these out; the evaluator says so rather than guessing a value.
    for (op, a, b) in [
        (Bin::Add, int(I32, 1), int(I64, 1)),
        (Bin::Add, Value::Bool(true), Value::Bool(true)),
        (Bin::Add, Value::F32(1.0), Value::F64(1.0)),
        (Bin::And, Value::F32(1.0), Value::F32(1.0)),
        (Bin::Shl, int(I32, 1), int(I32, 1)),
        (Bin::Lt, Value::Unit, Value::Unit),
        (Bin::Lt, Value::Bool(false), Value::Bool(true)),
    ] {
        assert!(matches!(binary(op, &a, &b), Err(Fault::Internal(_))), "{op:?} {a:?} {b:?}");
    }
}

#[test]
fn comparisons_of_the_other_scalars() {
    // §6.3: `Char` is ordered by the code point; `Bool` and `()` only have `==` and `!=`.
    let t = |b: bool| Ok(Value::Bool(b));
    check(&[
        (Bin::Lt, Value::Char('a'), Value::Char('b'), t(true)),
        (Bin::Gt, Value::Char('\u{3042}'), Value::Char('z'), t(true)),
        (Bin::Eq, Value::Char('a'), Value::Char('a'), t(true)),
        (Bin::Eq, Value::Bool(true), Value::Bool(false), t(false)),
        (Bin::Ne, Value::Bool(true), Value::Bool(false), t(true)),
        (Bin::Eq, Value::Unit, Value::Unit, t(true)),
    ]);
}

#[test]
fn the_ranges_of_the_integer_kinds() {
    use IntKind::*;
    // 2^(bits-1) and 2^bits, worked out: the same table the vectors' `MIN` and `MAX` rows give.
    for (k, bits, min, max) in [
        (I8, 8, -128, 127),
        (I16, 16, -32768, 32767),
        (I32, 32, -2147483648, 2147483647),
        (I64, 64, i64::MIN.into(), i64::MAX.into()),
        (U8, 8, 0, 255),
        (U16, 16, 0, 65535),
        (U32, 32, 0, 4294967295),
        (U64, 64, 0, u64::MAX.into()),
    ] {
        assert_eq!((k.bits(), k.min(), k.max()), (bits, min, max), "{k:?}");
    }
}

// The defaults (§6.3, §6.4, §11.2) and the sameness of values (§13.4).

#[test]
fn defaults_of_the_scalars_and_the_aggregates() {
    let sc = |s| Shape::Scalar(s);
    let (i32t, f32t) = (Scalar::Int(IntKind::I32), Scalar::F32);
    assert!(i32t.default_value().unwrap().same(&int(IntKind::I32, 0)));
    assert!(f32t.default_value().unwrap().same(&Value::F32(0.0)), "+0.0");
    assert!(Scalar::Bool.default_value().unwrap().same(&Value::Bool(false)));
    assert!(Scalar::Unit.default_value().unwrap().same(&Value::Unit));
    assert!(Scalar::Char.default_value().is_none(), "Char has no Default (the table of §6.3)");
    // Tuples and arrays: elementwise.
    let tuple = Shape::Tuple(vec![sc(i32t), sc(f32t), sc(Scalar::Bool)]);
    let want = Value::Tuple(vec![int(IntKind::I32, 0), Value::F32(0.0), Value::Bool(false)]);
    assert!(tuple.default_value().unwrap().same(&want));
    let array = Shape::Array(Box::new(sc(f32t)), 3);
    assert!(array.default_value().unwrap().same(&Value::Array(vec![Value::F32(0.0); 3])));
    // An element type without a default gives no default, even for no element (`[T; N]` has `Default` when `T` has).
    assert!(Shape::Array(Box::new(sc(Scalar::Char)), 0).default_value().is_none());
    assert!(Shape::Tuple(vec![sc(i32t), sc(Scalar::Char)]).default_value().is_none());
    // A struct: the declared value of a field, else the default of its type; a declared value needs no `Default`.
    let record = Shape::Struct(vec![
        (None, sc(i32t)),
        (Some(Value::Char('a')), sc(Scalar::Char)),
        (Some(Value::F32(0.5)), sc(f32t)),
    ]);
    let want = Value::Struct(vec![int(IntKind::I32, 0), Value::Char('a'), Value::F32(0.5)]);
    assert!(record.default_value().unwrap().same(&want));
    assert!(Shape::Struct(vec![(None, sc(Scalar::Char))]).default_value().is_none());
    // Nested: a tuple of an array and a struct.
    let nested = Shape::Tuple(vec![Shape::Array(Box::new(sc(i32t)), 2), Shape::Struct(vec![(None, sc(Scalar::Bool))])]);
    let want = Value::Tuple(vec![Value::Array(vec![int(IntKind::I32, 0); 2]), Value::Struct(vec![Value::Bool(false)])]);
    assert!(nested.default_value().unwrap().same(&want));
}

#[test]
fn sameness_is_by_bits_with_any_nan_alike() {
    let (pz, nz) = (Value::F32(0.0), f32b(NEG0));
    assert!(!pz.same(&nz) && !nz.same(&pz), "0.0 and -0.0 differ");
    assert!(Value::F32(f32::NAN).same(&f32b(0xffc0_0001)), "any NaN is the same as any NaN");
    assert!(Value::F64(f64::NAN).same(&Value::F64(-f64::NAN)));
    assert!(!Value::F32(f32::NAN).same(&Value::F64(f64::NAN)), "F32 and F64 are different types");
    assert!(!Value::F32(f32::NAN).same(&Value::F32(1.0)));
    assert!(!int(IntKind::I32, 1).same(&int(IntKind::I64, 1)), "the kind is part of the value");
    assert!(!int(IntKind::U8, 1).same(&Value::Bool(true)));
    let pair = |x| Value::Tuple(vec![int(IntKind::I8, 1), x]);
    assert!(pair(Value::F32(0.0)).same(&pair(Value::F32(0.0))));
    assert!(!pair(Value::F32(0.0)).same(&pair(f32b(NEG0))), "the difference is seen inside a tuple");
    assert!(!Value::Tuple(vec![]).same(&Value::Array(vec![])), "a tuple is not an array");
    let variant = |tag, v| Value::Enum { tag, fields: vec![v] };
    assert!(variant(1, Value::F32(f32::NAN)).same(&variant(1, f32b(0x7fc0_0001))));
    assert!(!variant(1, Value::Unit).same(&variant(2, Value::Unit)), "the variant is part of the value");
    assert!(!Value::Struct(vec![Value::Unit]).same(&Value::Struct(vec![])));
}
