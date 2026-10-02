//! Unit tests of the interpreter on hand-built Core (numeric rules of spec
//! §3.3, §3.4, §13.4 and the S-25 decisions). End-to-end tests over Onsa
//! source live in `crates/onsa_tests/tests/interp.rs`.

use onsa_core::prim::{MathFn, Prim};
use onsa_core::*;
use onsa_diag::{FileId, Span};

use crate::{Interp, Panic, Value};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn int(k: IntKind, n: i128) -> Expr {
    Expr::new(Ty::Int(k), sp(), ExprKind::Lit(Lit::Int(n)))
}

fn f32_(x: f32) -> Expr {
    Expr::new(Ty::Float(FloatKind::F32), sp(), ExprKind::Lit(Lit::F32(x)))
}

fn bin(op: BinOp, overflow: Overflow, a: Expr, b: Expr) -> Expr {
    let ty = a.ty.clone();
    Expr::new(ty, sp(), ExprKind::Binary { op, overflow, lhs: Box::new(a), rhs: Box::new(b) })
}

fn prim(p: Prim, ty: Ty, args: Vec<Expr>) -> Expr {
    Expr::new(
        ty,
        sp(),
        ExprKind::Prim { prim: p, args: args.into_iter().map(|e| Arg { mode: Mode::Borrow, expr: e }).collect() },
    )
}

/// Run `e` as the body of a function with no parameters.
fn eval(e: Expr) -> Result<Value, Panic> {
    let m = Module {
        fns: vec![FnDef {
            name: "f".into(),
            params: Vec::new(),
            ret: e.ty.clone(),
            sret: false,
            rt: false,
            locals: Vec::new(),
            body: Some(Block { stmts: Vec::new(), value: Some(Box::new(e)) }),
            span: sp(),
        }],
        ..Default::default()
    };
    let interp = Interp::new(&m);
    interp.call(FnId(0), Vec::new())
}

fn as_i128(v: Value) -> i128 {
    v.to_i128().expect("integer")
}

#[test]
fn checked_arithmetic_panics_on_overflow() {
    assert_eq!(
        as_i128(eval(bin(BinOp::Add, Overflow::Checked, int(IntKind::I32, 1), int(IntKind::I32, 2))).unwrap()),
        3
    );
    let e = eval(bin(BinOp::Add, Overflow::Checked, int(IntKind::I32, i32::MAX as i128), int(IntKind::I32, 1)))
        .unwrap_err();
    assert!(e.message.contains("overflow"), "{}", e.message);
    let e = eval(bin(BinOp::Mul, Overflow::Checked, int(IntKind::U8, 16), int(IntKind::U8, 16))).unwrap_err();
    assert!(e.message.contains("overflow"));
    let e = eval(bin(BinOp::Sub, Overflow::Checked, int(IntKind::U32, 0), int(IntKind::U32, 1))).unwrap_err();
    assert!(e.message.contains("overflow"));
}

#[test]
fn wrapping_and_saturating() {
    assert_eq!(
        as_i128(
            eval(bin(BinOp::Add, Overflow::Wrap, int(IntKind::I32, i32::MAX as i128), int(IntKind::I32, 1))).unwrap()
        ),
        i32::MIN as i128
    );
    assert_eq!(
        as_i128(
            eval(bin(BinOp::Add, Overflow::Sat, int(IntKind::I32, i32::MAX as i128), int(IntKind::I32, 1))).unwrap()
        ),
        i32::MAX as i128
    );
    assert_eq!(as_i128(eval(bin(BinOp::Sub, Overflow::Wrap, int(IntKind::U8, 0), int(IntKind::U8, 1))).unwrap()), 255);
    assert_eq!(as_i128(eval(bin(BinOp::Sub, Overflow::Sat, int(IntKind::U8, 0), int(IntKind::U8, 1))).unwrap()), 0);
    assert_eq!(as_i128(eval(bin(BinOp::Mul, Overflow::Wrap, int(IntKind::I8, 100), int(IntKind::I8, 3))).unwrap()), 44);
    assert_eq!(
        as_i128(eval(bin(BinOp::Mul, Overflow::Sat, int(IntKind::I8, -100), int(IntKind::I8, 3))).unwrap()),
        -128
    );
}

#[test]
fn division_rules() {
    // §3.4: truncation toward zero, remainder takes the dividend's sign.
    assert_eq!(
        as_i128(eval(bin(BinOp::Div, Overflow::Checked, int(IntKind::I32, -7), int(IntKind::I32, 2))).unwrap()),
        -3
    );
    assert_eq!(
        as_i128(eval(bin(BinOp::Rem, Overflow::Checked, int(IntKind::I32, -7), int(IntKind::I32, 2))).unwrap()),
        -1
    );
    let e = eval(bin(BinOp::Div, Overflow::Checked, int(IntKind::I32, 1), int(IntKind::I32, 0))).unwrap_err();
    assert!(e.message.contains("division by zero"));
    let e = eval(bin(BinOp::Div, Overflow::Checked, int(IntKind::I32, i32::MIN as i128), int(IntKind::I32, -1)))
        .unwrap_err();
    assert!(e.message.contains("overflow"));
    // `div_euclid` / `rem_euclid`.
    let v = eval(prim(
        Prim::RemEuclid(IntKind::I32),
        Ty::Int(IntKind::I32),
        vec![int(IntKind::I32, -7), int(IntKind::I32, 2)],
    ))
    .unwrap();
    assert_eq!(as_i128(v), 1);
}

#[test]
fn shifts_are_checked_against_the_width() {
    assert_eq!(
        as_i128(eval(bin(BinOp::Shl, Overflow::Checked, int(IntKind::I32, 1), int(IntKind::U32, 31))).unwrap()),
        i32::MIN as i128
    );
    assert_eq!(
        as_i128(eval(bin(BinOp::Shr, Overflow::Checked, int(IntKind::I32, -8), int(IntKind::U32, 1))).unwrap()),
        -4
    );
    assert_eq!(
        as_i128(eval(bin(BinOp::Shr, Overflow::Checked, int(IntKind::U8, 0x80), int(IntKind::U32, 7))).unwrap()),
        1
    );
    let e = eval(bin(BinOp::Shl, Overflow::Checked, int(IntKind::I32, 1), int(IntKind::U32, 32))).unwrap_err();
    assert!(e.message.contains("shift"));
}

#[test]
fn float_arithmetic_stays_in_f32() {
    let v = eval(bin(BinOp::Add, Overflow::Checked, f32_(0.1), f32_(0.2))).unwrap();
    assert_eq!(v.as_f32().unwrap(), 0.1f32 + 0.2f32);
    let v = eval(bin(BinOp::Rem, Overflow::Checked, f32_(-7.5), f32_(2.0))).unwrap();
    assert_eq!(v.as_f32().unwrap(), -1.5); // fmod keeps the dividend's sign
}

#[test]
fn trunc_to_int_panics_or_saturates() {
    let p = |sat: bool, x: f32| {
        eval(prim(
            Prim::TruncToInt { from: FloatKind::F32, to: IntKind::I32, sat },
            Ty::Int(IntKind::I32),
            vec![f32_(x)],
        ))
    };
    assert_eq!(as_i128(p(false, -3.9).unwrap()), -3);
    assert!(p(false, 1e10).is_err());
    assert!(p(false, f32::NAN).is_err());
    assert_eq!(as_i128(p(true, 1e10).unwrap()), i32::MAX as i128);
    assert_eq!(as_i128(p(true, -1e10).unwrap()), i32::MIN as i128);
    assert_eq!(as_i128(p(true, f32::NAN).unwrap()), 0);
}

#[test]
fn round_is_half_to_even_and_min_max_propagate_nan() {
    let math = |f: MathFn, x: f32, y: f32| {
        let args = if f.arity() == 2 { vec![f32_(x), f32_(y)] } else { vec![f32_(x)] };
        eval(prim(Prim::Math(f, FloatKind::F32), Ty::Float(FloatKind::F32), args)).unwrap().as_f32().unwrap()
    };
    assert_eq!(math(MathFn::Round, 0.5, 0.0), 0.0);
    assert_eq!(math(MathFn::Round, 1.5, 0.0), 2.0);
    assert_eq!(math(MathFn::Round, -2.5, 0.0), -2.0);
    assert!(math(MathFn::Min, f32::NAN, 1.0).is_nan());
    assert!(math(MathFn::Max, 1.0, f32::NAN).is_nan());
    assert_eq!(math(MathFn::Min, 1.0, 2.0), 1.0);
    assert!(math(MathFn::Min, -0.0, 0.0).is_sign_negative());
    assert!(math(MathFn::Max, -0.0, 0.0).is_sign_positive());
    assert_eq!(math(MathFn::Fmod, 5.5, 2.0), 1.5);
    assert_eq!(math(MathFn::Sqrt, 16.0, 0.0), 4.0);
}

#[test]
fn int_to_float_rounds_to_nearest_even() {
    // 16777217 is halfway between two f32 values; nearest-even picks 16777216.
    let v = eval(prim(
        Prim::IntToFloat { from: IntKind::I32, to: FloatKind::F32 },
        Ty::Float(FloatKind::F32),
        vec![int(IntKind::I32, 16_777_217)],
    ))
    .unwrap();
    assert_eq!(v.as_f32().unwrap(), 16_777_216.0);
}

#[test]
fn narrow_and_checked_return_options() {
    let v = eval(prim(
        Prim::Narrow { from: IntKind::I64, to: IntKind::I32 },
        Ty::Enum(TypeId(0)),
        vec![int(IntKind::I64, 1 << 40)],
    ))
    .unwrap();
    assert!(matches!(v, Value::Enum { tag: 0, .. }));
    let v = eval(prim(
        Prim::Checked(onsa_core::prim::CheckedOp::Add, IntKind::U8),
        Ty::Enum(TypeId(0)),
        vec![int(IntKind::U8, 200), int(IntKind::U8, 55)],
    ))
    .unwrap();
    assert!(matches!(v, Value::Enum { tag: 1, .. }));
}

#[test]
fn bits_round_trip() {
    let v = eval(prim(Prim::ToBits(FloatKind::F32), Ty::Int(IntKind::U32), vec![f32_(1.0)])).unwrap();
    assert_eq!(as_i128(v), 0x3f80_0000);
}
