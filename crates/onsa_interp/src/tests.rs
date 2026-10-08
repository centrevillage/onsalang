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

/// Run a test on the stack of a command: the interpreter runs only there (R-05).
fn on_stack(f: impl FnOnce() + Send) {
    onsa_diag::stack::run(f)
}

fn as_i128(v: Value) -> i128 {
    v.to_i128().expect("integer")
}

#[test]
fn checked_arithmetic_panics_on_overflow() {
    on_stack(|| {
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
    })
}

#[test]
fn wrapping_and_saturating() {
    on_stack(|| {
        assert_eq!(
            as_i128(
                eval(bin(BinOp::Add, Overflow::Wrap, int(IntKind::I32, i32::MAX as i128), int(IntKind::I32, 1)))
                    .unwrap()
            ),
            i32::MIN as i128
        );
        assert_eq!(
            as_i128(
                eval(bin(BinOp::Add, Overflow::Sat, int(IntKind::I32, i32::MAX as i128), int(IntKind::I32, 1)))
                    .unwrap()
            ),
            i32::MAX as i128
        );
        assert_eq!(
            as_i128(eval(bin(BinOp::Sub, Overflow::Wrap, int(IntKind::U8, 0), int(IntKind::U8, 1))).unwrap()),
            255
        );
        assert_eq!(as_i128(eval(bin(BinOp::Sub, Overflow::Sat, int(IntKind::U8, 0), int(IntKind::U8, 1))).unwrap()), 0);
        assert_eq!(
            as_i128(eval(bin(BinOp::Mul, Overflow::Wrap, int(IntKind::I8, 100), int(IntKind::I8, 3))).unwrap()),
            44
        );
        assert_eq!(
            as_i128(eval(bin(BinOp::Mul, Overflow::Sat, int(IntKind::I8, -100), int(IntKind::I8, 3))).unwrap()),
            -128
        );
    })
}

#[test]
fn division_rules() {
    on_stack(|| {
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
    })
}

#[test]
fn shifts_are_checked_against_the_width() {
    on_stack(|| {
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
    })
}

#[test]
fn float_arithmetic_stays_in_f32() {
    on_stack(|| {
        let v = eval(bin(BinOp::Add, Overflow::Checked, f32_(0.1), f32_(0.2))).unwrap();
        assert_eq!(v.as_f32().unwrap(), 0.1f32 + 0.2f32);
        let v = eval(bin(BinOp::Rem, Overflow::Checked, f32_(-7.5), f32_(2.0))).unwrap();
        assert_eq!(v.as_f32().unwrap(), -1.5); // fmod keeps the dividend's sign
    })
}

#[test]
fn trunc_to_int_panics_or_saturates() {
    on_stack(|| {
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
    })
}

#[test]
fn round_is_half_to_even_and_min_max_propagate_nan() {
    on_stack(|| {
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
    })
}

#[test]
fn int_to_float_rounds_to_nearest_even() {
    on_stack(|| {
        // 16777217 is halfway between two f32 values; nearest-even picks 16777216.
        let v = eval(prim(
            Prim::IntToFloat { from: IntKind::I32, to: FloatKind::F32 },
            Ty::Float(FloatKind::F32),
            vec![int(IntKind::I32, 16_777_217)],
        ))
        .unwrap();
        assert_eq!(v.as_f32().unwrap(), 16_777_216.0);
    })
}

#[test]
fn narrow_and_checked_return_options() {
    on_stack(|| {
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
    })
}

#[test]
fn bits_round_trip() {
    on_stack(|| {
        let v = eval(prim(Prim::ToBits(FloatKind::F32), Ty::Int(IntKind::U32), vec![f32_(1.0)])).unwrap();
        assert_eq!(as_i128(v), 0x3f80_0000);
    })
}

fn u32_() -> Ty {
    Ty::Int(IntKind::U32)
}

fn u32_local(i: u32) -> Expr {
    Expr::new(u32_(), sp(), ExprKind::Local(LocalId(i)))
}

fn read_const(i: u32) -> Expr {
    Expr::new(u32_(), sp(), ExprKind::Const(ConstId(i)))
}

fn call(f: u32, args: Vec<Expr>) -> Expr {
    Expr::new(
        u32_(),
        sp(),
        ExprKind::Call { fn_: FnId(f), args: args.into_iter().map(|e| Arg { mode: Mode::Borrow, expr: e }).collect() },
    )
}

fn value_block(stmts: Vec<Stmt>, e: Expr) -> Block {
    Block { stmts, value: Some(Box::new(e)) }
}

/// `fn <name>(n: U32) -> U32 { if n == 0 { <zero> } else { <deeper> } }`, with
/// `extra` locals of type `ty` after `n`.
fn recursive_fn(name: &str, zero: Expr, deeper: Expr, extra: Vec<Ty>) -> FnDef {
    let cond = Expr::new(
        Ty::Bool,
        sp(),
        ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(u32_local(0)), rhs: Box::new(int(IntKind::U32, 0)) },
    );
    let body = Expr::new(
        u32_(),
        sp(),
        ExprKind::IfExpr {
            cond: Box::new(cond),
            then: value_block(Vec::new(), zero),
            else_: value_block(Vec::new(), deeper),
        },
    );
    let mut locals = vec![Local { name: "n".into(), ty: u32_() }];
    locals.extend(extra.into_iter().enumerate().map(|(i, ty)| Local { name: format!("k{i}"), ty }));
    FnDef {
        name: name.into(),
        params: vec![Param { local: LocalId(0), mode: Mode::Borrow, ty: u32_() }],
        ret: u32_(),
        sret: false,
        rt: false,
        locals,
        body: Some(value_block(Vec::new(), body)),
        span: sp(),
    }
}

/// `n - 1`.
fn n_minus_1() -> Expr {
    bin(BinOp::Sub, Overflow::Checked, u32_local(0), int(IntKind::U32, 1))
}

/// The kinds of expression a recursive call is nested in, one level each,
/// the value staying 0: the most expensive kinds of the measurement of
/// [`crate::MAX_CALL_DEPTH`].
#[derive(Clone, Copy, Debug)]
enum Level {
    /// `0 + (x)`.
    Add,
    /// `[x][0]`.
    ArrayIndex,
    /// `(x, 0).0`.
    TupleField,
    /// `{ let k = A(x); match k { A(v) => v } }` (an enum `E { A(U32) }`).
    Match,
}

const LEVELS: [Level; 4] = [Level::Add, Level::ArrayIndex, Level::TupleField, Level::Match];

/// `f(n)`: the call `f(n - 1)` under `levels` levels of `level`; `f(n)` makes
/// `n` nested calls.
fn recursion_under(level: Level, levels: usize) -> Module {
    let mut deep = call(0, vec![n_minus_1()]);
    let mut extra = Vec::new();
    let enum_ty = Ty::Enum(TypeId(0));
    for i in 0..levels {
        deep = match level {
            Level::Add => bin(BinOp::Add, Overflow::Checked, int(IntKind::U32, 0), deep),
            Level::ArrayIndex => {
                let arr = Expr::new(Ty::Array(Box::new(u32_()), 1), sp(), ExprKind::Array(vec![deep]));
                Expr::new(u32_(), sp(), ExprKind::Index { base: Box::new(arr), index: Box::new(int(IntKind::U32, 0)) })
            }
            Level::TupleField => {
                let t =
                    Expr::new(Ty::Tuple(vec![u32_(), u32_()]), sp(), ExprKind::Tuple(vec![deep, int(IntKind::U32, 0)]));
                Expr::new(u32_(), sp(), ExprKind::Field { base: Box::new(t), index: 0 })
            }
            Level::Match => {
                let k = LocalId(1 + i as u32);
                extra.push(enum_ty.clone());
                let v =
                    Expr::new(enum_ty.clone(), sp(), ExprKind::Variant { ty: TypeId(0), tag: 0, fields: vec![deep] });
                let local = Expr::new(enum_ty.clone(), sp(), ExprKind::Local(k));
                let payload =
                    Expr::new(u32_(), sp(), ExprKind::Payload { base: Box::new(local.clone()), tag: 0, index: 0 });
                let switch = Expr::new(
                    u32_(),
                    sp(),
                    ExprKind::Switch {
                        scrutinee: Box::new(local),
                        arms: vec![(0, value_block(Vec::new(), payload))],
                        default: None,
                    },
                );
                let let_ = Stmt { kind: StmtKind::Let(k, v), span: sp() };
                Expr::new(u32_(), sp(), ExprKind::Block(value_block(vec![let_], switch)))
            }
        };
    }
    Module {
        types: vec![TypeDef {
            name: "E".into(),
            kind: TypeDefKind::Enum { variants: vec![("A".into(), vec![u32_()])] },
        }],
        fns: vec![recursive_fn("f", int(IntKind::U32, 0), deep, extra)],
        ..Default::default()
    }
}

/// `f(n: U32) -> U32 { if n == 0 { 0 } else { 0 + (0 + .. (0 + f(n - 1))) } }`,
/// the call under `levels` additions.
fn recursion_under_additions(levels: usize) -> Module {
    recursion_under(Level::Add, levels)
}

/// The message of the internal error `f` stops with ([`onsa_diag::internal::bug`]).
fn internal_error_of<T: std::fmt::Debug>(f: impl FnOnce() -> T) -> String {
    let payload = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).expect_err("an internal error");
    match payload.downcast::<onsa_diag::internal::InternalBug>() {
        Ok(b) => b.message,
        Err(p) => std::panic::resume_unwind(p),
    }
}

fn limit_message() -> String {
    format!("the call depth reached its limit of {}", crate::MAX_CALL_DEPTH)
}

/// Spec §12.5 (S-222): the body of an entry is at depth 0, calls 1 to 128
/// run and the 129th is a panic of the program, whatever the depth asked
/// for; the depth goes back with each finished call.
#[test]
fn a_call_beyond_the_limit_is_a_panic() {
    on_stack(|| {
        let m = recursion_under_additions(0);
        let interp = Interp::new(&m);
        // f(n) makes n nested calls.
        assert_eq!(as_i128(interp.call(FnId(0), vec![Value::U32(crate::MAX_CALL_DEPTH)]).unwrap()), 0);
        for n in [crate::MAX_CALL_DEPTH + 1, crate::MAX_CALL_DEPTH + 2, 10_000_000] {
            let e = interp.call(FnId(0), vec![Value::U32(n)]).unwrap_err();
            assert_eq!(e.message, limit_message(), "f({n})");
        }
        assert_eq!(as_i128(interp.call(FnId(0), vec![Value::U32(crate::MAX_CALL_DEPTH)]).unwrap()), 0);
    })
}

/// R-05, S-183: a recursive call under 256 levels of the most expensive
/// kinds of expression, 128 calls deep, fits the stack the safety net leaves
/// (with the `opt-level` of `Cargo.toml` in a debug build): the limit comes
/// first, in debug and in release.
#[test]
fn the_limit_comes_before_the_net_under_256_levels() {
    on_stack(|| {
        for level in LEVELS {
            let m = recursion_under(level, 256);
            let interp = Interp::new(&m);
            let r = interp.call(FnId(0), vec![Value::U32(crate::MAX_CALL_DEPTH)]);
            assert_eq!(r.map(as_i128), Ok(0), "{level:?}");
            let e = interp.call(FnId(0), vec![Value::U32(10_000_000)]).unwrap_err();
            assert_eq!(e.message, limit_message(), "{level:?}");
        }
    })
}

/// The least stack above `STACK_RESERVE` with which `run` finishes without
/// reaching the safety net, to 4 K (a bisection with
/// [`onsa_diag::stack::with_stack_left`]).
fn stack_needed(run: &dyn Fn()) -> usize {
    let top = onsa_diag::stack::remaining().expect("a command thread") - (64 << 10);
    let fits = |left: usize| {
        onsa_diag::stack::with_stack_left(left, || std::panic::catch_unwind(std::panic::AssertUnwindSafe(run)).is_ok())
    };
    let (mut lo, mut hi) = (crate::STACK_RESERVE, top);
    assert!(fits(hi), "does not fit the whole stack");
    while hi - lo > 4 << 10 {
        let mid = lo + (hi - lo) / 2;
        if fits(mid) { hi = mid } else { lo = mid }
    }
    hi - crate::STACK_RESERVE
}

/// The numbers behind [`crate::MAX_CALL_DEPTH`] (printed with `--nocapture`):
/// the stack of one call, and of one level of each kind of expression around
/// it, from two depths and two nestings. The rule it holds: 128 calls under
/// 256 levels of any kind use at most half of what the net leaves.
#[test]
fn measure_the_stack_of_calls_and_levels() {
    on_stack(|| {
        let budget = onsa_diag::stack::STACK_SIZE - crate::STACK_RESERVE;
        for level in LEVELS {
            let need = |levels: usize, depth: u32| {
                let m = recursion_under(level, levels);
                stack_needed(&|| {
                    let interp = Interp::new(&m);
                    interp.call(FnId(0), vec![Value::U32(depth)]).unwrap();
                })
            };
            let per_call = (need(0, 64) - need(0, 32)) / 32;
            let per_level = ((need(32, 32) - need(16, 32)) / 32) / 16;
            let at_limit = need(256, crate::MAX_CALL_DEPTH);
            println!(
                "{level:?}: {per_call} B a call, {per_level} B a level; 128 calls under 256 levels: {at_limit} B of {budget}"
            );
            assert!(at_limit * 2 <= budget, "{level:?}: {at_limit} of {budget}");
        }
    })
}

/// R-05: a run that uses up the stack before the limit (here: a thread whose
/// stack is nearly used up, `with_stack_left`) reaches the safety net, and
/// stops with an internal error, not a signal.
#[test]
fn the_safety_net_stops_with_an_internal_error() {
    on_stack(|| {
        let m = recursion_under_additions(0);
        let interp = Interp::new(&m);
        let message = onsa_diag::stack::with_stack_left(crate::STACK_RESERVE + (16 << 10), || {
            internal_error_of(|| interp.call(FnId(0), vec![Value::U32(crate::MAX_CALL_DEPTH)]))
        });
        assert!(message.contains("the limit does not fit the stack"), "{message}");
    })
}

/// `n` constants `C0 = 1`, `C(i) = C(i - 1) + 1`: a chain of `const`s that
/// read `const`s (not calls, S-222).
fn const_chain(n: u32) -> Module {
    let mut consts = vec![ConstDef { name: "C0".into(), ty: u32_(), init: int(IntKind::U32, 1) }];
    for i in 1..n {
        consts.push(ConstDef {
            name: format!("C{i}"),
            ty: u32_(),
            init: bin(BinOp::Add, Overflow::Checked, read_const(i - 1), int(IntKind::U32, 1)),
        });
    }
    Module { consts, ..Default::default() }
}

/// S-222: a chain of `const`s is not counted as calls; every `const` it
/// evaluates checks the safety net at its entry, so a chain longer than the
/// stack holds stops with an internal error (until W9-03). Tested on a stack
/// nearly used up, with a short chain; after it the same interpreter (P-1)
/// evaluates the chain on the whole stack.
#[test]
fn the_safety_net_stops_a_chain_of_consts() {
    on_stack(|| {
        let m = const_chain(50);
        let interp = Interp::new(&m);
        let message = onsa_diag::stack::with_stack_left(crate::STACK_RESERVE + (16 << 10), || {
            internal_error_of(|| interp.const_value(ConstId(49)))
        });
        assert!(message.contains("nest deeper than the stack holds"), "{message}");
        assert_eq!(interp.const_value(ConstId(49)).map(as_i128), Ok(50));
    })
}

/// S-222: a chain of `const`s is not counted as calls: 1000 of them, far
/// more than the limit, evaluate.
#[test]
fn a_chain_of_consts_is_not_counted() {
    on_stack(|| {
        let m = const_chain(1000);
        let interp = Interp::new(&m);
        assert_eq!(interp.const_value(ConstId(999)).map(as_i128), Ok(1000));
    })
}

/// `f` of [`recursion_under_additions`]`(0)`, `const D<i> = f(<d>)` for each
/// of `ds` (`f(d)` is call 1 of the initializer and makes `d` more), and `g(n) = if n == 0 { D0 } else { g(n - 1) }`, which reads the
/// first `const` `n` calls deep.
fn consts_of_recursion(ds: &[u32]) -> Module {
    let mut m = recursion_under_additions(0);
    m.consts = ds
        .iter()
        .enumerate()
        .map(|(i, d)| ConstDef {
            name: format!("D{i}"),
            ty: u32_(),
            init: call(0, vec![int(IntKind::U32, *d as i128)]),
        })
        .collect();
    m.fns.push(recursive_fn("g", read_const(0), call(1, vec![n_minus_1()]), Vec::new()));
    m
}

/// Spec §12.5 (S-222, W2-04/b 1 and 2): the initializer of a `const` is an
/// evaluation of its own, from depth 0, wherever it is read first: deep in a
/// call, at the top of a test, or from outside (a build).
#[test]
fn a_const_counts_from_zero_wherever_it_is_read() {
    on_stack(|| {
        let m = consts_of_recursion(&[crate::MAX_CALL_DEPTH - 1, crate::MAX_CALL_DEPTH]);
        // Read first 100 calls deep.
        let interp = Interp::new(&m);
        assert_eq!(interp.call(FnId(1), vec![Value::U32(100)]).map(as_i128), Ok(0));
        // Read first from outside, as a build does.
        let interp = Interp::new(&m);
        assert_eq!(interp.const_value(ConstId(0)).map(as_i128), Ok(0));
        // One more call: a panic of the evaluation, the same each time.
        let interp = Interp::new(&m);
        for _ in 0..2 {
            assert_eq!(interp.const_value(ConstId(1)).unwrap_err().message, limit_message());
        }
    })
}

/// P-1: an internal error that unwinds through an evaluation leaves the
/// interpreter as it was: the depth comes back, and the `const` being
/// evaluated is not left "in progress" (a tool, the vectors' runner, goes on
/// with the same interpreter).
#[test]
fn an_internal_error_leaves_the_interpreter_as_it_was() {
    on_stack(|| {
        let mut m = consts_of_recursion(&[crate::MAX_CALL_DEPTH - 1]);
        // Each call of `f` under 64 additions: about 18 K.
        m.fns[0] = recursion_under_additions(64).fns.remove(0);
        let interp = Interp::new(&m);
        // The safety net stops the `const`, read 100 calls deep in `g`: `g`
        // fits in the stack left (100 calls of about 1 K), the `const`'s 128
        // calls of `f` (about 2.3 M) do not.
        let message = onsa_diag::stack::with_stack_left(crate::STACK_RESERVE + (512 << 10), || {
            internal_error_of(|| interp.call(FnId(1), vec![Value::U32(100)]))
        });
        // The net names the nested evaluation, not the limit (W2-04/b2).
        assert!(message.contains("in 2 nested evaluations"), "{message}");
        assert_eq!(interp.const_value(ConstId(0)).map(as_i128), Ok(0));
        assert_eq!(interp.call(FnId(0), vec![Value::U32(crate::MAX_CALL_DEPTH)]).map(as_i128), Ok(0));
        let e = interp.call(FnId(0), vec![Value::U32(crate::MAX_CALL_DEPTH + 1)]).unwrap_err();
        assert_eq!(e.message, limit_message());
    })
}

/// R-05: the interpreter runs only on the stack of a command; on any other
/// thread an entry stops with an internal error at once.
#[test]
fn an_entry_off_the_stack_of_a_command_is_an_internal_error() {
    let message = internal_error_of(|| eval(int(IntKind::I32, 1)));
    assert!(message.contains("without the stack of a command"), "{message}");
}
