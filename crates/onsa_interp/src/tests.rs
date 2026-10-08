//! Unit tests of the interpreter on hand-built Core (numeric rules of spec
//! §3.3, §3.4, §13.4 and the S-25 decisions). End-to-end tests over Onsa
//! source live in `crates/onsa_tests/tests/interp.rs`.

use onsa_core::prim::{MathFn, Prim};
use onsa_core::*;
use onsa_diag::{FileId, Span};

use crate::{Failure, Interp, Panic, Value};

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
            fp_relaxed: false,
            test: None,
        }],
        ..Default::default()
    };
    let interp = Interp::new(&m);
    interp.call(FnId(0), Vec::new()).map_err(panic_of)
}

/// The panic of a failure that must be one.
fn panic_of(f: Failure) -> Panic {
    match f {
        Failure::Panic(p) => p,
        f => panic!("not a panic: {f:?}"),
    }
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
        fp_relaxed: false,
        test: None,
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
            let e = panic_of(interp.call(FnId(0), vec![Value::U32(n)]).unwrap_err());
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
            let e = panic_of(interp.call(FnId(0), vec![Value::U32(10_000_000)]).unwrap_err());
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
            assert_eq!(panic_of(interp.const_value(ConstId(1)).unwrap_err()).message, limit_message());
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
        let e = panic_of(interp.call(FnId(0), vec![Value::U32(crate::MAX_CALL_DEPTH + 1)]).unwrap_err());
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

// ------------------------------------------------- W2-03: the numeric edges

fn f64_(x: f64) -> Expr {
    Expr::new(Ty::Float(FloatKind::F64), sp(), ExprKind::Lit(Lit::F64(x)))
}

/// R-04: the products of two `U64`s whose exact value is beyond `i128`
/// (above 2^127): `*` panics, `*%` wraps modulo 2^64, `*|` saturates, and
/// `checked_mul` gives `None`; the host's arithmetic never overflows.
#[test]
fn u64_products_beyond_i128() {
    on_stack(|| {
        let max = u64::MAX as i128;
        let u = |n: i128| int(IntKind::U64, n);
        let wrap = |a: i128, b: i128| as_i128(eval(bin(BinOp::Mul, Overflow::Wrap, u(a), u(b))).unwrap());
        let sat = |a: i128, b: i128| as_i128(eval(bin(BinOp::Mul, Overflow::Sat, u(a), u(b))).unwrap());
        // (2^64 - 1)^2 = 2^128 - 2^65 + 1 = 1 modulo 2^64.
        assert_eq!(wrap(max, max), 1);
        assert_eq!(sat(max, max), max);
        // 2^63 * 2^63 = 2^126 fits i128; modulo 2^64 it is 0.
        assert_eq!(wrap(1 << 63, 1 << 63), 0);
        // (2^64 - 1) * 2 = 2^65 - 2, modulo 2^64: 2^64 - 2.
        assert_eq!(wrap(max, 2), max - 1);
        assert_eq!(sat(max, 2), max);
        // The exact product 2^64 - 1 = (2^32 - 1)(2^32 + 1) fits.
        let fits = eval(bin(BinOp::Mul, Overflow::Checked, u(4_294_967_295), u(4_294_967_297))).unwrap();
        assert_eq!(as_i128(fits), max);
        let e = eval(bin(BinOp::Mul, Overflow::Checked, u(max), u(max))).unwrap_err();
        assert!(e.message.contains("overflow"), "{}", e.message);
        let checked = |a: i128, b: i128| {
            eval(prim(
                Prim::Checked(onsa_core::prim::CheckedOp::Mul, IntKind::U64),
                Ty::Enum(TypeId(0)),
                vec![u(a), u(b)],
            ))
            .unwrap()
        };
        assert!(matches!(checked(max, max), Value::Enum { tag: 0, .. }));
        assert!(matches!(checked(4_294_967_295, 4_294_967_297), Value::Enum { tag: 1, .. }));
        // I64: the most negative product, I64.MIN * I64.MIN = 2^126, saturates to MAX and wraps to 0.
        let i = |n: i128| int(IntKind::I64, n);
        let min = i64::MIN as i128;
        assert_eq!(as_i128(eval(bin(BinOp::Mul, Overflow::Sat, i(min), i(min))).unwrap()), i64::MAX as i128);
        assert_eq!(as_i128(eval(bin(BinOp::Mul, Overflow::Sat, i(min), i(2))).unwrap()), min);
        assert_eq!(as_i128(eval(bin(BinOp::Mul, Overflow::Wrap, i(min), i(min))).unwrap()), 0);
    })
}

/// R-19, spec §3.4: `MIN % -1` and `MIN.rem_euclid(-1)` are 0 at every
/// signed width; `MIN / -1` and `MIN.div_euclid(-1)` panic.
#[test]
fn min_rem_minus_one_is_zero() {
    on_stack(|| {
        for k in [IntKind::I8, IntKind::I16, IntKind::I32, IntKind::I64] {
            let (min, _) = crate::value::int_range(k);
            let rem = eval(bin(BinOp::Rem, Overflow::Checked, int(k, min), int(k, -1))).unwrap();
            assert_eq!(as_i128(rem), 0, "{k:?}");
            let e = eval(bin(BinOp::Div, Overflow::Checked, int(k, min), int(k, -1))).unwrap_err();
            assert!(e.message.contains("overflow") && e.message.contains('/'), "{}", e.message);
            let re = eval(prim(Prim::RemEuclid(k), Ty::Int(k), vec![int(k, min), int(k, -1)])).unwrap();
            assert_eq!(as_i128(re), 0, "{k:?}");
            assert!(eval(prim(Prim::DivEuclid(k), Ty::Int(k), vec![int(k, min), int(k, -1)])).is_err());
            let e = eval(bin(BinOp::Rem, Overflow::Checked, int(k, min), int(k, 0))).unwrap_err();
            assert!(e.message.contains("division by zero"), "{}", e.message);
        }
    })
}

/// R-19, spec §3.3: the 64-bit `trunc_*` panic at 2^63 (`I64`) and 2^64
/// (`U64`), from `F32` and `F64`, and `_sat` gives the bound; the values
/// just below fit.
#[test]
fn trunc_to_64_bits_at_the_powers_of_two() {
    on_stack(|| {
        let t = |from: FloatKind, x: f64, to: IntKind, sat: bool| {
            let arg = match from {
                FloatKind::F32 => f32_(x as f32),
                FloatKind::F64 => f64_(x),
            };
            eval(prim(Prim::TruncToInt { from, to, sat }, Ty::Int(to), vec![arg]))
        };
        let p63 = 9_223_372_036_854_775_808.0;
        let p64 = 18_446_744_073_709_551_616.0;
        for from in [FloatKind::F32, FloatKind::F64] {
            assert!(t(from, p63, IntKind::I64, false).is_err(), "{from:?}");
            assert!(t(from, p64, IntKind::U64, false).is_err(), "{from:?}");
            assert_eq!(as_i128(t(from, p63, IntKind::I64, true).unwrap()), i64::MAX as i128);
            assert_eq!(as_i128(t(from, p64, IntKind::U64, true).unwrap()), u64::MAX as i128);
            assert_eq!(as_i128(t(from, -p63, IntKind::I64, false).unwrap()), i64::MIN as i128);
            assert_eq!(as_i128(t(from, p63, IntKind::U64, false).unwrap()), 1 << 63);
            assert!(t(from, -1.0, IntKind::U64, false).is_err());
            assert_eq!(as_i128(t(from, -0.9, IntKind::U64, false).unwrap()), 0);
        }
        // The largest F64 below 2^63 and below 2^64.
        assert_eq!(
            as_i128(t(FloatKind::F64, 9_223_372_036_854_774_784.0, IntKind::I64, false).unwrap()),
            9_223_372_036_854_774_784
        );
        assert_eq!(
            as_i128(t(FloatKind::F64, 18_446_744_073_709_549_568.0, IntKind::U64, false).unwrap()),
            18_446_744_073_709_549_568
        );
        // I32 keeps its bounds.
        assert!(t(FloatKind::F64, 2_147_483_648.0, IntKind::I32, false).is_err());
        assert_eq!(as_i128(t(FloatKind::F64, 2_147_483_647.9, IntKind::I32, false).unwrap()), i32::MAX as i128);
    })
}

/// S-106, spec §3.4: `to_bits()` of every NaN is the positive quiet NaN.
#[test]
fn to_bits_of_a_nan_is_the_positive_quiet_nan() {
    on_stack(|| {
        let b32 =
            |x: f32| as_i128(eval(prim(Prim::ToBits(FloatKind::F32), Ty::Int(IntKind::U32), vec![f32_(x)])).unwrap());
        let b64 =
            |x: f64| as_i128(eval(prim(Prim::ToBits(FloatKind::F64), Ty::Int(IntKind::U64), vec![f64_(x)])).unwrap());
        for x in [f32::NAN, -f32::NAN, f32::from_bits(0x7F80_0001), f32::from_bits(0xFFC0_1234)] {
            assert_eq!(b32(x), 0x7FC0_0000, "{:#x}", x.to_bits());
        }
        for x in [f64::NAN, -f64::NAN, f64::from_bits(0x7FF0_0000_0000_0001), f64::from_bits(0xFFF8_0000_0000_0042)] {
            assert_eq!(b64(x), 0x7FF8_0000_0000_0000, "{:#x}", x.to_bits());
        }
        assert_eq!(b32(-0.0), 0x8000_0000);
        assert_eq!(b64(f64::INFINITY), 0x7FF0_0000_0000_0000);
    })
}

// ------------------------------------- W2-03: R-92 (1), R-137, S-224

/// R-92 (1), R-137: a value of the wrong type where Core's types promise
/// another is an internal error, never read as 0 and never a panic of the
/// program.
#[test]
fn values_of_the_wrong_type_are_internal_errors() {
    on_stack(|| {
        let i32_ = |n| int(IntKind::I32, n);
        let i64_ = |n| int(IntKind::I64, n);
        let int_ = |k: &str, found: &str| format!("an integer of `{k}` expected, found {found}");
        let i64_found = "an integer of `I64`";
        // An `I64` value under an expression whose type says `I32`.
        let lying = || {
            Expr::new(
                Ty::Int(IntKind::I32),
                sp(),
                ExprKind::Binary {
                    op: BinOp::Add,
                    overflow: Overflow::Checked,
                    lhs: Box::new(i64_(1)),
                    rhs: Box::new(i64_(2)),
                },
            )
        };
        let block = |e: Expr| Block { stmts: Vec::new(), value: Some(Box::new(e)) };
        // (what, the check that stops it, the expression)
        let cases: Vec<(&str, String, Expr)> = vec![
            ("two integer types", int_("I32", i64_found), bin(BinOp::Add, Overflow::Checked, i32_(1), i64_(1))),
            (
                "a shift by an I32",
                int_("U32", "an integer of `I32`"),
                bin(BinOp::Shl, Overflow::Checked, i32_(1), i32_(1)),
            ),
            ("an integer and a float", int_("I32", "an `F32`"), bin(BinOp::Mul, Overflow::Checked, i32_(1), f32_(1.0))),
            (
                "a negation of a Bool",
                "an integer expected, found a `Bool`".into(),
                Expr::new(
                    Ty::Bool,
                    sp(),
                    ExprKind::Unary(UnOp::Neg, Box::new(Expr::new(Ty::Bool, sp(), ExprKind::Lit(Lit::Bool(true))))),
                ),
            ),
            (
                "a comparison of two integer types",
                int_("I32", i64_found),
                Expr::new(
                    Ty::Bool,
                    sp(),
                    ExprKind::Cmp { op: CmpOp::Lt, lhs: Box::new(i32_(1)), rhs: Box::new(i64_(2)) },
                ),
            ),
            (
                "a comparison of two float types",
                "an integer expected, found an `F32`".into(),
                Expr::new(
                    Ty::Bool,
                    sp(),
                    ExprKind::Cmp { op: CmpOp::Lt, lhs: Box::new(f32_(1.0)), rhs: Box::new(f64_(2.0)) },
                ),
            ),
            (
                "a cast of a value of another type than the operand's",
                int_("I32", i64_found),
                Expr::new(Ty::Float(FloatKind::F64), sp(), ExprKind::Cast(Box::new(lying()))),
            ),
            (
                "a cast that narrows",
                "loses information".into(),
                Expr::new(Ty::Int(IntKind::I8), sp(), ExprKind::Cast(Box::new(i32_(300)))),
            ),
            (
                "a condition that is not a Bool",
                "a `Bool` expected, found an integer of `I32`".into(),
                Expr::new(
                    Ty::Int(IntKind::I32),
                    sp(),
                    ExprKind::IfExpr { cond: Box::new(i32_(1)), then: block(i32_(1)), else_: block(i32_(2)) },
                ),
            ),
            (
                "abs of a float",
                int_("I32", "an `F32`"),
                prim(Prim::IntAbs(IntKind::I32), Ty::Int(IntKind::I32), vec![f32_(1.0)]),
            ),
            (
                "min of another width",
                int_("I32", i64_found),
                prim(Prim::IntMin(IntKind::I32), Ty::Int(IntKind::I32), vec![i32_(1), i64_(2)]),
            ),
            (
                "narrow from another width",
                int_("I64", "an integer of `I32`"),
                prim(Prim::Narrow { from: IntKind::I64, to: IntKind::I8 }, Ty::Enum(TypeId(0)), vec![i32_(1)]),
            ),
            (
                "is_nan of an integer",
                "an `F32` expected, found an integer of `I32`".into(),
                prim(Prim::IsNan(FloatKind::F32), Ty::Bool, vec![i32_(1)]),
            ),
            (
                "is_nan of the other float",
                "an `F32` expected, found an `F64`".into(),
                prim(Prim::IsNan(FloatKind::F32), Ty::Bool, vec![f64_(1.0)]),
            ),
            (
                "to_bits of the other float",
                "an `F64` expected, found an `F32`".into(),
                prim(Prim::ToBits(FloatKind::F64), Ty::Int(IntKind::U64), vec![f32_(1.0)]),
            ),
            (
                "trunc of the other float",
                "an `F64` expected, found an `F32`".into(),
                prim(
                    Prim::TruncToInt { from: FloatKind::F64, to: IntKind::I32, sat: false },
                    Ty::Int(IntKind::I32),
                    vec![f32_(1.0)],
                ),
            ),
            (
                "the second operand of pow",
                "an `F32` expected, found an `F64`".into(),
                prim(Prim::Math(MathFn::Pow, FloatKind::F32), Ty::Float(FloatKind::F32), vec![f32_(1.0), f64_(1.0)]),
            ),
            (
                "pow with one operand",
                "given 1 operands, not 2".into(),
                prim(Prim::Math(MathFn::Pow, FloatKind::F32), Ty::Float(FloatKind::F32), vec![f32_(1.0)]),
            ),
            (
                "assert_near of F32s",
                "an `F64` expected, found an `F32`".into(),
                prim(Prim::Std("std.dsp.test.assert_near".into()), Ty::Unit, vec![f32_(1.0), f32_(5.0), f32_(0.0)]),
            ),
            (
                "an index of I32",
                int_("U32", "an integer of `I32`"),
                Expr::new(
                    Ty::Int(IntKind::I32),
                    sp(),
                    ExprKind::Index {
                        base: Box::new(Expr::new(
                            Ty::Array(Box::new(Ty::Int(IntKind::I32)), 1),
                            sp(),
                            ExprKind::Array(vec![i32_(7)]),
                        )),
                        index: Box::new(i32_(0)),
                    },
                ),
            ),
        ];
        for (what, expected, e) in cases {
            let message = internal_error_of(|| eval(e));
            assert!(message.contains(&expected), "{what}: {message}");
        }
        // The two bounds of a `for` of two integer types.
        let for_ = Stmt {
            kind: StmtKind::ForRange(LocalId(0), i32_(0), i64_(3), Block { stmts: Vec::new(), value: None }),
            span: sp(),
        };
        let m = Module {
            fns: vec![FnDef {
                name: "f".into(),
                params: Vec::new(),
                ret: Ty::Unit,
                sret: false,
                rt: false,
                locals: vec![Local { name: "i".into(), ty: Ty::Int(IntKind::I32) }],
                body: Some(Block { stmts: vec![for_], value: None }),
                span: sp(),
                fp_relaxed: false,
                test: None,
            }],
            ..Default::default()
        };
        let interp = Interp::new(&m);
        let message = internal_error_of(|| interp.call(FnId(0), Vec::new()));
        assert!(message.contains(&int_("I32", i64_found)), "for: {message}");
    })
}

/// R-137: an internal failure no longer reaches the program as a panic whose
/// message starts with `internal:`.
#[test]
fn an_internal_failure_is_not_a_panic() {
    on_stack(|| {
        // A local read before it is written.
        let read = Expr::new(Ty::Int(IntKind::I32), sp(), ExprKind::Local(LocalId(0)));
        let m = Module {
            fns: vec![FnDef {
                name: "f".into(),
                params: Vec::new(),
                ret: Ty::Int(IntKind::I32),
                sret: false,
                rt: false,
                locals: vec![Local { name: "x".into(), ty: Ty::Int(IntKind::I32) }],
                body: Some(Block { stmts: Vec::new(), value: Some(Box::new(read)) }),
                span: sp(),
                fp_relaxed: false,
                test: None,
            }],
            ..Default::default()
        };
        let interp = Interp::new(&m);
        let message = internal_error_of(|| interp.call(FnId(0), Vec::new()));
        assert!(message.contains("before initialization") && !message.starts_with("internal:"), "{message}");
    })
}

/// A call of a function without a body is an internal error (lowering never
/// makes one).
#[test]
fn a_call_of_a_function_without_a_body_is_an_internal_error() {
    on_stack(|| {
        let m = Module {
            fns: vec![FnDef {
                name: "t".into(),
                params: Vec::new(),
                ret: Ty::Unit,
                sret: false,
                rt: false,
                locals: Vec::new(),
                body: None,
                span: sp(),
                fp_relaxed: false,
                test: None,
            }],
            ..Default::default()
        };
        let interp = Interp::new(&m);
        let message = internal_error_of(|| interp.call(FnId(0), Vec::new()));
        assert!(message.contains("no body"), "{message}");
    })
}

/// S-224, S-242: a `std` function the interpreter does not run is found
/// before the run ([`crate::unsupported`]) where the entries of the run reach
/// it (spec §15.2): in the body of a function a root is or calls, and in the
/// initializer of a `const` a reached function reads; nowhere else. A run
/// that reaches it stops with [`Failure::Unsupported`], not a panic.
/// [`crate::std_prim`] decides both.
#[test]
fn an_unimplemented_std_function_is_unsupported() {
    on_stack(|| {
        let gen_ = || prim(Prim::Std("std.test.gen.f32".into()), Ty::Unit, vec![f32_(0.0), f32_(1.0)]);
        let near = prim(Prim::Std("std.dsp.test.assert_near".into()), Ty::Unit, vec![f64_(1.0), f64_(1.0), f64_(0.0)]);
        let read_g = Expr::new(Ty::Unit, sp(), ExprKind::Const(ConstId(0)));
        let call = |f: u32| Expr::new(Ty::Unit, sp(), ExprKind::Call { fn_: FnId(f), args: Vec::new() });
        let fn_ = |name: &str, value: Expr| FnDef {
            name: name.into(),
            params: Vec::new(),
            ret: Ty::Unit,
            sret: false,
            rt: false,
            locals: Vec::new(),
            body: Some(Block { stmts: Vec::new(), value: Some(Box::new(value)) }),
            span: sp(),
            fp_relaxed: false,
            test: None,
        };
        let m = Module {
            fns: vec![
                fn_("f", gen_()),
                fn_("g", near),
                // Reads `G`, whose initializer uses the generator.
                fn_("h", read_g),
                // Calls `h`.
                fn_("k", call(2)),
            ],
            consts: vec![ConstDef { name: "G".into(), ty: Ty::Unit, init: gen_() }],
            ..Default::default()
        };
        let found = |roots: &[u32]| {
            let roots: Vec<FnId> = roots.iter().map(|&f| FnId(f)).collect();
            crate::unsupported(&m, &roots)
        };
        // No root, or a root that reaches only what the interpreter runs.
        assert!(found(&[]).is_empty());
        assert!(found(&[1]).is_empty(), "{:?}", found(&[1]));
        // The body of a root; the initializer of a `const` a root reads, and
        // of one that a function the root calls reads.
        for roots in [&[0][..], &[2], &[3]] {
            let got = found(roots);
            assert_eq!(got.len(), 1, "{roots:?}: {got:?}");
            assert_eq!(got[0].std_fn, "std.test.gen.f32");
        }
        let all = found(&[0, 1, 2, 3]);
        assert_eq!(all.len(), 2, "{all:?}");
        assert!(all.iter().all(|u| u.std_fn == "std.test.gen.f32"));
        let d = all[0].diagnostic();
        assert_eq!(d.code, onsa_diag::Code::E0200);
        assert!(d.message.contains("std.test.gen.f32"), "{}", d.message);
        let interp = Interp::new(&m);
        assert!(
            matches!(interp.call(FnId(0), Vec::new()), Err(Failure::Unsupported(u)) if u.std_fn == "std.test.gen.f32")
        );
        assert!(matches!(interp.const_value(ConstId(0)), Err(Failure::Unsupported(_))));
        assert!(matches!(interp.call(FnId(3), Vec::new()), Err(Failure::Unsupported(_))));
        assert!(interp.call(FnId(1), Vec::new()).is_ok());
    })
}

// ------------------------------------------------- W2-10: `onsa test`'s failures

/// Spec §6.3: the `Show` string of a float, which the panic messages use
/// (`docs/onsa-tools.md` §4): the shortest decimal that reads back, with a
/// point, in the exponent form at `1.0e21` and above and below `1.0e-7`.
#[test]
fn show_of_floats_is_the_form_of_spec_6_3() {
    let f64s: &[(f64, &str)] = &[
        (0.0, "0.0"),
        (-0.0, "-0.0"),
        (1.0, "1.0"),
        (-2.5, "-2.5"),
        (0.1, "0.1"),
        (0.1 + 0.2, "0.30000000000000004"),
        (123.456, "123.456"),
        (1.0e20, "100000000000000000000.0"),
        (1.0e21, "1.0e21"),
        (1.5e21, "1.5e21"),
        (1.0e308, "1.0e308"),
        (-1.7e308, "-1.7e308"),
        (f64::MAX, "1.7976931348623157e308"),
        (1.0e-7, "0.0000001"),
        (1.5e-8, "1.5e-8"),
        (5e-324, "5.0e-324"),
        (f64::NAN, "NaN"),
        (f64::INFINITY, "inf"),
        (f64::NEG_INFINITY, "-inf"),
    ];
    for &(x, want) in f64s {
        assert_eq!(crate::show(&Value::F64(x)), want, "{x:?}");
    }
    let f32s: &[(f32, &str)] = &[
        (0.1, "0.1"),
        (16777216.0, "16777216.0"),
        (3.4028235e38, "3.4028235e38"),
        (1.0e-7, "0.0000001"),
        (-0.0, "-0.0"),
    ];
    for &(x, want) in f32s {
        assert_eq!(crate::show(&Value::F32(x)), want, "{x:?}");
    }
}

/// Spec §11.8 (S-241): `assert_near(a, b, tol)` passes when `a == b || abs(a -
/// b) <= tol`; a `tol` not finite and at least 0 fails before the comparison;
/// the messages are those of `std/dsp/test.onsa`, with the numbers in `Show`.
#[test]
fn assert_near_follows_spec_11_8() {
    on_stack(|| {
        let near = |a: f64, b: f64, tol: f64| {
            eval(prim(Prim::Std("std.dsp.test.assert_near".into()), Ty::Unit, vec![f64_(a), f64_(b), f64_(tol)]))
        };
        let inf = f64::INFINITY;
        for (a, b, tol) in [(1.0, 1.0, 0.0), (inf, inf, 0.0), (0.0, -0.0, -0.0), (1.0, 1.25, 0.5), (1.0, 2.0, f64::MAX)]
        {
            assert!(near(a, b, tol).is_ok(), "({a}, {b}, {tol})");
        }
        let failed = |a: f64, b: f64, tol: f64| near(a, b, tol).expect_err("a failure").message;
        assert_eq!(
            failed(1.0e308, -1.0e308, 1.0),
            "assert_near failed: 1.0e308 and -1.0e308 differ by inf, more than 1.0"
        );
        assert_eq!(failed(1.0, 1.5, 0.25), "assert_near failed: 1.0 and 1.5 differ by 0.5, more than 0.25");
        assert_eq!(failed(f64::NAN, f64::NAN, 1.0), "assert_near failed: NaN and NaN differ by NaN, more than 1.0");
        for (tol, shown) in [(-1.0, "-1.0"), (inf, "inf"), (-inf, "-inf"), (f64::NAN, "NaN")] {
            assert_eq!(
                failed(1.0, 1.0, tol),
                format!("assert_near: the tolerance {shown} is not a finite number at least 0"),
                "{tol}"
            );
        }
    })
}

/// Spec §18.1 (S-233): a panic keeps the calls it went out of, innermost
/// first, up to the entry; a call beyond the limit has the 128 calls under it.
#[test]
fn a_panic_lists_the_calls_it_went_out_of() {
    on_stack(|| {
        let m = recursion_under_additions(0);
        let interp = Interp::new(&m);
        let e = panic_of(interp.call(FnId(0), vec![Value::U32(10_000)]).unwrap_err());
        assert_eq!(e.calls.len(), crate::MAX_CALL_DEPTH as usize);
        assert!(e.calls.iter().all(|c| c.callee == FnId(0)), "{:?}", e.calls);
        // A panic in the entry itself went out of no call.
        let e =
            eval(prim(Prim::Std("std.dsp.test.assert_near".into()), Ty::Unit, vec![f64_(1.0), f64_(2.0), f64_(0.0)]))
                .expect_err("a failure");
        assert!(e.calls.is_empty(), "{:?}", e.calls);
    })
}
