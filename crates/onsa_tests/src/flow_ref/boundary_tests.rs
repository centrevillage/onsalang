//! The tests of the boundary of an exported flow (W7-18 U2b, §9.2, §11.6, §14.2): a panic of a call zeroes all of its outputs
//! (the frames done before it too) and poisons the instance, a poisoned one gives zeros and `reset` frees it, an `init` that
//! panicked leaves it uninitialized (`process` is zeros, `reset` does nothing, only `init` again frees it), and a length of a
//! column that is not the frames is the first panic of a call. The status is the `int` of the C API (0 `Ok`, 1 `Poisoned`).
//! The values are worked out by hand from the spec, in the comment of each test.
//!
//! The evaluator has no side effect to count, so the tests count the calls of a function the host gives (`counted`): a call
//! that is counted was evaluated, one that is not was not.

use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

use super::boundary::{Boundary, Status};
use super::expr::Stop;
use super::expr_tests::{def_named, i32v, with_checked};
use super::flow::{Ctx, PanicAt};
use super::flow_tests::{counted, counter, host, with_flow};
use super::host::TableHost;
use super::scalar::{Fault, PanicKind};
use super::sema_view::View;
use super::value::{IntKind, Value};

fn ints(xs: &[i128]) -> Vec<Value> {
    xs.iter().map(|x| i32v(*x)).collect()
}

/// The integers of the outputs, or the output itself (`{:?}`) for what is not one.
fn nums(vs: &[Value]) -> Vec<i128> {
    vs.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { panic!("not an integer: {v:?}") }).collect()
}

fn ok<T>(r: Result<T, Stop>) -> T {
    r.unwrap_or_else(|stop| panic!("an error and not an outcome: {stop:?}"))
}

/// The panic the last call poisoned the instance with, as its stage, kind and the text of the expression it is at.
fn why(b: &Boundary, src: &str) -> Option<(PanicAt, PanicKind, String)> {
    b.last_panic().map(|(at, stop)| {
        let Fault::Panic(kind) = stop.fault else { panic!("a panic that is no panic: {stop:?}") };
        (*at, kind, src[stop.at.start as usize..stop.at.end as usize].to_string())
    })
}

/// A flow with an input of each clock and the three host counts: `ci` of the `init` input, `cb` of the `block` one, `cs` of the
/// `sample` one. `k = 10 a`, `q = 100 / x` (the panic), `s` the running sum of the `q` (`prev~(^s)` is the `s` of the frame
/// before, 0 at first), and the output `s + k + b`.
fn acc_src() -> String {
    format!(
        "{}flow acc(a: I32 at init, p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let k = ci(a) * 10
  let b = cb(p)
  let q = 100 / cs(x)
  let s = q + prev~(^s)
  s + k + b
}}",
        counted(&["ci", "cb", "cs"])
    )
}

#[test]
fn a_panic_zeroes_the_outputs_of_the_whole_call_and_poisons_the_instance_until_reset() {
    // §9.2: "interrupts the call, fills all of the outputs of the call (all channels and all frames, the frames computed before
    // the panic too) with zero and makes the instance poisoned. The `process` after it outputs silence and does not recover
    // until `reset`". §11.6: `reset` sets the delays back to `init`, the time to 0, "poisoned is freed", and keeps the `let`s of
    // `init`. §14.2: a poisoned instance gives 1 and is not evaluated.
    // a = 1 (k = 10), p = 0 (b = 0). Call 1, x = 50, 25: q = 2, 4; s = 2, 6; the outputs s + 10 are 12, 16 (status 0).
    // Call 2, x = 10, 0: frame 0 is q = 10, s = 6 + 10 = 16 (the output would be 26), frame 1 panics (`100 / 0`): the outputs are
    // [0, 0] and the status 1, the 26 of the frame done is not given. Every `process` after it is zeros for the frames it
    // is given (3, then 0: an empty output), the status 1, no `let` evaluated (the counts stay) and the time where it was.
    // After `reset` x = 50, 25 give 12, 16 again (the state `s` of the second call is not read: with it they would be 28
    // and 32), `ci` has not run again (k is the 10 of `init`, still used) and the time is 2 again.
    counter!(row_i, N_I);
    counter!(row_b, N_B);
    counter!(row_s, N_S);
    let src = acc_src();
    let text = src.clone();
    with_flow(&src, "acc", move |view, def| {
        let mut table = TableHost::default().with("t.ci", row_i).with("t.cb", row_b).with("t.cs", row_s);
        let counts = || [&N_I, &N_B, &N_S].map(|c| c.load(Relaxed));
        let mut b = Boundary::new(view, def, 48000.0);
        assert_eq!(ok(b.init(&[("a", i32v(1))], host(&mut table))), Status::Ok);
        let p = [("p", i32v(0))];
        let mut call = |b: &mut Boundary, xs: &[i128]| {
            let col = ints(xs);
            let (status, outs) = ok(b.process(&p, &[("x", &col[..])], xs.len(), host(&mut table)));
            (status, nums(&outs))
        };
        assert_eq!(call(&mut b, &[50, 25]), (Status::Ok, vec![12, 16]));
        assert_eq!(why(&b, &text), None);
        assert_eq!(call(&mut b, &[10, 0]), (Status::Poisoned, vec![0, 0]));
        assert_eq!(why(&b, &text), Some((PanicAt::Sample(1), PanicKind::DivZero, "100 / cs(x)".into())));
        let after_the_panic = (counts(), b.ctx());
        assert_eq!(after_the_panic.0, [1, 2, 4]);
        for xs in [&[1, 2, 3][..], &[], &[7]] {
            assert_eq!(call(&mut b, xs), (Status::Poisoned, vec![0; xs.len()]));
            assert_eq!((counts(), b.ctx()), after_the_panic, "a poisoned call evaluates nothing and goes no frame");
        }
        b.reset();
        assert_eq!(why(&b, &text), None);
        assert_eq!(call(&mut b, &[50, 25]), (Status::Ok, vec![12, 16]));
        assert_eq!(counts(), [1, 3, 6]);
        assert_eq!(b.ctx(), Some(Ctx { sample_rate: 48000.0, tick: 2 }));
    });
}

/// `k` is `100 / a` of `init`, and the output is `k + x + prev~(x)`, with the count `cs` of the frames evaluated.
const INIT_PANIC: &str = "flow g(a: I32 at init, x: I32 at sample) -> I32 at sample {
  let k = 100 / a
  let c = cs(x)
  k + c + prev~(x)
}";

#[test]
fn an_init_that_panics_leaves_the_instance_uninitialized_and_only_init_again_frees_it() {
    // §14.2: "a panic in `init` stops `init` and gives 1, fills the state with zeros and marks it uninitialized. `process` on an
    // uninitialized instance fills all outputs with 0 and gives 1 (as a poisoned one does), `reset` does nothing. The recovery is
    // the `init` again only". `100 / a` of `init` is the panic for a = 0 (the stage `Init`): the status 1; the instance has no time
    // (`ctx` is none); a `process` of 2 frames is [0, 0] with 1 and evaluates nothing (the count of `cs` stays 0), and so
    // is one of 0 frames ([]); `reset` does nothing (the next `process` is still 1).
    // `init` again with a = 5 is the recovery: k = 20, and x = 1, 2 give k + x + prev~(x) = 20 + 1 + 0, 20 + 2 + 1 = 21, 23. An
    // `init` that panics on an instance that works is the same (the state is zeros and it is uninitialized), and one more
    // `init` with a = 5 starts from the beginning: x = 1 gives 21 again (the `prev~` of the old run is not read).
    counter!(row_s, N_S);
    let src = format!("{}{INIT_PANIC}", counted(&["cs"]));
    let text = src.clone();
    with_flow(&src, "g", move |view, def| {
        let mut table = TableHost::default().with("t.cs", row_s);
        let mut b = Boundary::new(view, def, 48000.0);
        let call = |b: &mut Boundary, table: &mut TableHost, xs: &[i128]| {
            let col = ints(xs);
            let (status, outs) = ok(b.process(&[], &[("x", &col[..])], xs.len(), host(table)));
            (status, nums(&outs))
        };
        assert_eq!(ok(b.init(&[("a", i32v(0))], None)), Status::Poisoned);
        assert_eq!(why(&b, &text), Some((PanicAt::Init, PanicKind::DivZero, "100 / a".into())));
        assert_eq!(b.ctx(), None);
        assert_eq!(call(&mut b, &mut table, &[1, 2]), (Status::Poisoned, vec![0, 0]));
        assert_eq!(call(&mut b, &mut table, &[]), (Status::Poisoned, vec![]));
        b.reset();
        assert_eq!(
            (call(&mut b, &mut table, &[1, 2]), b.ctx()),
            ((Status::Poisoned, vec![0, 0]), None),
            "reset does nothing"
        );
        assert_eq!(N_S.load(Relaxed), 0);
        assert_eq!(ok(b.init(&[("a", i32v(5))], host(&mut table))), Status::Ok);
        assert_eq!(why(&b, &text), None);
        assert_eq!(call(&mut b, &mut table, &[1, 2]), (Status::Ok, vec![21, 23]));
        assert_eq!(ok(b.init(&[("a", i32v(0))], None)), Status::Poisoned);
        assert_eq!((call(&mut b, &mut table, &[1]), b.ctx()), ((Status::Poisoned, vec![0]), None));
        assert_eq!(ok(b.init(&[("a", i32v(5))], host(&mut table))), Status::Ok);
        assert_eq!(call(&mut b, &mut table, &[1]), (Status::Ok, vec![21]));
        assert_eq!(N_S.load(Relaxed), 3);
    });
}

/// Two `sample` inputs and a `block` one: `s` is the running sum of `x + y`, the output `s + b` (`b` is the `block` input).
fn two_src() -> String {
    format!(
        "{}flow two(p: I32 at block, x: I32 at sample, y: I32 at sample) -> I32 at sample {{
  let b = cb(p)
  let s = x + y + prev~(^s)
  s + b
}}",
        counted(&["cb"])
    )
}

#[test]
fn a_column_of_another_length_is_the_first_panic_of_the_call_before_any_state_moves() {
    // §11.6: "the lengths of all the `Span`s of the `sample` inputs and outputs are equal, and a panic (poisoned) if they differ.
    // The lengths are compared at the start of the call, once, before any state is moved". p = 100 (b = 100). Call 1, x = 1, 2
    // and y = 10, 20: s = 11, 33, the outputs 111, 133. Then the calls that differ in length: the columns x of 3 and y of 2 for
    // 3 frames, and the columns x and y of 2 for 3 frames (the outputs are the 3 frames the call has): both are the panic of the
    // start (`PanicAt::Start`, kind `Length`) with the outputs [0, 0, 0] and the status 1. No state moved: `cb` was not
    // evaluated (the count stays 1) and the time stays 2. The instance is poisoned (the next call, of equal lengths, is zeros),
    // and `reset` frees it: x = 1, 2 and y = 10, 20 give 111, 133 again (not 144, 166, which are the sums of the state not reset).
    counter!(row_b, N_B);
    let src = two_src();
    let text = src.clone();
    with_flow(&src, "two", move |view, def| {
        let mut table = TableHost::default().with("t.cb", row_b);
        let mut b = Boundary::new(view, def, 48000.0);
        assert_eq!(ok(b.init(&[], None)), Status::Ok);
        let p = [("p", i32v(100))];
        let mut call = |b: &mut Boundary, (x, y): (&[i128], &[i128]), frames: usize| {
            let (x, y) = (ints(x), ints(y));
            let r = b.process(&p, &[("x", &x[..]), ("y", &y[..])], frames, host(&mut table));
            let (status, outs) = ok(r);
            (status, nums(&outs))
        };
        assert_eq!(call(&mut b, (&[1, 2], &[10, 20]), 2), (Status::Ok, vec![111, 133]));
        for (cols, frames) in [((&[1, 2, 3][..], &[10, 20][..]), 3), ((&[1, 2][..], &[10, 20][..]), 3)] {
            assert_eq!(call(&mut b, cols, frames), (Status::Poisoned, vec![0, 0, 0]), "{cols:?}");
            assert_eq!(why(&b, &text).map(|(at, kind, _)| (at, kind)), Some((PanicAt::Start, PanicKind::Length)));
            assert_eq!((N_B.load(Relaxed), b.ctx().map(|c| c.tick)), (1, Some(2)), "the state did not move");
            b.reset();
            assert_eq!(call(&mut b, (&[1, 2], &[10, 20]), 2), (Status::Ok, vec![111, 133]), "reset frees it");
            N_B.store(1, Relaxed);
        }
        // Poisoned: the next call is zeros whatever its lengths, and it is the same instance as before the `reset`.
        assert_eq!(call(&mut b, (&[1], &[2, 3]), 2), (Status::Poisoned, vec![0, 0]));
        assert_eq!(call(&mut b, (&[1, 2], &[10, 20]), 2), (Status::Poisoned, vec![0, 0]));
        b.reset();
        assert_eq!(call(&mut b, (&[1, 2], &[10, 20]), 2), (Status::Ok, vec![111, 133]));
    });
}

#[test]
fn a_panic_of_the_block_stage_poisons_the_instance_in_a_call_of_0_frames_too() {
    // §11.6: a call of 0 frames evaluates the `block` stage once, so a panic of it is a panic of the call, §14.2: "a `process` of
    // `frames` 0 is a right call, and evaluates the `block` stage only", and an instance that is poisoned or not initialized
    // gives 1 without evaluating, as any call. `q = cb(100 / p)`: p = 0 is the panic of `block` (in the stage `Block`), and for
    // 0 frames the outputs are the empty vector, the status 1. A call after it (p = 5, 2 frames) is zeros [0, 0] with 1 and does
    // not evaluate (the count `cb` stays 0). After `reset` the call p = 5 is q = 20: x = 1, 2 give 21, 22 (the status 0, `cb`
    // 1 time); a call of 0 frames with p = 5 is the empty outputs and the status 0 (it is not poisoned); and a p = 0 with 3
    // frames is the panic of `block` again: the three zeros and 1 (the frames are not run).
    counter!(row_b, N_B);
    let src = format!(
        "{}flow blk(p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let q = cb(100 / p)
  x + q
}}",
        counted(&["cb"])
    );
    let text = src.clone();
    with_flow(&src, "blk", move |view, def| {
        let mut table = TableHost::default().with("t.cb", row_b);
        let mut b = Boundary::new(view, def, 48000.0);
        assert_eq!(ok(b.init(&[], None)), Status::Ok);
        let mut call = |b: &mut Boundary, p: i128, xs: &[i128]| {
            let col = ints(xs);
            let r = b.process(&[("p", i32v(p))], &[("x", &col[..])], xs.len(), host(&mut table));
            let (status, outs) = ok(r);
            (status, nums(&outs))
        };
        assert_eq!(call(&mut b, 0, &[]), (Status::Poisoned, vec![]));
        assert_eq!(why(&b, &text), Some((PanicAt::Block, PanicKind::DivZero, "100 / p".into())));
        assert_eq!(call(&mut b, 5, &[1, 2]), (Status::Poisoned, vec![0, 0]));
        assert_eq!(N_B.load(Relaxed), 0);
        b.reset();
        assert_eq!(call(&mut b, 5, &[1, 2]), (Status::Ok, vec![21, 22]));
        assert_eq!(call(&mut b, 5, &[]), (Status::Ok, vec![]));
        assert_eq!(N_B.load(Relaxed), 2);
        assert_eq!(call(&mut b, 0, &[1, 2, 3]), (Status::Poisoned, vec![0, 0, 0]));
    });
}

const SHAPES: &str = "struct Pair { a: I32 = 7, b: I32 = 3 }
struct Wide { l: [I32; 2], r: I32 = 5 }
flow arr(x: I32 at sample) -> [I32; 2] at sample { [x, 100 / x] }
flow rec(x: I32 at sample) -> Pair at sample { Pair { a: x, b: 100 / x } }
flow wide(x: I32 at sample) -> Wide at sample { Wide { l: [x, x], r: 100 / x } }
flow real(x: I32 at sample) -> F32 at sample { if 100 / x > 3 { 2.5 } else { 0.5 } }
flow flag(x: I32 at sample) -> Bool at sample { 100 / x > 3 }";

/// The outputs of `name` for x = 4, 0 (the second frame panics), and for x = 4 (no panic).
fn shapes(name: &'static str) -> (Vec<Value>, Vec<Value>) {
    with_flow(SHAPES, name, move |view, def| {
        let mut b = Boundary::new(view, def, 48000.0);
        assert_eq!(ok(b.init(&[], None)), Status::Ok);
        let good = ok(b.process(&[], &[("x", &ints(&[4])[..])], 1, None));
        assert_eq!(good.0, Status::Ok);
        b.reset();
        let (status, outs) = ok(b.process(&[], &[("x", &ints(&[4, 0])[..])], 2, None));
        assert_eq!(status, Status::Poisoned);
        (good.1, outs)
    })
}

#[test]
fn the_zeros_of_a_panic_are_the_zero_of_every_leaf_of_the_type_of_the_output() {
    // §9.2: all the channels and all the frames of the outputs are 0. The output `[I32; 2]` is `[0, 0]` for each frame, one
    // that is a struct is the zero of each field and not the value its declaration gives (`a: I32 = 7` is 0 here, not the 7 that
    // `T.default()` would be), a field that is an array is `[0, 0]`, a float the `+0.0` (all bits 0) and a `Bool` `false`.
    // x = 4 is the values by hand (100 / 4 = 25 > 3): [4, 25], `Pair { 4, 25 }`, `Wide { [4, 4], 25 }`, 2.5, and true.
    let zero = || i32v(0);
    let pair = || vec![zero(), zero()];
    let (good, bad) = shapes("arr");
    assert!(good[0].same(&Value::Array(vec![i32v(4), i32v(25)])), "{good:?}");
    assert!(bad.iter().all(|v| v.same(&Value::Array(pair()))) && bad.len() == 2, "{bad:?}");
    let (good, bad) = shapes("rec");
    assert!(good[0].same(&Value::Struct(vec![i32v(4), i32v(25)])), "{good:?}");
    assert!(bad.iter().all(|v| v.same(&Value::Struct(pair()))) && bad.len() == 2, "{bad:?}");
    let (good, bad) = shapes("wide");
    assert!(good[0].same(&Value::Struct(vec![Value::Array(vec![i32v(4), i32v(4)]), i32v(25)])), "{good:?}");
    assert!(
        bad.iter().all(|v| v.same(&Value::Struct(vec![Value::Array(pair()), zero()]))) && bad.len() == 2,
        "{bad:?}"
    );
    let (good, bad) = shapes("real");
    assert!(good[0].same(&Value::F32(2.5)) && bad.iter().all(|v| matches!(v, Value::F32(x) if x.to_bits() == 0)));
    let (good, bad) = shapes("flag");
    assert!(good[0].same(&Value::Bool(true)) && bad.iter().all(|v| v.same(&Value::Bool(false))) && bad.len() == 2);
}

#[test]
fn a_panic_in_a_flow_it_calls_or_in_a_replica_is_the_panic_of_the_call() {
    // §9.2: "a panic in a function called from Onsa goes to the nearest boundary (an exported flow)": a flow the exported one
    // calls (`top` calls `child` and adds 1) and one replica of a `par~` are the same. `top` for x = 5, 0: frame 0 is
    // 100 / 5 + 1 = 21, frame 1 is the panic of the `100 / x` in `child`: the outputs are [0, 0]. `fan` is `100 / (x - i)` for
    // i = 0, 1, 2 (`U32`): x = 5 gives [20, 25, 33] (100 / 3 = 33), x = 2 gives 50, 100 and the replica 2 divides by
    // 2 - 2 = 0: the outputs are two arrays [0, 0, 0]. The status is 1 for both and the next `process` is zeros.
    let src = "flow child(x: I32 at sample) -> I32 at sample { 100 / x }
flow top(x: I32 at sample) -> I32 at sample { child~(x) + 1 }
flow fan(x: U32 at sample) -> [U32; 3] at sample { par~ i in 0 ..< 3 { 100 / (x - i) } }";
    let text = src.to_string();
    let (top, fan) = with_checked(src, true, move |a| {
        let view = View::new(a);
        let run = |name, kind: IntKind, xs: &[i128]| {
            let mut b = Boundary::new(view, def_named(a, name), 48000.0);
            assert_eq!(ok(b.init(&[], None)), Status::Ok);
            let col: Vec<Value> = xs.iter().map(|x| Value::int(kind, *x)).collect();
            let first = ok(b.process(&[], &[("x", &col[..])], xs.len(), None));
            let again = ok(b.process(&[], &[("x", &col[..1])], 1, None));
            (first, again, why(&b, &text))
        };
        (run("top", IntKind::I32, &[5, 0]), run("fan", IntKind::U32, &[5, 2]))
    });
    assert_eq!(top.0.0, Status::Poisoned);
    assert_eq!(nums(&top.0.1), [0, 0]);
    assert_eq!((top.1.0, nums(&top.1.1)), (Status::Poisoned, vec![0]));
    assert_eq!(top.2, Some((PanicAt::Sample(1), PanicKind::DivZero, "100 / x".into())));
    let zeros = Value::Array(vec![Value::int(IntKind::U32, 0); 3]);
    assert_eq!(fan.0.0, Status::Poisoned);
    assert!(fan.0.1.len() == 2 && fan.0.1.iter().all(|v| v.same(&zeros)), "{:?}", fan.0.1);
    assert_eq!((fan.1.0, fan.1.1.len()), (Status::Poisoned, 1));
    assert_eq!(fan.2.map(|(at, kind, _)| (at, kind)), Some((PanicAt::Sample(1), PanicKind::DivZero)));
}

#[test]
fn a_panic_in_a_branch_not_taken_of_if_tilde_and_match_tilde_is_the_panic_of_the_call() {
    // §11.5, §9.2: `if~` and `match~` evaluate every branch, so a panic of the branch that is not taken is the panic of the
    // call, and the call is zeros with the status 1. `if~ c { 1 } else { 100 / d }` for c = true, d = 0 and
    // `match~ k { 0 => 1, _ => 100 / d }` for k = 0, d = 0 (the first arm is taken): the panic of `100 / d` at frame 0, the
    // outputs [0] (one frame). With d = 4 the same calls are 1 (the status 0): nothing panics, and the branch taken is the value.
    let src = "flow sel(c: Bool at sample, d: I32 at sample) -> I32 at sample { if~ c { 1 } else { 100 / d } }
flow arms(k: I32 at sample, d: I32 at sample) -> I32 at sample { match~ k { 0 => 1, _ => 100 / d } }";
    let got = with_checked(src, false, |a| {
        let view = View::new(a);
        let run = |name, first: Value, d: i128| {
            let mut b = Boundary::new(view, def_named(a, name), 48000.0);
            assert_eq!(ok(b.init(&[], None)), Status::Ok);
            let cols = [("c", &[first.clone()][..]), ("d", &[i32v(d)][..])];
            let cols = if name == "sel" { cols } else { [("k", &[first][..]), ("d", &[i32v(d)][..])] };
            let (status, outs) = ok(b.process(&[], &cols, 1, None));
            (status, nums(&outs), b.last_panic().map(|(at, _)| *at))
        };
        [
            run("sel", Value::Bool(true), 0),
            run("sel", Value::Bool(true), 4),
            run("arms", i32v(0), 0),
            run("arms", i32v(0), 4),
        ]
    });
    let (panic, fine) = ((Status::Poisoned, vec![0], Some(PanicAt::Sample(0))), (Status::Ok, vec![1], None));
    assert_eq!(got, [panic.clone(), fine.clone(), panic, fine]);
}

#[test]
fn a_form_the_evaluator_has_not_is_an_error_of_the_call_and_not_a_status() {
    // A string literal (`"ab".len()`, §11.5) is a form the evaluator has not: `init` is `Unavailable`, whatever the values. It
    // is no panic of the program, so it is not the status 1 (that is the program's, which the C API reports).
    let src = "flow p(x: F32 at sample) -> F32 at sample { x + F32.round_from(\"ab\".len()) }";
    let r = with_flow(src, "p", |view, def| Boundary::new(view, def, 48000.0).init(&[], None));
    assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })), "{r:?}");
}

/// A call stopped at the limit of the tree leaves the count of the places as it was: the calls after it stop at the
/// limit too, and do not pass with the count of the `let` given back (the break side of W7-18 U2b, the medium item).
#[test]
fn a_call_stopped_at_the_limit_leaves_the_count_of_the_places_and_the_next_calls_stop_too() {
    let src = "flow g(x: I32 at sample) -> I32 at sample {
  let big = [x; 500000]
  let d = delay~(x, 600000)
  big[0] + d
}";
    with_flow(src, "g", |view, def| {
        let mut b = Boundary::new(view, def, 48000.0);
        assert_eq!(ok(b.init(&[], None)), Status::Ok);
        for call in 0..4 {
            let col = ints(&[5, 4]);
            let r = b.process(&[], &[("x", &col[..])], 2, None);
            assert!(
                matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })),
                "call {call}: {:?}",
                r.map(|(s, _)| s)
            );
        }
    });
}
