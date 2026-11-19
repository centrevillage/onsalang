//! The tests of hoisting on the evaluator (W7-05 U1/t, §11.3, S-1157, S-1093, S-1046): a part of a `let` or of the output that is of a slower
//! clock is made by the stage of that clock, once, whether the value is read or not. A panic of it is the panic of that stage, a call of 0
//! frames too; the value is the one that the `let` reads where it is written; the parts in a position of a condition are left where they are
//! (the guarded fields are of U2). Every value and every stage is worked out by hand in the comment of the test.

use super::expr::Stop;
use super::expr_tests::{i32v, is};
use super::flow::{Instance, Outcome, PanicAt};
use super::flow_tests::with_flow;
use super::scalar::{Fault, PanicKind};
use super::value::Value;

/// The stage and the kind of the panic of a call, or none.
fn panics(o: Result<Outcome, Stop>) -> Option<(PanicAt, PanicKind)> {
    match o.expect("a stop that is no outcome") {
        Outcome::Ok(_) => None,
        Outcome::Panic { at, stop: Stop { fault: Fault::Panic(k), .. } } => Some((at, k)),
        Outcome::Panic { .. } => panic!("a panic that is no panic"),
    }
}

#[test]
fn a_block_part_of_a_sample_expression_panics_at_the_block_stage_with_no_frame() {
    // `100 / d` is of `block`, in a `sample` expression: made by `process` once, so d = 0 panics in a call of 0 frames (§11.6) and
    // in a call of 3 frames at the `block` stage (not at the first frame); d = 4 gives 25 in each frame (x = 1, 2: 25, 50).
    let src = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { x * (100 / d) }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let r = me.process_outcome(&[("d", i32v(0))], &[("x", &[])], 0, None);
        assert_eq!(panics(r), Some((PanicAt::Block, PanicKind::DivZero)));
        let xs = [i32v(1), i32v(2), i32v(3)];
        let r = me.process_outcome(&[("d", i32v(0))], &[("x", &xs[..])], 3, None);
        assert_eq!(panics(r), Some((PanicAt::Block, PanicKind::DivZero)));
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let outs = me.process(&[("d", i32v(4))], &[("x", &xs[..2])], 2, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(25)) && is(&Ok(outs[1].clone()), &i32v(50)), "{outs:?}");
        assert!(me.process(&[("d", i32v(4))], &[("x", &[])], 0, None).expect("0 frames").is_empty());
    });
}

#[test]
fn an_init_part_panics_at_init_and_is_made_once() {
    // `100 / n` is of `init`: n = 0 panics in `init`, before any call; n = 5 gives 20, and the value is kept: the second call of
    // `process` (d = 3, so `d + 100 / n` = 23, a block part that holds the init one) reads the same 20 (x = 2: 46).
    let src = "flow f(x: I32 at sample, n: I32 at init, d: I32 at block) -> I32 at sample { x * (d + 100 / n) }";
    with_flow(src, "f", |view, def| {
        let r = Instance::init(view, def, 8.0, &[("n", i32v(0))], None);
        match r {
            Err(Stop { fault: Fault::Panic(PanicKind::DivZero), .. }) => {}
            other => panic!("init did not panic: {:?}", other.map(|_| ())),
        }
        let mut me = Instance::init(view, def, 8.0, &[("n", i32v(5))], None).expect("init");
        let outs = me.process(&[("d", i32v(3))], &[("x", &[i32v(2)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(46)), "{outs:?}");
        let outs = me.process(&[("d", i32v(1))], &[("x", &[i32v(2)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(42)), "{outs:?}");
    });
}

#[test]
fn a_block_part_is_made_again_for_each_call() {
    // The kept value of the call before is not read: d = 1 then d = 2 gives 100 / 1 = 100 then 50 (x = 1).
    let src = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { x * (100 / d) }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        for (d, want) in [(1, 100), (2, 50), (5, 20)] {
            let outs = me.process(&[("d", i32v(d))], &[("x", &[i32v(1)])], 1, None).expect("process");
            assert!(is(&Ok(outs[0].clone()), &i32v(want)), "{outs:?}");
        }
    });
}

#[test]
fn the_part_of_a_let_and_of_the_output_and_in_the_argument_of_a_node_are_made_by_their_stage() {
    // `a`'s part `100 / d`, the output's part `100 / e` and the delay's argument part `100 / g`: each panics at the `block` stage
    // with 0 frames, whichever is 0 (the first by position first, S-1159 provisional: the one of the panic is not told here).
    let src = "flow f(x: I32 at sample, d: I32 at block, e: I32 at block, g: I32 at block) -> I32 at sample {
  let a = x + 100 / d
  a + prev~(x * (100 / g)) + 100 / e
}";
    with_flow(src, "f", |view, def| {
        let params = |d, e, g| [("d", i32v(d)), ("e", i32v(e)), ("g", i32v(g))];
        for (d, e, g) in [(0, 1, 1), (1, 0, 1), (1, 1, 0)] {
            let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
            let r = me.process_outcome(&params(d, e, g), &[("x", &[])], 0, None);
            assert_eq!(panics(r), Some((PanicAt::Block, PanicKind::DivZero)), "{d} {e} {g}");
        }
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let r = me.process_outcome(&params(1, 1, 1), &[("x", &[])], 0, None);
        assert_eq!(panics(r), None);
    });
}

#[test]
fn a_part_that_is_not_copy_is_not_hoisted_and_the_copy_part_in_it_is() {
    // `Wrap` has no derive list, so it is Affine and not Copy: `Wrap { a: 100 / d, b: 1 }` is read where it is written, and
    // `100 / d` in it is made at `block`: d = 0 panics in a call of 0 frames; d = 4 gives 26 * x.
    let src = "struct Wrap { a: I32, b: I32 }
rt fn pick(w: Wrap, x: I32) -> I32 { x * (w.a + w.b) }
flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { pick(Wrap { a: 100 / d, b: 1 }, x) }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let r = me.process_outcome(&[("d", i32v(0))], &[("x", &[])], 0, None);
        assert_eq!(panics(r), Some((PanicAt::Block, PanicKind::DivZero)));
        let outs = me.process(&[("d", i32v(4))], &[("x", &[i32v(2)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(52)), "{outs:?}");
    });
}

#[test]
fn a_part_in_a_branch_is_not_hoisted_here() {
    // The branch of an `if` and the right side of `&&` are positions of a condition (S-1157, the guarded fields are of U2): `100 / d`
    // with d = 0 is made where it is reached, so a call of 0 frames does not panic and a frame whose branch is taken does (at `sample`).
    // The condition `x > 0` and the object of a `match` are not branches: `100 / d > 1` in the condition panics at `block`.
    let src = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if x > 0 { 100 / d } else { 0 } }
flow g(x: I32 at sample, d: I32 at block) -> I32 at sample { if 100 / d > 1 { x } else { 0 } }
flow h(x: I32 at sample, d: I32 at block) -> I32 at sample { if x > 0 && 100 / d > 1 { 1 } else { 0 } }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        assert_eq!(panics(me.process_outcome(&[("d", i32v(0))], &[("x", &[])], 0, None)), None);
        let r = me.process_outcome(&[("d", i32v(0))], &[("x", &[i32v(-1)])], 1, None);
        assert_eq!(panics(r), None);
        let r = me.process_outcome(&[("d", i32v(0))], &[("x", &[i32v(1)])], 1, None);
        assert_eq!(panics(r), Some((PanicAt::Sample(0), PanicKind::DivZero)));
    });
    with_flow(src, "g", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let r = me.process_outcome(&[("d", i32v(0))], &[("x", &[])], 0, None);
        assert_eq!(panics(r), Some((PanicAt::Block, PanicKind::DivZero)));
    });
    with_flow(src, "h", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        assert_eq!(panics(me.process_outcome(&[("d", i32v(0))], &[("x", &[])], 0, None)), None);
    });
}

#[test]
fn a_name_a_constant_and_sample_rate_are_not_hoisted() {
    // Nothing of these panics; the values are what they are: x * g + 2 * 3 + sample_rate() with g = 2, rate 8 and x = 1: 2 + 6 + 8 = 16.
    let src = "flow f(x: F32 at sample, g: F32 at block) -> F32 at sample { x * g + 2.0 * 3.0 + sample_rate() }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let outs = me.process(&[("g", Value::F32(2.0))], &[("x", &[Value::F32(1.0)])], 1, None).expect("process");
        assert!(outs[0].same(&Value::F32(16.0)), "{outs:?}");
    });
}

#[test]
fn a_constant_that_panics_is_not_hoisted_to_init() {
    // `10 / z` where `z` is a `const` of 0 is a constant expression: W9-03 makes it at compile time (E0419); until then it is read where
    // it is written, at `sample`, so `init` and a call of 0 frames do not panic and a frame does (the interpreter's reading).
    let src = "const Z: I32 = 0
flow f(x: I32 at sample) -> I32 at sample { x + 10 / Z }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        assert_eq!(panics(me.process_outcome(&[], &[("x", &[])], 0, None)), None);
        let r = me.process_outcome(&[], &[("x", &[i32v(1)])], 1, None);
        assert_eq!(panics(r), Some((PanicAt::Sample(0), PanicKind::DivZero)));
    });
}
