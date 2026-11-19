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

// ---------------------------------------------------------------------------------------------------------------------------------
// W7-05 U2/t, S-1157 (D'): the guarded parts. A part in a position of a condition is made by the fastest of its clock and the stages of
// the conditions on the way, when they hold; a condition of a later stage (`sample`, or one the reader evaluates) leaves the part where
// it is reached. `d - 1` is 0 for d = 1, so d = 1 is the panic of each flow below.

type Inputs = &'static [(&'static str, i32)];

/// The stage and the kind of the panic of one call of 0 frames (`init` with `init`, then `block` is made, no frame) with the inputs given.
fn zero_frames(src: &'static str, name: &'static str, init: Inputs, block: Inputs) -> Option<(PanicAt, PanicKind)> {
    with_flow(src, name, move |view, def| {
        let cfg: Vec<(&str, Value)> = init.iter().map(|(n, v)| (*n, i32v(i128::from(*v)))).collect();
        match Instance::init(view, def, 8.0, &cfg, None) {
            Err(Stop { fault: Fault::Panic(k), .. }) => Some((PanicAt::Init, k)),
            Err(e) => panic!("init: {e:?}"),
            Ok(mut me) => {
                let params: Vec<(&str, Value)> = block.iter().map(|(n, v)| (*n, i32v(i128::from(*v)))).collect();
                panics(me.process_outcome(&params, &[("x", &[])], 0, None))
            }
        }
    })
}

#[test]
fn a_part_of_block_under_a_condition_of_block_is_made_at_block_where_it_holds() {
    // `d != 0` holds for d = 1 and `100 / (d - 1)` is made at `block`: a call of 0 frames panics there. d = 0: nothing is made. d = 2: 100.
    let src =
        "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if d != 0 { x * (100 / (d - 1)) } else { x } }";
    assert_eq!(zero_frames(src, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames(src, "f", &[], &[("d", 0)]), None);
    assert_eq!(zero_frames(src, "f", &[], &[("d", 2)]), None);
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let outs = me.process(&[("d", i32v(2))], &[("x", &[i32v(3)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(300)), "{outs:?}");
        // The next call does not read the part of the call before: d = 0 gives x.
        let outs = me.process(&[("d", i32v(0))], &[("x", &[i32v(3)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(3)), "{outs:?}");
    });
}

#[test]
fn the_else_branch_and_the_right_side_of_and_or_are_guarded_by_what_takes_them() {
    let else_ =
        "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if d == 0 { x } else { x * (100 / (d - 1)) } }";
    assert_eq!(zero_frames(else_, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames(else_, "f", &[], &[("d", 0)]), None);
    let and = "flow f(x: I32 at sample, d: I32 at block) -> Bool at sample { d != 0 && 100 / (d - 1) > x }";
    assert_eq!(zero_frames(and, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames(and, "f", &[], &[("d", 0)]), None);
    let or = "flow f(x: I32 at sample, d: I32 at block) -> Bool at sample { d == 0 || 100 / (d - 1) > x }";
    assert_eq!(zero_frames(or, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames(or, "f", &[], &[("d", 0)]), None);
}

#[test]
fn the_stage_of_a_guarded_part_is_the_fastest_of_its_clock_and_its_conditions() {
    // An `init` part under a condition of `block` is made at `block` (init does not panic with a = 1); a `block` part under a condition of
    // `init` is made at `block`; an `init` part under a condition of `init` is made at `init`.
    let init_in_block = "flow f(x: I32 at sample, a: I32 at init, d: I32 at block) -> I32 at sample { if d != 0 { x * (100 / (a - 1)) } else { x } }";
    assert_eq!(zero_frames(init_in_block, "f", &[("a", 1)], &[("d", 0)]), None);
    assert_eq!(zero_frames(init_in_block, "f", &[("a", 1)], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    let block_in_init = "flow f(x: I32 at sample, a: I32 at init, d: I32 at block) -> I32 at sample { if a != 0 { x * (100 / (d - 1)) } else { x } }";
    assert_eq!(zero_frames(block_in_init, "f", &[("a", 0)], &[("d", 1)]), None);
    assert_eq!(zero_frames(block_in_init, "f", &[("a", 1)], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    let init_in_init =
        "flow f(x: I32 at sample, a: I32 at init) -> I32 at sample { if a != 0 { x * (100 / (a - 1)) } else { x } }";
    assert_eq!(zero_frames(init_in_init, "f", &[("a", 1)], &[]), Some((PanicAt::Init, PanicKind::DivZero)));
    assert_eq!(zero_frames(init_in_init, "f", &[("a", 0)], &[]), None);
}

#[test]
fn a_condition_of_sample_leaves_the_part_where_it_is_reached() {
    // A call of 0 frames does not panic; the frame whose condition holds does, at `sample`; the `block` condition inside it changes nothing.
    let src = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if x > 0 { if d != 0 { x * (100 / (d - 1)) } else { x } } else { 0 } }";
    assert_eq!(zero_frames(src, "f", &[], &[("d", 1)]), None);
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let r = me.process_outcome(&[("d", i32v(1))], &[("x", &[i32v(-1)])], 1, None);
        assert_eq!(panics(r), None);
        let r = me.process_outcome(&[("d", i32v(1))], &[("x", &[i32v(-1), i32v(2)])], 2, None);
        assert_eq!(panics(r), Some((PanicAt::Sample(1), PanicKind::DivZero)));
    });
}

#[test]
fn the_arm_of_a_match_is_guarded_by_the_object_and_the_patterns_up_to_it() {
    let src =
        "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { match d { 0 => x, _ => x * (100 / (d - 1)) } }";
    assert_eq!(zero_frames(src, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames(src, "f", &[], &[("d", 0)]), None);
    // The guard of an arm is under the object and the pattern: a guard of `block` that is reached is made at `block`, a guard of `sample`
    // stops the arms after it.
    let guard = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { match d { n if 100 / (n - 1) > 5 => x, _ => 0 } }";
    assert_eq!(zero_frames(guard, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    let late = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { match d { n if x > n => 1, _ => 100 / (d - 1) } }";
    assert_eq!(zero_frames(late, "f", &[], &[("d", 1)]), None);
}

#[test]
fn a_panic_under_a_condition_is_a_panic_of_the_stage_that_decides_it() {
    let block =
        "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if d == 0 { panic(\"bad d\") } else { x } }";
    assert_eq!(zero_frames(block, "f", &[], &[("d", 0)]), Some((PanicAt::Block, PanicKind::Explicit)));
    assert_eq!(zero_frames(block, "f", &[], &[("d", 3)]), None);
    let init =
        "flow f(x: I32 at sample, a: I32 at init) -> I32 at sample { if a == 0 { panic(\"bad a\") } else { x } }";
    assert_eq!(zero_frames(init, "f", &[("a", 0)], &[]), Some((PanicAt::Init, PanicKind::Explicit)));
    let sample = "flow f(x: I32 at sample) -> I32 at sample { if x < 0 { panic(\"negative\") } else { x } }";
    assert_eq!(zero_frames(sample, "f", &[], &[]), None);
    with_flow(sample, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let r = me.process_outcome(&[], &[("x", &[i32v(1), i32v(-1)])], 2, None);
        assert_eq!(panics(r), Some((PanicAt::Sample(1), PanicKind::Explicit)));
    });
}

#[test]
fn a_constant_condition_is_decided_and_the_part_of_block_it_takes_is_made_at_block() {
    // S-1157 with S-888 (c'): a constant condition is decided before `init` (W9-03 takes its branch at compile time, as if `constexpr`), so
    // the part of `block` under `Z != 0` is made at `block` when `Z != 0` holds: a call of 0 frames panics, and under `Z == 0` it does not.
    let on = "const Z: I32 = 1\nflow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if Z != 0 { x * (100 / (d - 1)) } else { x } }";
    assert_eq!(zero_frames(on, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames(on, "f", &[], &[("d", 2)]), None);
    let off = "const Z: I32 = 0\nflow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if Z != 0 { x * (100 / (d - 1)) } else { x } }";
    assert_eq!(zero_frames(off, "f", &[], &[("d", 1)]), None);
}

#[test]
fn a_constant_condition_that_panics_is_decided_where_a_part_under_it_is_made_else_where_it_is_read() {
    // `2 % 0` panics (DivZero) and is a constant condition, which is an input of E0419 under W9-03 (it is taken at compile time); the stage
    // that decides it until then is the one of the Core: a stage decides it when a part that the stage makes is in a branch, arm or right
    // side under it (in any one, whichever it takes), else the reader evaluates it where it is reached.
    // Nothing of `init` or `block` is under it in `if (2 % 0) != 0 { x } else { x }`, so `init` and a call of 0 frames do not panic, and a
    // frame does at `sample` (x = 1: frame 0). The same for the right side of `&&` and the arms of a `match`.
    let none = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if (2 % 0) != 0 { x } else { x } }";
    let and = "flow f(x: I32 at sample) -> Bool at sample { (2 % 0) != 0 && x > 0 }";
    let arms = "const Z: I32 = 2\nflow f(x: I32 at sample) -> I32 at sample { match Z % 0 { 0 => x, _ => x + 1 } }";
    for (src, has_d) in [(none, true), (and, false), (arms, false)] {
        let block: Inputs = if has_d { &[("d", 1)] } else { &[] };
        assert_eq!(zero_frames(src, "f", &[], block), None, "{src}");
        with_flow(src, "f", move |view, def| {
            let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
            let params: Vec<(&str, Value)> = block.iter().map(|(n, v)| (*n, i32v(i128::from(*v)))).collect();
            let r = me.process_outcome(&params, &[("x", &[i32v(1)])], 1, None);
            assert_eq!(panics(r), Some((PanicAt::Sample(0), PanicKind::DivZero)), "{src}");
        });
    }
    // A part of `block` under it (`100 / d`, d = 1 does not panic by itself) makes the stage `block` decide it: the panic is the one of the
    // condition, at `block`, in a call of 0 frames, and in the branch it does not take as well (the condition is decided, not the part).
    let under =
        "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if (2 % 0) != 0 { x * (100 / d) } else { x } }";
    assert_eq!(zero_frames(under, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    let else_ =
        "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { if (2 % 0) != 0 { x } else { x * (100 / d) } }";
    assert_eq!(zero_frames(else_, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    let right = "flow f(x: I32 at sample, d: I32 at block) -> Bool at sample { (2 % 0) != 0 && 100 / d > x }";
    assert_eq!(zero_frames(right, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    // A part of `init` under it is made at `init` (the stage the condition is decided at is the same as the part's).
    let init =
        "flow f(x: I32 at sample, a: I32 at init) -> I32 at sample { if (2 % 0) != 0 { x * (100 / a) } else { x } }";
    assert_eq!(zero_frames(init, "f", &[("a", 1)], &[]), Some((PanicAt::Init, PanicKind::DivZero)));
}

#[test]
fn a_block_expression_is_walked() {
    // `({ x * (100 / (d - 1)) })`: the part of `block` in the block expression is made at `block` (§11.3, the carry-over of U1). A nested block
    // holds one expression (E0806, §11.2), so it binds no name that a part could read.
    let plain = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { x * ({ x * (100 / (d - 1)) }) }";
    assert_eq!(zero_frames(plain, "f", &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames(plain, "f", &[], &[("d", 2)]), None);
}

#[test]
fn a_struct_of_copy_elements_is_copy_and_a_part_of_its_own() {
    // §4.6: `Wrap` has no derive list and is Copy by its structure. `Wrap { a: 100 / d }` is made at `block` as a whole: d = 0 panics in a call of 0 frames.
    let src = "struct Wrap { a: I32 }\nrt fn pick(w: Wrap, x: I32) -> I32 { x * w.a }\nflow f(x: I32 at sample, d: I32 at block) -> I32 at sample { pick(Wrap { a: 100 / d }, x) }";
    assert_eq!(zero_frames(src, "f", &[], &[("d", 0)]), Some((PanicAt::Block, PanicKind::DivZero)));
}

// ---------------------------------------------------------------------------------------------------------------------------------
// W7-05 U3/t, S-1157, S-1140 (§11.3, §11.5): the body of a `par~`. The index `i` is a value of `init`, so a part of the body that reads it
// and a part of `block` are parts of each replica, made by their stage, once for each replica (S-1140, provisional: the field of the part is
// one for each replica). `100 / (d - i)` is made for i = 0, 1 and is a division by zero for d = 1 at i = 1; `d - i` is a `U32`.

use super::value::IntKind;

fn u32v(v: u32) -> Value {
    Value::int(IntKind::U32, i128::from(v))
}

type U32Inputs = &'static [(&'static str, u32)];

/// The panic of a call of 0 frames of the flow `f` of `src` (one `sample` input `x`), with the inputs of `init` and of `block` given.
fn zero_frames_u32(src: &'static str, init: U32Inputs, block: U32Inputs) -> Option<(PanicAt, PanicKind)> {
    with_flow(src, "f", move |view, def| {
        let cfg: Vec<(&str, Value)> = init.iter().map(|(n, v)| (*n, u32v(*v))).collect();
        match Instance::init(view, def, 8.0, &cfg, None) {
            Err(Stop { fault: Fault::Panic(k), .. }) => Some((PanicAt::Init, k)),
            Err(e) => panic!("init: {e:?}"),
            Ok(mut me) => {
                let params: Vec<(&str, Value)> = block.iter().map(|(n, v)| (*n, u32v(*v))).collect();
                panics(me.process_outcome(&params, &[("x", &[])], 0, None))
            }
        }
    })
}

const PAR_BLOCK: &str = "flow f(x: U32 at sample, d: U32 at block) -> U32 at sample {
  let ys = par~ i in 0 ..< 2 { x * (100 / (d - i)) }
  ys[0] + ys[1]
}";

#[test]
fn a_part_of_block_of_a_par_body_is_made_at_block_for_each_replica() {
    // d = 1 divides by zero for i = 1: a call of 0 frames panics at the `block` stage; d = 2 and d = 3 do not. d = 3, x = 1 gives 33 + 50 = 83
    // and d = 2 gives 50 + 100 = 150, the next call making its parts again (d = 4: 25 + 33 = 58).
    assert_eq!(zero_frames_u32(PAR_BLOCK, &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames_u32(PAR_BLOCK, &[], &[("d", 2)]), None);
    assert_eq!(zero_frames_u32(PAR_BLOCK, &[], &[("d", 3)]), None);
    with_flow(PAR_BLOCK, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        for (d, want) in [(3, 83), (2, 150), (4, 25 + 33)] {
            let outs = me.process(&[("d", u32v(d))], &[("x", &[u32v(1)])], 1, None).expect("process");
            assert!(is(&Ok(outs[0].clone()), &u32v(want)), "d = {d}: {outs:?}");
        }
    });
}

#[test]
fn a_part_of_init_of_a_par_body_is_made_at_init_for_each_replica() {
    // `100 / (k - i)`: k = 1 divides by zero for i = 1 at `init`, before any call; k = 2 gives 50 and 100, 150 * x (x = 2: 300), kept by the next call.
    let src = "flow f(x: U32 at sample, k: U32 at init) -> U32 at sample {
  let ys = par~ i in 0 ..< 2 { x * (100 / (k - i)) }
  ys[0] + ys[1]
}";
    assert_eq!(zero_frames_u32(src, &[("k", 1)], &[]), Some((PanicAt::Init, PanicKind::DivZero)));
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[("k", u32v(2))], None).expect("init");
        for _ in 0..2 {
            let outs = me.process(&[], &[("x", &[u32v(2)])], 1, None).expect("process");
            assert!(is(&Ok(outs[0].clone()), &u32v(300)), "{outs:?}");
        }
    });
}

#[test]
fn a_part_of_block_that_does_not_read_the_index_and_the_output_of_block_are_made_at_block() {
    // `100 / d` in the body is the same in each replica and panics at `block` with d = 0; the same for the `par~` of the output expression.
    let in_a_let = "flow f(x: U32 at sample, d: U32 at block) -> U32 at sample {
  let ys = par~ i in 0 ..< 2 { x * (100 / d) + i }
  ys[0] + ys[1]
}";
    let in_the_output = "flow f(x: U32 at sample, d: U32 at block) -> U32 at sample {
  sum2(par~ i in 0 ..< 2 { x * (100 / (d - i)) })
}
rt fn sum2(xs: [U32; 2]) -> U32 { xs[0] + xs[1] }";
    assert_eq!(zero_frames_u32(in_a_let, &[], &[("d", 0)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames_u32(in_a_let, &[], &[("d", 4)]), None);
    assert_eq!(zero_frames_u32(in_the_output, &[], &[("d", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames_u32(in_the_output, &[], &[("d", 2)]), None);
}

#[test]
fn a_par_in_a_par_has_a_part_for_each_pair() {
    // `100 / (d - (i + j))`: the pair (1, 1) divides by zero for d = 2; d = 3 gives 33 + 50 + 50 + 100 = 233 (x = 1).
    let src = "flow f(x: U32 at sample, d: U32 at block) -> U32 at sample {
  let m = par~ i in 0 ..< 2 { sum2(par~ j in 0 ..< 2 { x * (100 / (d - (i + j))) }) }
  m[0] + m[1]
}
rt fn sum2(xs: [U32; 2]) -> U32 { xs[0] + xs[1] }";
    assert_eq!(zero_frames_u32(src, &[], &[("d", 2)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames_u32(src, &[], &[("d", 3)]), None);
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let outs = me.process(&[("d", u32v(3))], &[("x", &[u32v(1)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &u32v(233)), "{outs:?}");
    });
}

#[test]
fn a_condition_in_a_par_body_guards_the_part_of_each_replica() {
    // A condition of `block` that holds: `100 / (n - i)` for i = 0, 1 is made at `block` (n = 1 panics in a call of 0 frames); one that does not hold
    // makes nothing (n = 0 does not panic, though `n - i` would be below 0). A condition of `sample` leaves the part where it is reached: a call of
    // 0 frames does not panic, a frame that does not take the branch does not (x = 0), the one that takes it does (x = 1, n = 1, the frame 0).
    let block = "flow f(x: U32 at sample, n: U32 at block) -> U32 at sample {
  let ys = par~ i in 0 ..< 2 { if n != 0 { x * (100 / (n - i)) } else { x } }
  ys[0] + ys[1]
}";
    assert_eq!(zero_frames_u32(block, &[], &[("n", 1)]), Some((PanicAt::Block, PanicKind::DivZero)));
    assert_eq!(zero_frames_u32(block, &[], &[("n", 2)]), None);
    assert_eq!(zero_frames_u32(block, &[], &[("n", 0)]), None);
    let sample = "flow f(x: U32 at sample, n: U32 at block) -> U32 at sample {
  let ys = par~ i in 0 ..< 2 { if x > 0 { x * (100 / (n - i)) } else { x } }
  ys[0] + ys[1]
}";
    assert_eq!(zero_frames_u32(sample, &[], &[("n", 1)]), None);
    with_flow(sample, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let r = me.process_outcome(&[("n", u32v(1))], &[("x", &[u32v(0)])], 1, None);
        assert_eq!(panics(r), None);
        let r = me.process_outcome(&[("n", u32v(1))], &[("x", &[u32v(1)])], 1, None);
        assert_eq!(panics(r), Some((PanicAt::Sample(0), PanicKind::DivZero)));
    });
}

#[test]
fn the_index_of_a_par_is_of_init_not_a_constant() {
    // The `par~` of `c` reads the index only: its clock is `init` (§11.5: a value of `init`, not a compile-time constant).
    let src = "flow f(x: U32 at sample) -> U32 at sample {
  let c = par~ i in 0 ..< 2 { i * 2 }
  x + c[0] + c[1]
}";
    with_flow(src, "f", |view, def| {
        let me = Instance::init(view, def, 8.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [super::flow::Clock::Init, super::flow::Clock::Sample]);
    });
}

#[test]
fn a_whole_par_of_init_is_one_part_made_at_init_and_kept_by_reset() {
    // `x * sum3(par~ i in 0 ..< 3 { 100 / (k - i) })` is of `init` as a whole: k = 2 divides by zero for i = 2 at `init`; k = 4 gives
    // 25 + 33 + 50 = 108 (x = 1; x = 2 after `reset`: 216), the value kept.
    let src = "flow f(x: U32 at sample, k: U32 at init) -> U32 at sample {
  x * sum3(par~ i in 0 ..< 3 { 100 / (k - i) })
}
rt fn sum3(xs: [U32; 3]) -> U32 { xs[0] + xs[1] + xs[2] }";
    assert_eq!(zero_frames_u32(src, &[("k", 2)], &[]), Some((PanicAt::Init, PanicKind::DivZero)));
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[("k", u32v(4))], None).expect("init");
        let outs = me.process(&[], &[("x", &[u32v(1)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &u32v(25 + 33 + 50)), "{outs:?}");
        me.reset();
        let outs = me.process(&[], &[("x", &[u32v(2)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &u32v(2 * (25 + 33 + 50))), "{outs:?}");
    });
}
