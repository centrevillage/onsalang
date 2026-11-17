//! The tests of the instances a flow calls, `reset`, `sample_rate()` and `sample_tick()` (W7-18 U1c): a call `f~(…)` makes
//! an instance at its place (§11.5), with its own state, its own `init`, its own `block` stage and its frames; `reset`
//! puts every state back (§11.6); `sample_rate()` and `sample_tick()` read the time of the instance (§11.4). The values
//! and the counts are worked out by hand from the spec, in the comment of each test.

use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

use super::expr::Stop;
use super::expr_tests::{def_named, i32v, is, panic_at, with_checked};
use super::flow::{Clock, Instance};
use super::flow_tests::{counted, counter, host, init_stop, with_flow};
use super::host::TableHost;
use super::scalar::{Fault, PanicKind};
use super::sema_view::View;
use super::state_tests::{f32s, floats, go, run, same};
use super::value::Value;

/// `acc~(x)` is the sum of the inputs so far: `s[n] = x[n] + s[n - 1]` (§11.4: `prev~` is the value of the last tick).
const ACC: &str = "flow acc(x: F32 at sample) -> F32 at sample {
  let s = x + prev~(^s)
  s
}
";

#[test]
fn a_call_of_a_flow_is_its_output_for_the_arguments_of_each_clock() {
    // §11.5: `gain~(x, k)` is the output of `gain` for x (`sample`) and g = k (`block`): x * g. With k = 2.0 and x = 1, 2, 3
    // it is 2, 4, 6, and 1.0 added by the caller makes 3, 5, 7. A call of 0 frames between two calls changes nothing.
    let src = "flow gain(x: F32 at sample, g: F32 at block) -> F32 at sample { x * g }
flow top(x: F32 at sample, k: F32 at block) -> F32 at sample { gain~(x, k) + 1.0 }";
    let k = vec![("k", Value::F32(2.0))];
    let outs = run(src, "top", vec![], k, vec![("x", floats(&[1.0, 2.0, 3.0]))], vec![2, 0, 1]);
    same(&f32s(&outs), &[3.0, 5.0, 7.0]);
}

#[test]
fn two_calls_of_a_flow_are_two_instances_with_a_state_each() {
    // §11.5: an instance for each place of the call. `acc` is the running sum. For x = 1, 2, 3, 4: `acc~(x)` is 1, 3, 6, 10
    // and `acc~(x * 10.0)` is 10, 30, 60, 100, so the sum is 11, 33, 66, 110 (one shared state would give other sums). In
    // calls of 1 and 3 frames the outputs are the same, and so are they when one call is inside the other (`acc~(acc~(x))`:
    // the sums of 1, 1, 1, 1 are 1, 2, 3, 4, and their sums are 1, 3, 6, 10).
    let src = format!(
        "{ACC}flow two(x: F32 at sample) -> F32 at sample {{ acc~(x) + acc~(x * 10.0) }}
flow nested(x: F32 at sample) -> F32 at sample {{ acc~(acc~(x)) }}"
    );
    let xs = floats(&[1.0, 2.0, 3.0, 4.0]);
    for calls in [vec![4], vec![1, 3]] {
        let outs = run(&src, "two", vec![], vec![], vec![("x", xs.clone())], calls);
        same(&f32s(&outs), &[11.0, 33.0, 66.0, 110.0]);
    }
    same(&go(&src, "nested", &[1.0; 4]), &[1.0, 3.0, 6.0, 10.0]);
}

#[test]
fn an_instance_inside_what_a_delay_saves_runs_once_for_each_frame() {
    // §11.4: what a delay saves is evaluated after the body, once. `prev~(acc~(x))` for x = 1, 1, 1, 1 is the sums 1, 2, 3, 4
    // one tick late: 0, 1, 2, 3; next to a call of its own, `acc~(x) + prev~(acc~(x))` is 1, 3, 5, 7. A call that is an
    // argument of a delay of the callee (`lp~(prev~(x))`) is a call as well: x = 1, 2, 3: prev 0, 1, 2; sums 0, 1, 3.
    let src = format!(
        "{ACC}flow late(x: F32 at sample) -> F32 at sample {{ prev~(acc~(x)) }}
flow both(x: F32 at sample) -> F32 at sample {{ acc~(x) + prev~(acc~(x)) }}
flow after(x: F32 at sample) -> F32 at sample {{ acc~(prev~(x)) }}"
    );
    same(&go(&src, "late", &[1.0; 4]), &[0.0, 1.0, 2.0, 3.0]);
    same(&go(&src, "both", &[1.0; 4]), &[1.0, 3.0, 5.0, 7.0]);
    same(&go(&src, "after", &[1.0, 2.0, 3.0]), &[0.0, 1.0, 3.0]);
}

#[test]
fn a_call_is_evaluated_in_a_condition_and_gives_a_struct_to_its_fields() {
    // §11.5: the condition of an `if` is always evaluated, so it may hold an instance: `acc~(x) > 2.5` for x = 1, 1, 1, 1
    // (the sums 1, 2, 3, 4) is false, false, true, true: 0, 0, 1, 1. §11.2: an output is a struct, and the field of it is
    // read: `pan~(x)` is `Stereo { l: x, r: x * 0.5 }`, so l + r is 3.0 for x = 2.0.
    let src = format!(
        "{ACC}struct Stereo {{ l: F32, r: F32 }}
flow pan(x: F32 at sample) -> Stereo at sample {{ Stereo {{ l: x, r: x * 0.5 }} }}
flow gate(x: F32 at sample) -> F32 at sample {{ if acc~(x) > 2.5 {{ 1.0 }} else {{ 0.0 }} }}
flow mix(x: F32 at sample) -> F32 at sample {{
  let s = pan~(x)
  s.l + s.r
}}"
    );
    same(&go(&src, "gate", &[1.0; 4]), &[0.0, 0.0, 1.0, 1.0]);
    same(&go(&src, "mix", &[2.0]), &[3.0]);
}

#[test]
fn the_inputs_of_a_child_of_each_clock_are_given_at_its_own_stage() {
    // §11.3, §11.5: `ramp` has p[0] = start (`init`) and p[n + 1] = p[n] + step (`block`, the step of the call that makes
    // the frame). `top` gives it start = 2 * s (an expression of `init`) and its own `st`. With s = 1.0: the call of 3
    // frames with st = 0.5 gives 2.0, 2.5, 3.0 (the stored value is 3.5 after it); a call of 0 frames with st = 100 does not
    // change it; the call of 2 frames with st = 1.0 gives 3.5, 4.5.
    let src = "flow ramp(start: F32 at init, step: F32 at block) -> F32 at sample {
  let p = prev~(^q, start)
  let q = p + step
  p
}
flow top(s: F32 at init, st: F32 at block) -> F32 at sample { ramp~(s * 2.0, st) }";
    with_flow(src, "top", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[("s", Value::F32(1.0))], None).expect("init");
        let mut outs = Vec::new();
        for (st, frames) in [(0.5, 3), (100.0, 0), (1.0, 2)] {
            outs.extend(me.process(&[("st", Value::F32(st))], &[], frames, None).expect("process"));
        }
        same(&f32s(&outs), &[2.0, 2.5, 3.0, 3.5, 4.5]);
    });
}

#[test]
fn a_child_has_its_init_once_its_block_stage_in_each_call_and_its_frames_in_each_frame() {
    // §11.3, §11.6: the child `cnt` has a `let` of each clock, each made by a function of the host that counts its calls.
    // `ci` (`init`) is made once, at the `init` of the parent; `cb` (`block`) once for each call of `process`, a call of 0
    // frames too; `cs` (`sample`) for each frame. The parent calls `cp` before the call (its argument) and after it, in each
    // frame, so the host is given to the child and back. `reset` makes none of them again (§11.6: the values of `init` are
    // kept). a = 1000, p = 100: the child is 1000 + 100 + x; the parent is 2 * that: 2202, 2204, 2206 for x = 1, 2, 3.
    counter!(row_i, N_I);
    counter!(row_b, N_B);
    counter!(row_s, N_S);
    counter!(row_p, N_P);
    let src = format!(
        "{}flow cnt(a: I32 at init, p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let k = ci(a)
  let b = cb(p)
  let s = cs(x)
  k + b + s
}}
flow top(a: I32 at init, p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let y = cnt~(a, p, cp(x))
  y + cp(y)
}}",
        counted(&["ci", "cb", "cs", "cp"])
    );
    let counts = || [&N_I, &N_B, &N_S, &N_P].map(|c| c.load(Relaxed));
    with_flow(&src, "top", move |view, def| {
        let mut t =
            TableHost::default().with("t.ci", row_i).with("t.cb", row_b).with("t.cs", row_s).with("t.cp", row_p);
        let mut me = Instance::init(view, def, 48000.0, &[("a", i32v(1000))], host(&mut t)).expect("init");
        assert_eq!(counts(), [1, 0, 0, 0]);
        let p = [("p", i32v(100))];
        let outs = me.process(&p, &[("x", &[i32v(1), i32v(2), i32v(3)])], 3, host(&mut t)).expect("process");
        assert!(outs.iter().zip([2202, 2204, 2206]).all(|(o, w)| is(&Ok(o.clone()), &i32v(w))), "{outs:?}");
        assert_eq!(counts(), [1, 1, 3, 6]);
        me.process(&p, &[("x", &[])], 0, host(&mut t)).expect("a call of 0 frames");
        assert_eq!(counts(), [1, 2, 3, 6]);
        me.reset();
        let outs = me.process(&p, &[("x", &[i32v(4), i32v(5)])], 2, host(&mut t)).expect("process");
        assert!(outs.iter().zip([2208, 2210]).all(|(o, w)| is(&Ok(o.clone()), &i32v(w))), "{outs:?}");
        assert_eq!(counts(), [1, 3, 5, 10]);
    });
}

#[test]
fn a_call_has_the_clock_of_the_output_and_not_of_its_arguments() {
    // §11.3: the clock of a call is the clock of the output of the flow (`sample`), whatever the clocks of the arguments.
    // `ticker` has an input of `block` only, and its output counts the frames (1, 2, 3, 4): the call runs for each frame,
    // though no argument changes (a call of 0 frames between does not count). The `let`s of the parent that read the call
    // are of `sample`; `sample_rate()` is of `init`, and the `let` that reads only it is too.
    let src = "flow ticker(p: I32 at block) -> I32 at sample {
  let c = prev~(^c) + 1
  c
}
flow top(p: I32 at block) -> I32 at sample {
  let y = ticker~(p)
  y
}
flow rate(x: F32 at sample) -> F32 at sample {
  let r = sample_rate()
  let q = r * 2.0
  x * q
}";
    with_flow(src, "top", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Sample, Clock::Sample]);
        let mut outs = Vec::new();
        for frames in [2, 0, 2] {
            outs.extend(me.process(&[("p", i32v(7))], &[], frames, None).expect("process"));
        }
        assert!(outs.iter().zip([1, 2, 3, 4]).all(|(o, w)| is(&Ok(o.clone()), &i32v(w))), "{outs:?}");
    });
    with_flow(src, "rate", |view, def| {
        let me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Init, Clock::Init, Clock::Sample]);
    });
}

#[test]
fn reset_puts_back_every_delay_of_the_instance_and_of_the_instances_it_calls() {
    // §11.6: `reset` makes the delays what `init` made them, the instances inside too, and the time 0; the `init` values
    // (here 2 * k = 8.0, the `init` of a delay in a child) are kept, not made again. x = 1, 2, 3 each time.
    //   top = acc~(x) + hold~(x, k * 2.0) + delay~(x, 2)
    //   first call:  acc 1 3 6, hold 8 1 2, delay 0 0 1  -> 9, 4, 9
    //   second, with no `reset`: acc 7 9 12, hold 3 1 2, delay 2 3 1  -> 12, 13, 15 (the states went on)
    //   after `reset`: as the first call  -> 9, 4, 9
    let src = format!(
        "{ACC}flow hold(x: F32 at sample, s: F32 at init) -> F32 at sample {{ prev~(x, s) }}
flow top(x: F32 at sample, k: F32 at init) -> F32 at sample {{ acc~(x) + hold~(x, k * 2.0) + delay~(x, 2) }}"
    );
    with_flow(&src, "top", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[("k", Value::F32(4.0))], None).expect("init");
        let xs = floats(&[1.0, 2.0, 3.0]);
        let call = |me: &mut Instance| f32s(&me.process(&[], &[("x", &xs[..])], 3, None).expect("process"));
        same(&call(&mut me), &[9.0, 4.0, 9.0]);
        assert_eq!(me.ctx.tick, 3);
        same(&call(&mut me), &[12.0, 13.0, 15.0]);
        assert_eq!(me.ctx.tick, 6);
        me.reset();
        assert_eq!(me.ctx.tick, 0);
        same(&call(&mut me), &[9.0, 4.0, 9.0]);
        // A reset before any frame, and two in a row, leave the instance as it was.
        me.reset();
        me.reset();
        same(&call(&mut me), &[9.0, 4.0, 9.0]);
    });
}

#[test]
fn reset_reaches_the_instances_at_every_depth() {
    // §11.6: "the sub-instances are reset recursively". `mid` is `acc~(x) + prev~(x)`, and `top` calls it at two places, the
    // second on x * 10: for x = 1, 2, 3 the first `mid` is 1 + 0, 3 + 1, 6 + 2 = 1, 4, 8, the second 10, 40, 80, so `top` is
    // 11, 44, 88; after `reset` the same again, not the sums that go on.
    let src = format!(
        "{ACC}flow mid(x: F32 at sample) -> F32 at sample {{ acc~(x) + prev~(x) }}
flow top(x: F32 at sample) -> F32 at sample {{ mid~(x) + mid~(x * 10.0) }}"
    );
    with_flow(&src, "top", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        let xs = floats(&[1.0, 2.0, 3.0]);
        let call = |me: &mut Instance| f32s(&me.process(&[], &[("x", &xs[..])], 3, None).expect("process"));
        same(&call(&mut me), &[11.0, 44.0, 88.0]);
        me.reset();
        same(&call(&mut me), &[11.0, 44.0, 88.0]);
    });
}

#[test]
fn sample_rate_is_the_rate_init_was_given_in_the_flow_and_in_the_flows_it_calls() {
    // §11.4: `sample_rate()` is the rate of the instance (the host's, for every instance called today). With 8.0:
    // `x * sample_rate()` is 4.0 and 16.0 for 0.5 and 2.0; the child `half` of `x / sample_rate()` is 0.25 for 2.0; and
    // `scale~(x, sample_rate())` gives it as the `init` argument of the child (made at `init`, with the time of the parent):
    // 1.5 * 8.0 = 12.0 and 2.0 * 8.0 = 16.0. `reset` keeps it.
    let src = "flow direct(x: F32 at sample) -> F32 at sample { x * sample_rate() }
flow half(x: F32 at sample) -> F32 at sample { x / sample_rate() }
flow via(x: F32 at sample) -> F32 at sample { half~(x) }
flow scale(x: F32 at sample, r: F32 at init) -> F32 at sample { x * r }
flow given(x: F32 at sample) -> F32 at sample { scale~(x, sample_rate()) }";
    let at8 = |name: &'static str, xs: [f32; 2]| {
        with_flow(src, name, move |view, def| {
            let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
            me.reset();
            f32s(&me.process(&[], &[("x", &floats(&xs)[..])], 2, None).expect("process"))
        })
    };
    same(&at8("direct", [0.5, 2.0]), &[4.0, 16.0]);
    same(&at8("via", [2.0, 4.0]), &[0.25, 0.5]);
    same(&at8("given", [1.5, 2.0]), &[12.0, 16.0]);
}

#[test]
#[ignore = "W7-09: the check gives `sample_tick()` E0200 (R-288) and no type, so the tables are not whole"]
fn sample_tick_counts_the_frames_since_init_and_reset_and_a_child_reads_the_same() {
    // §11.4: `sample_tick()` is the time since `reset` in ticks, a `U32` that goes round at 2^32, 0 at `init` and at `reset`
    // and not touched by anything else; in a child it is the time of the instance that calls (no `.down~` yet). The first
    // frame reads 0 (a gap of the spec, reported with this unit). A call of 3 frames reads 0, 1, 2, the next of 2 reads
    // 3, 4, a call of 0 frames none; after `reset` 0, 1. From 2^32 - 1 the frames read 4294967295, 0, 1. `sample_tick()` is of `sample`.
    // The check of this version gives it E0200 and the call no type: the tables are not whole, so this waits for W7-09.
    let src = "flow t(x: F32 at sample) -> U32 at sample { sample_tick() }
flow c(x: F32 at sample) -> U32 at sample { t~(x) }
flow clk(x: F32 at sample) -> U32 at sample {
  let n = sample_tick()
  n
}";
    for name in ["t", "c"] {
        let ticks = with_checked(src, false, move |a| {
            let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
            let read = |me: &mut Instance, frames: usize| {
                let xs = vec![Value::F32(0.0); frames];
                let outs = me.process(&[], &[("x", &xs[..])], frames, None).expect("process");
                outs.iter()
                    .map(|v| if let Value::Int(_, n, _) = v { *n } else { panic!("not an integer: {v:?}") })
                    .collect()
            };
            let mut all: Vec<Vec<i128>> = vec![read(&mut me, 3), read(&mut me, 2), read(&mut me, 0)];
            me.reset();
            all.push(read(&mut me, 2));
            me.ctx.tick = u32::MAX;
            all.push(read(&mut me, 3));
            all
        });
        assert_eq!(ticks, [vec![0, 1, 2], vec![3, 4], vec![], vec![0, 1], vec![4294967295, 0, 1]], "{name}");
    }
    with_checked(src, false, |a| {
        let me = Instance::init(View::new(a), def_named(a, "clk"), 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Sample, Clock::Sample]);
    });
}

#[test]
fn the_places_of_all_the_instances_of_the_tree_are_held_to_the_limit_and_not_each() {
    // The evaluator keeps `Limits::most` (2^20) places for the delay lines of a tree, as for one instance: a delay line of
    // 400 000 is under it alone and twice (800 000, and the 8 places of each instance), and three times (1 200 000) is over,
    // wherever the calls are: three calls of one flow, and two levels (a child with a line of 600 000 that calls another).
    // The line that goes over is not made: `Unavailable` at `init`.
    let src = "flow line(x: F32 at sample) -> F32 at sample { delay~(x, 400000) }
flow two(x: F32 at sample) -> F32 at sample { line~(x) + line~(x * 2.0) }
flow three(x: F32 at sample) -> F32 at sample { line~(x) + line~(x * 2.0) + line~(x * 3.0) }
flow leaf(x: F32 at sample) -> F32 at sample { delay~(x, 600000) }
flow mid(x: F32 at sample) -> F32 at sample { leaf~(x) + delay~(x, 600000) }
flow deep(x: F32 at sample) -> F32 at sample { mid~(x) }";
    for (name, ok) in [("line", true), ("two", true), ("three", false), ("leaf", true), ("deep", false)] {
        let r = init_stop(true, src, name);
        match (ok, &r) {
            (true, None) | (false, Some((Fault::Unavailable(_), _))) => {}
            _ => panic!("{name}: {r:?}"),
        }
    }
}

#[test]
fn a_chain_of_flows_that_call_the_next_has_the_instance_of_each() {
    // §11.5: 200 flows, each calling the next, the last a `prev~`: one instance of each, and the value is the `prev~` of the
    // last: the input one frame late (0 first). A flow that is called by two others has an instance for each of them.
    let n = 200;
    let mut src = String::from("flow c0(x: F32 at sample) -> F32 at sample { prev~(x) }\n");
    for i in 1..n {
        src += &format!("flow c{i}(x: F32 at sample) -> F32 at sample {{ c{}~(x) }}\n", i - 1);
    }
    let name: &'static str = Box::leak(format!("c{}", n - 1).into_boxed_str());
    same(&go(&src, name, &[1.0, 2.0, 3.0]), &[0.0, 1.0, 2.0]);
}

#[test]
fn a_panic_of_a_child_is_a_panic_of_the_call_at_the_place_in_the_child() {
    // §9.2, §11.5: the panic of a flow called is the panic of its caller, at the expression of the child that panics: `x / d`
    // with d = 0 in a frame (the `block` input of the call is what the parent gives), and the `let` of `block` of a child
    // (`100 / d`), made in a call of 0 frames as well (S-1093: a `let of a stage is made whether or not it is read).
    // The panic of the `init` of a child (`10 / a`) is the panic of `init` of the parent.
    let src = "flow div(x: I32 at sample, d: I32 at block) -> I32 at sample { x / d }
flow top(x: I32 at sample, d: I32 at block) -> I32 at sample { div~(x, d) }
flow bdiv(d: I32 at block, x: I32 at sample) -> I32 at sample {
  let q = 100 / d
  x + q
}
flow top2(d: I32 at block, x: I32 at sample) -> I32 at sample { bdiv~(d, x) }
flow idiv(a: I32 at init, x: I32 at sample) -> I32 at sample {
  let k = 10 / a
  x + k
}
flow top3(a: I32 at init, x: I32 at sample) -> I32 at sample { idiv~(a, x) }";
    let text = src.to_string();
    with_flow(src, "top", {
        let text = text.clone();
        move |view, def| {
            let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
            let r = me.process(&[("d", i32v(0))], &[("x", &[i32v(5)])], 1, None).map(|_| Value::Unit);
            assert_eq!(panic_at(&r, &text), (PanicKind::DivZero, "x / d".to_string()));
            let outs = me.process(&[("d", i32v(5))], &[("x", &[i32v(20)])], 1, None).expect("process");
            assert!(is(&Ok(outs[0].clone()), &i32v(4)), "{outs:?}");
        }
    });
    with_flow(src, "top2", {
        let text = text.clone();
        move |view, def| {
            let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
            let r = me.process(&[("d", i32v(0))], &[("x", &[])], 0, None).map(|_| Value::Unit);
            assert_eq!(panic_at(&r, &text), (PanicKind::DivZero, "100 / d".to_string()));
            let outs = me.process(&[("d", i32v(5))], &[("x", &[i32v(1)])], 1, None).expect("process");
            assert!(is(&Ok(outs[0].clone()), &i32v(21)), "{outs:?}");
        }
    });
    with_flow(src, "top3", move |view, def| {
        let r = Instance::init(view, def, 48000.0, &[("a", i32v(0))], None).map(|_| Value::Unit);
        assert_eq!(panic_at(&r.map_err(|s: Stop| s), &text), (PanicKind::DivZero, "10 / a".to_string()));
    });
}

#[test]
fn a_par_in_a_child_is_unavailable_at_the_init_of_the_parent() {
    // U2 has `par~`: the instance of a flow that has one cannot be made, and the parent's `init` says so (`Unavailable`),
    // not a frame later; the flow that has none is made.
    let src = "flow p(x: F32 at sample) -> F32 at sample {
  let ys = par~ i in 0 ..< 2 { x }
  ys[0]
}
flow q(x: F32 at sample) -> F32 at sample { p~(x) }
flow r(x: F32 at sample) -> F32 at sample { x }
flow s(x: F32 at sample) -> F32 at sample { r~(x) }";
    let r = init_stop(true, src, "q");
    assert!(matches!(&r, Some((Fault::Unavailable(_), at)) if at == "par~ i in 0 ..< 2 { x }"), "{r:?}");
    assert_eq!(init_stop(true, src, "s"), None);
}

#[test]
fn the_default_of_an_omitted_init_in_a_child_is_the_default_of_its_own_type() {
    // §11.4: an omitted `init` is `T.default()` of the type of the delay in the child, whatever the types of the caller: the
    // child of an `I32` starts at 0 (7, 8 give 0, 7) and the child of an `F32` at +0.0 (1.5, 2.5 give 0.0, 1.5).
    let src = "flow pi(x: I32 at sample) -> I32 at sample { prev~(x) }
flow pf(x: F32 at sample) -> F32 at sample { prev~(x) }
flow ti(x: I32 at sample) -> I32 at sample { pi~(x) }
flow tf(x: F32 at sample) -> F32 at sample { pf~(x) }";
    let outs = run(src, "ti", vec![], vec![], vec![("x", vec![i32v(7), i32v(8)])], vec![2]);
    assert!(outs.iter().zip([0, 7]).all(|(o, w)| is(&Ok(o.clone()), &i32v(w))), "{outs:?}");
    same(&go(src, "tf", &[1.5, 2.5]), &[0.0, 1.5]);
}

#[test]
fn the_instances_are_counted_in_the_limit_and_a_chain_too_deep_stops_and_does_not_overflow() {
    // The evaluator holds some 100 thousand instances (8 places each of the 2^20, `INSTANCE`), not the 2^20 that a flow
    // calling two flows, each calling two, and so on down 20 levels makes, and a chain of flows so deep that the stack
    // (64 MiB, about 9 KB for a level) does not hold it stops. Both are `Unavailable` at `init`, with no overflow.
    let mut src = String::from("flow l0(x: F32 at sample) -> F32 at sample { x }\n");
    for i in 1..=20 {
        src += &format!("flow l{i}(x: F32 at sample) -> F32 at sample {{ l{}~(x) + l{}~(x) }}\n", i - 1, i - 1);
    }
    let r = init_stop(true, &src, "l20");
    assert!(matches!(&r, Some((Fault::Unavailable(_), _))), "{r:?}");
    let mut src = String::from("flow d0(x: F32 at sample) -> F32 at sample { x }\n");
    for i in 1..=9000 {
        src += &format!("flow d{i}(x: F32 at sample) -> F32 at sample {{ d{}~(x) }}\n", i - 1);
    }
    let r = init_stop(true, &src, "d9000");
    assert!(matches!(&r, Some((Fault::Unavailable(_), _))), "{r:?}");
}
