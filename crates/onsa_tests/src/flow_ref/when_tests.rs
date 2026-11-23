//! The tests of `.when~(c)` on the evaluator (W7-10 U1e; §11.9, §11.10, S-1209, S-1222, S-1129 (1)): the part runs on the ticks of W where the condition holds, its grid counts the frames it ran while
//! `sample_tick()` is the caller's time, the output holds while it is stopped (`T.default()` before its first run, the last element N times for an output at `sample * N`), and `reset` puts it back. The
//! values are worked out by hand from the spec, in the comment of each test. The condition is a `block` input `c`, given for each call of `process`; `cnt~(1.0)` gives 1 2 3 ... at its runs.

use super::expr_tests::{def_named, with_checked};
use super::flow::Instance;
use super::scalar::Fault;
use super::sema_view::View;
use super::state_tests::{f32s, same};
use super::value::Value;

const CNT: &str = "flow cnt(k: F32 at block) -> F32 at sample {
  let n = k + prev~(^n)
  n
}
flow g2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] * 10.0 }
";

/// The outputs of the flow `name` of `CNT` and `src` for the calls `(c, frames)` one after the other on one instance, with a `reset` where `c` is `None`.
fn calls(src: &str, name: &'static str, calls: &[(Option<bool>, usize)]) -> Vec<Value> {
    let src = format!("{CNT}{src}");
    let calls = calls.to_vec();
    with_checked(&src, true, move |a| {
        let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
        let mut outs = Vec::new();
        for (c, n) in calls {
            match c {
                Some(c) => outs.extend(me.process(&[("c", Value::Bool(c))], &[], n, None).expect("process")),
                None => me.reset(),
            }
        }
        outs
    })
}

#[test]
fn a_when_at_the_clock_of_the_call_runs_where_the_condition_holds_and_holds_the_output_else() {
    // W = P = `sample` (§11.10): c = 1 1 1 0 0 1 1 runs the frames 0 1 2 5 6 as the runs 1 2 3 4 5; the frames 3 and 4 keep 3.
    let src = "flow f(c: Bool at block) -> F32 at sample { cnt~(1.0).when~(c) }";
    let given = [(Some(true), 3), (Some(false), 2), (Some(true), 2)];
    same(&f32s(&calls(src, "f", &given)), &[1.0, 2.0, 3.0, 3.0, 3.0, 4.0, 5.0]);
    // A part that never ran gives `T.default()`.
    same(&f32s(&calls(src, "f", &[(Some(false), 3)])), &[0.0, 0.0, 0.0]);
}

#[test]
fn a_when_outside_a_down_reads_the_condition_at_the_grid_and_stops_the_grid() {
    // W = `sample / 4`, the output of `cnt~(1.0).down~(4)` (§11.10, S-1209): c is read at the frames 0, 4, 8, 12 (true, false, true, true). The part runs at the grids 0, 2, 3 as its runs
    // 1, 2, 3 (its grid counts the frames it ran: 0, 4, 8), and the grid 1 keeps 1: 1 1 1 1, 1 1 1 1, 2 2 2 2, 3 3 3 3.
    let src = "flow f(c: Bool at block) -> F32 at sample { cnt~(1.0).down~(4).when~(c) at sample }";
    let given = [(Some(true), 4), (Some(false), 4), (Some(true), 8)];
    let want = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 3.0, 3.0, 3.0, 3.0];
    same(&f32s(&calls(src, "f", &given)), &want);
    // The same inside: `x.when~(c).down~(4)` reads c at the same grid (§11.10, "合成").
    let src = "flow f(c: Bool at block) -> F32 at sample { cnt~(1.0).when~(c).down~(4) at sample }";
    same(&f32s(&calls(src, "f", &given)), &want);
}

#[test]
fn the_grid_in_a_when_counts_the_frames_the_part_ran_and_sample_tick_is_the_time_of_the_caller() {
    // §11.9, §11.4, S-1129 (1): `t2` reads `sample_tick()` at its `sample / 2`, on the grid of its runs. c = 1 0 0 1 1 1: the runs are the frames 0 3 4 5 (the runs 0 1 2 3), the grid ticks
    // at the runs 0 and 2 (the frames 0 and 4) and reads the time there, 0 and 4: 0, 0 0 (stopped), 0, 4 4.
    let src = "flow t2() -> U32 at sample {
  let l = sample_tick() at (sample / 2)
  l at sample
}
flow f(c: Bool at block) -> U32 at sample { t2~().when~(c) }";
    let outs = calls(src, "f", &[(Some(true), 1), (Some(false), 2), (Some(true), 3)]);
    let ticks: Vec<i128> =
        outs.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { panic!("not an integer: {v:?}") }).collect();
    assert_eq!(ticks, [0, 0, 0, 0, 4, 4]);
}

#[test]
fn a_stopped_output_at_sample_times_n_reads_the_last_element_at_each_tick() {
    // S-1222: `cnt~(1.0).up~(2)` runs twice a frame; g2 = e0 + 10 e1. c = 1 0 1: 1 + 20 = 21, stopped: the last element 2 at both ticks, 2 + 20 = 22, then 3 + 40 = 43.
    let src = "flow f(c: Bool at block) -> F32 at sample { g2~(cnt~(1.0).up~(2).when~(c)) }";
    same(&f32s(&calls(src, "f", &[(Some(true), 1), (Some(false), 1), (Some(true), 1)])), &[21.0, 22.0, 43.0]);
    // Before its first run the N elements are `T.default()`: 0.
    same(&f32s(&calls(src, "f", &[(Some(false), 2)])), &[0.0, 0.0]);
}

#[test]
fn reset_puts_back_the_output_held_the_condition_read_and_the_frames_counted() {
    // §11.6, §11.9: `cnt~(1.0).down~(2)` under a `when~` at `sample / 2`. 3 frames of c = true give 1 1 2 and count 3 frames. After `reset` the grid of the caller starts at 0: c = false at
    // the frame 0 holds `T.default()` (not 2) for 0 0, and c = true at the frame 2 runs the part from its start (its grid at 0, not at 3): 1 1.
    let src = "flow f(c: Bool at block) -> F32 at sample { cnt~(1.0).down~(2).when~(c) at sample }";
    let given = [(Some(true), 3), (None, 0), (Some(false), 2), (Some(true), 2)];
    same(&f32s(&calls(src, "f", &given)), &[1.0, 1.0, 2.0, 0.0, 0.0, 1.0, 1.0]);
}

#[test]
fn the_runs_of_an_up_that_are_more_than_the_evaluator_holds_are_unavailable_before_they_run() {
    // 2^21 runs of `one` a frame are more than `Limits::most` (2^20) elements: the evaluator stops before it runs them (W7-16 U7).
    let src = "flow one() -> F32 at sample { 1.0 }
flow first(x: F32 at (sample * 2097152)) -> F32 at sample { x[0] }
flow f(c: Bool at block) -> F32 at sample { first~(one~().up~(2097152)) }";
    let src = format!("{CNT}{src}");
    let r = with_checked(&src, true, |a| {
        let mut me = Instance::init(View::new(a), def_named(a, "f"), 48000.0, &[], None).expect("init");
        me.process(&[("c", Value::Bool(true))], &[], 1, None).map_err(|s| s.fault)
    });
    assert!(matches!(r, Err(Fault::Unavailable(m)) if m.starts_with("a burst at `sample * N`")), "{r:?}");
}
