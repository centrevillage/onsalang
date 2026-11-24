//! The tests of a `.when~(c)` and a `.reset_if~(c)` inside a block (an `.up~` and a `.down~` outside it) and of a `.when~` of a burst under an `.up~` on the evaluator (W7-10 U3ae; §11.10, §11.9, §11.3, S-1209, S-1226):
//! a condition faster than the tick of the boundary is gathered as an input of the head is and the run j reads its entry, a value of the parameter kinds (with an `at` too) is read at the run, and a reset due at the
//! tick of the boundary puts the rings back before the runs (S-1226 (γ)). The values are worked out by hand from the spec, in the comment of each test; `cnt` gives 1 2 3 ... at its runs (`reset_tests::HEADS`).

use super::reset_tests::outs;
use super::state_tests::same;

const MORE: &str =
    "flow g4(x: F32 at (sample * 4)) -> F32 at sample { x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0 }
flow pk2(x: Bool at (sample * 2)) -> Bool at sample { x[1] }
flow h2(c: Bool at sample) -> Bool at (sample / 2) { pk2~(c).down~(2) }
flow slot8(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(8)
  let n = prev~(^n) + 1.0
  (s at sample) * 100.0 + n
}
";

#[test]
fn a_signal_condition_in_a_block_is_gathered_with_the_inputs_and_each_run_reads_its_own_entry() {
    // The ticks 0 2 4 6 gather c of the two frames before (the defaults at the tick 0) and deal the outputs of the 2 runs to the tick and the frame after. c = 1 1 0 1 1 1 0 0: the tick 0 is stopped (0 0), the tick 2 runs
    // both (1 2), the tick 4 holds 2 at the run 0 and makes 3, the tick 6 makes 4 5.
    let when = format!("{MORE}flow top(c: Bool at sample) -> F32 at sample {{ cnt~().when~(c).up~(2).down~(2) }}");
    same(&outs(&when, "top", None, &[("c", &[1, 1, 0, 1, 1, 1, 0, 0])]), &[0.0, 0.0, 1.0, 2.0, 2.0, 3.0, 4.0, 5.0]);
    // A reset: r at the frame 3 is the entry 1 of the tick 4: the run 1 is put back first: 1 2 3 4 5 1 2 3.
    let reset = format!("{MORE}flow top(r: Bool at sample) -> F32 at sample {{ cnt~().reset_if~(r).up~(2).down~(2) }}");
    same(&outs(&reset, "top", None, &[("r", &[0, 0, 0, 1, 0, 0, 0, 0])]), &[1.0, 2.0, 3.0, 4.0, 5.0, 1.0, 2.0, 3.0]);
}

#[test]
fn a_value_of_the_parameter_kinds_with_an_at_in_a_block_is_read_at_the_run_and_not_gathered() {
    // §11.3: `p at sample` is the value of p now (x is there for the frames). Gathered, the tick 0 would read `false` (the defaults) and the part would run there (no `when~`) or not be put back (`reset_if~`).
    let when = format!(
        "{MORE}flow top(x: Bool at sample, p: Bool at block) -> F32 at sample {{ cnt~().when~(p at sample).up~(2).down~(2) }}"
    );
    same(&outs(&when, "top", Some(true), &[("x", &[0; 6])]), &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
    let reset = format!(
        "{MORE}flow top(x: Bool at sample, p: Bool at block) -> F32 at sample {{ cnt~().reset_if~(p at sample).up~(2).down~(2) }}"
    );
    same(&outs(&reset, "top", Some(true), &[("x", &[0; 6])]), &[1.0; 6]);
}

#[test]
fn a_condition_gathered_by_two_boundaries_goes_through_both_rings() {
    // `.up~(4).down~(2).down~(2)`: the outer `.down~` gathers c of 2 frames at its ticks (every 2), the inner one 2 of those (4 values) at its ticks (every 4), and the 4 runs of a tick deal 4 values, one to each frame from it.
    // The tick 0 holds the defaults, the tick 4 the frames 0 1 (the defaults of the outer ring at the tick 0) and 2 3 (c(0), c(1)): with c true all along, 0 0 0 0, 0 0 1 2, 3 4 5 6.
    let src =
        format!("{MORE}flow top(c: Bool at sample) -> F32 at sample {{ cnt~().when~(c).up~(4).down~(2).down~(2) }}");
    let want = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
    same(&outs(&src, "top", None, &[("c", &[1; 12])]), &want);
}

#[test]
fn a_reset_at_the_tick_of_the_boundary_puts_the_ring_back_before_the_runs_read_it() {
    // `h2~(r)` is r(p - 1) at the even position p: the reset at the tick 4 (r at the frame 3) comes before the work of that tick, the ring of c included (§11.10, "その刻みに続く x の段の前に"; no work of a slower tick in the
    // part): both runs read `false`, the held output is put back: 0 0 1 2 0 0, and the tick 6 runs from the start: 1 2.
    let src = format!(
        "{MORE}flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ cnt~().when~(c).up~(2).down~(2).reset_if~(h2~(r)) }}"
    );
    let cols: [(&str, &[u8]); 2] = [("c", &[1; 8]), ("r", &[0, 0, 0, 1, 0, 0, 0, 0])];
    same(&outs(&src, "top", None, &cols), &[0.0, 0.0, 1.0, 2.0, 0.0, 0.0, 1.0, 2.0]);
}

#[test]
fn a_reset_at_the_tick_of_the_boundary_puts_the_ring_back_before_the_runs_also_with_slower_work_a_when_runs_in_its_w() {
    // S-1226 (γ), the case `reset_ring_order_s1226.onsa` (whose test the walker skips: two columns in an `In`): `slot8` has a stage of `sample / 8`, slower than R (`sample / 2`), which the `when~` runs in its W (S-1228:
    // the reset comes before it). The tick 0 reads the defaults (0 0); the tick 2 makes the runs 0 and 1 (101 102, the run 0 a tick of `sample / 8`: s = 1). At the tick 4 the part, the ring of c too, is put back before
    // the runs: both read `false` and hold the output put back (0 0). The ticks 6 8 10 make the runs 2 .. 7 from the start (no tick of `sample / 8` there: s = 0): 1 2 3 4 5 6.
    let src = format!(
        "{MORE}flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ slot8~(1.0).when~(c).up~(2).down~(2).reset_if~(h2~(r)) }}"
    );
    let cols: [(&str, &[u8]); 2] = [("c", &[1; 12]), ("r", &[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])];
    same(&outs(&src, "top", None, &cols), &[0.0, 0.0, 101.0, 102.0, 0.0, 0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
}

#[test]
fn a_when_of_a_burst_under_an_up_holds_the_burst_of_its_last_run() {
    // `cnt~().up~(2)` gives 2 values a run of the outer `.up~(2)`, and c (a value of `sample`, slower than W) is read held at both runs: c = 0 1 0 1: the frame 0 holds the defaults (0), the frame 1 makes 1 2 | 3 4 (4321), the
    // frame 2 reads the last value 4 four times (4444), the frame 3 makes 5 6 | 7 8 (8765).
    let src = format!("{MORE}flow top(c: Bool at sample) -> F32 at sample {{ g4~(cnt~().up~(2).when~(c).up~(2)) }}");
    same(&outs(&src, "top", None, &[("c", &[0, 1, 0, 1])]), &[0.0, 4321.0, 4444.0, 8765.0]);
}

#[test]
fn a_reset_between_two_ticks_of_a_boundary_that_deals_puts_the_array_back_before_the_caller_reads_it() {
    // Not a modifier in a block (a form of U2, which the evaluator had wrong): `cb` counts the true inputs, [n, 10 n] at each of the 4 runs of a tick of the `.down~(4)` (every 4 frames), which gathers c of the 4 frames
    // before. `h2~(r)` is r(p - 1) at the even position p: the resets at the frames 2 and 8. The tick 0 reads the defaults (0 0 0 0); the reset at 2 puts back the ring (c(0), c(1)), the count and the dealt array; the tick 4
    // reads 0 0 1 1: 0, 0, 1 + 100, 2 + 200. At the frame 8 the tick (`sample / 4`, slower than R) deals first, and the reset at `sample / 2` puts the array back after it and before the caller reads it there (§11.10: "条件の刻みより
    // 遅い刻みは…その位置で先に書いた後に戻す", the array is `T.default()` until the next tick): 0 for the frames 8 .. 11.
    let src = format!("{MORE}flow cb(b: Bool at sample) -> F32 at (sample * 2) {{
  let n = prev~(^n) + (if b {{ 1.0 }} else {{ 0.0 }})
  [n, n * 10.0]
}}
flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ g2~(cb~(c).up~(2).up~(2).down~(4).reset_if~(h2~(r))) }}");
    let cols: [(&str, &[u8]); 2] = [("c", &[1; 12]), ("r", &[0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])];
    same(&outs(&src, "top", None, &cols), &[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 101.0, 202.0, 0.0, 0.0, 0.0, 0.0]);
}

#[test]
fn a_condition_of_sample_tick_alone_gathered_under_an_outer_when_reads_the_time_its_ring_is_written_at() {
    // §11.4: `sample_tick()` is the time of the place that reads it; gathered (§11.10), that is where the outer ring is written, which the outer `when~(c)` runs at the frames it ran (c false at 5 and 13: the runs
    // q = 0 .. 4 at the frames 0 .. 4, 5 .. 11 at 6 .. 12, 12 13 at 14 15; the ring of `sample / 2` is written at q' = 0 2 4 6 8 10, the frames 0 2 4 7 9 11: true false false false true false). The `.down~(4)` ticks
    // at q = 0 4 8 12 (the frames 0 4 9 14) and deals its 4 runs; its runs 0 and 2 read the ring of q - 4 and q - 2, and a true one runs `cnt` twice (the `.up~(2)`), dealt to the runs j and j + 1, a false one holds
    // the last value: the tick 0 gives 0 0 0 0, the tick 4 1 2 2 2 (the frame 5 holds 1), the tick 9 2 2 2 2 (the frame 13 holds 2), the tick 14 3 4.
    let src = format!(
        "{MORE}flow top(c: Bool at sample) -> F32 at sample {{ cnt~().up~(2).when~(sample_tick() % 3 == 0).down~(2).up~(4).down~(4).when~(c) }}"
    );
    let mut c = [1; 16];
    (c[5], c[13]) = (0, 0);
    let want = [0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 3.0, 4.0];
    same(&outs(&src, "top", None, &[("c", &c)]), &want);
    // With an `at` it is a value of `sample / 2`, read as a signal is: the ring holds the caller's value of its last tick, the frame 6 (true) at q' = 6: the tick 9 holds 2 at its run 0 and makes 3 4 at its run 2,
    // and the tick 14 reads false false: 4 4.
    let at = format!(
        "{MORE}flow top(c: Bool at sample) -> F32 at sample {{ cnt~().up~(2).when~((sample_tick() at (sample / 2)) % 3 == 0).down~(2).up~(4).down~(4).when~(c) }}"
    );
    let want = [0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 2.0, 3.0, 4.0, 4.0, 4.0, 4.0];
    same(&outs(&at, "top", None, &[("c", &c)]), &want);
}

#[test]
fn a_reset_of_sample_tick_alone_gathered_under_an_outer_when_reads_the_time_its_ring_is_written_at() {
    // c false at 1 only: the run q = 0 at the frame 0 and q = t - 1 from the frame 2. The ring of `sample / 2` is written at q' = 0 2 4 ..., the frames 0 3 5 7 9 11 13 15: false, then true (odd frames). The `.down~(4)`
    // ticks at q = 0 4 8 12 (the frames 0 5 9 13); the reset is read at its runs 0 and 2 (the ring of q - 4 and q - 2) before `cnt` runs twice there: the tick 0 reads the defaults: 1 2 3 4 (the frame 1 holds 1);
    // the tick 5 reads false true: 5 6 1 2; the ticks 9 and 13 read true true: 1 2 1 2.
    let src = format!(
        "{MORE}flow top(c: Bool at sample) -> F32 at sample {{ cnt~().up~(2).reset_if~(sample_tick() % 2 == 1).down~(2).up~(4).down~(4).when~(c) }}"
    );
    let mut c = [1; 16];
    c[1] = 0;
    let want = [1.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 1.0, 2.0, 1.0, 2.0, 1.0, 2.0, 1.0, 2.0, 1.0];
    same(&outs(&src, "top", None, &[("c", &c)]), &want);
}
