//! The tests of a `.when~(c)` and a `.reset_if~(c)` inside a block (an `.up~` and a `.down~` outside it) and of a `.when~` of a burst under an `.up~` on the evaluator (W7-10 U3ae; §11.10, §11.9, §11.3, S-1209, S-1226):
//! a condition faster than the tick of the boundary is gathered as an input of the head is and the run j reads its entry, a value of the parameter kinds (with an `at` too) is read at the run, and a reset due at the
//! tick of the boundary puts the rings back before the runs (S-1226 (γ)). The values are worked out by hand from the spec, in the comment of each test; `cnt` gives 1 2 3 ... at its runs (`reset_tests::HEADS`).

use super::expr_tests::{def_named, with_checked};
use super::flow::Instance;
use super::reset_tests::{HEADS, outs};
use super::sema_view::View;
use super::state_tests::{f32s, same};
use super::value::Value;

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
    // reads 0 0 1 1: 0, 0, 1 + 100, 2 + 200. At the frame 8 the tick (`sample / 4`, slower than R) deals first, and the reset at `sample / 2` puts the array back after it and before the caller reads it there (§11.10: "刻みで書いて速い段が読むフィールド…は `T.default()` に戻る。カウンタは進んだままなので、次のその刻みまで `T.default()` が読まれる", the array is `T.default()` until the next tick): 0 for the frames 8 .. 11.
    let src = format!("{MORE}flow cb(b: Bool at sample) -> F32 at (sample * 2) {{
  let n = prev~(^n) + (if b {{ 1.0 }} else {{ 0.0 }})
  [n, n * 10.0]
}}
flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ g2~(cb~(c).up~(2).up~(2).down~(4).reset_if~(h2~(r))) }}");
    let cols: [(&str, &[u8]); 2] = [("c", &[1; 12]), ("r", &[0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])];
    same(&outs(&src, "top", None, &cols), &[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 101.0, 202.0, 0.0, 0.0, 0.0, 0.0]);
}

#[test]
fn a_condition_of_sample_tick_alone_gathered_under_an_outer_when_is_the_one_with_the_at_of_w() {
    // S-1230 (G): the time alone is the value the body that wrote it kept at its last tick of W, `sample / 2` (the even frames), also where the outer `when~(c)` runs the ring off that grid: c false at 5 and 13, so the runs
    // are q = 0 .. 4 at the frames 0 .. 4, 5 .. 11 at 6 .. 12, 12 13 at 14 15, and the ring is written at q' = 0 2 4 6 8 10, the frames 0 2 4 7 9 11, with the times 0 2 4 6 8 10: true false false true false false. The
    // `.down~(4)` ticks at q = 0 4 8 12 (the frames 0 4 9 14) and deals its 4 runs; its runs 0 and 2 read the ring of q - 4 and q - 2, and a true one runs `cnt` twice (the `.up~(2)`), dealt to the runs j and j + 1, a false
    // one holds the last value: the tick 0 gives 0 0 0 0, the tick 4 1 2 2 2 (the frame 5 holds 1), the tick 9 2 2 3 4 (the frame 13 holds 4), the tick 14 4 4.
    let mut c = [1; 16];
    (c[5], c[13]) = (0, 0);
    let want = [0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 2.0, 3.0, 4.0, 4.0, 4.0, 4.0];
    for k in ["sample_tick() % 3 == 0", "(sample_tick() at (sample / 2)) % 3 == 0"] {
        let src = format!(
            "{MORE}flow top(c: Bool at sample) -> F32 at sample {{ cnt~().up~(2).when~({k}).down~(2).up~(4).down~(4).when~(c) }}"
        );
        same(&outs(&src, "top", None, &[("c", &c)]), &want);
    }
}

#[test]
fn a_reset_of_sample_tick_alone_gathered_under_an_outer_when_is_the_one_with_the_at_of_w() {
    // c false at 1 only: the run q = 0 at the frame 0 and q = t - 1 from the frame 2. The ring of `sample / 2` is written at q' = 0 2 4 ..., the frames 0 3 5 7 9 11 ..., with the times 0 2 4 6 8 10: false true false true
    // false true (the times of the frames themselves are odd: never true). The `.down~(4)` ticks at q = 0 4 8 12 (the frames 0 5 9 13); the reset is read at its runs 0 and 2 (the ring of q - 4 and q - 2) before `cnt` runs
    // twice there: the tick 0 reads the defaults: 1 2 3 4 (the frame 1 holds 1); the tick 5 reads false true: 5 6 1 2; the ticks 9 and 13 the same: 3 4 1 2.
    let src = format!(
        "{MORE}flow top(c: Bool at sample) -> F32 at sample {{ cnt~().up~(2).reset_if~(sample_tick() % 4 == 2).down~(2).up~(4).down~(4).when~(c) }}"
    );
    let mut c = [1; 16];
    c[1] = 0;
    let want = [1.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 1.0, 2.0, 3.0, 4.0, 1.0, 2.0, 3.0, 4.0, 1.0];
    same(&outs(&src, "top", None, &[("c", &c)]), &want);
}

/// c false at 1 and 8: the runs are at the frames 0 2 .. 7 9 .. 13, and the ticks of a block of 2 in a `when~(c)` (its runs 0 2 4 6 8 10) at the frames 0 3 5 7 10 12.
const OFF: [u8; 14] = [1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1];

#[test]
fn a_condition_of_sample_tick_alone_under_an_outer_when_reads_the_time_of_the_last_tick_of_w_in_the_body_that_wrote_it()
{
    // S-1230 (G), §11.4: the ticks read the time of the last even frame, 0 2 4 6 10 12: `% 4 == 2` is false true false true true false (the times of the frames 0 3 5 7 10 12 would be true at 10 alone). The tick 0 holds 0 0
    // (the frames 0 2), 3 makes 1 2 (3 4), 5 holds 2 2, 7 makes 3 4 (7 and 9), 10 makes 5 6, 12 holds 6 6. The same in two blocks, whose ticks are the same.
    let want = [0.0, 0.0, 0.0, 1.0, 2.0, 2.0, 2.0, 3.0, 3.0, 4.0, 5.0, 6.0, 6.0, 6.0];
    for after in ["", ".up~(2).down~(2)"] {
        let src = format!(
            "flow top(c: Bool at sample) -> F32 at sample {{ cnt~().up~(2).when~(sample_tick() % 4 == 2).down~(2){after}.when~(c) }}"
        );
        same(&outs(&src, "top", None, &[("c", &OFF)]), &want);
    }
    // The resets at the ticks 3 7 10: 1 2 | 1 2 | 3 4 | 1 2 | 1 2 | 3 4.
    let src = "flow top(c: Bool at sample) -> F32 at sample { cnt~().up~(2).reset_if~(sample_tick() % 4 == 2).down~(2).when~(c) }";
    let want = [1.0, 1.0, 2.0, 1.0, 2.0, 3.0, 4.0, 1.0, 1.0, 2.0, 1.0, 2.0, 3.0, 4.0];
    same(&outs(src, "top", None, &[("c", &OFF)]), &want);
}

#[test]
fn a_value_of_block_mixed_with_the_time_is_the_one_of_the_tick_of_w_too() {
    // The same with `p &&` (the `at` of W on the whole is the same expression), and `process` cut at the frame 7, between the tick 6 of W and the tick 7 of the part that reads it: p is true in the first call and false in the
    // second, the tick 7 still reads what the frame 6 kept (true && true): 3 4 (the frames 7 and 9). The ticks 10 and 12 read false: 4.
    for k in [
        "p && sample_tick() % 4 == 2",
        "(p && sample_tick() % 4 == 2) at (sample / 2)",
        "sample_tick() % 4 == 2 && (p at (sample / 2))",
    ] {
        let src = format!(
            "{HEADS}flow top(c: Bool at sample, p: Bool at block) -> F32 at sample {{ cnt~().up~(2).when~({k}).down~(2).when~(c) }}"
        );
        let got = with_checked(&src, true, |a| {
            let mut me = Instance::init(View::new(a), def_named(a, "top"), 48000.0, &[], None).expect("init");
            let c = OFF.map(|b| Value::Bool(b == 1));
            let mut got = Vec::new();
            for (p, c) in [(true, &c[..7]), (false, &c[7..])] {
                let outs = me.process(&[("p", Value::Bool(p))], &[("c", c)], c.len(), None).expect("process");
                got.extend(f32s(&outs));
            }
            got
        });
        same(&got, &[0.0, 0.0, 0.0, 1.0, 2.0, 2.0, 2.0, 3.0, 3.0, 4.0, 4.0, 4.0, 4.0, 4.0]);
    }
}

#[test]
fn the_tick_of_w_is_that_of_the_body_that_wrote_the_condition_where_its_caller_stops_it() {
    // `fa` runs at the frames 0 2 .. 7 9 .. 13 (d = OFF), its runs i = 0 .. 11, and ticks its `sample / 2` at the even ones, the frames 0 3 5 7 10 12, whose times it keeps (§11.4: the time is the caller's in a `when~`).
    // c is false at the frame 3 (the run 2): the block runs at i = 0 1 3 .. 11 and ticks at i = 0 3 5 7 9 11, which read the times of i = 0 2 4 6 8 10: 0 3 5 7 10 12: `% 5 == 0` is true false true false true false
    // (the times at its ticks, the frames 0 4 6 9 11 13, would be true at 0 alone). `fa` gives 1 2, 2 at the stopped run, 2 2 | 3 4 | 4 4 | 5 6 | 6, and the frames 1 and 8 hold.
    let src =
        "flow fa(c: Bool at sample) -> F32 at sample { cnt~().up~(2).when~(sample_tick() % 5 == 0).down~(2).when~(c) }
flow top(c: Bool at sample, d: Bool at sample) -> F32 at sample { fa~(c).when~(d) }";
    let mut c = [1; 14];
    c[3] = 0;
    let want = [1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 3.0, 4.0, 4.0, 4.0, 4.0, 5.0, 6.0, 6.0];
    same(&outs(src, "top", None, &[("c", &c), ("d", &OFF)]), &want);
}

#[test]
fn a_reset_puts_back_the_condition_kept_by_the_body_it_is_of_and_not_the_one_of_its_own_chain() {
    // c is false at 1: the block ticks at the frames 0 3 5 7, which read the times 0 2 4 6 (`% 4 == 2`: false true false true). The reset at the frame 3, between two ticks of W: of the chain, whose condition is the
    // caller's (R-492), the tick 3 reads what the frame 2 kept (true): 1 2, then 2 2, 3 4 (the frames 7 8). Of the flow `fa` whose body has the chain, what its `sample / 2` kept is put back too (§11.10: `T.default()` until
    // the next tick): the tick 3 reads false: 0 0, 0 0 (the time 4), 1 2 (the time 6).
    let part = "cnt~().up~(2).when~(sample_tick() % 4 == 2).down~(2).when~(c)";
    let src = format!(
        "flow fa(c: Bool at sample) -> F32 at sample {{ {part} }}
flow chain(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ {part}.reset_if~(r) }}
flow named(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ fa~(c).reset_if~(r) }}"
    );
    let cols: [(&str, &[u8]); 2] = [("c", &[1, 0, 1, 1, 1, 1, 1, 1, 1]), ("r", &[0, 0, 0, 1, 0, 0, 0, 0, 0])];
    same(&outs(&src, "chain", None, &cols), &[0.0, 0.0, 0.0, 1.0, 2.0, 2.0, 2.0, 3.0, 4.0]);
    same(&outs(&src, "named", None, &cols), &[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 2.0]);
    // The same where the condition is gathered: the ring is written at the frames 0 3 5 7 9 11 ..., and the `.down~(4)` ticks at 0 5 9 13 17. The reset at the frame 7 takes back the ring and what the frame 6 kept, so the ring
    // is written with false there (the frame 5 was taken back, 9 is the time 8): the tick 5 deals 0 0 (the rest is put back: 0 0), the tick 9 0 0 0 0, the tick 13 (the times 8 and 10: false true) 0 0 1 2, the tick 17 2.
    let src = format!(
        "flow fa(c: Bool at sample) -> F32 at sample {{ {} }}
flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ fa~(c).reset_if~(r) }}",
        part.replace(".when~(c)", ".up~(4).down~(4).when~(c)")
    );
    let (mut c, mut r, mut want) = ([1; 18], [0; 18], [0.0; 18]);
    (c[1], r[7]) = (0, 1);
    (want[15], want[16], want[17]) = (1.0, 2.0, 2.0);
    same(&outs(&src, "top", None, &[("c", &c), ("r", &r)]), &want);
}
