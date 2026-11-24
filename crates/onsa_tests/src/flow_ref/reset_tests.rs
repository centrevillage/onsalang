//! The tests of `.reset_if~(r)` on the evaluator (W7-10 U2e; §11.10, §11.9, S-1186, S-1218, S-1222, S-1228) and of a head input slower than the W of a `.when~`: the part is put back at the tick of its condition, after
//! the slower stages wrote (not those a `when~` inside runs in its W, `reset_order_tests`) and before the first work of a stage that is not slower, once a frame before the first run of an `.up~`, and at a stopped frame of a `when~` inside; the phase
//! counters and what a `when~` remembers go on. The values are worked out by hand from the spec, in the comment of each test. `slot(f)` writes `s` at `sample / 2` (its grid) and counts the frames in `n`: 100 s + n.

use super::expr_tests::{def_named, with_checked};
use super::flow::Instance;
use super::sema_view::View;
use super::state_tests::{f32s, same};
use super::value::Value;

const HEADS: &str = "flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}
flow slot(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(2)
  let n = prev~(^n) + 1.0
  (s at sample) * 100.0 + n
}
flow slot4(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(4)
  let n = prev~(^n) + 1.0
  (s at sample) * 100.0 + n
}
flow cnt() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}
flow g2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] * 10.0 }
flow sl(p: F32 at (sample / 2)) -> F32 at sample {
  let h = p + 1.0
  h at sample
}
";

/// The outputs of the flow `name` of `HEADS` and `src` for one call of `process` of the `sample` columns `cols` (by the input name, 0 and 1) and the `block` input `p`.
pub(super) fn outs(src: &str, name: &'static str, p: Option<bool>, cols: &[(&'static str, &[u8])]) -> Vec<f32> {
    let src = format!("{HEADS}{src}");
    let cols: Vec<(&'static str, Vec<Value>)> =
        cols.iter().map(|(n, c)| (*n, c.iter().map(|b| Value::Bool(*b == 1)).collect())).collect();
    with_checked(&src, true, move |a| {
        let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
        let given: Vec<(&str, &[Value])> = cols.iter().map(|(n, c)| (*n, &c[..])).collect();
        let params: Vec<(&str, Value)> = p.map(|p| ("p", Value::Bool(p))).into_iter().collect();
        f32s(&me.process(&params, &given, cols[0].1.len(), None).expect("process"))
    })
}

#[test]
fn a_reset_at_a_frame_of_the_grid_comes_after_the_slower_stage_wrote_and_one_between_leaves_the_field_at_its_default() {
    // W = P = `sample`: r at the frame 4 (a grid): the grid writes s = 3, the reset takes s, n and the child back: 1 2, then the grid 6 gives s = 1, n = 3. r at the frame 3 (no grid): s = 0 until the
    // grid 4 writes 1 (the counter did not move): 1, 102 103 204 205.
    let src = "flow top(r: Bool at sample) -> F32 at sample { slot~(1.0).reset_if~(r) }";
    same(
        &outs(src, "top", None, &[("r", &[0, 0, 0, 0, 1, 0, 0, 0])]),
        &[101.0, 102.0, 203.0, 204.0, 1.0, 2.0, 103.0, 104.0],
    );
    same(
        &outs(src, "top", None, &[("r", &[0, 0, 0, 1, 0, 0, 0, 0])]),
        &[101.0, 102.0, 203.0, 1.0, 102.0, 103.0, 204.0, 205.0],
    );
}

#[test]
fn a_reset_outside_a_when_puts_back_the_stopped_frames_and_the_held_output_and_one_inside_only_the_frames_that_run() {
    // c = 1 1 0 1 0 0 1 1 (the runs 0 .. 4 at the frames 0 1 3 6 7), r = 0 0 1 1 0 1 0 0. Outside: the stopped frame 2 resets (the held output 0); the run 2 at the frame 3 is a grid of the part, which the `when~` runs in
    // its W: the part is put back before it (S-1228), and it writes s = 1 from the start: n = 1, 101; the frame 4 holds 101; the stopped frame 5 is reset to 0; the run 3 (no grid) is 1; the run 4 (a grid) s = 1, n = 2: 102.
    // Inside: the stopped frames are not reset: the frame 2 holds 102; the run 2 is 1, held at 4 and 5; the run 3 is 2; the run 4 is s = 1, n = 3: 103.
    let cols: [(&str, &[u8]); 2] = [("c", &[1, 1, 0, 1, 0, 0, 1, 1]), ("r", &[0, 0, 1, 1, 0, 1, 0, 0])];
    let outside =
        "flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample { slot~(1.0).when~(c).reset_if~(r) }";
    let inside = "flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample { slot~(1.0).reset_if~(r).when~(c) }";
    same(&outs(outside, "top", None, &cols), &[101.0, 102.0, 0.0, 101.0, 101.0, 0.0, 1.0, 102.0]);
    same(&outs(inside, "top", None, &cols), &[101.0, 102.0, 102.0, 1.0, 1.0, 1.0, 2.0, 103.0]);
}

#[test]
fn a_reset_at_sample_over_two_comes_before_the_stage_that_a_when_inside_moves_to_its_w() {
    // `slot4` writes s at `sample / 4` of the grid of the part, which the `when~` runs in its W (`sample`), a stage after R; p is read at the frames 0 2 4 6 (`sample / 2`). c = 1 1 0 1 1 0 1 1: the runs at the frames 0 1 3 4 6 7,
    // the grid of the part at the runs 0 and 4 (the frames 0 and 6), where the reset comes first (S-1228) and s = 1 is written from the start; n starts again at each even frame: 101 102, the stopped frame 2 is reset to 0,
    // 1 (the frame 3, n from the reset at 2), 1, held 1 at 5, 101 102.
    let src = "flow top(c: Bool at sample, p: Bool at block) -> F32 at sample { slot4~(1.0).when~(c).reset_if~(p at (sample / 2)) }";
    same(
        &outs(src, "top", Some(true), &[("c", &[1, 1, 0, 1, 1, 0, 1, 1])]),
        &[101.0, 102.0, 0.0, 1.0, 1.0, 1.0, 101.0, 102.0],
    );
}

#[test]
fn a_reset_inside_or_outside_an_up_is_once_a_frame_before_the_first_of_its_runs() {
    // `cnt` gives 1 2 3 ... at its runs, two a frame: g2 = e0 + 10 e1 = 21 43 65 ...; r at the frames 2 and 5 starts the runs of that frame again: 21 43 21 43 65 21, in both orders (a reset before each run would give 11).
    let want = [21.0, 43.0, 21.0, 43.0, 65.0, 21.0];
    let r: [(&str, &[u8]); 1] = [("r", &[0, 0, 1, 0, 0, 1])];
    let inner = "flow top(r: Bool at sample) -> F32 at sample { g2~(cnt~().reset_if~(r).up~(2)) }";
    let outer = "flow top(r: Bool at sample) -> F32 at sample { g2~(cnt~().up~(2).reset_if~(r)) }";
    same(&outs(inner, "top", None, &r), &want);
    same(&outs(outer, "top", None, &r), &want);
    // A `when~` between, c = 1 1 0 0 1 1 and r at the frame 3: the stopped frame 2 reads the last value 4 twice (44), the stopped frame 3 is reset to [0; 2] (S-1222), and the runs start again: 21 43.
    let held =
        "flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample { g2~(cnt~().up~(2).when~(c).reset_if~(r)) }";
    same(
        &outs(held, "top", None, &[("c", &[1, 1, 0, 0, 1, 1]), ("r", &[0, 0, 0, 1, 0, 0])]),
        &[21.0, 43.0, 44.0, 0.0, 21.0, 43.0],
    );
}

#[test]
fn a_head_input_slower_than_w_is_read_by_the_part_at_the_tick_of_its_own_grid() {
    // q = 1 1 2 2 3 3 ... (the frame / 2 + 1); c = 0 1 1 0 0 1 1 1 0 1 1 1: the runs at the frames 1 2 5 6 7 9 10 11, the ticks of `sample / 2` of the part at the runs 0 2 4 6 (the frames 1 5 7 10), which read the caller's
    // last q there (1 3 4 6): h = 2 4 5 7, held between; the frame 0 is `T.default()`.
    let src = "flow top(c: Bool at sample) -> F32 at sample {
  let q = cnt~().down~(2)
  sl~(q).when~(c)
}";
    let c: [(&str, &[u8]); 1] = [("c", &[0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1])];
    same(&outs(src, "top", None, &c), &[0.0, 2.0, 2.0, 2.0, 2.0, 4.0, 4.0, 5.0, 5.0, 5.0, 7.0, 7.0]);
}

#[test]
fn after_a_reset_a_when_inside_reads_the_callers_value_of_a_tick_that_is_not_in_the_part() {
    // q = 1 2 3 4 at the frames 0 2 4 6 (in the caller, not in the part); c from the frame 1: the ticks of `sample / 2` of the part at the frames 1 3 5 7. The reset at the frame 4 puts back the field h and
    // the held output (0) and not q: the frame 5 reads q = 3 (h = 4), the frame 7 q = 4. The interpreter gives the same.
    let src = "flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {
  let q = cnt~().down~(2)
  sl~(q).when~(c).reset_if~(r)
}";
    let cols: [(&str, &[u8]); 2] = [("c", &[0, 1, 1, 1, 1, 1, 1, 1]), ("r", &[0, 0, 0, 0, 1, 0, 0, 0])];
    same(&outs(src, "top", None, &cols), &[0.0, 2.0, 2.0, 3.0, 0.0, 4.0, 4.0, 5.0]);
}
