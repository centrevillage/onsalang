//! The tests of the order of a `.reset_if~(r)` outside a `.when~(c)` and the slower ticks inside that the `when~` runs in its W (W7-10 (P); §11.10, §11.9, S-1228): the reset is at the stage of the caller of its
//! tick, before all the work of the part at that stage or later, so a slower tick inside runs after it from the start where it runs at a tick of the reset (it is not written first). The same with an `.up~`, a `.down~`
//! that deals between, and a named flow whose body has the `when~` (the same values as the chain written out). The values are worked out by hand from the spec, in the comment of each test; `slot(f)` writes `s` at
//! `sample / 2` of its grid and counts its frames in `n`: 100 s + n (`reset_tests::HEADS`).

use super::reset_tests::outs;
use super::state_tests::same;

const MORE: &str = "flow slot8(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(8)
  let n = prev~(^n) + 1.0
  (s at sample) * 100.0 + n
}
flow mk4() -> F32 at (sample * 4) {
  let n = cnt~() * 10.0
  [n, n + 1.0, n + 2.0, n + 3.0]
}
flow g2k(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] * 1000.0 }
flow pk4(x: Bool at (sample * 4)) -> Bool at sample { x[3] }
flow h4(c: Bool at sample) -> Bool at (sample / 4) { pk4~(c).down~(4) }
flow ws(c: Bool at sample) -> F32 at sample { slot~(1.0).when~(c) }
";

#[test]
fn a_reset_at_w_outside_a_when_comes_before_the_slower_tick_inside_and_a_named_flow_gives_the_same() {
    // c = 1 1 1 0 1 1 1 1: the runs 0 .. 6 at the frames 0 1 2 4 5 6 7, the grid of `slot` at the runs 0 2 4 6 (the frames 0 2 5 7). r at the frame 5, a grid: the part is put back first and the grid writes
    // from the start (s = 1, n = 1): 101 102 203, held 203, 204, 101 102 203 (written first and put back after, it would be 1 2 103).
    let cols: [(&str, &[u8]); 2] = [("c", &[1, 1, 1, 0, 1, 1, 1, 1]), ("r", &[0, 0, 0, 0, 0, 1, 0, 0])];
    let want = [101.0, 102.0, 203.0, 203.0, 204.0, 101.0, 102.0, 203.0];
    let chain = "flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample { slot~(1.0).when~(c).reset_if~(r) }";
    let named =
        format!("{MORE}flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ ws~(c).reset_if~(r) }}");
    same(&outs(chain, "top", None, &cols), &want);
    same(&outs(&named, "top", None, &cols), &want);
    // r at the frame 4 (the run 3, no grid): the same as with no `when~` there: n = 1, s = 0 until the grid at the frame 5: 1 102 103 204.
    let cols: [(&str, &[u8]); 2] = [("c", &[1, 1, 1, 0, 1, 1, 1, 1]), ("r", &[0, 0, 0, 0, 1, 0, 0, 0])];
    let want = [101.0, 102.0, 203.0, 203.0, 1.0, 102.0, 103.0, 204.0];
    same(&outs(chain, "top", None, &cols), &want);
    same(&outs(&named, "top", None, &cols), &want);
}

#[test]
fn a_reset_slower_than_w_comes_before_a_tick_inside_slower_than_it() {
    // `h4~(r)` is r(p - 1) at p, a multiple of 4: the reset at the frame 8 (`sample / 4`). `slot8` writes s at `sample / 8` of its grid (the frames 0 and 8, c true), which the `when~` runs in its W (`sample`), a stage
    // after R: the part is put back before it, and the frames 8 .. 15 are those of 0 .. 7: 101 .. 108 twice (written first, the frame 8 would be 1).
    let src = format!(
        "{MORE}flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample {{ slot8~(1.0).when~(c).reset_if~(h4~(r)) }}"
    );
    let mut r = [0; 16];
    r[7] = 1;
    let want: Vec<f32> = (0..16).map(|i| 101.0 + (i % 8) as f32).collect();
    same(&outs(&src, "top", None, &[("c", &[1; 16]), ("r", &r)]), &want);
}

#[test]
fn a_reset_outside_an_up_comes_before_the_slower_tick_of_its_first_run() {
    // The reset at `sample / 2` (p true: the even frames), once a frame before the first of the 2 runs; `slot8` is on the grid of the runs (all of them, p true): the run 8 (the frame 4, its run 0) writes s. The
    // frame 0: 101 102; 1: 103 104 (no reset); 2: put back, the runs 4 5: 1 2; 3: 3 4; the frame 4 is put back before the run 8 writes s = 1: 101 102, and so on: 102101 104103 2001 4003 twice.
    let src = format!(
        "{MORE}flow top(x: Bool at sample, p: Bool at block) -> F32 at sample {{ g2k~(slot8~(1.0).when~(p).up~(2).reset_if~(p at (sample / 2))) }}"
    );
    let want = [102101.0, 104103.0, 2001.0, 4003.0, 102101.0, 104103.0, 2001.0, 4003.0];
    same(&outs(&src, "top", Some(true), &[("x", &[0; 8])]), &want);
}

#[test]
fn a_reset_outside_a_when_of_a_boundary_that_deals_puts_the_array_back_before_its_tick_makes_one() {
    // `mk4` makes [10 n, 10 n + 1, ...] at the ticks of the `.down~(4)` (the runs 0 4 8 ... of the `when~`, p true: the frames 0 2 4 ... of the caller, the run 0 of each), which the `when~` runs in its W. The reset
    // (p, once a frame of the caller before the first run) puts the part back before it: n = 1 at each tick, 10 11 dealt to the 2 runs: 120; at the odd frames the array is put back and not made again: 0.
    let src = format!(
        "{MORE}flow top(x: Bool at sample, p: Bool at block) -> F32 at sample {{ g2~(mk4~().down~(4).when~(p).reset_if~(p).up~(2)) }}"
    );
    same(&outs(&src, "top", Some(true), &[("x", &[0; 6])]), &[120.0, 0.0, 120.0, 0.0, 120.0, 0.0]);
}

#[test]
fn a_reset_inside_a_when_still_comes_after_the_slower_tick() {
    // The `reset_if~` inside: the slower tick of `slot` is not moved for it, so it writes first and is put back after (§11.10): c true, r at the frame 4 (a grid): 101 102 203 204, then n = 1, s = 0: 1 2, and the
    // grid 6 writes s = 1: 103 104.
    let src = "flow top(c: Bool at sample, r: Bool at sample) -> F32 at sample { slot~(1.0).reset_if~(r).when~(c) }";
    let cols: [(&str, &[u8]); 2] = [("c", &[1; 8]), ("r", &[0, 0, 0, 0, 1, 0, 0, 0])];
    same(&outs(src, "top", None, &cols), &[101.0, 102.0, 203.0, 204.0, 1.0, 2.0, 103.0, 104.0]);
}
