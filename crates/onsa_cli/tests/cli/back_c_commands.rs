//! A call in the first argument of a delay, and a part with a `^` in it, in the C that `onsa build` writes (W7-11 U2b/t2; spec §11.3, §11.4, §11.2, §13.4, §14.2; S-1233, S-1241, S-1244): the exported flow is run through the C program of
//! `down_two_boundaries_c_commands.rs` (`init`, `process` in the pieces it is given, a piece of 0 frames too, and `reset` after the frames of another run with `x = 101`), each flow in one build and one compile of the driver. The run has
//! `x = c + 1` at the frame c = 0 .. 11; the values are worked out by hand from §11.4 ("遅延の `e` の中の遅延は、保存の前の出力を読む": `prev~(e)` gives `e` of the frame before, `T.default()` at the frame 0) and §11.3 (a call in the first
//! argument is done where it is written; the values do not depend on the order), `gg(x) = x + prev~(x)` (gives 2 c + 1 at the frame c):
//! - `a = prev~(gg~(x))`: `2 c - 1` at c >= 1 (0 at c = 0), a call outside a `par~`.
//! - `e = prev~(pair~(x))` (`pair` gives the array `[x, 2 x]`, a Copy value that is not a number): `e[0] + e[1]` is `3 c` at c >= 1.
//! - `ys = par~ i in 0 ..< 2 { prev~(gg~(x * (i + 1))) }`: the copy i gives `(i + 1) (2 c - 1)`; the sum is `3 (2 c - 1)`, a call in a `par~`.
//! - `m = prev~(match~ v { Some(b) => gg~(x) + b, None => 0.0 })` (`v` is `Some(x)` where `x > 3`): the call of the arm is done at every frame (`~`), so the arm at the frame c is `2 c + 1 + c + 1` for c >= 3 and 0 before, and `m` is
//!   the arm of the frame before: `3 c - 1` for c >= 4 (11 at c = 4), 0 before it.
//! - `d = prev~(dws4~(x))` (`dws4` gathers the 4 frames before its tick, at `sample / 4`, 0 at its first tick: 0 10 26 ... at the frames 0 4 8; the delay of the grid gives the one before): `d` is 0 0 10 at the grids, 10 at the frames 8 .. 11.
//!   The output is `a + e[0] + e[1] + 100 (ys[0] + ys[1]) + 10000 m + 1000000 d`, the terms in the digits apart (`a + e[0] + e[1]` is at most 54, `ys` at most 63, `m` at most 32).
//! - a part with a `^` in the first argument (`prev~((^k4 * 2.0) at sample)`, `k4` below, a value of the grid of `sample / 4`; S-1244 (1): the value of `^k4` is that of the same frame): the grid has `k4 = c / 4 + 2` (`cnt` counts
//!   the runs, 1 2 3, and `k4` adds 1), so the delay gives `2 k4` of the frame before (0 at the frame 0), and the output adds `x`.

use crate::down_two_boundaries_c_commands::{build_flows, driver, frames_of};

const CALLS: &str = "\
flow gg(x: F32 at sample) -> F32 at sample {
  x + prev~(x)
}

flow pair(x: F32 at sample) -> [F32; 2] at sample {
  [x, x * 2.0]
}

flow sum4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] + x[2] + x[3]
}

flow dws4(x: F32 at sample) -> F32 at (sample / 4) {
  sum4~(x).down~(4)
}

@export
pub flow calls_in_a_delay(x: F32 at sample) -> F32 at sample {
  let v: Option[F32] = if x > 3.0 { Some(x) } else { None }
  let a = prev~(gg~(x))
  let e = prev~(pair~(x))
  let ys = par~ i in 0 ..< 2 { prev~(gg~(x * F32.round_from(i + 1))) }
  let m = prev~(match~ v { Some(b) => gg~(x) + b, None => 0.0 })
  let d = prev~(dws4~(x))
  a + e[0] + e[1] + (ys[0] + ys[1]) * 100.0 + m * 10000.0 + (d at sample) * 1000000.0
}
";

const LATE: &str = "\
flow cnt() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}

@export
pub flow late_in_a_delay(x: F32 at sample) -> F32 at sample {
  let d4 = cnt~().down~(4)
  let y = prev~((^k4 * 2.0) at sample)
  let k4 = d4 + 1.0
  y + x
}
";

/// The frames of one run of 12 frames of `flow` (it has the input `x`), in one call, in the pieces `1 1 5 7` and after a `reset` that follows 0, 1, 3, 5, 6 or 7 frames of another run, are `want`.
fn same_in_c(tag: &str, src: &str, flow: &str, want: &[i64]) {
    let dir = build_flows(tag, src);
    let exe = driver(&dir, flow, true);
    for junk in [0, 1, 3, 5, 6, 7] {
        for cuts in [&[][..], &[1, 1, 5, 7][..]] {
            assert_eq!(
                frames_of(&exe, junk, 12, cuts),
                want,
                "{flow} after {junk} frames of another run, cut at {cuts:?}"
            );
        }
    }
}

/// The call of a flow in the first argument of a delay: outside a `par~`, in a `par~`, in an arm of a `match~`, of a flow that gives an array, and of a flow that gives `sample / 4`.
#[test]
fn a_call_in_the_first_argument_of_a_delay_gives_the_values_worked_out_in_c() {
    let want = [0, 304, 909, 1514, 112119, 142724, 173329, 203934, 10234539, 10265144, 10295749, 10326354];
    same_in_c("back_c_calls", CALLS, "calls_in_a_delay", &want);
}

/// A part with a `^` that waits for the stage of its delay (S-1244 (1)): the values of a `let` below it, which the Core of `d439fac` stops at (R-520).
#[test]
fn a_caret_read_in_a_part_of_the_first_argument_of_a_delay_gives_the_values_worked_out_in_c() {
    let want = [1, 6, 7, 8, 9, 12, 13, 14, 15, 18, 19, 20];
    same_in_c("back_c_late", LATE, "late_in_a_delay", &want);
}
