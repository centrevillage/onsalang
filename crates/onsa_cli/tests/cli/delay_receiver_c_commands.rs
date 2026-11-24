//! `.when~(c)` and `.reset_if~(r)` on a built-in delay in the C that `onsa build` writes (W7-10 U3b/t; spec §11.10, §11.9, §11.4, §13.4, §14.2; S-1209, S-1228): the values of `tests/spec/flow_semantics/delay_receiver_values.onsa`, run in the C of the
//! exported flows through the C program of `down_two_boundaries_c_commands.rs` (`init`, `process` in the pieces it is given, a piece of 0 frames too, and `reset` after the frames of another run with `x = 101` and `p = 5`). The run has
//! `x = 1, 2, 3 ...` (and `p = 10`); every value is worked out by hand from §11.10 as in the case files (the delay runs at the frames where the condition holds, a stopped frame keeps the last output, `T.default()` 0 before the first run, and a
//! delay counts the frames it ran). With `c = x != 3 && x != 5 && x != 6` (the frames 2, 4 and 5 are stopped) and `r = x == 3 || x == 4 || x == 6` (the frames 2, 3 and 5):
//! - `prev~(x).when~(c)`: the runs are the frames 0 1 3 6 7 8 9 and give 0 1 2 4 7 8 9 (each reads what the run before stored), the stopped frames keep the last one: 0 1 1 2 2 2 4 7 8 9.
//! - `delay~(x, 2).reset_if~(x == 5.0)` (the frame 4): the ring and the write position are put back before the frame, which gives its own input: 0 0 1 2 | 0 0 5 6 7 8.
//! - `prev~(x).when~(c).reset_if~(r)`: the reset outside the `when~` also resets the stopped frames and the held output (the frames 2 and 5 read 0) and the stored value: 0 1 0 0 0 0 0 7 8 9; `prev~(x).reset_if~(r).when~(c)`: only the frames that run
//!   (the frame 3 resets the stored 2 first): 0 1 1 0 0 0 4 7 8 9.
//! - `prev~(l).when~(l != 30.0)` with `l = acc~(p).down~(4)` (10 20 30 40 50 60 at the grids of 4 frames): the delay ticks at the grid, the grid 2 is stopped; the grids 0 1 3 4 5 give 0 10 20 40 50 and the grid 2 keeps 10, each held 4 frames.
//! - `prev~(x).reset_if~(k == 2.0)` with `k = acc~(1.0).down~(4)` (the grid 1, the frame 4): the reset is before the stage of the delay at that frame: 0 1 2 3 | 0 5 6 7 8 9.

use crate::down_two_boundaries_c_commands::{build_flows, driver, frames_of};

const FLOWS: &str = "\
flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}

@export
pub flow when_prev(x: F32 at sample) -> F32 at sample {
  prev~(x).when~(x != 3.0 && x != 5.0 && x != 6.0)
}

@export
pub flow reset_delay(x: F32 at sample) -> F32 at sample {
  delay~(x, 2).reset_if~(x == 5.0)
}

@export
pub flow when_then_reset(x: F32 at sample) -> F32 at sample {
  prev~(x).when~(x != 3.0 && x != 5.0 && x != 6.0).reset_if~(x == 3.0 || x == 4.0 || x == 6.0)
}

@export
pub flow reset_then_when(x: F32 at sample) -> F32 at sample {
  prev~(x).reset_if~(x == 3.0 || x == 4.0 || x == 6.0).when~(x != 3.0 && x != 5.0 && x != 6.0)
}

@export
pub flow reset_slower_than_the_delay(x: F32 at sample) -> F32 at sample {
  let k = acc~(1.0).down~(4)
  prev~(x).reset_if~(k == 2.0)
}

@export
pub flow slow_when(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  let l = acc~(p).down~(4)
  prev~(l).when~(l != 30.0) at sample
}
";

/// Each flow: the frames of one run of `frames` frames (`has_input`: it has the input `x`), in one call, in the pieces `1 1 5 7` and after a `reset` that follows 0, 1, 3, 5, 6 or 7 frames of another run, are `want`.
fn same_in_c(tag: &str, flows: &[(&str, bool, u32, Vec<i64>)]) {
    let dir = build_flows(tag, FLOWS);
    for (flow, has_input, frames, want) in flows {
        let exe = driver(&dir, flow, *has_input);
        for junk in [0, 1, 3, 5, 6, 7] {
            for cuts in [&[][..], &[1, 1, 5, 7][..]] {
                assert_eq!(
                    &frames_of(&exe, junk, *frames, cuts),
                    want,
                    "{flow} after {junk} frames of another run, cut at {cuts:?}"
                );
            }
        }
    }
}

/// W = P = K: the condition is read at each frame, the delay runs on the frames where it holds and counts them (the frames 2, 4 and 5 are stopped, §11.10), and the reset puts the ring back before the frame.
#[test]
fn a_when_and_a_reset_if_on_a_delay_give_the_values_of_the_case_files_in_c() {
    same_in_c(
        "delay_receiver_c_p",
        &[
            ("when_prev", true, 10, vec![0, 1, 1, 2, 2, 2, 4, 7, 8, 9]),
            ("reset_delay", true, 10, vec![0, 0, 1, 2, 0, 0, 5, 6, 7, 8]),
        ],
    );
}

/// The order of a `when~` and a `reset_if~` on a delay: the one outside also resets the stopped frames and the held output, the one inside only the frames that run.
#[test]
fn a_when_and_a_reset_if_on_a_delay_in_both_orders_give_the_values_of_the_case_files_in_c() {
    same_in_c(
        "delay_receiver_c_order",
        &[
            ("when_then_reset", true, 10, vec![0, 1, 0, 0, 0, 0, 0, 7, 8, 9]),
            ("reset_then_when", true, 10, vec![0, 1, 1, 0, 0, 0, 4, 7, 8, 9]),
        ],
    );
}

/// A delay of a value of `sample / 4`: it ticks at the grid and is stopped there (the grid 2: l = 30), and a reset whose condition ticks at the grid is before the stage of the delay at that frame (§11.9, §11.10).
#[test]
fn a_delay_at_a_slower_clock_and_a_slower_reset_if_give_the_values_of_the_case_files_in_c() {
    let mut want = vec![];
    for (value, frames) in [(0, 4), (10, 4), (10, 4), (20, 4), (40, 4), (50, 4)] {
        want.extend(vec![value; frames]);
    }
    same_in_c(
        "delay_receiver_c_slow",
        &[
            ("slow_when", false, 24, want),
            ("reset_slower_than_the_delay", true, 10, vec![0, 1, 2, 3, 0, 5, 6, 7, 8, 9]),
        ],
    );
}
