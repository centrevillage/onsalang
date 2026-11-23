//! `.reset_if~(r)` in the C that `onsa build` writes (W7-10 U2b/t; spec §11.10, §11.9, §13.4, §14.2; S-559, S-1186, S-1209): the values of `tests/spec/flow_semantics/reset_if_values.onsa` for the condition read at the call (W = P), run in the C
//! of the exported flows through the C program of `down_two_boundaries_c_commands.rs` (`init`, `process` in the pieces it is given, a piece of 0 frames too, and `reset` after the frames of another run with `x = 101`). The run has `x = 1, 2, 3 ...`;
//! every value is worked out by hand from §11.10 as in the case files. The head `slot(f)` gives at its frame j (0, 1, 2 ...) 100 s + n, s = f (j / 2 + 1) (the field written by its stage of `sample / 2`, read by its stage of `sample`) and n = j + 1:
//! - `slot~(1.0).reset_if~(x == 4.0)` (the frame 3): the reset puts n, the child and the field s back, not the counter: the frame 3 gives 1, the grid at the frame 4 gives s = 1, n = 2: 101 102 203 1 102 103 204 205 306 307.
//! - `slot~(1.0).reset_if~(x == 5.0)` (the frame 4, a grid): the grid writes first and the reset takes it back: 101 102 203 204 1 2 103 104 205 206.
//! - `slot~(1.0).when~(c).reset_if~(r)` and `slot~(1.0).reset_if~(r).when~(c)` with c = x != 3, 5, 6 (the frames 2, 4, 5 stop) and r = x == 3, 4, 6 (the frames 2, 3, 5): the first resets the stopped frames and the held output too:
//!   101 102 0 1 1 0 1 102 103 204; the second only the frames that run: 101 102 102 1 1 1 2 103 104 205.

use crate::down_two_boundaries_c_commands::{build_flows, driver, frames_of};

const FLOWS: &str = "\
flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}

flow slot(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(2)
  let n = prev~(^n) + 1.0
  (s at sample) * 100.0 + n
}

@export
pub flow reset_at_a_frame(x: F32 at sample) -> F32 at sample {
  slot~(1.0).reset_if~(x == 4.0)
}

@export
pub flow reset_at_a_grid(x: F32 at sample) -> F32 at sample {
  slot~(1.0).reset_if~(x == 5.0)
}

@export
pub flow when_then_reset(x: F32 at sample) -> F32 at sample {
  slot~(1.0).when~(x != 3.0 && x != 5.0 && x != 6.0).reset_if~(x == 3.0 || x == 4.0 || x == 6.0)
}

@export
pub flow reset_then_when(x: F32 at sample) -> F32 at sample {
  slot~(1.0).reset_if~(x == 3.0 || x == 4.0 || x == 6.0).when~(x != 3.0 && x != 5.0 && x != 6.0)
}
";

/// Each flow: the 10 frames of one run, in one call, in the pieces `1 1 5 7` and after a `reset` that follows 0, 1, 3, 5, 6 or 7 frames of another run, are `want`.
fn same_in_c(tag: &str, flows: &[(&str, Vec<i64>)]) {
    let dir = build_flows(tag, FLOWS);
    for (flow, want) in flows {
        let exe = driver(&dir, flow, true);
        for junk in [0, 1, 3, 5, 6, 7] {
            for cuts in [&[][..], &[1, 1, 5, 7][..]] {
                assert_eq!(
                    &frames_of(&exe, junk, 10, cuts),
                    want,
                    "{flow} after {junk} frames of another run, cut at {cuts:?}"
                );
            }
        }
    }
}

/// W = P: the frame that resets gives its own first value, the field that a slower stage wrote is T.default() until the next grid, and the counter of the grid is not put back (§11.10).
#[test]
fn a_reset_if_read_at_the_call_gives_the_values_of_the_case_files_in_c() {
    same_in_c(
        "reset_if_c_p",
        &[
            ("reset_at_a_frame", vec![101, 102, 203, 1, 102, 103, 204, 205, 306, 307]),
            ("reset_at_a_grid", vec![101, 102, 203, 204, 1, 2, 103, 104, 205, 206]),
        ],
    );
}

/// The order of a `when~` and a `reset_if~`: the one outside also resets the stopped frames and the held output (the frames 2 and 5 read 0 after the reset), the one inside only the frames that run.
#[test]
fn a_reset_if_and_a_when_in_both_orders_give_the_values_of_the_case_files_in_c() {
    same_in_c(
        "reset_if_c_order",
        &[
            ("when_then_reset", vec![101, 102, 0, 1, 1, 0, 1, 102, 103, 204]),
            ("reset_then_when", vec![101, 102, 102, 1, 1, 1, 2, 103, 104, 205]),
        ],
    );
}
