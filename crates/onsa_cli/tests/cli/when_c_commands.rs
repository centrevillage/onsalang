//! `.when~(c)` in the C that `onsa build` writes (W7-10 U1/t; spec §11.10, §11.9, §13.4, §14.2; S-1209, S-1217): the values of `tests/spec/flow_semantics/when_values.onsa` and `when_slow_values.onsa` for the condition read at the call
//! (W = P) and at a slower clock (W = `sample / 4`, in both orders with `.down~(4)`), run in the C of the exported flows through the C program of `down_two_boundaries_c_commands.rs` (`init`, `process` in the pieces it is given,
//! a piece of 0 frames too, and `reset` after the frames of another run with `x = 101` and `p = 5`). The run has `x = 1, 2, 3 ...` and `p = 10`; every value is worked out by hand from §11.10 as in the case files. The head `slot(f)`
//! gives at its run j (0, 1, 2 ...) 100 s + n, s = f (j / 2 + 1) (the field written by its stage of `sample / 2`, read by its stage of `sample`) and n = j + 1:
//! - `slot~(1.0).when~(c)` with c false at x = 3, 4, 7: the runs at the frames 0 1 4 5 7 8 9 give 101 102 203 204 305 306 407 and the stopped frames keep the last one: 101 102 102 102 203 204 204 305 306 407.
//! - `slot~(p).down~(4).when~(k > 2.0)` and `slot~(p).when~(k > 2.0).down~(4)` (`k` = the grid + 1, p = 10): the first two grids read 0 (never ran); the runs 0 .. 3 at the grids 2 .. 5 give 1001 1002 2003 2004, each held 4 frames.
//!   A `reset` after any frames of the run before it (p = 5) leaves no last output and no count: the next frame is the frame 0.

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
pub flow when_p(x: F32 at sample) -> F32 at sample {
  slot~(1.0).when~(x != 3.0 && x != 4.0 && x != 7.0)
}

@export
pub flow down_then_when(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  let k = acc~(1.0).down~(4)
  slot~(p).down~(4).when~(k > 2.0) at sample
}

@export
pub flow when_then_down(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  let k = acc~(1.0).down~(4)
  slot~(p).when~(k > 2.0).down~(4) at sample
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

/// W = P: the condition is read at each frame, the part runs on the frames where it holds and its grid of `sample / 2` counts the runs (the frames 2, 3 and 6 are stopped, §11.10).
#[test]
fn a_when_read_at_the_call_gives_the_values_of_the_case_files_in_c() {
    same_in_c("when_c_p", &[("when_p", true, 10, vec![101, 102, 102, 102, 203, 204, 204, 305, 306, 407])]);
}

/// W = `sample / 4`: the grid is read at the position of the chain, so `.down~(4).when~(c)` and `.when~(c).down~(4)` run the part at the same grids (the grids 2 .. 5), whose runs are 1001 1002 2003 2004.
#[test]
fn a_when_read_at_a_slower_clock_gives_the_same_values_in_both_orders_in_c() {
    let mut want = vec![0; 8];
    for (value, frames) in [(1001, 4), (1002, 4), (2003, 4), (2004, 4)] {
        want.extend(vec![value; frames]);
    }
    same_in_c("when_c_slow", &[("down_then_when", false, 24, want.clone()), ("when_then_down", false, 24, want)]);
}
