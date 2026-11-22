//! A chain with an `.up~(N)` in it, in the C that `onsa build` writes (W7-16 U6b3/t; spec §11.9, §11.4, §14.2, §13.4; S-1207, S-1214, S-1217, S-1186): the values of
//! `tests/spec/flow_semantics/up_chain_values.onsa`, run in the C of the exported flows (`@export`, `kind = "source"`) through the C program of `down_two_boundaries_c_commands.rs` (`init`, `process` in the pieces it is
//! given, a piece of 0 frames too (§13.4), and `reset`; it prints the frames). Worked out by hand, as in the case file (`x = c + 1` at the frame c, the run has `p = 10`, the junk before a `reset` has `x = 101` and `p = 5`):
//! - `thru~(x).up~(2).down~(2)` (a block of 2: 2 samples late): 0 0 1 2 3 ... 14.
//! - `step2~(p).down~(2).up~(4).down~(4)` (`step2` gives [n p, n p + 1] at its n-th run): 10 11 20 21 | 30 31 40 41 | 50 51 60 61 | 70 71 80 81, the window that the up widens kept (the case file).
//! - `g4~(step2~(p).down~(2).up~(4))` (the bundle of the up, 4 elements of 2 runs read by the caller): 11110 n + 12010 with n = 2 b + 1 in the frame b: 23120 45340 67560 89780 112000 134220 156440 178660.
//! - `p + F32.round_from(tk)` in `.up~(2).down~(4) at sample`, the time 2 v + j of the part of the down 4 held: p + 0 0 1 1 2 2 ... (10 10 11 11 12 12 ...).
//!
//! The package is built with the manifest of `down_two_boundaries_c_commands.rs` (prefix `dm_`).

use crate::down_two_boundaries_c_commands::{build_flows, driver, frames_of};

const FLOWS: &str = "\
flow thru(x: F32 at sample) -> F32 at sample {
  x
}

flow step2(p: F32 at block) -> F32 at (sample * 2) {
  let n = prev~(^n) + 1.0
  [n * p, n * p + 1.0]
}

flow g4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0
}

flow tkp(p: F32 at block) -> F32 at sample {
  p + F32.round_from(sample_tick())
}

@export
pub flow delay_up(x: F32 at sample) -> F32 at sample {
  thru~(x).up~(2).down~(2)
}

@export
pub flow widen(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  step2~(p).down~(2).up~(4).down~(4)
}

@export
pub flow bundle(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  g4~(step2~(p).down~(2).up~(4))
}

@export
pub flow time_up(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  tkp~(p).up~(2).down~(4) at sample
}
";

/// Each flow is run in one call, in the pieces `1 1 5 7` (a piece of 0 frames) and after a `reset` that follows 0, 1, 3, 5, 6 or 7 frames of another run: the same values (§13.4, S-1186: the next frame is the frame 0).
#[test]
fn the_values_of_the_chains_with_an_up_are_the_same_in_c() {
    let dir = build_flows("up_chain_c_values", FLOWS);
    let delay: Vec<i64> = [0, 0].into_iter().chain(1..=14).collect();
    let widen: Vec<i64> = vec![10, 11, 20, 21, 30, 31, 40, 41, 50, 51, 60, 61, 70, 71, 80, 81];
    let bundle: Vec<i64> = vec![23120, 45340, 67560, 89780, 112000, 134220, 156440, 178660];
    let time: Vec<i64> = vec![10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15];
    for (flow, has_input, frames, want) in [
        ("delay_up", true, 16, &delay),
        ("widen", false, 16, &widen),
        ("bundle", false, 8, &bundle),
        ("time_up", false, 12, &time),
    ] {
        let exe = driver(&dir, flow, has_input);
        for junk in [0, 1, 3, 5, 6, 7] {
            for cuts in [&[][..], &[1, 1, 5, 7][..]] {
                assert_eq!(
                    &frames_of(&exe, junk, frames, cuts),
                    want,
                    "{flow} after {junk} frames of another run, cut at {cuts:?}"
                );
            }
        }
    }
}
