//! A call that takes or gives a bundle at the caller (a port or an output at `sample * N` with no chain, and a `.down~(N)` that deals or gathers one), in the C that `onsa build` writes (W7-16 U6b2/t; spec §11.9, §14.2,
//! §13.4; S-1204, S-1214 (3), S-1207, S-1186): the forms of `tests/spec/flow_semantics/bursts_values.onsa`, run in the C of the exported flows through the C program of `down_two_boundaries_c_commands.rs` (`init`,
//! `process` in the pieces it is given, a piece of 0 frames too, and `reset` after the frames of another run with `x = 101` and `p = 5`). The run has `x = 1, 2, 3 ...` (`x = c + 1`) and `p = 10`; the values are worked
//! out by hand from §11.9 as in the case file:
//! - `g2~(pair~(x))` (the pair `2 x - 1`, `2 x` goes by with no delay, `g2` takes `x[0] + 10 x[1]`): `22 x - 1` = 21, 43, 65, 87 ...
//! - `g2~(p) + g2~(1.0)` (a `block` value and a constant are 2 equal elements): `11 p + 11` = 121.
//! - `g4~(mk8~(p).down~(2))` (the 8 elements `p .. p + 7` of the head at the even frames go 4 to each of the 2 frames): `1111 p + 3210` = 14320 and `1111 p + 7654` = 18764 in turn; the head reads `p` at its tick.
//! - `g2~(mk8~(p).down~(2).down~(2))` (2 elements to each of the 4 frames of the run): `11 p + 22 j + 10` = 120, 142, 164, 186.
//! - `g8~(pair4i~(x)).down~(2) at sample` (the 4 elements `x .. x + 3` of each of the frames c - 2 and c - 1 are gathered at the even frame c, 0 before the first frame; the weights `2^i`): 0 at c = 0 and `255 c + 563` (1073,
//!   1583, 2093 ...), each held 2 frames.
//! - the two together with a state, `g2~(ramp2~(1.0)) + g4~(mk8~(p).down~(2))`: the n-th frame of `ramp2` has `n, n + 0.5` (`11 n + 5` = 16, 27, 38 ...) and so 14336, 18791, 14358, 18813 ... A `reset` puts the counter of
//!   `ramp2` and the dealt array back, and the next frame is a tick.

use crate::down_two_boundaries_c_commands::{build_flows, driver, frames_of};

const FLOWS: &str = "\
flow g2(x: F32 at (sample * 2)) -> F32 at sample {
  x[0] + x[1] * 10.0
}

flow g4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0
}

flow g8(x: F32 at (sample * 8)) -> F32 at sample {
  x[0] + x[1] * 2.0 + x[2] * 4.0 + x[3] * 8.0 + x[4] * 16.0 + x[5] * 32.0 + x[6] * 64.0 + x[7] * 128.0
}

flow pair(x: F32 at sample) -> F32 at (sample * 2) {
  [x * 2.0 - 1.0, x * 2.0]
}

flow pair4i(x: F32 at sample) -> F32 at (sample * 4) {
  [x, x + 1.0, x + 2.0, x + 3.0]
}

flow mk8(p: F32 at block) -> F32 at (sample * 8) {
  [p, p + 1.0, p + 2.0, p + 3.0, p + 4.0, p + 5.0, p + 6.0, p + 7.0]
}

flow ramp2(f: F32 at block) -> F32 at (sample * 2) {
  let n = f + prev~(^n)
  [n, n + 0.5]
}

@export
pub flow burst_direct(x: F32 at sample) -> F32 at sample {
  g2~(pair~(x))
}

@export
pub flow burst_block(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  g2~(p) + g2~(1.0)
}

@export
pub flow deal_into_g4(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  g4~(mk8~(p).down~(2))
}

@export
pub flow deal_into_g2(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  g2~(mk8~(p).down~(2).down~(2))
}

@export
pub flow gather_a_burst(x: F32 at sample) -> F32 at sample {
  g8~(pair4i~(x)).down~(2) at sample
}

@export
pub flow combo(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  let a = g2~(ramp2~(1.0))
  let d = g4~(mk8~(p).down~(2))
  a + d
}
";

/// Each flow: the frames of one run of `frames` frames (at least 7, the last cut) (`has_input`: it has the input `x`), in one call, in the pieces `1 1 5 7` and after a `reset` that follows 0, 1, 3, 5, 6 or 7 frames of another run, are `want`.
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

/// A bundle that goes by with no chain, and a `block` value and a constant given to a port at `sample * 2`: the values worked out in the header.
#[test]
fn the_values_of_a_bundle_that_goes_by_are_the_same_in_c() {
    same_in_c(
        "bursts_c_by",
        &[("burst_direct", true, 8, vec![21, 43, 65, 87, 109, 131, 153, 175]), ("burst_block", false, 8, vec![121; 8])],
    );
}

/// A bundle that one or two `.down~(2)` deal to the frames of the caller, and a bundle that a `.down~(2)` gathers: the values worked out in the header.
#[test]
fn the_values_of_a_chain_that_gives_or_takes_a_bundle_are_the_same_in_c() {
    let four = [14320, 18764].repeat(6);
    let two = [120, 142, 164, 186].repeat(3);
    let gather = vec![0, 0, 1073, 1073, 1583, 1583, 2093, 2093, 2603, 2603, 3113, 3113, 3623, 3623, 4133, 4133];
    same_in_c(
        "bursts_c_chain",
        &[("deal_into_g4", false, 12, four), ("deal_into_g2", false, 12, two), ("gather_a_burst", true, 16, gather)],
    );
}

/// A bundle with a state next to a dealt one: the state of `ramp2` and the dealt array are put back by `reset` (the run after it is the one of a state just made, S-1186) and a cut of the run at any frame changes nothing.
#[test]
fn the_state_of_a_bundle_and_a_dealt_array_are_put_back_by_a_reset_in_c() {
    let want = vec![14336, 18791, 14358, 18813, 14380, 18835, 14402, 18857, 14424, 18879, 14446, 18901];
    same_in_c("bursts_c_state", &[("combo", false, 12, want)]);
}
