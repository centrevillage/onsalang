//! A chain of `.down~(N)` that gathers or deals past its first boundary, in the C that `onsa build` writes (W7-16 U6b1/t; spec §11.9, §14.2, §13.4; S-1207, S-1214 (1), S-1186): the values of
//! `tests/spec/flow_semantics/down_two_boundaries_values.onsa`, run in the C of the exported flows (`@export`, `kind = "source"`), through a C program of its own that calls `init`, `process` in the pieces it is given
//! (a piece of 0 frames too, §13.4: the host cuts the frames anywhere) and `reset`, and prints the frames. The package is built with the manifest of `down_chain_time_c_commands.rs`. The C is compiled by `clang`.
//!
//! The values are worked out by hand, as in the case file (the part runs at the frames that are multiples of 4; `x = c + 1`, 0 before the first frame):
//! - `g4~(x).down~(2).down~(2) at sample` (a port at `sample * 4`): the frames c - 6 .. c - 3 are gathered, 0 0 0 0 | 2100 x 4 | 6543 x 4 | 10987 x 4 (c = 4: 0 0 1 2 = 100 + 2000; c = 8: 3 4 5 6; c = 12: 7 8 9 10).
//! - `rev4~(x).down~(2).down~(2)` (the same elements dealt backwards from the tick): 0 0 0 0 | 2 1 0 0 | 6 5 4 3 | 10 9 8 7.
//! - `mk4~(p).down~(2).down~(2)` (p = 10): 10 11 12 13 at each tick; `mk2~(p).down~(2).down~(2) at sample`: 10 10 11 11 at each tick.
//!
//! A `reset` after any number of frames of other values (x = 101, p = 5) gives the run of a state just made (the first tick has the defaults in its ring, §11.9; the next frame is the frame 0, S-1186), and the pieces
//! `1 1 5 7` give the same as one call.

use std::process::Command;

use crate::test_support::{Dir, run};

const MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[export]\nprefix = \"dm_\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

const FLOWS: &str = "\
flow g4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0
}

flow rev4(x: F32 at (sample * 4)) -> F32 at (sample * 4) {
  [x[3], x[2], x[1], x[0]]
}

flow mk4(p: F32 at block) -> F32 at (sample * 4) {
  [p, p + 1.0, p + 2.0, p + 3.0]
}

flow mk2(p: F32 at block) -> F32 at (sample * 2) {
  [p, p + 1.0]
}

@export
pub flow gather22(x: F32 at sample) -> F32 at sample {
  g4~(x).down~(2).down~(2) at sample
}

@export
pub flow reverse22(x: F32 at sample) -> F32 at sample {
  rev4~(x).down~(2).down~(2)
}

@export
pub flow deal22(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  mk4~(p).down~(2).down~(2)
}

@export
pub flow deal2_22(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  mk2~(p).down~(2).down~(2) at sample
}
";

/// The package built for the host (a build that ends with 0 and no internal error).
fn build(tag: &str) -> Dir {
    let dir = Dir::bare(tag);
    dir.write("onsa.toml", MANIFEST);
    dir.write("main.onsa", FLOWS);
    let out = run(dir.root(), &["build", "--target", "host"]);
    assert_eq!(out.code, 0, "build: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    dir
}

/// A C program for `flow` (compiled once). Its arguments are the number of frames of the other run (`junk`) before the `reset`, the number of frames of the run, and the places where the run is cut into calls of `process`
/// (a place twice is a call of 0 frames). The frames of the junk have `x = 101` and `p = 5`, the run `x = 1, 2, 3 ...` (`x = c + 1`) and `p = 10`; it prints the frames of the run on one line, each as an integer.
fn driver(dir: &Dir, flow: &str, has_input: bool) -> String {
    let up = flow.to_uppercase();
    let (xs, set_junk, set_run) = if has_input {
        (
            "xs + a, ",
            "for (uint32_t i = 0; i < junk; i++) xs[i] = 101.0f;",
            "for (uint32_t i = 0; i < frames; i++) xs[i] = (float)(i + 1);",
        )
    } else {
        ("", "prm.p = 5.0f;", "prm.p = 10.0f;")
    };
    let c = format!(
        r#"#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "dm_{flow}.h"
int main(int argc, char** argv) {{
  static _Alignas(16) unsigned char mem[DM_{up}_SIZE];
  static float xs[256], out[256];
  if (argc < 3) return 9;
  dm_{flow}* s = (dm_{flow}*)mem;
  if (dm_{flow}_init(s, NULL, 8.0f) != 0) return 2;
  dm_{flow}_params prm;
  dm_{flow}_params_default(&prm);
  uint32_t junk = (uint32_t)strtoul(argv[1], NULL, 10), frames = (uint32_t)strtoul(argv[2], NULL, 10);
  {set_junk}
  {{
    uint32_t a = 0, b = junk;
    if (dm_{flow}_process(s, &prm, {xs}out, b - a) != 0) return 3;
  }}
  dm_{flow}_reset(s);
  {set_run}
  uint32_t a = 0;
  for (int k = 3; k <= argc; k++) {{
    uint32_t b = k < argc ? (uint32_t)strtoul(argv[k], NULL, 10) : frames;
    if (dm_{flow}_process(s, &prm, {xs}out + a, b - a) != 0) return 4;
    a = b;
  }}
  for (uint32_t i = 0; i < frames; i++) printf("%.0f ", out[i]);
  printf("\n");
  return 0;
}}
"#
    );
    let src = dir.file(&format!("drv_{flow}.c"), &c);
    let exe = dir.path(&format!("drv_{flow}"));
    let host = dir.path("target/host");
    let unit = dir.path("target/host/onsa_demo.c");
    let cc = Command::new("clang")
        .args(["-std=c11", "-O1", "-I", &host, &src, &unit, "-o", &exe])
        .output()
        .unwrap_or_else(|e| panic!("the C compiler `clang` is needed: {e}"));
    assert!(
        cc.status.success(),
        "clang: {}{}\n{c}",
        String::from_utf8_lossy(&cc.stdout),
        String::from_utf8_lossy(&cc.stderr)
    );
    exe
}

/// The frames the driver printed for `junk` frames of another run, then a run of `frames` frames cut at `cuts`.
fn frames_of(exe: &str, junk: u32, frames: u32, cuts: &[u32]) -> Vec<i64> {
    let mut args = vec![junk.to_string(), frames.to_string()];
    args.extend(cuts.iter().map(u32::to_string));
    let ran = Command::new(exe).args(&args).output().expect("run the driver");
    assert_eq!(ran.status.code(), Some(0), "the driver {args:?}: {ran:?}");
    String::from_utf8(ran.stdout)
        .expect("utf-8")
        .split_whitespace()
        .map(|w| w.parse::<i64>().unwrap_or_else(|_| panic!("an integer, not `{w}`")))
        .collect()
}

/// A gather and a gather-and-deal at two boundaries: the values worked out in the header, in one call, in the pieces `1 1 5 7` (a piece of 0 frames) and after a `reset` that follows 1, 3, 5, 6 or 7 frames of another run.
#[test]
fn the_values_of_a_chain_that_gathers_at_two_boundaries_are_the_same_in_c() {
    let dir = build("two_boundaries_c_gather");
    let gather: Vec<i64> = vec![0, 0, 0, 0, 2100, 2100, 2100, 2100, 6543, 6543, 6543, 6543, 10987, 10987, 10987, 10987];
    let reverse: Vec<i64> = vec![0, 0, 0, 0, 2, 1, 0, 0, 6, 5, 4, 3, 10, 9, 8, 7];
    for (flow, want) in [("gather22", &gather), ("reverse22", &reverse)] {
        let exe = driver(&dir, flow, true);
        for junk in [0, 1, 3, 5, 6, 7] {
            for cuts in [&[][..], &[1, 1, 5, 7][..]] {
                assert_eq!(
                    &frames_of(&exe, junk, 16, cuts),
                    want,
                    "{flow} after {junk} frames of another run, cut at {cuts:?}"
                );
            }
        }
    }
}

/// A deal at two boundaries: `mk4~(p).down~(2).down~(2)` gives p p+1 p+2 p+3 at each tick (10 11 12 13), `mk2~(p).down~(2).down~(2) at sample` each of its two elements for 2 frames (10 10 11 11); in one call, in pieces, and after
/// a `reset` in the middle of a run of 5 (p = 5): the next frame is a tick again (S-1186).
#[test]
fn the_values_of_a_chain_that_deals_at_two_boundaries_are_the_same_in_c() {
    let dir = build("two_boundaries_c_deal");
    let four: Vec<i64> = vec![10, 11, 12, 13, 10, 11, 12, 13, 10, 11, 12, 13];
    let two: Vec<i64> = vec![10, 10, 11, 11, 10, 10, 11, 11, 10, 10, 11, 11];
    for (flow, want) in [("deal22", &four), ("deal2_22", &two)] {
        let exe = driver(&dir, flow, false);
        for junk in [0, 1, 3, 5, 6, 7] {
            for cuts in [&[][..], &[1, 1, 5, 7][..]] {
                assert_eq!(
                    &frames_of(&exe, junk, 12, cuts),
                    want,
                    "{flow} after {junk} frames of another run, cut at {cuts:?}"
                );
            }
        }
    }
}
