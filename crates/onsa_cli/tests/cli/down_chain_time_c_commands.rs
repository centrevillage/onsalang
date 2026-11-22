//! The time of a chain of `.down~(N)` past the turn of the words, in the C that `onsa build` writes (W7-16 U6a3/t; spec §11.4, §12.4, §14.2; S-1217, S-1211, S-1127; the decision of S-1217 for where the counter
//! is advanced): the cases of the files `tests/spec/` cannot write `_tick` (an Onsa `test` has no field of the state with a name that starts with `_`), and a `[[test.host]]` step has no step that writes the state, so the
//! case writes a C program of its own. It builds the package, reads the offsets of `_tick` and `_tick_hi` from `onsa interface` (the layout of the state is the layout of §12.4, the same alone and embedded, and
//! the caller of the C API owns the memory of the state, §14.2), calls `<prefix><flow>_init`, writes the two words, calls `process` over a run of frames, and reads the words back.
//!
//! §11.4: the number of the part is the number of the outermost flow divided by the product of the N, rounded down, cut to `U32` last ("割るのは `U32` に切る前の数なので、… その刻みの 2^32 で一周し"). The number
//! of the outermost flow is the two words together, T = `_tick_hi` * 2^32 + `_tick`, one more at each frame; the counter turns the `_tick` over to 0 and carries into `_tick_hi`. The case writes a `_tick` that is a multiple
//! of the product of the N of the path (the child's own counter of the phase is not written, and a `_tick` that is not a multiple would put the ticks of the part off the frames of the program). Every value is T / P
//! worked out in whole numbers by hand (the cases are in the comments), cut to 32 bits.
//!
//! - from T = 2^32 - 4, `.down~(4)`: the part reads 2^30 - 1 for the 4 frames before the turn of `_tick` and 2^30 after it; after the 8 frames `_tick` is 4 and `_tick_hi` is 1.
//! - from T = 2^34 - 4 (`_tick_hi` 3), `.down~(4)`: 2^32 - 1 for 4 frames, then 2^32 cut to `U32` (0); after them `_tick_hi` is 4.
//! - from T = 2^40 - 256, `.down~(256)`: 2^32 - 1 at the first frame, 0 at the frame 256 (T = 2^40, the 2^32 of the quotient).
//! - at T = 2^56 - 2^24, 2^56 and 2^56 + 2^24, `.down~(2^24)` and `.down~(4096).down~(4096)` (the product of the N at its limit, §11.9): 2^32 - 1, 0 (the quotient 2^32 cut to `U32`) and 1; one frame from each.
//! - a flow that only reads the time, from `_tick` 2^32 - 1: 4294967295, 0, 1 (the same as before U6a3: the place where `_tick` is advanced changes, not the values).
//! - after `reset`, `_tick` and `_tick_hi` are 0 and the first frame reads 0 (S-1127).
//!
//! The texts are written from the spec; none is taken from the output of the compiler. The C is compiled by `clang` (the C check of this repository uses it); a machine with none fails the cases.

use std::process::Command;

use crate::slow_stage_commands::state_fields;
use crate::test_support::{Dir, run};

const MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[export]\nprefix = \"dm_\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// The flows of the chains: the part reads the time in its output, `@export` on each (§14.2).
const CHAINS: &str = "\
flow tk() -> U32 at sample {
  sample_tick()
}

@export
pub flow down4() -> U32 at sample {
  tk~().down~(4) at sample
}

@export
pub flow down256() -> U32 at sample {
  tk~().down~(256) at sample
}

@export
pub flow down16m() -> U32 at sample {
  tk~().down~(16777216) at sample
}

@export
pub flow down4k_down4k() -> U32 at sample {
  tk~().down~(4096).down~(4096) at sample
}
";

/// A flow that only reads the time, outermost: it has `_tick` and no upper word.
const ALONE: &str = "@export\npub flow alone() -> U32 at sample {\n  sample_tick()\n}\n";

/// A built package: its directory, the text of `onsa interface`, and the `clang` compile of one driver.
struct Built {
    dir: Dir,
    interface: String,
}

fn build(tag: &str, flows: &str) -> Built {
    let dir = Dir::bare(tag);
    dir.write("onsa.toml", MANIFEST);
    dir.write("main.onsa", flows);
    let out = run(dir.root(), &["build", "--target", "host"]);
    assert_eq!(out.code, 0, "build: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    let out = run(dir.root(), &["interface"]);
    assert_eq!(out.code, 0, "interface: {}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);
    Built { dir, interface: out.stdout }
}

/// A C program for `flow` (compiled once): it takes `_tick`, `_tick_hi`, the number of frames and the frames to print as arguments, and
/// calls `init`, writes the two words into the state, calls `process` over the frames (in calls of at most 4096), prints the values at the wanted frames, the two words after the run and after `reset`,
/// and the first value after the `reset`.
struct Driver {
    exe: String,
}

impl Driver {
    fn new(b: &Built, flow: &str) -> Driver {
        let fields = state_fields(&b.interface, flow);
        let offset = |name: &str| fields.iter().find(|f| f.0 == name).map(|f| f.1);
        let off_tick = offset("_tick").unwrap_or_else(|| panic!("{flow} has `_tick`: {fields:?}"));
        let up = flow.to_uppercase();
        let (write_hi, read_hi) = match offset("_tick_hi") {
            Some(o) => (format!("memcpy(mem + {o}, &hi, 4);"), format!("memcpy(&hi, mem + {o}, 4);")),
            None => (String::new(), String::new()),
        };
        let c = format!(
            r#"#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "dm_{flow}.h"
int main(int argc, char** argv) {{
  static _Alignas(16) unsigned char mem[DM_{up}_SIZE];
  static uint32_t out[4096];
  if (argc < 4) return 9;
  dm_{flow}* s = (dm_{flow}*)mem;
  if (dm_{flow}_init(s, NULL, 8.0f) != 0) return 2;
  uint32_t tick = (uint32_t)strtoul(argv[1], NULL, 10), hi = (uint32_t)strtoul(argv[2], NULL, 10);
  uint32_t frames = (uint32_t)strtoul(argv[3], NULL, 10);
  memcpy(mem + {off_tick}, &tick, 4);
  {write_hi}
  dm_{flow}_params p;
  dm_{flow}_params_default(&p);
  uint32_t done = 0;
  while (done < frames) {{
    uint32_t n = frames - done;
    if (n > 4096) n = 4096;
    if (dm_{flow}_process(s, &p, out, n) != 0) return 3;
    for (int k = 4; k < argc; k++) {{
      uint32_t w = (uint32_t)strtoul(argv[k], NULL, 10);
      if (w >= done && w - done < n) printf("v %u %u\n", w, out[w - done]);
    }}
    done += n;
  }}
  hi = 0;
  memcpy(&tick, mem + {off_tick}, 4);
  {read_hi}
  printf("after %u %u\n", tick, hi);
  dm_{flow}_reset(s);
  hi = 0;
  memcpy(&tick, mem + {off_tick}, 4);
  {read_hi}
  printf("reset %u %u\n", tick, hi);
  if (dm_{flow}_process(s, &p, out, 1) != 0) return 4;
  printf("first %u\n", out[0]);
  return 0;
}}
"#
        );
        let src = b.dir.file(&format!("drv_{flow}.c"), &c);
        let exe = b.dir.path(&format!("drv_{flow}"));
        let host = b.dir.path("target/host");
        let unit = b.dir.path("target/host/onsa_demo.c");
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
        Driver { exe }
    }

    /// One run with `_tick` = `tick` and `_tick_hi` = `hi` written before `frames` frames; the lines printed.
    fn run(&self, tick: u32, hi: u32, frames: u32, want: &[u32]) -> Vec<String> {
        let mut args = vec![tick.to_string(), hi.to_string(), frames.to_string()];
        args.extend(want.iter().map(u32::to_string));
        let ran = Command::new(&self.exe).args(&args).output().expect("run the driver");
        assert_eq!(ran.status.code(), Some(0), "the driver {args:?}: {ran:?}");
        String::from_utf8(ran.stdout).expect("utf-8").lines().map(str::to_string).collect()
    }
}

fn v(frame: u32, value: u32) -> String {
    format!("v {frame} {value}")
}

/// From T = 2^32 - 4 under `.down~(4)`: the quotient is 2^30 - 1 (T = 2^32 - 4) then 2^30 (T = 2^32, where `_tick` has turned to 0 and `_tick_hi` is 1). After 8 frames T = 2^32 + 4: `_tick` 4, `_tick_hi` 1.
#[test]
fn the_time_under_down_4_goes_on_where_the_lower_word_turns_over() {
    let b = build("time_c_turn", CHAINS);
    let got = Driver::new(&b, "down4").run(u32::MAX - 3, 0, 8, &[0, 3, 4, 7]);
    let want = vec![
        v(0, 1073741823),
        v(3, 1073741823),
        v(4, 1073741824),
        v(7, 1073741824),
        "after 4 1".to_string(),
        "reset 0 0".to_string(),
        "first 0".to_string(),
    ];
    assert_eq!(got, want);
}

/// From T = 3 * 2^32 + 2^32 - 4 = 2^34 - 4 under `.down~(4)`: the quotient is 2^32 - 1, then 2^32 at T = 2^34, which is cut to `U32` last and is 0 (the part's own time turns over at its 2^32, §11.4). `_tick_hi` is 4 after.
#[test]
fn the_time_under_down_4_turns_over_at_its_own_2_to_the_32() {
    let b = build("time_c_wrap", CHAINS);
    let got = Driver::new(&b, "down4").run(u32::MAX - 3, 3, 8, &[0, 3, 4, 7]);
    let want = vec![
        v(0, 4294967295),
        v(3, 4294967295),
        v(4, 0),
        v(7, 0),
        "after 4 4".to_string(),
        "reset 0 0".to_string(),
        "first 0".to_string(),
    ];
    assert_eq!(got, want);
}

/// From T = 2^40 - 256 under `.down~(256)` (`_tick_hi` 255, `_tick` 2^32 - 256): 2^32 - 1 at the first frame, and at the frame 256 (T = 2^40) the quotient is 2^32, which is 0; after 257 frames `_tick` is 1 and `_tick_hi` 256.
#[test]
fn the_time_under_down_256_turns_over_at_t_2_to_the_40() {
    let b = build("time_c_256", CHAINS);
    let got = Driver::new(&b, "down256").run(0u32.wrapping_sub(256), 255, 257, &[0, 255, 256]);
    let want = vec![
        v(0, 4294967295),
        v(255, 4294967295),
        v(256, 0),
        "after 1 256".to_string(),
        "reset 0 0".to_string(),
        "first 0".to_string(),
    ];
    assert_eq!(got, want);
}

/// The product of the N at its limit, 2^24 (§11.9), whether it is one `.down~(16777216)` or two `.down~(4096)`: the part reads (T / 2^24) cut to `U32`, where T = `_tick_hi` * 2^32 + `_tick` is 2^56 - 2^24 (the
/// quotient 2^32 - 1: `_tick_hi` 2^24 - 1, `_tick` 2^32 - 2^24), 2^56 (the quotient 2^32, which is 0: `_tick_hi` 2^24, `_tick` 0) and 2^56 + 2^24 (the quotient 2^32 + 1, which is 1: `_tick` 2^24). One frame is run
/// from each, so the cases do not go through 2^24 frames; after the frame `_tick` is one more.
#[test]
fn the_time_under_a_product_of_2_to_the_24_turns_over_at_t_2_to_the_56() {
    let b = build("time_c_56", CHAINS);
    let n = 1u32 << 24;
    for flow in ["down16m", "down4k_down4k"] {
        let d = Driver::new(&b, flow);
        for (tick, hi, value) in [(0u32.wrapping_sub(n), n - 1, 4294967295), (0, n, 0), (n, n, 1)] {
            let want =
                vec![v(0, value), format!("after {} {hi}", tick + 1), "reset 0 0".to_string(), "first 0".to_string()];
            assert_eq!(d.run(tick, hi, 1, &[0]), want, "{flow} from _tick {tick}, _tick_hi {hi}");
        }
    }
}

/// A flow that only reads the time, outermost, from `_tick` = 2^32 - 1: 4294967295, 0, 1 (the number is a `U32` that turns over, §11.4), `_tick` is 2 after, 0 after `reset`, and the first frame after reads 0. It has no
/// `_tick_hi`: the same as before U6a3, only the place that advances `_tick` is the `process` and not the `tick` (the decision of S-1217).
#[test]
fn a_flow_that_only_reads_the_time_turns_over_and_starts_again_after_reset() {
    let b = build("time_c_alone", ALONE);
    assert!(!b.interface.contains("_tick_hi"), "no `.down~`, no upper word: {}", b.interface);
    let got = Driver::new(&b, "alone").run(u32::MAX, 0, 3, &[0, 1, 2]);
    let want = vec![
        v(0, 4294967295),
        v(1, 0),
        v(2, 1),
        "after 2 0".to_string(),
        "reset 0 0".to_string(),
        "first 0".to_string(),
    ];
    assert_eq!(got, want);
}
