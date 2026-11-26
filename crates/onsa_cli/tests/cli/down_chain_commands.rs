//! A chain of `.down~(N)` that gathers and deals nothing, over a part that reads no `sample_tick()`, in the commands of `onsa` (W7-16 U6a1/t; spec §11.9, §12.4, §11.6, §9.2; S-1079, S-1088, S-1179 (2),
//! S-1206, S-1159, S-1233, S-1207, Q-09): what the case `tests/spec/flow_semantics/down_chain_values.onsa` cannot pin.
//!
//! - `onsa interface` of the parent of such a chain has the state of the child and the counter of the phase (`_tick`) after `_sample_rate` and before the fields of the `let`s (§12.4, S-1179 (2)). That the
//!   parent has the field is the choice of the implementation (§11.9 "誰が欄を持つかは実装の選択"); where it is, is the spec's. A parent of a part that reads no `sample_tick()` has no `_tick_hi` (§12.4: the field of the upper word of the time is only of a flow with a `.down~` before a read of `sample_tick()`, S-1211, S-1217; the flows that have it are in `down_chain_time_commands.rs`).
//! - Which of two panics at one position is reported (`onsa test`, the `failure` of the test): the slower tick first (§11.9, S-1079), and at one stage the order of the text: the work of the part under the chain
//!   is where the call is written, so a `let` above the call is before it and a `let` below it after (§11.3, S-1206, S-1159, S-1233; the order of the whole stage is in `stage_order_commands.rs`).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::{bytes_of, line_of, state_fields, state_size, stop_line};
use crate::test_support::{Dir, run};

/// §12.4 and S-1179 (2): the parent of a chain of downs has the phase counter after `_sample_rate` (when the parent reads `sample_rate()`) and before the fields of the `let`s, and the field of the child is the
/// state of the child (`acc.State`, which has the same layout alone and embedded, §12.4); the node of a `let` of a tick is `<let>.<kind>_<number>` and the node in the output expression is `_out.<kind>_<number>` (§11.6).
/// The parent that does not read `sample_rate()` has the counter first. No stage of a down chain makes the size unknown.
#[test]
fn the_interface_of_a_parent_of_a_down_chain_has_the_counter_after_sample_rate_and_the_state_of_the_child() {
    let src = "pub flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}

pub flow first(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let c = acc~(p).down~(4)
  x * (c at sample) * sample_rate()
}

pub flow second(p: F32 at block, x: F32 at sample) -> F32 at sample {
  x * (acc~(p).down~(2).down~(2) at sample)
}
";
    let d = Dir::pkg("down_chain_interface");
    d.write("m.onsa", src);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);

    let field = |fs: &[(String, u64, String)], name: &str| {
        fs.iter().find(|f| f.0 == name).unwrap_or_else(|| panic!("a field `{name}` in {fs:?}")).clone()
    };
    let f = state_fields(&out.stdout, "first");
    let names: Vec<&str> = f.iter().map(|x| x.0.as_str()).collect();
    assert_eq!(&names[..2], ["_sample_rate", "_tick"], "the counter is after `_sample_rate`: {names:?}");
    assert_eq!((f[0].1, f[1].1), (0, 4), "the counter is next to `_sample_rate`: {f:?}");
    assert!(f[1].2.contains("4 bytes, align 4"), "{}", f[1].2);
    assert_eq!(names[names.len() - 2..], ["_poisoned", "_initialized"], "{names:?}");
    let child = field(&f, "c.acc_0");
    assert_eq!(
        bytes_of(&child.2),
        state_size(&out.stdout, "acc"),
        "the field of the child is the state of `acc`: {}",
        child.2
    );
    let at = |n: &str| names.iter().position(|x| *x == n).unwrap_or_else(|| panic!("a field `{n}` in {names:?}"));
    assert!(at("_tick") < at("c.acc_0"), "the counter is before the child: {names:?}");

    let g = state_fields(&out.stdout, "second");
    let names: Vec<&str> = g.iter().map(|x| x.0.as_str()).collect();
    assert_eq!(
        (names[0], g[0].1),
        ("_tick", 0),
        "a parent that does not read `sample_rate()` has the counter first: {names:?}"
    );
    let child = field(&g, "_out.acc_0");
    assert_eq!(bytes_of(&child.2), state_size(&out.stdout, "acc"), "the field of the child: {}", child.2);
}

/// The source `flows` and the test `stops` that renders `f` (a `block` input `p` of 0) over `frames` frames.
fn stops(flows: &str, frames: u32) -> String {
    format!(
        "{flows}\ntest \"stops\" {{\n  let o = f.render(f.Params {{ p: 0 }}, {frames}, 8.0)\n  assert o.out[0] == 0\n}}\n"
    )
}

/// The part: `d` is the `p` of the run before (1 at the first), so the second run divides by the 0 of `p`.
const KID: &str =
    "flow kid(p: I32 at block) -> I32 at sample {\n  let d = prev~(p at sample, 1)\n  let q = 100 / d\n  q\n}\n\n";

/// A part under `.down~(4)` that stops alone stops at its own division, at its second tick, the frame 4.
#[test]
fn the_panic_of_a_part_under_a_down_chain_is_reported_at_its_own_division() {
    let flows = format!("{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  kid~(p).down~(4) at sample\n}}\n");
    let src = stops(&flows, 5);
    assert_eq!(stop_line("down_chain_panic_alone", &src), line_of(&src, "100 / d"), "{src}");
}

/// §11.9 (S-1079, "比の違う遅い刻みどうしは遅い方（N の大きい方）から並び"): at the frame 8 the part under `.down~(8)` (the stage `sample / 8` of the parent) and a stage of the parent at `sample / 2` (a delay of
/// 4 ticks, the 0 of the first) both divide by 0; the slower tick is the part's, so its division (`100 / d`) is reported, not the parent's (`200 / b`, written first).
#[test]
fn of_a_stage_of_the_parent_and_a_part_under_a_down_chain_at_one_position_the_slower_is_reported() {
    let flows = format!(
        "{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  let b = delay~(p at (sample / 2), 4, 1)\n  let qb = 200 / b\n  (qb at sample) + (kid~(p).down~(8) at sample)\n}}\n"
    );
    let src = stops(&flows, 9);
    assert_eq!(stop_line("down_chain_panic_slower", &src), line_of(&src, "100 / d"), "the stage of sample / 8: {src}");
}

/// S-1233 (S-1206, S-1159; §11.3 "インスタンスの呼び出し … がその段に持つ仕事 | 出力をその段で読むかによらず、呼び出しを書いた位置（式の評価の順の中の位置）"): at one stage (the part under `.down~(4)` runs at the stage
/// `sample / 4` of the parent) the part runs where the call is written: after the `let`s above it (the call is in the output, `… at sample`) and before the ones below it (`let k = kid~(p).down~(4)` over the
/// `let`s). Both divide by the 0 at the frame 4; the one reported is the first of them in the order of the text.
#[test]
fn at_one_stage_the_part_under_a_down_chain_runs_where_the_call_is_written_s1233() {
    let let_first = format!(
        "{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  let e = prev~(p at (sample / 4), 1)\n  let r = 200 / e\n  (r at sample) + (kid~(p).down~(4) at sample)\n}}\n"
    );
    let child_first = format!(
        "{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  let k = kid~(p).down~(4)\n  let e = prev~(p at (sample / 4), 1)\n  let r = 200 / e\n  (r at sample) + (k at sample)\n}}\n"
    );
    for (tag, flows, first) in [
        ("down_chain_panic_let_first", &let_first, "200 / e"),
        ("down_chain_panic_child_first", &child_first, "100 / d"),
    ] {
        let src = stops(flows, 5);
        assert_eq!(stop_line(tag, &src), line_of(&src, first), "the first in the order of S-1233: {src}");
    }
}

/// S-1233 (S-1206, S-1159; W7-16 U6b3): the runs of a chain with an `.up~(N)` give the output of the call at the `sample` stage of the caller, so they run where the call is written, in the order of the text: a `let`
/// written before the call runs before the up (its division is reported), a `let` written after it runs after (the division of the part under the up is reported). Both divide by a value of `sample` (a `prev~`, so not at
/// `block`, §11.3) that is 0 at the frame 1: the caller by `p` of the frame before, the part by `p` of two of its frames before, at its frame 2, the run j = 0 of the frame 1.
#[test]
fn at_one_stage_the_runs_of_an_up_chain_run_where_the_call_is_written_s1233() {
    let part = "flow kidu(p: I32 at block) -> I32 at sample {\n  let d = prev~(prev~(p at sample, 1), 1)\n  100 / d\n}\n\nflow two(x: I32 at (sample * 2)) -> I32 at sample {\n  x[0] + x[1]\n}\n\n";
    let let_first = format!(
        "{part}pub flow f(p: I32 at block) -> I32 at sample {{\n  let e = prev~(p at sample, 1)\n  let r = 200 / e\n  r + two~(kidu~(p).up~(2))\n}}\n"
    );
    let up_first = format!(
        "{part}pub flow f(p: I32 at block) -> I32 at sample {{\n  let k = two~(kidu~(p).up~(2))\n  let e = prev~(p at sample, 1)\n  let r = 200 / e\n  r + k\n}}\n"
    );
    for (tag, flows, first) in
        [("up_chain_panic_let_first", &let_first, "200 / e"), ("up_chain_panic_up_first", &up_first, "100 / d")]
    {
        let src = stops(flows, 2);
        assert_eq!(stop_line(tag, &src), line_of(&src, first), "the first in the order of S-1233: {src}");
    }
}
