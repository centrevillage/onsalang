//! The field of the upper word of the time (`_tick_hi`) in `onsa interface` (W7-16 U6a3/t; spec §12.4, §11.4, §11.6; S-1211, S-1217, S-1179 (2)): which flows have it and where it is.
//!
//! §12.4: the fields that are not of a `let` are, in order, `_bulk`, `_sample_rate`, the phase counter (`_tick`, where it is put) "と、続けて時間の上の桁の欄（本体からの経路に `.down~` が一つでもあり、その先で
//! `sample_tick()` を読む flow が持つ。経路は子の flow の中を通して数え、`.up~` と打ち消す形も数える。その flow が一番外のときだけ使う、§11.4）". So the flow that has a `.down~` before a read of
//! `sample_tick()` (the part under the chain reads it, or a child of the part does, or the flow runs a flow that has such a chain) has `_tick_hi`, a `U32` right after `_tick` with no padding; a flow that reads
//! `sample_tick()` with no `.down~` before the read, a chain over a part that reads no time (also when the argument reads it: it is read in the caller, before the chain) and the part under the chain itself have none.
//! Where the phase counter is put is the choice of the implementation (§11.9), so the cases name `_tick_hi` and, when it is there, the field before it (`_tick`).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::state_fields;
use crate::test_support::{Dir, run};

/// The part that reads the time, a part that reads none, an argument that reads it, a child with no modifier that reads it, and the head that gathers and reads it.
const PARTS: &str = "\
flow tk() -> U32 at sample {
  sample_tick()
}

flow mid() -> U32 at sample {
  tk~()
}

flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}

flow pass(g: U32 at sample) -> U32 at sample {
  g
}

flow gboth(x: U32 at (sample * 4)) -> U32 at sample {
  x[0] * 10000 + x[3] * 100 + sample_tick()
}

";

/// The flows that have no `.down~` before a read of `sample_tick()`: they have no `_tick_hi` (S-1211, §12.4).
const WITHOUT: &str = "\
pub flow reads_only() -> U32 at sample {
  tk~()
}

pub flow reads_in_a_child() -> U32 at sample {
  mid~()
}

pub flow chain_over_no_time(p: F32 at block, x: F32 at sample) -> F32 at sample {
  x * (acc~(p).down~(4) at sample)
}

pub flow chain_over_no_time_with_time_in_the_argument() -> U32 at sample {
  pass~(sample_tick()).down~(4) at sample
}

pub flow no_time(x: F32 at sample) -> F32 at sample {
  x * 0.5
}
";

/// The flows that have a `.down~` before a read: over the part, over a child of the part, over a head that gathers, in a flow that runs such a flow, with `sample_rate()` before the counter.
const WITH: &str = "\
pub flow over_reader() -> U32 at sample {
  tk~().down~(2) at sample
}

pub flow over_child_reader() -> U32 at sample {
  mid~().down~(2) at sample
}

pub flow over_two_downs() -> U32 at sample {
  tk~().down~(4).down~(2) at sample
}

pub flow over_gather() -> U32 at sample {
  gboth~(sample_tick()).down~(4) at sample
}

pub flow runs_a_chain() -> U32 at sample {
  over_reader~()
}

pub flow with_the_rate(x: F32 at sample) -> F32 at sample {
  x * sample_rate() * F32.round_from(tk~().down~(2) at sample)
}
";

fn interface(tag: &str, src: &str) -> String {
    let d = Dir::pkg(tag);
    d.write("m.onsa", src);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    out.stdout
}

fn names_of(fields: &[(String, u64, String)]) -> Vec<&str> {
    fields.iter().map(|f| f.0.as_str()).collect()
}

/// A flow with no `.down~` before a read of `sample_tick()` has no `_tick_hi`: reading the time alone, in a child, a chain over a part that reads none, and one whose argument reads the time (the argument is
/// read in the caller, before the chain, so no `.down~` is before the read). These are lowered today, so the case holds before and after U6a3.
#[test]
fn a_flow_with_no_down_before_a_read_of_sample_tick_has_no_upper_word_of_the_time() {
    let text = interface("tick_hi_without", &format!("{PARTS}{WITHOUT}"));
    for flow in [
        "reads_only",
        "reads_in_a_child",
        "chain_over_no_time",
        "chain_over_no_time_with_time_in_the_argument",
        "no_time",
    ] {
        let fields = state_fields(&text, flow);
        assert!(!names_of(&fields).contains(&"_tick_hi"), "{flow} has no `_tick_hi`: {fields:?}");
    }
}

/// A flow with a `.down~` before a read has `_tick_hi`, a `U32` (4 bytes, align 4) right after `_tick` with no padding, before the fields of the `let`s and of the children (§12.4, S-1211): the chain over the part
/// that reads the time, over a child of the part, two downs, a head that gathers and reads, and a flow that runs a flow that has such a chain (the path is counted through the child).
#[test]
fn a_flow_with_a_down_before_a_read_of_sample_tick_has_the_upper_word_right_after_the_counter() {
    let text = interface("tick_hi_with", &format!("{PARTS}{WITH}"));
    for flow in ["over_reader", "over_child_reader", "over_two_downs", "over_gather", "runs_a_chain", "with_the_rate"] {
        let fields = state_fields(&text, flow);
        let names = names_of(&fields);
        let at =
            names.iter().position(|n| *n == "_tick_hi").unwrap_or_else(|| panic!("{flow} has `_tick_hi`: {names:?}"));
        assert!(at >= 1 && names[at - 1] == "_tick", "{flow}: `_tick_hi` follows `_tick` directly: {names:?}");
        assert_eq!(fields[at].1, fields[at - 1].1 + 4, "{flow}: no padding between the two words: {fields:?}");
        assert!(
            fields[at].2.contains("4 bytes, align 4"),
            "{flow}: a U32 (the interface shows its size): {}",
            fields[at].2
        );
        assert!(
            names[..at].iter().all(|n| ["_bulk", "_sample_rate", "_tick"].contains(n)),
            "{flow}: only `_bulk`, `_sample_rate` and `_tick` are before it, the fields of the `let`s and the children after: {names:?}"
        );
        assert_eq!(names[names.len() - 2..], ["_poisoned", "_initialized"], "{flow}: {names:?}");
    }
    let rate = state_fields(&text, "with_the_rate");
    assert_eq!(names_of(&rate)[..3], ["_sample_rate", "_tick", "_tick_hi"], "the order of §12.4: {rate:?}");
    assert_eq!((rate[0].1, rate[1].1, rate[2].1), (0, 4, 8), "{rate:?}");
}

/// §12.4: "`.up~` と打ち消す形も数える": a `.down~` that is cancelled by an `.up~` (`.down~(2).up~(2)`, `.up~(2).down~(2)`) is a `.down~` on the path, so the flow has `_tick_hi`. The `.up~` is lowered in U6b3, so
/// until then the commands stop at E0200 and `onsa interface` has no field list.
#[test]
fn a_down_cancelled_by_an_up_still_has_the_upper_word() {
    let src = format!(
        "{PARTS}pub flow down_up() -> U32 at sample {{\n  tk~().down~(2).up~(2) at sample\n}}\n\npub flow up_down() -> U32 at sample {{\n  tk~().up~(2).down~(2) at sample\n}}\n"
    );
    let text = interface("tick_hi_up", &src);
    for flow in ["down_up", "up_down"] {
        let names: Vec<String> = state_fields(&text, flow).into_iter().map(|f| f.0).collect();
        let at =
            names.iter().position(|n| n == "_tick_hi").unwrap_or_else(|| panic!("{flow} has `_tick_hi`: {names:?}"));
        assert_eq!(names[at - 1], "_tick", "{flow}: {names:?}");
    }
}
