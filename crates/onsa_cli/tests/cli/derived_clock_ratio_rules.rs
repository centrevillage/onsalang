//! The ratio rules of the derived clock `e at (sample / N)` in the flow check, and the gates round them (W7-09 U2r1/t; spec §11.3,
//! §11.4, §11.9, §18.1; S-1078, S-1077, S-565, S-1158): what the case files cannot pin. The files of the cases are
//! `flow_clock/derived_clock_ratio_rules.onsa`, `derived_clock_ratio_n_errors.onsa`, `derived_clock_ratio_bases.onsa`,
//! `derived_clock_times_in_an_expression.onsa`, `e0815_ratio_clash.onsa` and `derived_clock_non_rt_calls.onsa`.
//!
//! - The note of E0813 for a delay of a value of the parameter kinds shows `prev~(p at (sample / N))` (§11.4).
//! - A computed part of a tick read at a faster stage has a field of its own (S-1158 (c), W7-09 U2r2): `check` reads it (the last test, which U2r2's
//!   cases pair with `flow_clock/tick_fields_computed_parts.onsa`).
//!
//! A flow with a delay or a part of a tick `sample / N` and no modifier or child is lowered by `build`, `dump --core` and `test` since W7-16 U5a: its
//! tests are in `slow_stage_commands.rs` (what stays E0200 is there too). The texts are written from the spec; none is taken from the output of the
//! compiler. The checks run in this process (`check_input_out`).

use crate::test_support::sweep::check_input_out;
use crate::test_support::{code_of, diagnostics, doc_of, fixes_of, notes_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

fn diags(text: &str) -> Vec<Value> {
    let out = check_input_out(&PackageInput::single_file("a.onsa", text));
    assert!(out.code == 0 || out.code == 1, "onsa check ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

fn notes_text(d: &Value) -> String {
    notes_of(d).iter().map(|n| str_of(n, "message")).collect::<Vec<_>>().join("\n")
}

// ----------------------------------------------------------------------------- the note of E0813

/// §11.4: the first argument of a delay that is a value of the parameter kinds is E0813, with the candidate `at sample` and a note
/// that writes the derived clock `at (sample / N)` (a state is counted in ticks, and `block` has none). The delays and the form of
/// the argument do not change the note.
#[test]
fn the_e0813_of_a_delay_of_a_block_value_notes_the_derived_clock() {
    let calls = ["prev~(p)", "delay~(p, 2)", "vdelay~(p, x, 4)", "prev~(p * 2.0)", "prev~(q)"];
    for call in calls {
        let text = format!(
            "pub flow f(p: F32 at block, q: F32 at init, x: F32 at sample) -> F32 at sample {{\n  {call} + x\n}}\n"
        );
        let ds = diags(&text);
        assert_eq!(ds.len(), 1, "{call}: one error in the unit (§18.1), got {ds:?}");
        assert_eq!(code_of(&ds[0]), "E0813", "{call}: {}", ds[0]);
        assert_eq!(fixes_of(&ds[0]).len(), 1, "{call}: the candidate `at sample` stays: {}", ds[0]);
        let notes = notes_text(&ds[0]);
        assert!(notes.contains("at (sample / N)"), "{call}: a note writes `at (sample / N)`: {}", ds[0]);
    }
}

// ----------------------------------------------------------------------------- the computed part of a tick (U2r2)

fn flow_body(body: &str) -> String {
    format!(
        "pub flow f(p: F32 at block, q: F32 at block, x: F32 at sample) -> F32 at sample {{\n  let a = prev~(p at (sample / 4))\n  let c = prev~(q at (sample / 4))\n{body}\n}}\n"
    )
}

/// The bodies that read a computed part of a tick at a faster stage, with no condition that is decided elsewhere (S-1158 (c), §11.3: "段が刻みの計算した部分式は、
/// より速い式の中でもその刻みで評価し、値を隠れたフィールドに置く"), and the reads that make no part (a name, a part read at its own tick, a part at a ratio between).
const READS: [&str; 7] = [
    "  let b = (a * 2.0) at sample\n  x * b + (c at sample)",
    "  let b = (a + c) at sample\n  x * b",
    "  let b = (a + a) at sample\n  x * b + (c at sample)",
    "  (a at sample) * x + (c at sample)",
    "  let s = a * 2.0\n  let t = s + a\n  x * (t at sample) + (c at sample)",
    "  let b = a at (sample / 2)\n  x * (b at sample) + (c at sample)",
    "  x * (prev~(a * 0.5) at sample) + (c at sample)",
];

/// S-1158 (c): `check` reads each of the bodies with no diagnostic (the one error is for a position a condition selects, which the cases have).
#[test]
fn a_computed_part_of_a_tick_read_at_a_faster_stage_is_read_by_check() {
    for body in READS {
        let ds = diags(&flow_body(body));
        assert!(ds.is_empty(), "{body}: read as the spec has it, got {ds:?}");
    }
}
