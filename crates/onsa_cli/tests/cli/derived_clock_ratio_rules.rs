//! The ratio rules of the derived clock `e at (sample / N)` in the flow check, and the gates round them (W7-09 U2r1/t; spec §11.3,
//! §11.4, §11.9, §18.1; S-1078, S-1077, S-565, S-1158): what the case files cannot pin. The files of the cases are
//! `flow_clock/derived_clock_ratio_rules.onsa`, `derived_clock_ratio_n_errors.onsa`, `derived_clock_ratio_bases.onsa`,
//! `derived_clock_times_in_an_expression.onsa`, `e0815_ratio_clash.onsa` and `derived_clock_non_rt_calls.onsa`.
//!
//! - The note of E0813 for a delay of a value of the parameter kinds shows `prev~(p at (sample / N))` (§11.4).
//! - The flow that the clock checks accept is E0200 for `build`, `dump --core` and `test` (the Core of a derived clock is W7-16),
//!   and `check` reads it with no diagnostic.
//! - A computed part of a tick read at a faster stage waits for the field (S-1158, U2r2): it is E0200 until then, and the reads that
//!   need no field (a name, a part read at its own tick) are not. This test goes with the gate at U2r2.
//!
//! The texts are written from the spec; none is taken from the output of the compiler. The checks run in this process
//! (`check_input_out`); only the commands of the Core gate need a package on the disk.

use crate::test_support::sweep::check_input_out;
use crate::test_support::{Dir, code_of, diagnostics, doc_of, fixes_of, notes_of, run, span_of, str_of, test_json};
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

// ----------------------------------------------------------------------------- the gate of the Core

const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// A flow with a delay that ticks at `sample / 4` and is read at `sample` by its name: a form the clock checks accept.
const TICKING: &str = "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let lf = prev~(p at (sample / 4))\n  x * (lf at sample)\n}\n\ntest \"reads\" {\n  assert 1 + 1 == 2\n}\n";

fn error_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.contains("error[")).collect()
}

/// W7-09 (the Core of the ticks is W7-16): `check` reads the flow, and `build`, `dump --core` and `test` stop at it with E0200 and
/// nothing else, on the file of the flow (Q-09: what is in the spec and not in this version is E0200, not a wrong output).
#[test]
fn a_flow_with_a_derived_clock_is_e0200_for_build_dump_core_and_test() {
    let d = Dir::bare("ratio_core_gate");
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("main.onsa", TICKING);

    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 0, "check reads the flow: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{}", out.stdout);

    let dir = d.arg();
    let commands: [(&str, Vec<&str>); 3] = [
        ("build", vec!["build", "--target", "host"]),
        ("dump --core", vec!["dump", "--core", dir.as_str()]),
        ("test", vec!["test"]),
    ];
    for (name, args) in commands {
        let out = run(d.root(), &args);
        assert_eq!(out.code, 1, "{name}: {}{}", out.stdout, out.stderr);
        let both = format!("{}{}", out.stdout, out.stderr);
        let lines = error_lines(&both);
        assert!(!lines.is_empty(), "{name}: an error line: {both}");
        for l in &lines {
            assert!(l.contains("error[E0200]"), "{name}: only E0200: {l}");
            assert!(l.contains("main.onsa:"), "{name}: E0200 is on the file of the flow: {l}");
        }
        assert!(!both.contains("internal error"), "{name}: {both}");
    }

    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let ds = diagnostics(&doc);
    assert!(!ds.is_empty() && ds.iter().all(|x| code_of(x) == "E0200"), "{doc}");
    assert!(ds.iter().all(|x| span_of(&x["span"]).file == "main.onsa"), "{doc}");
    assert!(crate::test_support::tests_of(&doc).is_empty(), "nothing is run: {doc}");
}

// ----------------------------------------------------------------------------- the gate of the computed part (U2r2 removes it)

fn flow_body(body: &str) -> String {
    format!(
        "pub flow f(p: F32 at block, q: F32 at block, x: F32 at sample) -> F32 at sample {{\n  let a = prev~(p at (sample / 4))\n  let c = prev~(q at (sample / 4))\n{body}\n}}\n"
    )
}

/// S-1158 (c), §11.3 ("刻みのクロックの計算した部分式は、より速い式の中でもその刻みで評価し、値を隠れたフィールドに置く"): a computed
/// part of a tick (not a name) read at a faster stage is written in a field, which U2r2 gives; until then it is E0200, on the line of
/// the part. A name read at `sample`, a part that its own tick reads (a `let` of the tick) and a part at the clock of the line are not.
/// Removed with the gate at U2r2 (the final forms are the cases of that unit).
#[test]
fn a_computed_part_of_a_tick_read_at_a_faster_stage_is_e0200_until_the_field_of_u2r2() {
    // The forms the gate holds: the line of the part is the 4th of the text (the head, the two `let`s, then the body).
    let held = [
        "  let b = (a * 2.0) at sample\n  x * b + (c at sample)",
        "  let b = (a + c) at sample\n  x * b",
        "  let b = (a + a) at sample\n  x * b + (c at sample)",
    ];
    for body in held {
        let ds = diags(&flow_body(body));
        assert_eq!(ds.len(), 1, "{body}: one error, got {ds:?}");
        assert_eq!(code_of(&ds[0]), "E0200", "{body}: {}", ds[0]);
        assert_eq!(span_of(&ds[0]["span"]).line, 4, "{body}: on the line of the part: {}", ds[0]);
    }
    // The forms the gate does not hold.
    let free = [
        "  (a at sample) * x + (c at sample)",
        "  let s = a * 2.0\n  let t = s + a\n  x * (t at sample) + (c at sample)",
        "  let s = a + a\n  x * (s at sample) + (c at sample)",
        "  let b = a at (sample / 2)\n  x * (b at sample) + (c at sample)",
    ];
    for body in free {
        let ds = diags(&flow_body(body));
        assert!(ds.is_empty(), "{body}: read as the spec has it, got {ds:?}");
    }
}
