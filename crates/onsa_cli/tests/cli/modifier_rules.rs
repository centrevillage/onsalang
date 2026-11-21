//! The modifiers `.down~(N)`, `.up~(N)`, `.when~(c)` and `.reset_if~(c)` after the call of an instance (W7-09 U3a/t; spec §2.6, §11.2,
//! §11.4, §11.10, §18.1; S-555, S-556, S-811, S-1085, S-1086, S-1091): what the case files in `tests/spec/` cannot pin.
//!
//! - The candidate of the E0811 of a modifier written without the `~` adds the `~`, and that of the E0806 of a modifier called with `!`
//!   replaces the `!` with `~` (the files `fixes/e0811_modifier_without_tilde.onsa` and `fixes/e0806_modifier_bang.onsa` count the
//!   candidates; the text after the candidate is here, and no column is fixed).
//! - The note of the E0812 of a modifier shows the closed list when the receiver is a value or an instance with a name that is not in it
//!   (S-1085, S-1086: provisional readings, an open detail), and names the modifier for a delay that takes `down` or `up` (S-1091).
//! - The stop of `.down~` and `.up~` at the flow stage with E0200 until the clocks of the chain are read (W7-09 U3b): the last test, which
//!   U3b removes with the gate.
//!
//! The texts are written from the spec; none is taken from the output of the compiler. The checks run in this process, with no file written.

use crate::test_support::sweep::{check_file, check_input_out};
use crate::test_support::{apply, code_of, diagnostics, doc_of, edits_of, fixes_of, notes_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

const PRELUDE: &str = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  x * 0.5 + prev~(x) * 0.5\n}\n\n";

fn flow(body: &str) -> String {
    format!(
        "{PRELUDE}pub flow f(x: F32 at sample, c: Bool at sample, p: F32 at block) -> F32 at sample {{\n  {body}\n}}\n"
    )
}

/// The one diagnostic of the program, with the text after its one candidate.
fn one_candidate(source: &str, code: &str) -> String {
    let c = check_file("main.onsa", source);
    assert_eq!(c.diags.len(), 1, "one error in the unit (§18.1): {:?}\n{source}", c.diags);
    assert_eq!(c.diags[0].code, code, "{source}");
    assert_eq!(c.diags[0].fixes.len(), 1, "{code} has one candidate: {:?}\n{source}", c.diags[0].fixes);
    apply(source, &edits_of(&c.diags[0].fixes[0]))
}

fn all_become(forms: &[(&str, &str)], code: &str) {
    for (before, after) in forms {
        assert_eq!(one_candidate(&flow(before), code), flow(after), "{before}");
    }
}

/// §11.10: "`~` の無い `saw~(f0).when(c)` は E0811（修正候補は `~` を足す形）".
#[test]
fn the_candidate_of_a_modifier_without_a_tilde_adds_the_tilde() {
    let forms = [
        ("lp~(x).when(c)", "lp~(x).when~(c)"),
        ("lp~(x).reset_if(c)", "lp~(x).reset_if~(c)"),
        ("prev~(x).when(c)", "prev~(x).when~(c)"),
        ("lp~(x).reset_if~(c).when(c)", "lp~(x).reset_if~(c).when~(c)"),
        ("lp~(p).down~(2).when(c) at sample", "lp~(p).down~(2).when~(c) at sample"),
        ("lp~(lp~(x).when(c))", "lp~(lp~(x).when~(c))"),
    ];
    all_become(&forms, "E0811");
}

/// §11.2: the E0806 of a `!` call has the candidate that replaces the `!` with `~` when the callee is an instance (here the receiver is
/// one and the name is in the list).
#[test]
fn the_candidate_of_a_modifier_called_with_a_bang_replaces_it_with_a_tilde() {
    let forms = [
        ("lp~(x).when!(c)", "lp~(x).when~(c)"),
        ("lp~(x).reset_if!(c)", "lp~(x).reset_if~(c)"),
        ("lp~(p).down!(4) at sample", "lp~(p).down~(4) at sample"),
        ("prev~(x).when!(c)", "prev~(x).when~(c)"),
        ("lp~(x).when~(c).up!(2) at sample", "lp~(x).when~(c).up~(2) at sample"),
    ];
    all_become(&forms, "E0806");
}

fn diags(text: &str) -> Vec<Value> {
    let out = check_input_out(&PackageInput::single_file("a.onsa", text));
    assert!(out.code == 0 || out.code == 1, "onsa check ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

/// The one E0812 of the body, with no candidate, and the text of its notes.
fn e0812_notes(body: &str) -> String {
    let ds = diags(&flow(body));
    assert_eq!(ds.len(), 1, "{body}: one error: {ds:?}");
    assert_eq!(code_of(&ds[0]), "E0812", "{body}: {}", ds[0]);
    assert!(fixes_of(&ds[0]).is_empty(), "{body}: no candidate: {}", ds[0]);
    notes_of(&ds[0]).iter().map(|n| str_of(n, "message")).collect::<Vec<_>>().join("\n")
}

/// §11.10: "受け手が値のときは E0812 で、`~` を除く候補は出さず、note で受け手と一覧を示す" (S-1085, provisional reading (1)), and the same note
/// for an instance with a name that is not in the list (S-1086 (1)); a name that is not in the list on a value has the general note of §2.6.
#[test]
fn the_e0812_of_a_modifier_shows_the_list_of_the_modifiers() {
    let bodies = [
        "x.when~(c)",
        "let s = lp~(p).down~(4)\n  s.down~(2) at sample",
        "(lp~(x)).reset_if~(c)",
        "lp~(x).foo~(c)",
        "lp~(x).when~(c).Up~(2)",
    ];
    for body in bodies {
        let notes = e0812_notes(body);
        for name in ["down", "up", "when", "reset_if"] {
            assert!(notes.contains(name), "{body}: a note shows `{name}`: {notes}");
        }
    }
    let notes = e0812_notes("x.foo~(c)");
    assert!(!notes.is_empty() && !notes.contains("reset_if"), "the general note, not the list: {notes}");
}

/// S-1091, provisional reading (1): `down` and `up` after a built-in delay are the E0812 of the names stage, whose note is that of §11.4 and
/// names the modifier (the chain rate would be apart from the clock of the first argument).
#[test]
fn a_down_or_up_on_a_builtin_delay_is_the_e0812_with_the_note_of_the_delays() {
    for (body, name) in
        [("prev~(x).down~(2)", "down"), ("delay~(x, 2).up~(2)", "up"), ("vdelay~(x, x, 4).down~(2)", "down")]
    {
        let notes = e0812_notes(body);
        assert!(
            notes.contains("§11.4") && notes.contains(name),
            "{body}: a note of §11.4 that names the modifier: {notes}"
        );
    }
}

/// W7-09 U3a to U3b: the modifiers `.down~` and `.up~` pass the names stage and the type stage, and the flow stage stops at them with
/// E0200 (Q-09: the spec has them, the clocks of the chain are not read yet), and with nothing else. U3b removes the gate with this test.
#[test]
fn a_down_or_up_modifier_stops_at_the_flow_stage_with_e0200_until_u3b() {
    let bodies = [
        "lp~(p).down~(4) at sample",
        "lp~(p).down~(2).down~(2) at sample",
        "lp~(p).down~(4).up~(2) at sample",
        "let y = lp~(p).down~(4)\n  y at sample",
    ];
    for body in bodies {
        let ds = diags(&flow(body));
        assert_eq!(ds.len(), 1, "{body}: one error: {ds:?}");
        assert_eq!(code_of(&ds[0]), "E0200", "{body}: {}", ds[0]);
    }
}
