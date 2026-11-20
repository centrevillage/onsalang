//! The candidates around the check of `if~` (W7-06 U2/t; spec §2.6, §11.5, §18.1; S-110, S-394, S-1177, S-1183, S-1187).
//!
//! What the case files in `tests/spec/` cannot pin: the candidates applied one after the other until the program has no diagnostic (the
//! runner applies each candidate once, and compares the text after it only through the copy `.fixK`), and the candidates of the E0811 of
//! a plain branch that holds an `if~`. Every test uses the diagnostics and candidates of the check in this process (`check_file`), with no
//! file written; no test fixes a column or the name of a new `let`.

use crate::test_support::sweep::check_file;
use crate::test_support::{apply, edits_of};
use serde_json::Value;

const PRELUDE: &str = "pub flow acc(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(^y)\n  y\n}\n\n\
                       pub rt fn two(a: F32, b: F32) -> F32 {\n  a + b\n}\n\n";

fn program(flow: &str) -> String {
    format!("{PRELUDE}{flow}")
}

fn edited(text: &str, fix: &Value) -> String {
    apply(text, &edits_of(fix))
}

/// The text of the edits of a candidate, joined.
fn inserted(fix: &Value) -> String {
    edits_of(fix).iter().map(|e| e.replace.clone()).collect::<Vec<_>>().join("")
}

/// The first candidate of the first diagnostic applied again and again: the codes of the first diagnostic of each round until the program has
/// none (at most `limit` rounds, else the loop is not stopping).
fn first_candidates_until_clean(tag: &str, source: &str, limit: usize) -> Vec<String> {
    let mut text = source.to_string();
    let mut codes = Vec::new();
    for _ in 0..=limit {
        let c = check_file("main.onsa", &text);
        let Some(d) = c.diags.first() else { return codes };
        codes.push(d.code.clone());
        assert!(!d.fixes.is_empty(), "{tag}: a diagnostic with no candidate stops the loop: {:?}\n{text}", d);
        text = edited(&text, &d.fixes[0]);
    }
    panic!("{tag}: the candidates do not stop after {limit} rounds: {codes:?}\n{text}");
}

/// S-1187, §2.6: a line break between `if` and the `~` inside parentheses is the E0020, and its first candidate writes `if~`. A branch
/// that holds no thing with state makes the `if~` the E0812 (§11.5), whose candidate takes the `~` out again: the `~` is the writer's own, which the
/// candidate of the E0020 moved up, so taking it out undoes no step of the loop, and the program is clean after the two rounds. (`two(if` and
/// the `~` on the next line is the form of tests/spec/fixes/e0020_newline_if_tilde.onsa.)
#[test]
fn a_newline_before_the_tilde_leads_to_the_e0812_and_stops() {
    let flows = [
        "pub flow f(c: Bool at sample) -> F32 at sample {\n  two(if\n    ~ c { 1.0 } else { 2.0 }, 1.0)\n}\n",
        "pub flow f(c: Bool at sample) -> F32 at sample {\n  two(if\n    ~c { 1.0 } else { 2.0 }, 1.0)\n}\n",
        "pub flow f(c: Bool at sample, d: Bool at sample) -> F32 at sample {\n  two(if\n    ~ c { 1.0 } else if d { 2.0 } else { 3.0 }, 1.0)\n}\n",
    ];
    for (n, flow) in flows.iter().enumerate() {
        let source = program(flow);
        let codes = first_candidates_until_clean(&format!("newline_{n}"), &source, 4);
        assert_eq!(codes, ["E0020", "E0812"], "newline_{n}: the E0020, then the E0812 of the `if~` without state");
    }
}

/// With a thing with state in a branch the candidate of the E0020 is the last round.
#[test]
fn a_newline_before_the_tilde_with_state_in_a_branch_stops_after_one_round() {
    let source = program(
        "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  two(if\n    ~ c { acc~(x) } else { 2.0 }, 1.0)\n}\n",
    );
    assert_eq!(first_candidates_until_clean("newline_state", &source, 3), ["E0020"]);
}

/// The E0812 of an `if~` (§11.5, §2.6): one candidate, the removal of the `~`; the program after it has no diagnostic.
#[test]
fn the_e0812_has_the_one_candidate_that_takes_the_tilde_out() {
    let forms = [
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  if~ x > 0.0 { 1.0 } else { 0.0 }\n}\n",
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  if~ x > 1.0 { 1.0 } else if x > 0.0 { 2.0 } else { 3.0 }\n}\n",
        "pub flow f(x: F32 at sample, c: Bool at sample) -> [F32; 2] at sample {\n  if~ c { par i in 0 ..< 2 { x * F32.round_from(i) } } else { [x, x] }\n}\n",
        "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  let a = if~ c { x } else { 0.0 }\n  a\n}\n",
    ];
    for (n, flow) in forms.iter().enumerate() {
        let source = program(flow);
        let c = check_file("main.onsa", &source);
        assert_eq!(c.diags.len(), 1, "form {n}: {:?}", c.diags);
        let d = &c.diags[0];
        assert_eq!((d.code.as_str(), d.fixes.len()), ("E0812", 1), "form {n}: {:?}", d.fixes);
        assert_eq!(inserted(&d.fixes[0]), "", "form {n}: the candidate inserts nothing");
        let after = edited(&source, &d.fixes[0]);
        assert_eq!(after.matches("if~").count(), 0, "form {n}: the `~` is out:\n{after}");
        assert!(check_file("main.onsa", &after).diags.is_empty(), "form {n}: clean after the candidate:\n{after}");
    }
}

/// §11.5, S-110: an `if~` in a branch of a plain `if` is no help to the thing with state in its own branch: the outer branch is not
/// evaluated every sample, so the E0811 is the one of the outer `if`, and its first candidate writes the `~` of the outer `if`
/// (`if c { if~ d { … } else { … } } else { … }` → `if~ c { … }`); the program is clean after it.
#[test]
fn an_if_tilde_in_a_plain_branch_is_the_e0811_of_the_outer_branch() {
    let source = program(
        "pub flow f(x: F32 at sample, c: Bool at sample, d: Bool at sample) -> F32 at sample {\n  if c { if~ d { prev~(x) } else { x } } else { x }\n}\n",
    );
    let c = check_file("main.onsa", &source);
    assert_eq!(c.diags.len(), 1, "{:?}", c.diags);
    let d = &c.diags[0];
    assert_eq!(d.code, "E0811", "{d:?}");
    assert!(!d.fixes.is_empty(), "{d:?}");
    assert_eq!(inserted(&d.fixes[0]).trim(), "~", "the first candidate is a `~`");
    let after = edited(&source, &d.fixes[0]);
    assert!(after.contains("if~ c {"), "the `~` is right after the outer `if`:\n{after}");
    assert!(after.contains("if~ d {"), "the inner `if~` is as it was:\n{after}");
    assert!(check_file("main.onsa", &after).diags.is_empty(), "clean after the candidate:\n{after}");
}

/// S-394 (X1): the E0811 of the second condition of an `if~` chain has no `~` candidate (the `if~` is there already, and the condition stays
/// a place that is not evaluated every sample); the one candidate is the lift into a `let`, and the program after it has no diagnostic.
#[test]
fn the_e0811_of_a_chain_condition_of_an_if_tilde_has_the_lift_only() {
    let source = program(
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  if~ x > 1.0 { acc~(x) } else if prev~(x) > 0.0 { 2.0 } else { 0.0 }\n}\n",
    );
    let c = check_file("main.onsa", &source);
    assert_eq!(c.diags.len(), 1, "{:?}", c.diags);
    let d = &c.diags[0];
    assert_eq!((d.code.as_str(), d.fixes.len()), ("E0811", 1), "{:?}", d.fixes);
    assert!(inserted(&d.fixes[0]).contains("let "), "the candidate is the lift: {:?}", d.fixes);
    let after = edited(&source, &d.fixes[0]);
    assert!(check_file("main.onsa", &after).diags.is_empty(), "clean after the lift:\n{after}");
}
