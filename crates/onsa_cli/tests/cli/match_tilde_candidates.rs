//! The candidates around the check of `match~` (W7-06 U3a/t; spec §2.6, §11.5, §18.1; S-110, S-394, S-1172, S-1177, S-1183, S-1191).
//!
//! What the case files in `tests/spec/` cannot pin: the candidates applied one after the other until the program has no diagnostic (the
//! runner applies each candidate once, and compares the text after it only through the copy `.fixK`), and the candidates of the E0811 of
//! a plain branch that holds a `match~`. Every test uses the diagnostics and candidates of the check in this process (`check_file`), with
//! no file written; no test fixes a column or the name of a new `let`.

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

/// The E0812 of a `match~` (§11.5, §2.6): one candidate, the removal of the `~`; the program after it has no diagnostic.
#[test]
fn the_e0812_has_the_one_candidate_that_takes_the_tilde_out() {
    let forms = [
        "pub flow f(k: U32 at sample) -> F32 at sample {\n  match~ k { 0 => 1.0, _ => 2.0 }\n}\n",
        "pub flow f(x: F32 at sample, k: U32 at sample) -> [F32; 2] at sample {\n  match~ k { 0 => par i in 0 ..< 2 { x * F32.round_from(i) }, _ => [x, x] }\n}\n",
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let o: Option[F32] = if x > 2.0 { Some(x) } else { None }\n  match~ o { Some(v) if v > 3.0 => v * 2.0, Some(v) => v, None => 0.0 }\n}\n",
        "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  let a = match~ k { 0 => x, _ => 0.0 }\n  a\n}\n",
    ];
    for (n, flow) in forms.iter().enumerate() {
        let source = program(flow);
        let c = check_file("main.onsa", &source);
        assert_eq!(c.diags.len(), 1, "form {n}: {:?}", c.diags);
        let d = &c.diags[0];
        assert_eq!((d.code.as_str(), d.fixes.len()), ("E0812", 1), "form {n}: {:?}", d.fixes);
        assert_eq!(inserted(&d.fixes[0]), "", "form {n}: the candidate inserts nothing");
        let after = edited(&source, &d.fixes[0]);
        assert_eq!(after.matches("match~").count(), 0, "form {n}: the `~` is out:\n{after}");
        assert!(check_file("main.onsa", &after).diags.is_empty(), "form {n}: clean after the candidate:\n{after}");
    }
}

/// S-394 (X1): the E0811 of the guard of a `match~` has no `~` candidate (the `match~` is there already, and the guard stays a place that is
/// not evaluated every sample); the one candidate is the lift into a `let`, and the program after it has no diagnostic.
#[test]
fn the_e0811_of_a_guard_of_a_match_tilde_has_the_lift_only() {
    let forms = [
        "pub flow f(k: U32 at sample, x: F32 at sample) -> F32 at sample {\n  match~ k {\n    0 if acc~(x) > 1.0 => prev~(x),\n    _ => 0.0,\n  }\n}\n",
        "pub flow f(k: U32 at sample, x: F32 at sample) -> F32 at sample {\n  match~ k {\n    0 => 2.0,\n    1 if prev~(x) > 0.5 => acc~(x),\n    _ => 0.0,\n  }\n}\n",
        "pub flow f(k: U32 at sample, x: F32 at sample) -> F32 at sample {\n  let a = match~ k { 0 if prev~(x) > 0.0 => acc~(x), _ => 0.0 }\n  a\n}\n",
    ];
    for (n, flow) in forms.iter().enumerate() {
        let source = program(flow);
        let c = check_file("main.onsa", &source);
        assert_eq!(c.diags.len(), 1, "form {n}: {:?}", c.diags);
        let d = &c.diags[0];
        assert_eq!((d.code.as_str(), d.fixes.len()), ("E0811", 1), "form {n}: {:?}", d.fixes);
        assert!(inserted(&d.fixes[0]).contains("let "), "form {n}: the candidate is the lift: {:?}", d.fixes);
        let after = edited(&source, &d.fixes[0]);
        assert!(check_file("main.onsa", &after).diags.is_empty(), "form {n}: clean after the lift:\n{after}");
    }
}

/// S-394 (X1), S-1172 (§11.5: "式が腕の束縛を読むときと、`par~` の本体の中にあるときは、この候補を作らない"): the E0811 of a guard whose thing with
/// state reads a binding of its arm, or that is in the body of a `par~`, has no candidate at all, and is still the E0811 (no E0200, no crash).
#[test]
fn the_e0811_of_a_guard_that_cannot_be_lifted_has_no_candidate() {
    let forms = [
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let o: Option[F32] = if x > 2.0 { Some(x) } else { None }\n  match~ o {\n    Some(v) if acc~(v) > 0.5 => prev~(x),\n    _ => 0.0,\n  }\n}\n",
        "pub flow f(k: U32 at sample, x: F32 at sample) -> F32 at sample {\n  match~ k {\n    0 => acc~(x),\n    n if prev~(F32.round_from(n)) > 0.5 => 1.0,\n    _ => 0.0,\n  }\n}\n",
        "pub flow f(k: U32 at sample, x: F32 at sample) -> [F32; 2] at sample {\n  par~ i in 0 ..< 2 {\n    match~ k {\n      0 if prev~(x) > 0.0 => acc~(x),\n      _ => 0.0,\n    }\n  }\n}\n",
    ];
    for (n, flow) in forms.iter().enumerate() {
        let source = program(flow);
        let c = check_file("main.onsa", &source);
        assert_eq!(c.diags.len(), 1, "form {n}: {:?}", c.diags);
        assert_eq!(c.diags[0].code, "E0811", "form {n}: {:?}", c.diags[0]);
        assert!(c.diags[0].fixes.is_empty(), "form {n}: no candidate: {:?}", c.diags[0].fixes);
    }
}

/// §11.5, S-110: a `match~` in a branch of a plain `if` is no help to the thing with state in its own arm: the outer branch is not evaluated
/// every sample, so the E0811 is the one of the outer `if`, and its first candidate writes the `~` of the outer `if`
/// (`if c { match~ k { … } } else { … }` → `if~ c { … }`); the program is clean after it.
#[test]
fn a_match_tilde_in_a_plain_branch_is_the_e0811_of_the_outer_branch() {
    let source = program(
        "pub flow f(x: F32 at sample, k: U32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { match~ k { 0 => acc~(x), _ => 0.0 } } else { x }\n}\n",
    );
    let c = check_file("main.onsa", &source);
    assert_eq!(c.diags.len(), 1, "{:?}", c.diags);
    let d = &c.diags[0];
    assert_eq!(d.code, "E0811", "{d:?}");
    assert!(!d.fixes.is_empty(), "{d:?}");
    assert_eq!(inserted(&d.fixes[0]).trim(), "~", "the first candidate is a `~`");
    let after = edited(&source, &d.fixes[0]);
    assert!(after.contains("if~ c {"), "the `~` is right after the outer `if`:\n{after}");
    assert!(after.contains("match~ k {"), "the inner `match~` is as it was:\n{after}");
    assert!(check_file("main.onsa", &after).diags.is_empty(), "clean after the candidate:\n{after}");
}

/// §11.5 (the lift is not made for a thing that reads a binding of its arm; the other candidate stays): the E0811 of an arm of a plain `match` that
/// reads the binding has the `~` candidate only, and the `match~` that it makes checks clean (the binding has a `Default`).
#[test]
fn the_tilde_candidate_of_an_arm_that_reads_a_binding_makes_a_clean_match_tilde() {
    let source = program(
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let o: Option[F32] = if x > 2.0 { Some(x) } else { None }\n  match o {\n    Some(v) => acc~(v),\n    None => 0.0,\n  }\n}\n",
    );
    let c = check_file("main.onsa", &source);
    assert_eq!(c.diags.len(), 1, "{:?}", c.diags);
    let d = &c.diags[0];
    assert_eq!((d.code.as_str(), d.fixes.len()), ("E0811", 1), "{:?}", d.fixes);
    assert_eq!(inserted(&d.fixes[0]).trim(), "~", "the candidate is a `~`");
    let after = edited(&source, &d.fixes[0]);
    assert!(after.contains("match~ o {"), "the `~` is right after the `match`:\n{after}");
    assert!(check_file("main.onsa", &after).diags.is_empty(), "clean after the candidate:\n{after}");
}

/// The E0816 of a binding of an arm (§11.5, §18.1) has no candidate: the type has no `Default`, and the spec offers nothing to write.
#[test]
fn the_e0816_of_an_arm_binding_has_no_candidate() {
    let source = program(
        "pub struct Plain {\n  a: F32,\n}\n\npub flow f(x: F32 at sample) -> F32 at sample {\n  let o: Option[Plain] = if x > 0.0 { Some(Plain { a: x }) } else { None }\n  match~ o {\n    Some(p) => acc~(p.a),\n    None => 0.0,\n  }\n}\n",
    );
    let c = check_file("main.onsa", &source);
    assert_eq!(c.diags.len(), 1, "{:?}", c.diags);
    assert_eq!(c.diags[0].code, "E0816", "{:?}", c.diags[0]);
    assert!(c.diags[0].fixes.is_empty(), "no candidate: {:?}", c.diags[0].fixes);
}

/// S-1191, the provisional reading (2) (an open detail): a `match~` that holds a thing with state only in a guard is the E0812 first (its `~` comes
/// before the guard), the candidate takes the `~` out, and what is left is the E0811 of the guard of a plain `match`, whose lift ends the loop.
#[test]
fn a_match_tilde_with_state_only_in_a_guard_is_the_e0812_and_then_the_e0811() {
    let source = program(
        "pub flow f(k: U32 at sample, x: F32 at sample) -> F32 at sample {\n  match~ k {\n    0 if prev~(x) > 0.0 => 1.0,\n    _ => 0.0,\n  }\n}\n",
    );
    assert_eq!(first_candidates_until_clean("guard_only", &source, 4), ["E0812", "E0811"]);
}
