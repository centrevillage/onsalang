//! The candidates of the E0811 of a plain branch, of a guard and of a condition of a chain, and of the E0806 of the right of `&&` / `||`
//! (W7-06 U1/t; spec §2.6, §11.5; S-110, S-394, S-1172, S-1183).
//!
//! What the case files in `tests/spec/` cannot pin (the runner compares a text after a candidate only through the copy `.fixK`, which
//! the implementation writes, and the spec does not fix the name of the new `let`): the shape of the lift into a `let`
//! (§11.5: "最も外の状態を持つものの式 … を、それを含む本体の直下の `let`（か出力の式）の直前の新しい `let` に移し、元の位置を
//! その名前に置き換える。名前は本体のどの名前とも重ねない"), and that the candidates applied one after the other stop.
//!
//! Every test uses the diagnostics and candidates of the check in this process (`check_file`), with no file written. The name of the
//! new `let` is read from the text after the candidate; no test fixes it.

use std::collections::BTreeSet;

use crate::test_support::sweep::check_file;
use crate::test_support::{apply, edits_of};
use serde_json::Value;

const PRELUDE: &str = "pub flow acc(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(^y)\n  y\n}\n\n\
                       pub rt fn wrap(x: F32) -> F32 {\n  x\n}\n\n\
                       pub rt fn pair_sum(xs: [F32; 2]) -> F32 {\n  xs[0] + xs[1]\n}\n\n";

fn program(flow: &str) -> String {
    format!("{PRELUDE}{flow}")
}

/// The words of a text (names and keywords, as the runs of letters, digits and `_`).
fn words(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut cur = String::new();
    for c in text.chars().chain(std::iter::once(' ')) {
        if c.is_alphanumeric() || c == '_' {
            cur.push(c);
        } else if !cur.is_empty() {
            out.insert(std::mem::take(&mut cur));
        }
    }
    out
}

/// The only diagnostic of a program that is a flow with one error: its code and its candidates.
fn the_error(tag: &str, text: &str) -> (String, Vec<Value>) {
    let c = check_file("main.onsa", text);
    assert_eq!(c.diags.len(), 1, "{tag}: one diagnostic expected, got {:?}", c.diags);
    (c.diags[0].code.clone(), c.diags[0].fixes.clone())
}

fn edited(text: &str, fix: &Value) -> String {
    apply(text, &edits_of(fix))
}

/// The text of the edits of a candidate, joined.
fn inserted(fix: &Value) -> String {
    edits_of(fix).iter().map(|e| e.replace.clone()).collect::<Vec<_>>().join("")
}

/// The candidates that make a new `let` (the text they insert holds `let `), and those that insert a `~` only.
fn split(fixes: &[Value]) -> (Vec<&Value>, Vec<&Value>) {
    let lifts: Vec<&Value> = fixes.iter().filter(|f| inserted(f).contains("let ")).collect();
    let tildes: Vec<&Value> = fixes.iter().filter(|f| inserted(f).trim() == "~").collect();
    (lifts, tildes)
}

// ---- the shape of the lift into a `let` (spec §11.5, S-1172) --------------------------------------------

/// (tag, the flow, the code of the error, the text of the outermost thing with state, which the candidate moves).
fn the_lift_cases() -> Vec<(&'static str, String, &'static str, &'static str)> {
    let flow = |s: &str| program(s);
    vec![
        (
            "then_branch",
            flow(
                "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { acc~(x) } else { 0.0 }\n}\n",
            ),
            "E0811",
            "acc~(x)",
        ),
        (
            "arm",
            flow(
                "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  match k {\n    0 => acc~(x),\n    _ => 0.0,\n  }\n}\n",
            ),
            "E0811",
            "acc~(x)",
        ),
        (
            "inside_a_call",
            flow(
                "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { wrap(prev~(x)) } else { 0.0 }\n}\n",
            ),
            "E0811",
            "prev~(x)",
        ),
        (
            "value_of_a_let",
            flow(
                "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  let a = if c { prev~(x) } else { 0.0 }\n  a * 2.0\n}\n",
            ),
            "E0811",
            "prev~(x)",
        ),
        (
            "second_let",
            flow(
                "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  let b = x * 2.0\n  let a = if c { prev~(x) } else { b }\n  a + b\n}\n",
            ),
            "E0811",
            "prev~(x)",
        ),
        (
            "par_tilde_as_a_whole",
            flow(
                "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { pair_sum(par~ i in 0 ..< 2 { prev~(x * F32.round_from(i)) }) } else { 0.0 }\n}\n",
            ),
            "E0811",
            "par~ i in 0 ..< 2 { prev~(x * F32.round_from(i)) }",
        ),
        (
            "guard",
            flow(
                "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  match k {\n    0 if acc~(x) > 1.0 => 1.0,\n    _ => 0.0,\n  }\n}\n",
            ),
            "E0811",
            "acc~(x)",
        ),
        (
            "chain_condition",
            flow(
                "pub flow f(x: F32 at sample) -> F32 at sample {\n  if x > 1.0 { 1.0 } else if prev~(x) > 0.0 { 2.0 } else { 0.0 }\n}\n",
            ),
            "E0811",
            "prev~(x)",
        ),
        (
            "right_operand",
            flow("pub flow f(x: F32 at sample) -> Bool at sample {\n  x > 0.0 && acc~(x) > 1.0\n}\n"),
            "E0806",
            "acc~(x)",
        ),
        (
            "names_a_naive_name_would_clash_with",
            flow(
                "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  let acc_0 = x * 2.0\n  let state_0 = x * 3.0\n  let prev_0 = x * 4.0\n  let a = if c { acc~(x) } else { 0.0 }\n  a + acc_0 + state_0 + prev_0\n}\n",
            ),
            "E0811",
            "acc~(x)",
        ),
    ]
}

/// S-1172: the candidate moves the outermost thing with state into a new `let` that stands right before the statement that holds it
/// (the `let` of the body, or the output), puts the name of the new `let` where the thing was, and the name is a name
/// that the program does not have. Nothing else of the program changes, and the program after it has no diagnostic.
#[test]
fn the_lift_into_a_let_moves_the_outermost_thing_before_its_statement() {
    for (tag, source, want_code, lifted) in the_lift_cases() {
        let (code, fixes) = the_error(tag, &source);
        assert_eq!(code, want_code, "{tag}");
        let (lifts, _) = split(&fixes);
        assert_eq!(lifts.len(), 1, "{tag}: one candidate that lifts into a `let` expected, got {fixes:?}");
        let after = edited(&source, lifts[0]);

        // the lines that are not the lines of the program: the new `let` and the line that held the thing
        let before_lines: Vec<&str> = source.lines().collect();
        let after_lines: Vec<&str> = after.lines().collect();
        assert_eq!(after_lines.len(), before_lines.len() + 1, "{tag}: one line is added:\n{after}");
        let at = after_lines
            .iter()
            .position(|l| l.trim_start().starts_with("let ") && l.ends_with(&format!("= {lifted}")))
            .unwrap_or_else(|| panic!("{tag}: no `let <name> = {lifted}` line in:\n{after}"));
        let new_let = after_lines[at];
        let name = new_let.trim_start().strip_prefix("let ").unwrap().split(' ').next().unwrap().to_string();
        assert!(
            !name.is_empty() && !words(&source).contains(&name),
            "{tag}: the name {name:?} is a name of the program"
        );

        // the new `let` stands right before the statement (whose first line is the line after it); of the lines of the statement and
        // after it, only the line that held the thing changed, with the name in its place (the statement may be of several lines)
        assert_eq!(&after_lines[..at], &before_lines[..at], "{tag}: the lines before the `let` are as they were");
        let rest = &after_lines[at + 1..];
        let changed: Vec<usize> = (0..rest.len()).filter(|&k| rest[k] != before_lines[at + k]).collect();
        assert_eq!(changed.len(), 1, "{tag}: one line of the statement changes:\n{after}");
        let original = before_lines[at + changed[0]];
        assert_eq!(
            rest[changed[0]],
            original.replacen(lifted, &name, 1),
            "{tag}: the place of the thing reads the name:\n{after}"
        );
        let indent = |l: &str| l.len() - l.trim_start().len();
        assert_eq!(
            indent(new_let),
            indent(before_lines[at]),
            "{tag}: the new `let` is in the body, at the indent of the statement"
        );

        // the program after the candidate has no diagnostic (the lift is clean), and the thing is evaluated once
        let again = check_file("main.onsa", &after);
        assert!(again.diags.is_empty(), "{tag}: diagnostics after the lift: {:?}\n{after}", again.diags);
        assert_eq!(
            after.matches(lifted).count(),
            source.matches(lifted).count(),
            "{tag}: the thing is moved, not copied"
        );
    }
}

// ---- which candidates there are (spec §2.6, §11.5; S-394, S-1172) ---------------------------------------------

/// A branch has two candidates, in the order of the spec: the `~` after the `if` / `match` (`if~` / `match~`), then the lift
/// into a `let`.
#[test]
fn a_branch_has_the_tilde_and_then_the_lift() {
    let cases = [
        (
            "if",
            "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { acc~(x) } else { 0.0 }\n}\n",
        ),
        (
            "match",
            "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  match k {\n    0 => acc~(x),\n    _ => 0.0,\n  }\n}\n",
        ),
    ];
    for (tag, flow) in cases {
        let source = program(flow);
        let (code, fixes) = the_error(tag, &source);
        assert_eq!(code, "E0811", "{tag}");
        assert_eq!(fixes.len(), 2, "{tag}: {fixes:?}");
        assert_eq!(inserted(&fixes[0]).trim(), "~", "{tag}: the first candidate is the `~`");
        assert!(inserted(&fixes[1]).contains("let "), "{tag}: the second candidate is the lift");
        let tilde = edited(&source, &fixes[0]);
        let word = if tag == "if" { "if~ c" } else { "match~ k" };
        assert!(tilde.contains(word), "{tag}: the `~` is right after the keyword:\n{tilde}");
    }
}

/// S-394: the guard of a `match` and the second condition of a chain are not made evaluated every sample by a `~`, so the only
/// candidate is the lift; the E0806 of an operand has the lift only.
#[test]
fn a_guard_a_chain_condition_and_an_operand_have_only_the_lift() {
    for (tag, source, want_code, _) in the_lift_cases() {
        if !["guard", "chain_condition", "right_operand"].contains(&tag) {
            continue;
        }
        let (code, fixes) = the_error(tag, &source);
        assert_eq!(code, want_code, "{tag}");
        let (lifts, tildes) = split(&fixes);
        assert_eq!((fixes.len(), lifts.len(), tildes.len()), (1, 1, 0), "{tag}: {fixes:?}");
    }
}

/// S-1172, S-394 (X1): no lift when the thing reads a binding of the arm or is in the body of a `par~`; the guard then has no candidate
/// at all (E0811 is still reported); a branch has the `~` only.
#[test]
fn the_lift_is_not_made_where_it_cannot_be() {
    let guard_binding = program(
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let o: Option[F32] = if x > 2.0 { Some(x) } else { None }\n  match o {\n    Some(v) if acc~(v) > 0.5 => v,\n    _ => 0.0,\n  }\n}\n",
    );
    let (code, fixes) = the_error("guard_binding", &guard_binding);
    assert_eq!((code.as_str(), fixes.len()), ("E0811", 0), "a guard that reads a binding has no candidate: {fixes:?}");

    let guard_in_par = program(
        "pub flow f(k: U32 at sample, x: F32 at sample) -> [F32; 2] at sample {\n  par~ i in 0 ..< 2 {\n    match k {\n      0 if acc~(x * F32.round_from(i)) > 1.0 => 1.0,\n      _ => 0.0,\n    }\n  }\n}\n",
    );
    let (code, fixes) = the_error("guard_in_par", &guard_in_par);
    assert_eq!(
        (code.as_str(), fixes.len()),
        ("E0811", 0),
        "a guard in the body of a `par~` has no candidate: {fixes:?}"
    );

    let arm_binding = program(
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let o: Option[F32] = if x > 2.0 { Some(x) } else { None }\n  match o {\n    Some(v) => acc~(v),\n    None => 0.0,\n  }\n}\n",
    );
    let (code, fixes) = the_error("arm_binding", &arm_binding);
    let (lifts, tildes) = split(&fixes);
    assert_eq!(
        (code.as_str(), fixes.len(), lifts.len(), tildes.len()),
        ("E0811", 1, 0, 1),
        "an arm that reads a binding: {fixes:?}"
    );

    let branch_in_par = program(
        "pub flow f(x: F32 at sample, c: Bool at sample) -> [F32; 2] at sample {\n  par~ i in 0 ..< 2 {\n    if c { acc~(x * F32.round_from(i)) } else { 0.0 }\n  }\n}\n",
    );
    let (code, fixes) = the_error("branch_in_par", &branch_in_par);
    let (lifts, tildes) = split(&fixes);
    assert_eq!(
        (code.as_str(), fixes.len(), lifts.len(), tildes.len()),
        ("E0811", 1, 0, 1),
        "a branch in a `par~`: {fixes:?}"
    );

    let right_in_par = program(
        "pub flow f(x: F32 at sample) -> [F32; 2] at sample {\n  par~ i in 0 ..< 2 {\n    if x > 0.0 && acc~(x) > F32.round_from(i) { 1.0 } else { 0.0 }\n  }\n}\n",
    );
    let (code, fixes) = the_error("right_in_par", &right_in_par);
    assert_eq!(
        (code.as_str(), fixes.len()),
        ("E0806", 0),
        "an operand in the body of a `par~` has no candidate: {fixes:?}"
    );
}

// ---- the candidates applied one after the other stop (spec §18.1; S-1183) ----------------------------------

/// The candidate `pick` of the first diagnostic of the program, applied again and again; the number of rounds until the program has
/// no diagnostic (at most `limit`, else the loop is not stopping), and the number of diagnostics of each round.
fn applied_until_clean(tag: &str, source: &str, pick: &dyn Fn(&[Value]) -> usize, limit: usize) -> Vec<usize> {
    let mut text = source.to_string();
    let mut counts = Vec::new();
    for _ in 0..=limit {
        let c = check_file("main.onsa", &text);
        counts.push(c.diags.len());
        if c.diags.is_empty() {
            return counts;
        }
        let fixes = &c.diags[0].fixes;
        assert!(!fixes.is_empty(), "{tag}: a diagnostic with no candidate stops the loop: {:?}\n{text}", c.diags[0]);
        text = edited(&text, &fixes[pick(fixes)]);
    }
    panic!("{tag}: the candidates do not stop after {limit} rounds: {counts:?}\n{text}");
}

/// The lift takes the thing out of every branch it was in, so one round is enough, however deep the nest is.
#[test]
fn the_lift_applied_to_a_nested_branch_stops_in_one_round() {
    let nested = [
        (
            "if_in_if",
            "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { if x > 1.0 { acc~(x) } else { 0.0 } } else { 0.0 }\n}\n",
        ),
        (
            "match_in_if",
            "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  if x > 0.0 { match k { 0 => prev~(x), _ => 0.0 } } else { 0.0 }\n}\n",
        ),
        (
            "if_in_arm",
            "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  match k { 0 => if x > 0.0 { acc~(x) } else { 0.0 }, _ => 0.0 }\n}\n",
        ),
    ];
    for (tag, flow) in nested {
        let source = program(flow);
        let counts = applied_until_clean(tag, &source, &|fixes: &[Value]| fixes.len() - 1, 3);
        assert_eq!(counts, vec![1, 0], "{tag}: one error, then none");
    }
}

/// S-1183, the provisional reading (1): the `~` candidate of the innermost branch is shown although the outer branch stays an error; the
/// first candidate applied again and again ends, with one error each round and no more rounds than the branches are deep. The `if~` of the
/// candidate is read after the check of `if~` (W7-06 U2), the `match~` of the next test after that of `match~` (W7-06 U3a).
const NESTED_IF: [(&str, &str); 1] = [(
    "if_in_if",
    "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { if x > 1.0 { acc~(x) } else { 0.0 } } else { 0.0 }\n}\n",
)];

const NESTED_MATCH: [(&str, &str); 2] = [
    (
        "match_in_if",
        "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  if x > 0.0 { match k { 0 => prev~(x), _ => 0.0 } } else { 0.0 }\n}\n",
    ),
    (
        "if_in_arm",
        "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  match k { 0 => if x > 0.0 { acc~(x) } else { 0.0 }, _ => 0.0 }\n}\n",
    ),
];

fn the_first_candidate_stops(nested: &[(&str, &str)]) {
    for (tag, flow) in nested {
        let source = program(flow);
        let counts = applied_until_clean(tag, &source, &|_: &[Value]| 0, 4);
        assert!(
            counts.iter().all(|&n| n <= 1) && *counts.last().unwrap() == 0 && counts.len() <= 3,
            "{tag}: {counts:?}"
        );
    }
}

#[test]
fn the_tilde_applied_to_a_nested_if_stops() {
    the_first_candidate_stops(&NESTED_IF);
}

#[test]
fn the_tilde_applied_to_a_nested_match_stops() {
    the_first_candidate_stops(&NESTED_MATCH);
}
