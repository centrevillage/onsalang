//! The notes of two forms of W5-24 U5 that the case files cannot pin (the runner of the cases does not
//! compare notes): the readings of an E0010 that cannot be candidates (S-346, spec §18.1: a chain of
//! comparisons whose middle would be evaluated twice, and a reading over the nesting limit, §2.5),
//! and the `{` after a named handler (S-480, spec §8.3: its E0002 notes that the body of a handler
//! written in place follows the name of an effect).
//!
//! The inputs are the case files of `tests/spec/` (read where they are, nothing written); each test
//! checks that the note is there and the words that tell what it shows, not its whole text, which
//! the spec does not fix. The expectations are those of the test work (W5-24 U5/t).

use crate::test_support::{check, code_of};
use serde_json::Value;

fn case(path: &str) -> String {
    format!("{}/../../tests/spec/{path}", env!("CARGO_MANIFEST_DIR"))
}

fn notes_of(d: &Value) -> Vec<String> {
    d.get("notes")
        .and_then(Value::as_array)
        .map(|a| a.iter().map(|n| n["message"].as_str().unwrap_or("").to_string()).collect())
        .unwrap_or_default()
}

fn fixes_of(d: &Value) -> usize {
    d.get("fixes").and_then(Value::as_array).map_or(0, Vec::len)
}

/// The diagnostics of `code` in the case file `path`, at least one.
fn of_code(path: &str, code: &str) -> Vec<Value> {
    let diags: Vec<Value> = check(&case(path)).into_iter().filter(|d| code_of(d) == code).collect();
    assert!(!diags.is_empty(), "{path}: no {code}");
    diags
}

/// The first line of `text` that has `needle`, 1-based.
fn line_of(text: &str, needle: &str) -> u64 {
    text.lines().position(|l| l.contains(needle)).unwrap_or_else(|| panic!("no `{needle}`")) as u64 + 1
}

fn twice_noted(notes: &[String]) -> bool {
    notes.iter().any(|n| n.contains("evaluated twice") && n.contains("`let`"))
}

#[test]
fn a_reading_with_a_middle_evaluated_twice_is_a_note_beside_the_other_readings() {
    // §18.1, S-346: `a < b & h < c` has the candidate `(a < b) & (h < c)` and the note of
    // `a < (b & h) < c`, whose middle `b & h` would be evaluated twice: written with a `let`.
    for path in ["fixes/e0010_twice_candidate.onsa", "fixes/e0010_twice_nesting_edge.onsa"] {
        for d in of_code(path, "E0010") {
            assert_eq!(fixes_of(&d), 1, "{path}: one candidate: {d}");
            assert!(twice_noted(&notes_of(&d)), "{path}: the note of the reading evaluated twice: {d}");
        }
    }
}

#[test]
fn a_chain_with_only_readings_evaluated_twice_has_the_note_and_no_candidate() {
    // §18.1: the middle that is no name, literal or path of fields is evaluated twice; the note
    // writes it with a `let`.
    for d in of_code("fixes/e0010_twice_only.onsa", "E0010") {
        assert_eq!(fixes_of(&d), 0, "no candidate: {d}");
        assert!(twice_noted(&notes_of(&d)), "the note of the reading evaluated twice: {d}");
    }
}

#[test]
fn a_reading_over_the_nesting_limit_is_a_note_with_or_without_candidates() {
    // §18.1, S-346: `three_ops_one_fits` keeps one candidate, and the reading over 256 levels is
    // a note too (before S-346 it had none); `two_ops_none_fit` has none and the note.
    let path = "fixes/e0010_nesting_boundary.onsa";
    let text = std::fs::read_to_string(case(path)).unwrap();
    let diags = of_code(path, "E0010");
    for (function, fixes) in [("fn two_ops_none_fit", 0), ("fn three_ops_one_fits", 1)] {
        let line = line_of(&text, function) + 1;
        let d = diags.iter().find(|d| d["span"]["line"].as_u64() == Some(line)).expect("the E0010 of the function");
        assert_eq!(fixes_of(d), fixes, "{function}: the candidates that fit: {d}");
        let notes = notes_of(d);
        let deep = notes.iter().any(|n| n.contains("deeper than the limit") && n.contains("`let`"));
        assert!(deep, "{function}: the note of the reading over the limit: {notes:?}");
    }
}

#[test]
fn a_brace_after_a_named_handler_notes_where_the_body_of_a_handler_in_place_goes() {
    // §8.3, S-480: on the line, in brackets on the next line, with arguments or not, the E0002 of
    // the `{` notes that a named handler has no body and that the body follows the name of an effect.
    for path in [
        "negative/handler_name_brace_same_line.onsa",
        "negative/handler_name_brace_in_parens.onsa",
        "negative/handler_name_brace_next_line.onsa",
        "negative/handler_name_brace_next_line_args.onsa",
    ] {
        for d in of_code(path, "E0002") {
            let notes = notes_of(&d);
            let noted = notes.iter().any(|n| n.contains("named handler") && n.contains("name of an effect"));
            assert!(noted, "{path}: the note of the named handler: {d}");
        }
    }
}
