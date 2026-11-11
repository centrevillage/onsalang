//! The note of a clock on the binding side of a `let` or `var` whose value is `move a` in a flow
//! body (W5-24 U7a, S-381, spec §11.3, §5.2), which the case files cannot pin (the runner of the
//! cases does not compare notes): no parentheses hold `move a`, so no candidate moves the clock
//! onto the value, and the E0002 notes the rule (the clock goes after the whole value, and a `move`
//! value has no place for one).
//!
//! The input is the case file `tests/spec/negative/clock_on_binding_move_flow.onsa` (read where it
//! is, nothing written); the test checks that the note is there and the words that tell what it
//! shows, not its whole text, which the spec does not fix. The expectations are those of the test
//! work (W5-24 U7/t, its table of the notes).

use crate::test_support::{check, code_of};
use serde_json::Value;

fn notes_of(d: &Value) -> Vec<String> {
    d.get("notes")
        .and_then(Value::as_array)
        .map(|a| a.iter().map(|n| n["message"].as_str().unwrap_or("").to_string()).collect())
        .unwrap_or_default()
}

#[test]
fn a_clock_on_the_binding_of_a_move_value_in_a_flow_notes_the_rule_and_has_no_candidate() {
    let path = format!("{}/../../tests/spec/negative/clock_on_binding_move_flow.onsa", env!("CARGO_MANIFEST_DIR"));
    let diags: Vec<Value> = check(&path).into_iter().filter(|d| code_of(d) == "E0002").collect();
    // The five flows: no type, a type after the clock, a type before it, a pattern, a `var`.
    assert_eq!(diags.len(), 5, "one E0002 per flow: {diags:?}");
    for d in &diags {
        assert!(d.get("fixes").and_then(Value::as_array).is_none_or(Vec::is_empty), "no candidate: {d}");
        let notes = notes_of(d);
        let rule = notes.iter().any(|n| n.contains("value") && n.contains("at sample"));
        let moved = notes.iter().any(|n| n.contains("`move`") && n.contains("(move a)") && n.contains("§5.2"));
        assert!(rule && moved, "the note of the clock on the value and of the `move` value: {notes:?}");
    }
}
