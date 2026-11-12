//! The notes that decisions of W5-13 U1 add to diagnostics the case files pin (the runner of the
//! cases does not compare notes): S-1005 (§4.2, how a literal is given to a `FixedStr[N]` whose
//! capacity is a parameter), S-908 (§11.6, a type a flow generates implements no trait), S-912
//! (§4.4, the default value of a tuple, an array and `()`) and S-1014 (§15.1, the method form only
//! of a member of the trait before the `.`; `Show` shows an interpolation).
//!
//! The inputs are the case files of `tests/spec/` (read where they are, nothing written); each test
//! checks the words that tell what the note shows, not its whole text, which the spec does not fix.

use crate::test_support::{check, code_of, notes_of, span_of, str_of};
use serde_json::Value;

fn case(path: &str) -> String {
    format!("{}/../../tests/spec/{path}", env!("CARGO_MANIFEST_DIR"))
}

/// The diagnostics of `code` in the case file `path`, `count` of them.
fn of_code(path: &str, code: &str, count: usize) -> Vec<Value> {
    let diags: Vec<Value> = check(&case(path)).into_iter().filter(|d| code_of(d) == code).collect();
    assert_eq!(diags.len(), count, "{path}: the number of {code}: {diags:?}");
    diags
}

/// The messages of the notes of `d`.
fn notes(d: &Value) -> Vec<String> {
    notes_of(d).iter().map(|n| str_of(n, "message").to_string()).collect()
}

fn noted(d: &Value, words: &[&str]) -> bool {
    notes(d).iter().any(|n| words.iter().all(|w| n.contains(w)))
}

#[test]
fn a_literal_of_a_capacity_that_is_a_parameter_notes_an_argument_with_its_own() {
    // S-1005: `u.put_str!("warm")` and a function of two capacities; not the form that makes a
    // `FixedStr[N]` with `put_str!` and compares it with `==`.
    for d in of_code("negative/fixed_str_lit_param_capacity.onsa", "E0401", 6) {
        assert!(noted(&d, &["put_str!(\"warm\")", "const M: U32"]), "{d}");
        assert!(!notes(&d).iter().any(|n| n.contains("==")), "{d}");
    }
}

#[test]
fn a_trait_asked_of_a_generated_type_notes_that_it_has_none() {
    // S-908: the E0401 of an operator and the E0416 of a derive and of a bound.
    let path = "negative/generated_type_traits.onsa";
    for d in of_code(path, "E0401", 2).iter().chain(&of_code(path, "E0416", 2)) {
        assert!(noted(d, &["a flow generates", "no trait", "its fields", "method"]), "{d}");
    }
}

#[test]
fn the_default_of_an_alias_of_a_tuple_notes_a_literal_or_a_parameter() {
    // S-912: `A.default()` of an alias of a tuple, an array and `()`.
    for d in of_code("negative/alias_no_members_default.onsa", "E0302", 3) {
        assert!(noted(&d, &["literal", "T.default()"]), "{d}");
    }
}

#[test]
fn a_dot_after_a_trait_shows_the_method_form_of_a_member_alone() {
    // S-1014 (R-405): `Int.checked_add` is a member of `Int`, `Show` has no members (an
    // interpolation), and `Float.from_bits`, `Dup.dup` and `Copy.copy` are no members. A
    // member that takes no `self` (`Float.PI`, `Num.ZERO`, `Default.default`) has no method
    // form either (§15.1: the method form, and an associated function named after a type).
    let path = "module/dot_after_trait_name.onsa";
    let text = std::fs::read_to_string(case(path)).expect("the case file");
    let diags = of_code(path, "E0308", 12);
    let at = |d: &Value| text.lines().nth(span_of(&d["span"]).line as usize - 1).unwrap_or("").to_string();
    // The forms seen: a method, `Show`, no member, a member that is no method.
    let mut seen = [0; 4];
    for d in &diags {
        let line = at(d);
        let method = notes(d).iter().any(|n| n.contains("a method is called on a value"));
        if line.contains("checked_add") {
            assert!(noted(d, &["x.checked_add("]), "{d}");
            seen[0] += 1;
        } else if line.contains("Show.show") {
            assert!(noted(d, &["\"{x}\""]) && !method, "{d}");
            seen[1] += 1;
        } else if ["from_bits", "Dup.dup", "Copy.copy"].iter().any(|w| line.contains(w)) {
            assert!(!method, "{d}");
            seen[2] += 1;
        } else if ["Float.PI", "Num.ZERO", "Default.default"].iter().any(|w| line.contains(w)) {
            assert!(!method && noted(d, &["named after a type"]), "{d}");
            seen[3] += 1;
        }
    }
    assert_eq!(seen, [5, 1, 3, 3], "the forms of {path}");
}
