//! What the case files in `tests/spec/` cannot pin about the candidates of a diagnostic (X-6 V/t).
//!
//! The runner of the cases compares the text after a candidate only in the width of a space (a tab and
//! a space are the same), and it tells a diagnostic that has no candidate from one that has only in a
//! case that writes `fixes = 0` (X-15). These tests say both. They do not fix the words of a main message or
//! of a note (the spec does not promise them, S-345).
//!
//! Every test uses only the binary (`onsa check --json`).

use crate::test_support::{Dir, apply, check, edits_of, fixes_of};

// ---- the tab of an indent stays a tab (spec §2.1, §2.5, §18.1; the row `block_comment`) --------------

/// The program after the only candidate of the only diagnostic, which is an E0020 of a block comment.
fn after_the_doc_comment_candidate(tag: &str, source: &str) -> String {
    let dir = Dir::bare(tag);
    let path = dir.file("main.onsa", source);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{tag}: one diagnostic expected, got {diags:?}");
    assert_eq!(diags[0]["code"], "E0020", "{tag}: {}", diags[0]);
    let fixes = fixes_of(&diags[0]);
    assert!(!fixes.is_empty(), "{tag}: a candidate is expected");
    apply(source, &edits_of(fixes[0]))
}

#[test]
fn the_candidate_of_a_doc_block_comment_keeps_the_tab_of_the_indent() {
    // (name, source, the text that must be in the result: the doc line and the member below it)
    let cases: [(&str, &str, &str); 5] = [
        (
            "impl_own_line",
            "pub struct P {\n\tx: I32,\n}\n\nimpl P {\n\t/** d */\n\tpub fn get(self) -> I32 {\n\t\tself.x\n\t}\n}\n",
            "\t/// d\n\tpub fn get",
        ),
        (
            "impl_same_line",
            "pub struct P {\n\tx: I32,\n}\n\nimpl P {\n\t/** d */ pub fn get(self) -> I32 {\n\t\tself.x\n\t}\n}\n",
            "\t/// d\n\tpub fn get",
        ),
        ("field_own_line", "pub struct P {\n\t/** d */\n\tx: I32,\n}\n", "\t/// d\n\tx: I32"),
        ("field_same_line", "pub struct P {\n\t/** d */ x: I32,\n}\n", "\t/// d\n\tx: I32"),
        ("mixed_indent", "pub struct P {\n\t  /** d */ x: I32,\n}\n", "\t  /// d\n\t  x: I32"),
    ];
    for (tag, source, want) in cases {
        let result = after_the_doc_comment_candidate(tag, source);
        assert!(result.contains(want), "{tag}: {want:?} is not in {result:?}");
        assert!(
            result.lines().all(|l| !l.starts_with(' ')),
            "{tag}: a line of the result begins with a space: {result:?}"
        );
    }
}

// ---- a diagnostic with no candidate (spec §18.1; S-251, S-317, S-435) -------------------------------

#[test]
fn these_forms_have_no_candidate() {
    let cases: [(&str, &str); 9] = [
        // the four forms of the reasons that the note says (A26)
        (
            "float_choice_comment",
            "pub fn f(x: F32) -> I32 {\n  match x {\n    1.0 // c\n    | 2.0 => 1,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "range_unreadable_end",
            "pub fn f(x: I32) -> I32 {\n  match x {\n    1..< if x > 0 => 1,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "at_binding_comment",
            "pub fn f(x: I32) -> I32 {\n  match x {\n    k @ (1 | // c\n      2) => k,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "interpolation_and_negated_constant",
            "const LIMIT: I32 = 4\n\npub fn f(t: (Str, I32), n: I32) -> I32 uses {Alloc} {\n  match t {\n    (\"a{n}\", 1) | (\"b\", -LIMIT) => 1,\n    _ => 0,\n  }\n}\n",
        ),
        // an attribute in front of a heading that does not read
        ("attribute_before_a_failed_heading", "#[repr(C)]\npub(crate struct P { x: I32 }\n"),
        // a comment in the parentheses of a derive
        ("derive_comment_in_parentheses", "#[derive(Debug, /* c */ Clone)]\npub struct P { x: I32 }\n"),
        // a block comment after the `@`
        (
            "at_binding_block_comment",
            "pub fn f(x: I32) -> I32 {\n  match x {\n    k @ /* c */ 1 => k,\n    _ => 0,\n  }\n}\n",
        ),
        // the attribute with no declaration at all
        ("attribute_without_a_declaration", "#[inline]\nlet x = 1\n"),
        // a range with a comment in its end
        (
            "range_end_comment",
            "pub fn f(x: I32) -> I32 {\n  match x {\n    1..<(3 + // c\n      1) => 1,\n    _ => 0,\n  }\n}\n",
        ),
    ];
    for (tag, source) in cases {
        let dir = Dir::bare(tag);
        let path = dir.file("main.onsa", source);
        let diags = check(&path);
        assert!(!diags.is_empty(), "{tag}: a diagnostic is expected");
        let d = &diags[0];
        assert_eq!(d["code"], "E0002", "{tag}: {d}");
        assert!(fixes_of(d).is_empty(), "{tag}: the diagnostic has a candidate: {d}");
    }
}
