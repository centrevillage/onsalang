//! What the case files in `tests/spec/` cannot pin about the candidates of a diagnostic (X-6 V/t).
//!
//! The runner of the cases compares the text after a candidate only in the width of a space (a tab and
//! a space are the same), and it tells a diagnostic that has no candidate from one that has only in a
//! case that writes `fixes = 0` (X-15). These tests say both. They do not fix the words of a main message or
//! of a note (the spec does not promise them, S-345).
//!
//! Every test uses only the binary (`onsa check --json`).

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_shapes_{}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// The diagnostics of `onsa check --json <path>` (the exit code is 0 or 1).
fn check(path: &str) -> Vec<Value> {
    let out = Command::new(ONSA).args(["check", "--json", path]).output().expect("run onsa");
    let code = out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"));
    assert!(code == 0 || code == 1, "onsa check {path}: exit code {code}");
    let text = String::from_utf8(out.stdout).expect("utf-8 output");
    let v: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("no JSON ({e}): {text}"));
    match v.get("diagnostics") {
        Some(Value::Array(a)) => a.clone(),
        _ => panic!("the document has no `diagnostics` array: {v}"),
    }
}

fn fixes_of(d: &Value) -> Vec<&Value> {
    match d.get("fixes") {
        None => vec![],
        Some(f) => f.as_array().expect("`fixes` is an array").iter().collect(),
    }
}

/// One edit: a range as (line, column in characters), 1-based, and the new text.
struct Edit {
    start: (usize, usize),
    end: (usize, usize),
    replace: String,
}

fn edits_of(fix: &Value) -> Vec<Edit> {
    let pos = |s: &Value, l: &str, c: &str| -> (usize, usize) {
        let get = |k: &str| usize::try_from(s[k].as_u64().unwrap_or_else(|| panic!("no `{k}` in {s}"))).unwrap();
        (get(l), get(c))
    };
    fix["edits"]
        .as_array()
        .expect("`edits` is an array")
        .iter()
        .map(|e| Edit {
            start: pos(&e["span"], "line", "col"),
            end: pos(&e["span"], "end_line", "end_col"),
            replace: e["replace"].as_str().expect("`replace` is a string").to_string(),
        })
        .collect()
}

fn offset(text: &str, (line, col): (usize, usize)) -> usize {
    let mut start = 0;
    for _ in 1..line {
        start += text[start..].find('\n').expect("a line past the end of the file") + 1;
    }
    let rest = &text[start..];
    let line_len = rest.find('\n').unwrap_or(rest.len());
    match rest[..line_len].char_indices().nth(col - 1) {
        Some((i, _)) => start + i,
        None => start + line_len,
    }
}

fn apply(text: &str, edits: &[Edit]) -> String {
    let mut spans: Vec<(usize, usize, &str)> =
        edits.iter().map(|e| (offset(text, e.start), offset(text, e.end), e.replace.as_str())).collect();
    spans.sort_by_key(|&(a, b, _)| (a, b));
    let mut out = text.to_string();
    for &(a, b, r) in spans.iter().rev() {
        out.replace_range(a..b, r);
    }
    out
}

// ---- the tab of an indent stays a tab (spec §2.1, §2.5, §18.1; the row `block_comment`) --------------

/// The program after the only candidate of the only diagnostic, which is an E0020 of a block comment.
fn after_the_doc_comment_candidate(tag: &str, source: &str) -> String {
    let dir = Dir::new(tag);
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
        let dir = Dir::new(tag);
        let path = dir.file("main.onsa", source);
        let diags = check(&path);
        assert!(!diags.is_empty(), "{tag}: a diagnostic is expected");
        let d = &diags[0];
        assert_eq!(d["code"], "E0002", "{tag}: {d}");
        assert!(fixes_of(d).is_empty(), "{tag}: the diagnostic has a candidate: {d}");
    }
}
