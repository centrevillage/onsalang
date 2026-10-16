//! Empty brackets and the tuple index with a leading zero (spec §2.4, §2.5, §18.1, §18.2; S-513,
//! S-508): what the case files in `tests/spec/` cannot say (W3-13/t, unit 2).
//!
//! The case files pin the diagnostics and the text after each candidate: `fixes/empty_brackets_decls.onsa`,
//! `fixes/empty_brackets_uses.onsa`, `fixes/empty_brackets_pkg/` (E0002 with one candidate),
//! `fixes/tuple_index_leading_zero.onsa` (E0020), `negative/tuple_index_not_decimal.onsa` (E0002) and the
//! forms that are read (`fn/empty_brackets_valid.onsa`, `effects/empty_brackets_valid.onsa`,
//! `values/tuple_index_forms.onsa`). These tests say the rest:
//!
//! - the forms that a case file cannot hold because the declaration is not in this version (a trait, a
//!   trait method, `impl[] T for S`, an `extern` function: E0200 is a later stage, so a file that holds
//!   them has errors that a case file does not mark), with one candidate that takes the brackets out;
//! - the brackets with a comment inside have no candidate and a note (§2.5), where a case file would have
//!   to guess the line of the main position;
//! - what is left after the candidate of `Some()` (E0412, §2.5);
//! - a blank before empty brackets (two errors: the blank's E0020 first), and a word right after the
//!   brackets that stays a word of its own (§18.1);
//! - `onsa fmt` does not write a file with empty brackets or a tuple index with a leading zero, and
//!   exits with 2 (§18.2), with `--check` too, and the file next to it is written (docs/onsa-tools.md §3.1).
//!
//! Every test uses only the binary. Expected texts are written from the spec; none is taken from the
//! output of the compiler. The tests were written before the syntax of W3-13: those that fail until it
//! (the compiler reads these forms as before) run ignored until W3-13/i.

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_empty_brackets_{}_{tag}", std::process::id()));
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

fn onsa(args: &[&str]) -> Output {
    Command::new(ONSA).args(args).output().expect("run onsa")
}

fn code(out: &Output) -> i32 {
    out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"))
}

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// The diagnostics of `onsa check --json <path>` (exit code 0 or 1).
fn check(path: &str) -> Vec<Value> {
    let out = onsa(&["check", "--json", path]);
    let c = code(&out);
    assert!(c == 0 || c == 1, "onsa check {path}: exit code {c} (stderr: {})", String::from_utf8_lossy(&out.stderr));
    let text = String::from_utf8(out.stdout).expect("utf-8 output");
    let v: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("no JSON ({e}): {text}"));
    v["diagnostics"].as_array().unwrap_or_else(|| panic!("no `diagnostics` array: {v}")).clone()
}

fn code_of(d: &Value) -> &str {
    d["code"].as_str().expect("`code` is a string")
}

fn fixes_of(d: &Value) -> Vec<&Value> {
    d.get("fixes").and_then(Value::as_array).map(|a| a.iter().collect()).unwrap_or_default()
}

fn notes_of(d: &Value) -> Vec<&Value> {
    d.get("notes").and_then(Value::as_array).map(|a| a.iter().collect()).unwrap_or_default()
}

/// One edit: a range as (line, column, end line, end column), 1-based, columns in characters.
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

/// The byte offset of a (line, column in characters) position of `text`.
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
    for w in spans.windows(2) {
        assert!(w[0].1 <= w[1].0, "edits of one candidate overlap: {:?} and {:?}", w[0], w[1]);
    }
    let mut out = text.to_string();
    for &(a, b, r) in spans.iter().rev() {
        out.replace_range(a..b, r);
    }
    out
}

fn codes(ds: &[Value]) -> Vec<&str> {
    ds.iter().map(code_of).collect()
}

// ---- the candidate of the forms that a case file cannot hold ----------------------------------

/// (what the case says, the file as written, the file after the one candidate). One E0002 in each file,
/// the one candidate takes out the brackets from the opening one to the closing one (§2.5).
const CANDIDATES: &[(&str, &str, &str)] = &[
    (
        "the type parameters of a trait",
        "pub trait T[] {\n  fn value(self) -> I32\n}\n",
        "pub trait T {\n  fn value(self) -> I32\n}\n",
    ),
    (
        "the type parameters of an impl of a trait",
        "pub struct S {\n  n: I32,\n}\n\npub trait T {\n  fn value(self) -> I32\n}\n\nimpl[] T for S {\n  fn value(self) -> I32 {\n    self.n\n  }\n}\n",
        "pub struct S {\n  n: I32,\n}\n\npub trait T {\n  fn value(self) -> I32\n}\n\nimpl T for S {\n  fn value(self) -> I32 {\n    self.n\n  }\n}\n",
    ),
    (
        "the type parameters of a method of a trait",
        "pub trait T {\n  fn value[](self) -> I32\n}\n",
        "pub trait T {\n  fn value(self) -> I32\n}\n",
    ),
    (
        "the type parameters of a method of a trait that has a body",
        "pub trait T {\n  fn value[](self) -> I32 {\n    1\n  }\n}\n",
        "pub trait T {\n  fn value(self) -> I32 {\n    1\n  }\n}\n",
    ),
    (
        "the type parameters of an extern function",
        "extern \"C\" lib \"fastconv\" {\n  fn fc_scale[](x: I32) -> I32\n}\n",
        "extern \"C\" lib \"fastconv\" {\n  fn fc_scale(x: I32) -> I32\n}\n",
    ),
    (
        "the type parameters of an extern function that is rt",
        "extern \"C\" lib \"fastconv\" {\n  rt fn fc_scale[](x: I32) -> I32\n}\n",
        "extern \"C\" lib \"fastconv\" {\n  rt fn fc_scale(x: I32) -> I32\n}\n",
    ),
    (
        "the type parameters of the impl of a trait, with a space",
        "pub struct S {\n  n: I32,\n}\n\npub trait T {\n  fn value(self) -> I32\n}\n\nimpl[ ] T for S {\n  fn value(self) -> I32 {\n    self.n\n  }\n}\n",
        "pub struct S {\n  n: I32,\n}\n\npub trait T {\n  fn value(self) -> I32\n}\n\nimpl T for S {\n  fn value(self) -> I32 {\n    self.n\n  }\n}\n",
    ),
    (
        // §18.1: the reading outside the edit stays; `implT` would be one name (fixes/empty_brackets_joined.onsa).
        "the type parameters of the impl of a trait, right before its name",
        "pub struct S {\n  n: I32,\n}\n\npub trait T {\n  fn value(self) -> I32\n}\n\nimpl[]T for S {\n  fn value(self) -> I32 {\n    self.n\n  }\n}\n",
        "pub struct S {\n  n: I32,\n}\n\npub trait T {\n  fn value(self) -> I32\n}\n\nimpl T for S {\n  fn value(self) -> I32 {\n    self.n\n  }\n}\n",
    ),
];

#[test]
fn a_blank_before_empty_brackets_is_the_blank_first() {
    // Two errors (§2.5): the blank before the opener, then the empty brackets. The first in the text
    // is reported (S-281), the E0020 of the blank, with its candidate that takes the blank out; the
    // empty brackets are left for the next round (§18.1 binds a unit's only error alone). The same
    // for a blank before the `.` of a tuple index with a leading zero (§2.4).
    let d = Dir::new("blank");
    for (written, after) in [
        ("pub enum E {\n  A ( ),\n  B,\n}\n", "pub enum E {\n  A( ),\n  B,\n}\n"),
        ("pub fn f() -> I32 {\n  handle { 1 } with h ()\n}\n", "pub fn f() -> I32 {\n  handle { 1 } with h()\n}\n"),
        (
            "pub fn g(o: Option[I32]) -> I32 {\n  match o {\n    Some ( ) => 0,\n    None => 0,\n  }\n}\n",
            "pub fn g(o: Option[I32]) -> I32 {\n  match o {\n    Some( ) => 0,\n    None => 0,\n  }\n}\n",
        ),
        ("pub fn f(t: (I32, I32)) -> I32 {\n  t .01\n}\n", "pub fn f(t: (I32, I32)) -> I32 {\n  t.01\n}\n"),
    ] {
        let ds = check(&d.file("a.onsa", written));
        assert_eq!(codes(&ds), ["E0020"], "{written}");
        let fixes = fixes_of(&ds[0]);
        assert_eq!(fixes.len(), 1, "{written}: {}", ds[0]);
        assert_eq!(apply(written, &edits_of(fixes[0])), after);
    }
}

#[test]
fn the_word_after_the_brackets_of_a_handler_stays_a_word_of_its_own() {
    // `with h()else`: the brackets go, and `else` stays the keyword (not `helse`, §18.1), so the
    // `else` that does not go there is still an error of the syntax stage (the file has two).
    let d = Dir::new("joined");
    let written = "pub fn f() -> I32 {\n  handle { 1 } with h()else\n}\n";
    let ds = check(&d.file("a.onsa", written));
    let e0002: Vec<&Value> = ds.iter().filter(|x| code_of(x) == "E0002").collect();
    assert_eq!(e0002.len(), 1, "one E0002, got {:?}", codes(&ds));
    let fixes = fixes_of(e0002[0]);
    assert_eq!(fixes.len(), 1, "one candidate: {}", e0002[0]);
    let fixed = apply(written, &edits_of(fixes[0]));
    assert_eq!(fixed, "pub fn f() -> I32 {\n  handle { 1 } with h else\n}\n");
    assert!(codes(&check(&d.file("b.onsa", &fixed))).contains(&"E0002"), "the `else` is still an error");
}

#[test]
fn the_forms_of_declarations_that_are_not_in_this_version_have_the_one_candidate() {
    let d = Dir::new("candidates");
    for (what, written, after) in CANDIDATES {
        let path = d.file("a.onsa", written);
        let ds = check(&path);
        let e0002: Vec<&Value> = ds.iter().filter(|x| code_of(x) == "E0002").collect();
        assert_eq!(e0002.len(), 1, "{what}: one E0002, got {:?}", codes(&ds));
        let fixes = fixes_of(e0002[0]);
        assert_eq!(fixes.len(), 1, "{what}: one candidate: {}", e0002[0]);
        let fixed = apply(written, &edits_of(fixes[0]));
        assert_eq!(&fixed, after, "{what}: the text after the candidate");
        // The candidate leaves no error of the syntax stage: no E0002 or E0020 is left (the E0200 of the
        // declarations that are not in this version is a later stage).
        let path2 = d.file("b.onsa", &fixed);
        let left = check(&path2);
        assert!(
            left.iter().all(|x| code_of(x) != "E0002" && code_of(x) != "E0020"),
            "{what}: after the candidate: {:?}",
            codes(&left)
        );
    }
}

// ---- the brackets with a comment inside: no candidate (§2.5) ----------------------------------

/// (what the case says, the file as written). The comment is inside the brackets, so the line has to
/// break (there is no block comment, §2.1). §2.5: no candidate, and a note that says that the brackets
/// are not written. The error is one E0002; the main position is not compared.
const WITH_A_COMMENT: &[(&str, &str)] = &[
    ("a variant, the comment after the opening bracket", "pub enum E {\n  A( // note\n  ),\n  B,\n}\n"),
    ("a variant, the comment on a line of its own", "pub enum E {\n  A(\n    // note\n  ),\n  B,\n}\n"),
    ("a variant, a doc comment of the next variant", "pub enum E {\n  A( // note\n  ),\n  /// The second.\n  B,\n}\n"),
    ("a function's type parameters", "pub fn f[ // note\n]() -> I32 {\n  1\n}\n"),
    ("a function's type parameters, on a line of their own", "pub fn f[\n  // note\n]() -> I32 {\n  1\n}\n"),
    ("a struct's type parameters", "pub struct S[ // note\n] {\n  n: I32,\n}\n"),
    ("an enum's type parameters", "pub enum E[\n  // note\n] {\n  A,\n  B,\n}\n"),
    ("a trait's type parameters", "pub trait T[ // note\n] {\n  fn value(self) -> I32\n}\n"),
    (
        "the type parameters of an impl",
        "pub struct S {\n  n: I32,\n}\n\nimpl[ // note\n] S {\n  pub fn get(self) -> I32 {\n    self.n\n  }\n}\n",
    ),
    (
        "the type parameters of a method",
        "pub struct S {\n  n: I32,\n}\n\nimpl S {\n  pub fn get[ // note\n  ](self) -> I32 {\n    self.n\n  }\n}\n",
    ),
    ("a handler's arguments", "handler h( // note\n): Ask {\n  fn ask() -> I32 { 1 }\n}\n"),
    ("a handler's arguments, on a line of their own", "handler h(\n  // note\n): Ask {\n  fn ask() -> I32 { 1 }\n}\n"),
    ("the arguments of a `with`", "pub fn f() -> I32 {\n  handle { 1 } with h( // note\n  )\n}\n"),
    (
        "the arguments of a `with`, on a line of their own",
        "pub fn f() -> I32 {\n  handle { 1 } with h(\n    // note\n  )\n}\n",
    ),
    (
        "a pattern of a unit variant",
        "pub enum E {\n  A,\n  B(I32),\n}\n\npub fn f(e: E) -> I32 {\n  match e {\n    E.A( // note\n    ) => 1,\n    E.B(n) => n,\n  }\n}\n",
    ),
    (
        "the pattern None",
        "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    None(\n      // note\n    ) => 0,\n    Some(n) => n,\n  }\n}\n",
    ),
    (
        "the pattern Some",
        "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    Some( // note\n    ) => 1,\n    None => 0,\n  }\n}\n",
    ),
];

#[test]
fn brackets_with_a_comment_inside_have_no_candidate_and_a_note() {
    let d = Dir::new("comment");
    for (what, written) in WITH_A_COMMENT {
        let path = d.file("a.onsa", written);
        let ds = check(&path);
        let e0002: Vec<&Value> = ds.iter().filter(|x| code_of(x) == "E0002").collect();
        assert_eq!(e0002.len(), 1, "{what}: one E0002, got {:?}", codes(&ds));
        assert!(fixes_of(e0002[0]).is_empty(), "{what}: no candidate: {}", e0002[0]);
        assert!(!notes_of(e0002[0]).is_empty(), "{what}: a note that says the brackets are not written: {}", e0002[0]);
        assert!(!codes(&ds).contains(&"E0020"), "{what}: no E0020: {:?}", codes(&ds));
    }
}

#[test]
fn a_comment_outside_the_brackets_keeps_the_candidate() {
    // §2.5: only a comment inside the brackets takes the candidate away; a comment after the closing bracket
    // stays where it is when the brackets are taken out.
    let d = Dir::new("outside");
    let written = "pub enum E {\n  A(), // note\n  B,\n}\n\npub fn f[](x: I32) -> I32 { // note\n  x\n}\n";
    let path = d.file("a.onsa", written);
    let ds = check(&path);
    let e0002: Vec<&Value> = ds.iter().filter(|x| code_of(x) == "E0002").collect();
    assert_eq!(e0002.len(), 2, "one E0002 each: {:?}", codes(&ds));
    // §18.1: a candidate is applied alone, so each result keeps the other empty brackets.
    let mut fixed = Vec::new();
    for x in &e0002 {
        let fixes = fixes_of(x);
        assert_eq!(fixes.len(), 1, "one candidate: {x}");
        fixed.push(apply(written, &edits_of(fixes[0])));
    }
    assert!(fixed.iter().any(|f| f.contains("  A, // note\n")), "the comment after `A()` stays: {fixed:?}");
    assert!(
        fixed.iter().any(|f| f.contains("pub fn f(x: I32) -> I32 { // note\n")),
        "the comment after `f[]` stays: {fixed:?}"
    );
}

// ---- what is left after the candidate of `Some()` (§2.5) --------------------------------------

/// The pattern of a variant that has an element, with empty brackets: the candidate takes the brackets
/// out, and the count of the elements (E0412) is what is wrong after it (§2.5).
const WITH_AN_ELEMENT: &[(&str, &str, &str)] = &[
    (
        "Some",
        "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    Some() => 1,\n    None => 0,\n  }\n}\n",
        "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    Some => 1,\n    None => 0,\n  }\n}\n",
    ),
    (
        "a variant of a user's enum",
        "pub enum E {\n  A,\n  B(I32),\n}\n\npub fn f(e: E) -> I32 {\n  match e {\n    E.A => 0,\n    E.B() => 1,\n  }\n}\n",
        "pub enum E {\n  A,\n  B(I32),\n}\n\npub fn f(e: E) -> I32 {\n  match e {\n    E.A => 0,\n    E.B => 1,\n  }\n}\n",
    ),
    (
        "Some inside a tuple",
        "pub fn f(o: Option[I32], n: I32) -> I32 {\n  match (o, n) {\n    (Some(), 0) => 1,\n    _ => 0,\n  }\n}\n",
        "pub fn f(o: Option[I32], n: I32) -> I32 {\n  match (o, n) {\n    (Some, 0) => 1,\n    _ => 0,\n  }\n}\n",
    ),
];

#[test]
fn a_variant_with_an_element_is_left_with_a_count_error_after_the_candidate() {
    let d = Dir::new("count");
    for (what, written, after) in WITH_AN_ELEMENT {
        let path = d.file("a.onsa", written);
        let ds = check(&path);
        assert_eq!(codes(&ds), vec!["E0002"], "{what}: the error is the empty brackets, nothing else");
        let fixes = fixes_of(&ds[0]);
        assert_eq!(fixes.len(), 1, "{what}: one candidate: {}", ds[0]);
        let fixed = apply(written, &edits_of(fixes[0]));
        assert_eq!(&fixed, after, "{what}: the text after the candidate");
        let path2 = d.file("b.onsa", &fixed);
        let left = check(&path2);
        assert!(left.iter().any(|x| code_of(x) == "E0412"), "{what}: E0412 is left: {:?}", codes(&left));
        assert!(
            left.iter().all(|x| code_of(x) != "E0002" && code_of(x) != "E0020"),
            "{what}: no error of the syntax stage is left: {:?}",
            codes(&left)
        );
    }
}

#[test]
fn a_unit_variant_and_none_leave_nothing_after_the_candidate() {
    // The pattern of a unit variant (`E.A()`, `None()`): taking the brackets out gives the pattern that is
    // written right, so the file is clean (§2.5: only a variant that has an element is left with E0412).
    let d = Dir::new("unit");
    let written = "pub enum E {\n  A,\n  B(I32),\n}\n\npub fn f(e: E, o: Option[I32]) -> I32 {\n  let a = match e {\n    E.A() => 1,\n    E.B(n) => n,\n  }\n  a\n}\n\npub fn g(o: Option[I32]) -> I32 {\n  match o {\n    None() => 0,\n    Some(n) => n,\n  }\n}\n";
    let path = d.file("a.onsa", written);
    let ds = check(&path);
    assert_eq!(codes(&ds), vec!["E0002", "E0002"], "two errors, one in each function");
    // Both candidates are applied together: the edits of different candidates do not overlap.
    let mut edits = Vec::new();
    for x in &ds {
        let fixes = fixes_of(x);
        assert_eq!(fixes.len(), 1, "one candidate: {x}");
        edits.extend(edits_of(fixes[0]));
    }
    let fixed = apply(written, &edits);
    assert!(fixed.contains("E.A => 1,") && fixed.contains("None => 0,"), "{fixed}");
    let path2 = d.file("b.onsa", &fixed);
    let left = check(&path2);
    assert!(left.is_empty(), "nothing is left: {:?}", codes(&left));
}

// ---- fmt (§18.2) ------------------------------------------------------------------------------

/// (what the case says, the file as written, the code of the diagnostic that stops `fmt`). A file with a
/// diagnostic of the syntax stage is not written, and `fmt` exits with 2 (§18.2); the diagnostic is on the
/// standard output (docs/onsa-tools.md §3.1, §4).
const STOPS_FMT: &[(&str, &str, &str)] = &[
    ("a variant with empty brackets", "pub enum E {\n  A(),\n  B,\n}\n", "E0002"),
    ("type parameters that are empty", "pub fn f[]() -> I32 {\n  1\n}\n", "E0002"),
    ("a struct with empty type parameters", "pub struct S[] {\n  n: I32,\n}\n", "E0002"),
    (
        "an impl with empty type parameters",
        "pub struct S {\n  n: I32,\n}\n\nimpl[] S {\n  pub fn get(self) -> I32 {\n    self.n\n  }\n}\n",
        "E0002",
    ),
    ("a handler with empty brackets", "handler h(): Ask {\n  fn ask() -> I32 { 1 }\n}\n", "E0002"),
    ("a `with` with empty brackets", "pub fn f() -> I32 {\n  handle { 1 } with h()\n}\n", "E0002"),
    (
        "a pattern with empty brackets",
        "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    None() => 0,\n    Some(n) => n,\n  }\n}\n",
        "E0002",
    ),
    ("empty brackets with a comment inside", "pub enum E {\n  A( // note\n  ),\n  B,\n}\n", "E0002"),
    ("a tuple index with a leading zero", "pub fn f(t: (I32, I32)) -> I32 {\n  t.01\n}\n", "E0020"),
    ("a tuple index of two zeros", "pub fn f(t: (I32, I32)) -> I32 {\n  t.00\n}\n", "E0020"),
    ("a tuple index with a leading zero, nested", "pub fn f(t: ((I32, I32), I32)) -> I32 {\n  t.0.01\n}\n", "E0020"),
    ("a tuple index with a leading zero, assigned", "pub fn f(inout t: (I32, I32)) {\n  t.01 = 1\n}\n", "E0020"),
];

#[test]
fn fmt_does_not_write_a_file_with_empty_brackets_or_a_leading_zero_and_exits_with_2() {
    let d = Dir::new("fmt");
    for (what, written, expected) in STOPS_FMT {
        for args in [&["fmt"][..], &["fmt", "--check"][..]] {
            let path = d.file("a.onsa", written);
            let mut full: Vec<&str> = args.to_vec();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what} ({args:?}): {out:?}");
            assert_eq!(&read(&path), written, "{what} ({args:?}): the file is not written");
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(
                stdout.contains(expected),
                "{what} ({args:?}): the diagnostic {expected} is on the standard output: {out:?}"
            );
        }
    }
}

#[test]
fn fmt_writes_the_files_next_to_a_file_that_it_does_not_write() {
    // docs/onsa-tools.md §3.1: one file with an error of the syntax stage does not stop the others.
    let d = Dir::new("fmt_many");
    let bad = "pub fn f(t: (I32, I32)) -> I32 {\n  t.01\n}\n";
    let bad2 = "pub enum E {\n  A(),\n  B,\n}\n";
    let loose = "pub fn g() -> I32 {\n  1+2\n}\n";
    let p_bad = d.file("bad.onsa", bad);
    let p_bad2 = d.file("bad2.onsa", bad2);
    let p_loose = d.file("loose.onsa", loose);
    let out = onsa(&["fmt", &p_bad, &p_loose, &p_bad2]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(read(&p_bad), bad, "the file with a leading zero is not written");
    assert_eq!(read(&p_bad2), bad2, "the file with empty brackets is not written");
    assert_eq!(read(&p_loose), "pub fn g() -> I32 {\n  1 + 2\n}\n", "the file next to them is written");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("E0020") && stdout.contains("E0002"),
        "both diagnostics are on the standard output: {out:?}"
    );
}

#[test]
fn fmt_keeps_the_brackets_that_mean_something() {
    // §2.5: the empty brackets of a call, a function's arguments and the unit are not touched by `fmt`; the
    // elements of a variant and the type parameters are kept. (A file in the normal form is a fixed point.)
    let d = Dir::new("fmt_keep");
    let text = "pub enum E {\n  A,\n  B(I32),\n}\n\npub fn zero() -> I32 {\n  0\n}\n\npub fn id[T](x: T) -> T {\n  x\n}\n\npub fn run(f: fn() -> I32, u: ()) -> I32 {\n  let g = fn() -> I32 { 1 }\n  zero() + f.() + g.() + id(0)\n}\n";
    let path = d.file("a.onsa", text);
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&path), text, "nothing changes");
    let ds = check(&path);
    assert!(ds.is_empty(), "the file is clean: {:?}", codes(&ds));
}

#[test]
fn a_tuple_index_without_a_leading_zero_is_kept_by_fmt() {
    // §2.4: `t.0`, `t.1`, `t.10` are read (the digits are one index, so `t.10` is not `t.1` and a `0`).
    let d = Dir::new("fmt_index");
    let text = "pub fn f(t: (I32, I32, I32, I32, I32, I32, I32, I32, I32, I32, I32)) -> I32 {\n  t.0 + t.1 + t.10\n}\n";
    let path = d.file("a.onsa", text);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&path), text, "nothing changes");
    let ds = check(&path);
    assert!(ds.is_empty(), "the file is clean: {:?}", codes(&ds));
}
