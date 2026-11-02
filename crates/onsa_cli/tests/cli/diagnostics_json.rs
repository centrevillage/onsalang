//! The JSON form of a diagnostic, of a fix candidate and of a note (spec §18.1, R-87 (1)(2), S-81,
//! S-213): the keys of `span`, `end_line` always, columns in characters, a candidate with `title`
//! and `edits`, an insertion as a replacement of an empty range, `notes` as a list whose elements
//! have a `message` and a `span` only when they have a position. The text a candidate gives is
//! checked by applying its edits to the source, so the tests do not depend on which tokens an edit
//! covers.
//!
//! The document around the diagnostics (one object, the `diagnostics` array, the order, the file
//! names) is in check_json_document.rs (S-215, S-234). The reader below takes the `diagnostics`
//! array of that one object and nothing else.

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_diag_json_{}_{tag}", std::process::id()));
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

/// The `diagnostics` array of the document `onsa check --json <paths>` prints (§18.1: the output
/// is one JSON object).
fn check_json(paths: &[&str]) -> Vec<Value> {
    let mut args = vec!["check", "--json"];
    args.extend_from_slice(paths);
    let out = Command::new(ONSA).args(&args).output().expect("run onsa");
    let code = out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"));
    assert!(code == 1, "onsa {args:?}: exit code {code} (stderr: {})", String::from_utf8_lossy(&out.stderr));
    let text = String::from_utf8(out.stdout).expect("utf-8 output");
    let doc: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("not one JSON value ({e}): {text:?}"));
    doc.get("diagnostics")
        .unwrap_or_else(|| panic!("no `diagnostics` in the document: {doc}"))
        .as_array()
        .unwrap_or_else(|| panic!("`diagnostics` is not an array: {doc}"))
        .clone()
}

fn code_of(d: &Value) -> &str {
    d["code"].as_str().expect("`code` is a string")
}

fn by_code<'a>(ds: &'a [Value], code: &str) -> Vec<&'a Value> {
    ds.iter().filter(|d| code_of(d) == code).collect()
}

/// The candidates of a diagnostic. `fixes` is always there, an empty array when there is none (§18.1).
fn fixes_of(d: &Value) -> Vec<&Value> {
    d.get("fixes")
        .unwrap_or_else(|| panic!("{}: no `fixes` (it is written out even when empty): {d}", code_of(d)))
        .as_array()
        .expect("`fixes` is an array")
        .iter()
        .collect()
}

/// The notes of a diagnostic. `notes` is always there, an empty array when there is none (§18.1).
fn notes_of(d: &Value) -> Vec<&Value> {
    d.get("notes")
        .unwrap_or_else(|| panic!("{}: no `notes` (it is written out even when empty): {d}", code_of(d)))
        .as_array()
        .expect("`notes` is an array")
        .iter()
        .collect()
}

/// A span: file, 1-based line and column, `end_line` and `end_col` (the end is exclusive).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Span {
    file: String,
    line: usize,
    col: usize,
    end_line: usize,
    end_col: usize,
}

/// Reads a `span` object. Fails, naming the missing key, when one of the five keys is absent:
/// `end_line` is always there (§18.1), also for a one-line span.
fn span_of(v: &Value, what: &str) -> Span {
    let o = v.as_object().unwrap_or_else(|| panic!("{what}: `span` is not an object: {v}"));
    let int = |k: &str| -> usize {
        let x = o.get(k).unwrap_or_else(|| panic!("{what}: `span` has no `{k}`: {v}"));
        let n = x.as_u64().unwrap_or_else(|| panic!("{what}: `span.{k}` is not a non-negative integer: {v}"));
        usize::try_from(n).unwrap()
    };
    let file = o
        .get("file")
        .and_then(Value::as_str)
        .unwrap_or_else(|| panic!("{what}: `span.file` is not a string: {v}"))
        .to_string();
    let s = Span { file, line: int("line"), col: int("col"), end_line: int("end_line"), end_col: int("end_col") };
    assert!(
        s.line >= 1 && s.col >= 1 && s.end_line >= 1 && s.end_col >= 1,
        "{what}: lines and columns count from 1: {v}"
    );
    assert!((s.end_line, s.end_col) >= (s.line, s.col), "{what}: the end is before the start: {v}");
    s
}

/// One edit of a candidate: a span and the string that replaces it.
struct Edit {
    span: Span,
    replace: String,
}

fn edits_of(fix: &Value, what: &str) -> Vec<Edit> {
    let title = fix.get("title").unwrap_or_else(|| panic!("{what}: a candidate has no `title`: {fix}"));
    assert!(title.as_str().is_some_and(|t| !t.is_empty()), "{what}: `title` is a non-empty string: {fix}");
    let edits = fix
        .get("edits")
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("{what}: a candidate has no `edits` array: {fix}"));
    assert!(!edits.is_empty(), "{what}: a candidate with no edit: {fix}");
    edits
        .iter()
        .map(|e| {
            let span = span_of(e.get("span").unwrap_or_else(|| panic!("{what}: an edit has no `span`: {e}")), what);
            let replace = e
                .get("replace")
                .and_then(Value::as_str)
                .unwrap_or_else(|| panic!("{what}: an edit has no `replace` string: {e}"))
                .to_string();
            Edit { span, replace }
        })
        .collect()
}

/// The byte offset of the (1-based line, 1-based column in characters) position in `text`.
fn offset(text: &str, line: usize, col: usize) -> usize {
    let mut start = 0;
    for _ in 1..line {
        start += text[start..].find('\n').expect("a line past the end of the file") + 1;
    }
    let rest = &text[start..];
    let line_len = rest.find('\n').unwrap_or(rest.len());
    let mut chars = rest[..line_len].char_indices();
    match chars.nth(col - 1) {
        Some((i, _)) => start + i,
        None => {
            assert_eq!(rest[..line_len].chars().count() + 1, col, "a column past the end of line {line}");
            start + line_len
        }
    }
}

/// Applies edits (all in one file) to `text` at once. The ranges must not overlap.
fn apply(text: &str, edits: &[&Edit]) -> String {
    let mut spans: Vec<(usize, usize, &str)> = edits
        .iter()
        .map(|e| {
            (offset(text, e.span.line, e.span.col), offset(text, e.span.end_line, e.span.end_col), e.replace.as_str())
        })
        .collect();
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

/// The source after applying candidate `k` (0-based) of diagnostic `d` to the one file `path`.
fn after(d: &Value, k: usize, path: &str, text: &str) -> String {
    let fixes = fixes_of(d);
    let fix = fixes.get(k).unwrap_or_else(|| panic!("{}: no candidate {k}: {d}", code_of(d)));
    let edits = edits_of(fix, code_of(d));
    for e in &edits {
        assert!(
            std::path::Path::new(&e.span.file).file_name() == std::path::Path::new(path).file_name(),
            "an edit in another file: {}",
            e.span.file
        );
    }
    apply(text, &edits.iter().collect::<Vec<_>>())
}

fn replace_line(text: &str, line: usize, new: &str) -> String {
    let mut lines: Vec<&str> = text.split('\n').collect();
    lines[line - 1] = new;
    lines.join("\n")
}

/// One diagnostic of each of E0713, E0714, E0010, E0020 and E0320, in one-line spans. E0713,
/// E0714, E0020 and E0320 have one candidate. The text of the candidates of E0010 is in
/// tests/spec/fixes/e0010_candidates.onsa.
const MIXED: &str = "\
pub struct Pt {
  x: U32,
}

impl Pt {
  pub fn norm(self) -> U32 { self.x }
  pub fn scale(inout self, k: U32) { self.x = self.x * k }
}

pub fn missing_bang(inout p: Pt) {
  p.scale(2)
}

pub fn extra_bang(p: Pt) -> U32 {
  p.norm!()
}

pub fn mixed(a: U32, b: U32, c: U32) -> U32 {
  a < b < c
}

pub fn lower(x: i32) -> I32 {
  x
}

pub fn BadName() -> I32 {
  1
}
";

#[test]
fn a_span_has_file_line_col_end_line_end_col() {
    let d = Dir::new("keys");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    let codes: Vec<&str> = ds.iter().map(code_of).collect();
    for want in ["E0713", "E0714", "E0010", "E0020", "E0320"] {
        assert!(codes.contains(&want), "no {want} in {codes:?}");
    }
    for diag in &ds {
        let what = code_of(diag);
        let s = span_of(diag.get("span").unwrap_or_else(|| panic!("{what}: no `span`: {diag}")), what);
        assert!(s.file.ends_with("mixed.onsa"), "{what}: `span.file` is the file: {}", s.file);
        for fix in fixes_of(diag) {
            for e in edits_of(fix, what) {
                assert!(e.span.file.ends_with("mixed.onsa"), "{what}: an edit's `span.file`: {}", e.span.file);
            }
        }
    }
}

#[test]
fn end_line_is_there_for_a_one_line_span() {
    let d = Dir::new("end_line");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    for code in ["E0713", "E0714", "E0020", "E0320"] {
        let found = by_code(&ds, code);
        assert_eq!(found.len(), 1, "{code}");
        let s = span_of(&found[0]["span"], code);
        assert_eq!(s.end_line, s.line, "{code}: the span of one token stays on its line: {}", found[0]["span"]);
        assert!(s.end_col > s.col, "{code}: a token is not an empty range: {}", found[0]["span"]);
    }
}

#[test]
fn a_candidate_has_title_and_edits_with_a_span_and_replace() {
    let d = Dir::new("shape");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    let mut seen = 0;
    for diag in &ds {
        for fix in fixes_of(diag) {
            let _ = edits_of(fix, code_of(diag)); // title, edits, and in each edit span and replace
            let keys: Vec<&String> = fix.as_object().unwrap().keys().collect();
            assert!(
                !keys.iter().any(|k| ["replace", "insert_before", "insert_after"].contains(&k.as_str())),
                "{}: the old shape of a candidate: {fix}",
                code_of(diag)
            );
            seen += 1;
        }
    }
    assert!(seen >= 4, "too few candidates to say anything: {seen}");
}

#[test]
fn the_candidates_give_the_text_the_spec_describes() {
    let d = Dir::new("apply");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    // (code, the line of the file that changes, the line after applying the candidate)
    let cases = [
        ("E0713", 11, "  p.scale!(2)"),
        ("E0714", 15, "  p.norm()"),
        ("E0020", 22, "pub fn lower(x: I32) -> I32 {"),
        ("E0320", 26, "pub fn bad_name() -> I32 {"),
    ];
    for (code, line, new_line) in cases {
        let found = by_code(&ds, code);
        assert_eq!(found.len(), 1, "{code}");
        let fixes = fixes_of(found[0]);
        assert!(!fixes.is_empty(), "{code} has no candidate");
        let got = after(found[0], 0, &path, MIXED);
        // E0320 has one candidate that also renames the uses (S-82); this file has none
        let want = replace_line(MIXED, line, new_line);
        assert_eq!(got, want, "{code}: the first candidate");
    }
}

#[test]
fn an_insertion_is_a_replacement_of_an_empty_range() {
    let d = Dir::new("insertion");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    let found = by_code(&ds, "E0713");
    assert_eq!(found.len(), 1);
    let fixes = fixes_of(found[0]);
    assert_eq!(fixes.len(), 1, "E0713 has one candidate (§5.2)");
    let edits = edits_of(fixes[0], "E0713");
    assert_eq!(edits.len(), 1);
    let e = &edits[0];
    assert_eq!(e.replace, "!", "the candidate inserts the `!`");
    assert_eq!(
        (e.span.line, e.span.col),
        (e.span.end_line, e.span.end_col),
        "an insertion is an empty range: {:?}",
        e.span
    );
}

#[test]
fn columns_count_characters_and_not_bytes_or_utf16_units() {
    // Twelve code points that are 4 bytes in UTF-8 and 2 units in UTF-16, in a string literal before
    // the diagnostic on the same line.
    let emoji = "😀".repeat(12);
    let src = format!("pub fn f(xs: Span[F32]) -> U32 {{\n  let n = \"{emoji}\".len() + xs.len!()\n  n\n}}\n");
    let d = Dir::new("columns");
    let path = d.file("wide.onsa", &src);
    let ds = check_json(&[&path]);
    let found = by_code(&ds, "E0714");
    assert_eq!(found.len(), 1, "{ds:?}");
    // `  let n = "` is 11 characters (the quote is column 11), then 12 emoji, then `".len() + ` is 11
    // more: `xs` starts at column 34 and `xs.len!()` ends before column 43. In bytes the column
    // would be 70 or more, in UTF-16 units 46 or more.
    let s = span_of(&found[0]["span"], "E0714");
    assert_eq!(s.line, 2);
    assert!((34..=42).contains(&s.col), "column {} is not in characters: {}", s.col, found[0]["span"]);
    assert!(s.end_col <= 43, "end_col {} is not in characters", s.end_col);
    let got = after(found[0], 0, &path, &src);
    assert_eq!(got, src.replace("xs.len!()", "xs.len()"), "the candidate removes the `!`");
}

#[test]
fn a_candidate_that_joins_two_lines_is_a_range_over_two_lines_and_gives_the_joined_text() {
    // E0003: `else` on the line after `}` (§2.5). The candidate moves it to the previous line,
    // so the fixed text has `} else {` on one line.
    let src = "pub fn choose(c: Bool) -> I32 {\n  if c { 1 }\n  else { 2 }\n}\n";
    let d = Dir::new("join");
    let path = d.file("else.onsa", src);
    let ds = check_json(&[&path]);
    let found = by_code(&ds, "E0003");
    assert_eq!(found.len(), 1, "{ds:?}");
    let s = span_of(&found[0]["span"], "E0003");
    assert!(s.line >= 1 && s.end_line >= s.line);
    let got = after(found[0], 0, &path, src);
    let squeezed: String = got.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(squeezed, "pub fn choose(c: Bool) -> I32 { if c { 1 } else { 2 } }");
    let line = got.lines().find(|l| l.contains("if c")).expect("the `if` line");
    assert!(line.contains("else"), "`else` is on the line of the `}}`: {got:?}");
}

#[test]
fn spans_of_a_diagnostic_that_covers_several_lines_end_on_the_later_line() {
    // Any diagnostic whose range crosses a line break keeps `end_line` and `end_col` consistent:
    // the end is after the start, `end_col` is a column of `end_line`. The corpus is the files
    // below; the test does not say which diagnostic covers several lines.
    let d = Dir::new("multi");
    let src = "pub fn choose(c: Bool) -> I32 {\n  if c { 1 }\n  else { 2 }\n}\n";
    let path = d.file("else.onsa", src);
    let ds = check_json(&[&path]);
    assert!(!ds.is_empty());
    for diag in &ds {
        let s = span_of(&diag["span"], code_of(diag));
        let lines: Vec<&str> = src.split('\n').collect();
        let end_len = lines[s.end_line - 1].chars().count();
        assert!(s.end_col <= end_len + 1, "end_col is past the end of line {}: {}", s.end_line, diag["span"]);
        for fix in fixes_of(diag) {
            for e in edits_of(fix, code_of(diag)) {
                let l = lines[e.span.end_line - 1].chars().count();
                assert!(e.span.end_col <= l + 1, "an edit ends past the end of its line: {:?}", e.span);
            }
        }
    }
}

#[test]
fn a_diagnostic_without_a_candidate_has_an_empty_fixes_array() {
    let d = Dir::new("nofix");
    let path = d.file("nofix.onsa", "pub fn f() -> I32 {\n  1 $ 2\n}\n");
    let ds = check_json(&[&path]);
    let found = by_code(&ds, "E0001");
    assert_eq!(found.len(), 1, "{ds:?}");
    assert_eq!(found[0].get("fixes"), Some(&Value::Array(vec![])), "E0001 has no candidate: {}", found[0]);
}

#[test]
fn the_edits_of_two_candidates_of_different_diagnostics_are_independent() {
    // Applying the first candidate of every diagnostic at once gives a file where each line has
    // its own change (the case runner of tests/spec applies them the same way).
    let d = Dir::new("all");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    let mut edits: Vec<Edit> = Vec::new();
    for diag in &ds {
        if let Some(fix) = fixes_of(diag).first() {
            edits.extend(edits_of(fix, code_of(diag)));
        }
    }
    let refs: Vec<&Edit> = edits.iter().collect();
    let got = apply(MIXED, &refs); // fails on an overlap
    assert!(got.contains("p.scale!(2)") && got.contains("p.norm()") && got.contains("x: I32"), "{got}");
}

// ---- notes (S-213) ---------------------------------------------------------------------------------

/// A note: `message` always, a `span` (the same five keys as a diagnostic's) only when it has a
/// position. A note with no position has no `span` key, and never `"span": null`.
fn note_span(n: &Value, what: &str) -> Option<Span> {
    let msg = n.get("message").and_then(Value::as_str);
    assert!(msg.is_some_and(|m| !m.is_empty()), "{what}: a note has a non-empty `message` string: {n}");
    match n.get("span") {
        None => None,
        Some(s) => {
            assert!(!s.is_null(), "{what}: `\"span\": null` (a note with no position has no `span` key): {n}");
            Some(span_of(s, what))
        }
    }
}

/// E0020 for a `;` (§2.5, §18.1): the correct rule goes in a note, and that note has no position.
#[test]
fn a_note_that_explains_a_rule_has_a_message_and_no_span() {
    let d = Dir::new("note_rule");
    let path = d.file("semi.onsa", "pub fn g() -> I32 {\n  let a = 1;\n  a\n}\n");
    let ds = check_json(&[&path]);
    let found = by_code(&ds, "E0020");
    assert_eq!(found.len(), 1, "{ds:?}");
    let notes = notes_of(found[0]);
    assert!(!notes.is_empty(), "E0020 shows the rule in a note (§18.1): {}", found[0]);
    for n in notes {
        assert!(note_span(n, "E0020").is_none(), "the rule note has no position: {n}");
        assert!(n.get("span").is_none(), "no `span` key at all: {n}");
    }
}

/// E0304 for a name declared twice (§5.1; §11.2 gives the same rule for E0305): the later
/// declaration gets the diagnostic and the earlier one is shown by a note, with a position.
#[test]
fn a_note_that_points_at_a_place_has_a_message_and_a_full_span() {
    let d = Dir::new("note_place");
    let path = d.file("dup.onsa", "pub fn twice() -> I32 {\n  1\n}\n\npub fn twice() -> I32 {\n  2\n}\n");
    let ds = check_json(&[&path]);
    let found = by_code(&ds, "E0304");
    assert_eq!(found.len(), 1, "{ds:?}");
    let main = span_of(&found[0]["span"], "E0304");
    assert_eq!(main.line, 5, "the later declaration gets the diagnostic");
    let notes = notes_of(found[0]);
    let placed: Vec<Span> = notes.iter().filter_map(|n| note_span(n, "E0304")).collect();
    assert!(!placed.is_empty(), "the earlier declaration is shown by a note with a position: {}", found[0]);
    let first =
        placed.iter().find(|s| s.line == 1).unwrap_or_else(|| panic!("no note at the first declaration: {placed:?}"));
    assert_eq!(first.file, main.file, "a note's `span.file` has the form of the diagnostic's");
    assert!(first.file.ends_with("dup.onsa"), "the note's `span.file` is the file: {}", first.file);
    assert!(
        (first.col, first.end_col) == (8, 13) && first.end_line == 1,
        "the note covers the name `twice`: {first:?}"
    );
}

#[test]
fn every_note_of_every_diagnostic_has_a_message_and_a_span_or_no_span_key() {
    let d = Dir::new("notes_all");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    assert!(ds.len() >= 5);
    for diag in &ds {
        for n in notes_of(diag) {
            let _ = note_span(n, code_of(diag));
        }
    }
}

#[test]
fn a_diagnostic_with_no_note_has_an_empty_notes_array() {
    // The diagnostics of E0713 and E0714 say what is wrong in the message and give the fix in the
    // candidate. At least one diagnostic of MIXED has nothing to add in a note, and its `notes` is `[]`.
    let d = Dir::new("notes_empty");
    let path = d.file("mixed.onsa", MIXED);
    let ds = check_json(&[&path]);
    assert!(
        ds.iter().any(|x| x.get("notes") == Some(&Value::Array(vec![]))),
        "no diagnostic whose `notes` is `[]` and written out: {ds:?}"
    );
}
