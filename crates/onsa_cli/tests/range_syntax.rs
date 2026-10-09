//! The spellings of a range, `a..<b` and `a..=b` (spec §7, §3.1, §18.1, S-257): the diagnostics of
//! the wrong spellings, `onsa fmt` and `onsa diff --ast` on a range, and the closed range that this
//! version reads but does not lower (W3-18/t).
//!
//! The case files in `tests/spec/` pin the code and the line of each diagnostic and the text after
//! each candidate (`fixes/e0020_range_dots.onsa`, `negative/range_outside_header.onsa`,
//! `negative/range_types.onsa`, `negative/range_move.onsa`, `negative/range_inclusive_for_e0200.onsa`),
//! and `docs/foreign-forms.toml` lists the forms of other languages (`range_dots`,
//! `range_outside_header`). These tests say what those cannot: the main span of the E0020 (the range
//! symbol and nothing else), that the edit of a candidate changes that token and no other (S-251), that
//! the diagnostics have a note, that an error outside a header has no candidate and shows
//! `xs.slice(from, to)`, that `fmt` and `diff --ast` stop at the errors of the syntax stage (§18.2),
//! what `fmt` does with the operators in the ends, and that `diff --ast` sees the symbol and the ends.
//!
//! What is not here: the spaces around the range symbol and a line break after it. The spec does not
//! say how `fmt` writes them (§2.5, `docs/onsa-tools.md` §3.2 do not name the range symbols), so no
//! expected text of a file with `0 ..< n` or with the symbol at the end of a line is written (a gap
//! in the report of W3-18/t).
//!
//! Every test uses only the binary (`onsa check`, `onsa fmt`, `onsa diff --ast`, `onsa test`).
//! Expected texts are written from the spec; none is taken from the output of the compiler.
//!
//! The tests that need `..<` ran ignored until W3-18/i (a test cannot be silenced by
//! `tests/pending.toml`); each ignore names the work that removes it.

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_range_{}_{tag}", std::process::id()));
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

/// A function with `header` as the header of a `for` whose body counts the iterations.
fn loop_with(header: &str) -> String {
    format!(
        "pub fn f(n: U32, lo: U32, hi: U32, t: (U32, U32), xs: [F32; 3]) -> U32 {{\n  var c: U32 = 0\n  for _ in {header} {{\n    c = c + 1\n  }}\n  c\n}}\n"
    )
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

/// The only diagnostic of `diags`, which must have the code `want`.
fn expect_one<'a>(diags: &'a [Value], want: &str, what: &str) -> &'a Value {
    assert_eq!(diags.len(), 1, "{what}: one diagnostic: {diags:?}");
    assert_eq!(code_of(&diags[0]), want, "{what}: {}", diags[0]);
    &diags[0]
}

/// A position as (line, column), 1-based, columns in characters.
type Pos = (usize, usize);

struct Edit {
    start: Pos,
    end: Pos,
    replace: String,
}

fn span_of(d: &Value) -> (Pos, Pos) {
    let s = &d["span"];
    let get = |k: &str| usize::try_from(s[k].as_u64().unwrap_or_else(|| panic!("no `{k}` in {s}"))).unwrap();
    ((get("line"), get("col")), (get("end_line"), get("end_col")))
}

fn edits_of(fix: &Value) -> Vec<Edit> {
    fix["edits"]
        .as_array()
        .expect("`edits` is an array")
        .iter()
        .map(|e| {
            let s = &e["span"];
            let get = |k: &str| usize::try_from(s[k].as_u64().unwrap_or_else(|| panic!("no `{k}` in {s}"))).unwrap();
            Edit {
                start: (get("line"), get("col")),
                end: (get("end_line"), get("end_col")),
                replace: e["replace"].as_str().expect("`replace` is a string").to_string(),
            }
        })
        .collect()
}

/// The byte offset of a (line, column in characters) position of `text`.
fn offset(text: &str, (line, col): Pos) -> usize {
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

// ---- E0020: `..` and `...` in a header (§7, §18.1) ------------------------------------------------

/// (what the case says, the header of the `for`, the wrong symbol in it, the header with `..<`,
/// the header with `..=`). The candidates are `a..<b` first and `a..=b` second (§7, §18.1).
const WRONG_SYMBOLS: &[(&str, &str, &str, &str, &str)] = &[
    ("two dots", "0..n", "..", "0..<n", "0..=n"),
    ("three dots", "0...n", "...", "0..<n", "0..=n"),
    ("an end that is a sum", "0..n + 1", "..", "0..<n + 1", "0..=n + 1"),
    ("the ends are sums", "lo + 1..hi * 2", "..", "lo + 1..<hi * 2", "lo + 1..=hi * 2"),
    ("three dots and sums", "lo + 1...hi - 1", "...", "lo + 1..<hi - 1", "lo + 1..=hi - 1"),
    ("names", "lo..hi", "..", "lo..<hi", "lo..=hi"),
    ("a signed start", "-2..2", "..", "-2..<2", "-2..=2"),
    ("hexadecimal ends", "0x10..0x14", "..", "0x10..<0x14", "0x10..=0x14"),
    ("tuple fields", "t.0..t.1", "..", "t.0..<t.1", "t.0..=t.1"),
    ("a call in the end", "0..xs.len()", "..", "0..<xs.len()", "0..=xs.len()"),
];

#[test]
fn a_wrong_symbol_is_e0020_at_the_symbol_with_two_candidates_that_change_only_it() {
    // §18.1: the main span is the foreign form, here the one token; the candidates are the two readings
    // of the writer, `a..<b` first; the edit is the least one that changes the token (S-251), so the
    // ends, the operators and the spaces are the writer's. A note shows the rule.
    let d = Dir::new("wrong");
    for (what, header, symbol, with_lt, with_eq) in WRONG_SYMBOLS {
        let src = loop_with(header);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0020", what);
        let at = src.find(symbol).expect("the symbol is in the source");
        let line = 1 + src[..at].matches('\n').count();
        let col = 1 + src[src[..at].rfind('\n').map_or(0, |i| i + 1)..at].chars().count();
        let (start, end) = span_of(diag);
        assert_eq!(start, (line, col), "{what}: the span starts at the symbol: {diag}");
        assert_eq!(end, (line, col + symbol.len()), "{what}: the span ends with the symbol: {diag}");
        assert_eq!(diag["found"].as_str(), Some(*symbol), "{what}: `found` is the symbol: {diag}");
        let fixes = fixes_of(diag);
        assert_eq!(fixes.len(), 2, "{what}: two candidates, `..<` then `..=`: {diag}");
        for (k, (fix, want)) in fixes.iter().zip([with_lt, with_eq]).enumerate() {
            let edits = edits_of(fix);
            assert_eq!(edits.len(), 1, "{what}: candidate {}: one edit, the token: {fix}", k + 1);
            let e = &edits[0];
            assert!(
                start <= e.start && e.end <= end,
                "{what}: candidate {}: the edit {:?}..{:?} is outside the symbol {start:?}..{end:?}",
                k + 1,
                e.start,
                e.end
            );
            let fixed = apply(&src, &edits);
            assert_eq!(fixed, loop_with(want), "{what}: candidate {}", k + 1);
        }
        assert!(!notes_of(diag).is_empty(), "{what}: no note with the rule: {diag}");
    }
}

#[test]
fn the_candidate_with_the_half_open_symbol_leaves_a_program_with_no_diagnostic() {
    // §18.1: a candidate leaves no diagnostic of the same stage or an earlier one in the unit it
    // touches; with `..<` the unit is checked fully, so the whole check is silent.
    let d = Dir::new("clean");
    for (what, header, _, with_lt, _) in WRONG_SYMBOLS {
        let path = d.file("a.onsa", &loop_with(header));
        let fixed = {
            let diags = check(&path);
            let diag = expect_one(&diags, "E0020", what);
            apply(&read(&path), &edits_of(fixes_of(diag)[0]))
        };
        assert_eq!(fixed, loop_with(with_lt), "{what}");
        let after = d.file("b.onsa", &fixed);
        let diags = check(&after);
        assert!(diags.is_empty(), "{what}: the fixed program has diagnostics: {diags:?}\n{fixed}");
    }
}

#[test]
fn a_wrong_symbol_in_a_par_header_is_e0020_with_the_same_two_candidates() {
    // §11.5, §18.1: the same diagnostic and candidates as in a `for` header. The ends of a `par` are
    // constant expressions; a range binds more weakly than their operators (§3.1).
    let cases: [(&str, &str, &str, &str, &str); 4] = [
        ("two dots", "0..4", "..", "0..<4", "0..=4"),
        ("three dots", "0...4", "...", "0..<4", "0..=4"),
        ("a constant end that is a sum", "1..N + 1", "..", "1..<N + 1", "1..=N + 1"),
        ("sums in the ends", "N - 2...N * 2", "...", "N - 2..<N * 2", "N - 2..=N * 2"),
    ];
    let wrap = |header: &str| {
        format!(
            "const N: U32 = 3\n\npub flow f(x: F32 at sample) -> [F32; 4] at sample {{\n  par i in {header} {{\n    x * i.round_f32()\n  }}\n}}\n"
        )
    };
    let d = Dir::new("par");
    for (what, header, symbol, with_lt, with_eq) in cases {
        let src = wrap(header);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0020", what);
        let (start, end) = span_of(diag);
        assert_eq!(start.0, 4, "{what}: the line of the header: {diag}");
        assert_eq!(end.1 - start.1, symbol.len(), "{what}: the span is the symbol: {diag}");
        let fixes = fixes_of(diag);
        assert_eq!(fixes.len(), 2, "{what}: {diag}");
        for (fix, want) in fixes.iter().zip([with_lt, with_eq]) {
            assert_eq!(apply(&src, &edits_of(fix)), wrap(want), "{what}");
        }
    }
}

// ---- E0002: a range outside the header of a `for` or a `par` (§7) ---------------------------------

/// (what the case says, the body of the function). Whatever the spelling, there is no candidate: a
/// candidate that made `..<` out of `..` would leave the error of the place (§18.1: no candidate is
/// made that would not satisfy the contract), so the syntax error stands and a note shows `slice`.
const OUTSIDE: &[(&str, &str)] = &[
    ("a let with ..<", "  let r = 0..<n\n  n"),
    ("a let with ..=", "  let r = 0..=n\n  n"),
    ("a let with ..", "  let r = 0..n\n  n"),
    ("a let with ...", "  let r = 0...n\n  n"),
    ("a let with a sum in the end", "  let r = 0..<n + 1\n  n"),
    ("a part of an array", "  let s = xs[1..<3]\n  n"),
    ("a part of an array, closed", "  let s = xs[1..=2]\n  n"),
    ("a part of an array, two dots", "  let s = xs[1..3]\n  n"),
    ("an argument", "  take(0..<4)"),
    ("the tail expression", "  0..<n"),
    ("a tuple", "  let t2 = (0..<2, n)\n  n"),
];

#[test]
fn a_range_outside_a_header_is_one_e0002_with_no_candidate_and_a_note() {
    let d = Dir::new("outside");
    for (what, body) in OUTSIDE {
        let src =
            format!("pub fn take(r: U32) -> U32 {{\n  r\n}}\n\npub fn f(n: U32, xs: [I32; 4]) -> U32 {{\n{body}\n}}\n");
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0002", what);
        assert!(fixes_of(diag).is_empty(), "{what}: a candidate for a range that is not in a header: {diag}");
        let notes = notes_of(diag);
        assert!(!notes.is_empty(), "{what}: no note: {diag}");
        assert!(
            notes.iter().all(|n| n["message"].as_str().is_some_and(|m| !m.is_empty())),
            "{what}: an empty note: {diag}"
        );
    }
}

#[test]
fn the_note_of_a_part_of_an_array_shows_slice() {
    // §7: "部分は `xs.slice(from, to)`（§5.3）で書くことを note で示す".
    let d = Dir::new("slice");
    for (what, range) in [("half open", "xs[1..<3]"), ("closed", "xs[1..=2]"), ("two dots", "xs[1..3]")] {
        let src = format!("pub fn f(xs: [I32; 4]) -> I32 {{\n  let s = {range}\n  0\n}}\n");
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0002", what);
        let shown = notes_of(diag).iter().any(|n| n["message"].as_str().is_some_and(|m| m.contains("slice")));
        assert!(shown, "{what}: no note shows `slice`: {diag}");
    }
}

// ---- the correct forms are read -------------------------------------------------------------------

#[test]
fn the_half_open_range_is_read_whatever_the_ends() {
    // §7, §3.1, §4: the tokens around the symbol are read as the ends. `1.` is not a float before the
    // symbol, the digits after a `.` are an index, `-` is a prefix, `_` separates digits.
    let d = Dir::new("read");
    for header in [
        "0..<n",
        "1..<3",
        "0..<n + 1",
        "lo + 1..<hi - 1",
        "-2..<2",
        "0x10..<0x14",
        "1_000..<1_003",
        "t.0..<t.1",
        "t.0..<t.1 + 1",
        "0..<xs.len()",
        "lo..<hi * 2",
        "0..<(n as U32)",
    ] {
        let src = loop_with(header);
        let path = d.file("a.onsa", &src);
        let out = onsa(&["check", &path]);
        // Some of the headers are not well typed in this function (the types of `i` and `c`); the
        // point is that none is an error of the syntax stage.
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(!text.contains("error[E0002]"), "{header}: E0002: {text}");
        assert!(!text.contains("error[E0001]"), "{header}: E0001: {text}");
        assert!(!text.contains("error[E0020]"), "{header}: E0020: {text}");
    }
}

#[test]
fn a_bare_conversion_in_an_end_is_e0011() {
    // §3.3 (S-340): `as` is weaker than the range symbols too, so a conversion in an end is written in
    // parentheses: E0011, and its candidate puts them (both ends of one head, one diagnostic).
    let d = Dir::new("bare_cast");
    for (header, fixed) in [
        ("0..<n as U32", "0..<(n as U32)"),
        ("lo as U32..<9", "(lo as U32)..<9"),
        ("lo as U32..<n as U32", "(lo as U32)..<(n as U32)"),
    ] {
        let src = loop_with(header);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{header}: {diags:?}");
        assert_eq!(diags[0]["code"], "E0011", "{header}: {}", diags[0]);
        let edits = diags[0]["fixes"][0]["edits"].as_array().cloned().unwrap_or_default();
        let mut out = src.clone();
        let mut spans: Vec<(usize, String)> = edits
            .iter()
            .map(|e| {
                let line = e["span"]["line"].as_u64().unwrap() as usize;
                let col = e["span"]["col"].as_u64().unwrap() as usize;
                let start: usize = src.split_inclusive('\n').take(line - 1).map(str::len).sum::<usize>() + col - 1;
                (start, e["replace"].as_str().unwrap().to_string())
            })
            .collect();
        spans.sort_by(|a, b| b.0.cmp(&a.0));
        for (at, text) in spans {
            out.insert_str(at, &text);
        }
        assert_eq!(out, loop_with(fixed), "{header}");
    }
}

#[test]
fn a_bare_clock_in_an_end_is_e0011() {
    // §3.1, §11.3 (S-340, S-118): `at` has the strength of `as`, so a clock in an end of a range is
    // written in parentheses too: E0011 (of the syntax stage, also in a fn, where the clock itself is
    // the names stage's E0821), its candidate puts them; `as` and `at` in the two ends of one head are
    // one diagnostic.
    let d = Dir::new("bare_clock");
    for (header, fixed) in [
        ("0..<n at sample", "0..<(n at sample)"),
        ("lo at block..<9", "(lo at block)..<9"),
        ("lo as U32..<n at sample", "(lo as U32)..<(n at sample)"),
    ] {
        let src = loop_with(header);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{header}: {diags:?}");
        assert_eq!(diags[0]["code"], "E0011", "{header}: {}", diags[0]);
        let edits = diags[0]["fixes"][0]["edits"].as_array().cloned().unwrap_or_default();
        let mut out = src.clone();
        let mut spans: Vec<(usize, String)> = edits
            .iter()
            .map(|e| {
                let line = e["span"]["line"].as_u64().unwrap() as usize;
                let col = e["span"]["col"].as_u64().unwrap() as usize;
                let start: usize = src.split_inclusive('\n').take(line - 1).map(str::len).sum::<usize>() + col - 1;
                (start, e["replace"].as_str().unwrap().to_string())
            })
            .collect();
        spans.sort_by(|a, b| b.0.cmp(&a.0));
        for (at, text) in spans {
            out.insert_str(at, &text);
        }
        assert_eq!(out, loop_with(fixed), "{header}");
    }
    // The head of a `par` in a flow.
    let src = "pub flow g(n: U32 at init) -> [U32; 4] at sample {\n  par i in 0..<4 at init {\n    i\n  }\n}\n";
    let path = d.file("b.onsa", src);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!(diags[0]["code"], "E0011", "{}", diags[0]);
}

// ---- fmt and diff --ast stop at the errors of the syntax stage (§18.2) ------------------------------

/// Files with an error of the syntax stage around a range: (what, the file, the code of the error).
const SYNTAX_ERRORS: &[(&str, &str, &str)] = &[
    (
        "two dots in a for",
        "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for i in 0..n {\n    c = c + i\n  }\n  c\n}\n",
        "E0020",
    ),
    (
        "three dots in a for",
        "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for i in 0...n {\n    c = c + i\n  }\n  c\n}\n",
        "E0020",
    ),
    ("a range in a let", "pub fn f(n: U32) -> U32 {\n  let r = 0..<n\n  n\n}\n", "E0002"),
    ("a closed range in a let", "pub fn f(n: U32) -> U32 {\n  let r = 0..=n\n  n\n}\n", "E0002"),
    ("two dots in a let", "pub fn f(n: U32) -> U32 {\n  let r = 0..n\n  n\n}\n", "E0002"),
    ("a range as an index", "pub fn f(xs: [I32; 4]) -> I32 {\n  let s = xs[1..<3]\n  0\n}\n", "E0002"),
];

#[test]
fn fmt_and_diff_stop_at_a_wrong_range_symbol() {
    // §18.2: a file with a diagnostic of the syntax stage is not rewritten (exit code 2) and
    // `diff --ast` does not compare it (exit code 2); the diagnostic goes to the standard output.
    let d = Dir::new("stop");
    let other = d.file("other.onsa", "pub fn f(n: U32) -> U32 {\n  n\n}\n");
    for (what, text, want) in SYNTAX_ERRORS {
        let path = d.file("a.onsa", text);
        let diags = check(&path);
        expect_one(&diags, want, what);
        for args in [vec!["fmt"], vec!["fmt", "--check"]] {
            let mut full = args.clone();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what}: onsa {args:?}: {out:?}");
            assert_eq!(read(&path), *text, "{what}: the file is not rewritten");
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(
                stdout.contains(&format!("error[{want}]")),
                "{what}: the diagnostic is on the standard output: {out:?}"
            );
        }
        let diff = onsa(&["diff", "--ast", &path, &other]);
        assert_eq!(code(&diff), 2, "{what}: diff --ast: {diff:?}");
    }
}

// ---- fmt: the operators in the ends, and what it does not change -----------------------------------

/// (what the case says, the header as written, the strings that must be in the header after `fmt`).
/// §3.2: a space on both sides of a binary operator. What `fmt` writes around the range symbol is not
/// in the spec, so only the operators inside the ends are named, and the symbol itself.
const ENDS_AS_WRITTEN: &[(&str, &str, &[&str])] = &[
    ("a sum as the end", "0..<n+1", &["..<", "n + 1"]),
    ("sums in both ends", "lo+1..<hi*2", &["..<", "lo + 1", "hi * 2"]),
    ("a closed range", "0..=n+1", &["..=", "n + 1"]),
    ("a difference as the end", "0..<hi-1", &["..<", "hi - 1"]),
    ("a call with a sum in an argument", "0..<xs.len()+1", &["..<", "xs.len() + 1"]),
];

fn header_of(text: &str) -> &str {
    text.lines().find(|l| l.trim_start().starts_with("for ")).expect("a for line")
}

#[test]
fn fmt_writes_the_operators_in_the_ends_and_keeps_the_symbol() {
    let d = Dir::new("fmt_ends");
    for (what, header, wanted) in ENDS_AS_WRITTEN {
        let src = loop_with(header);
        let path = d.file("a.onsa", &src);
        let before = d.file("before.onsa", &src);
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        let text = read(&path);
        let line = header_of(&text);
        for w in *wanted {
            assert!(line.contains(w), "{what}: `{w}` is not in `{line}`");
        }
        // The same program (§18.2), and a fixed point.
        let diff = onsa(&["diff", "--ast", &before, &path]);
        assert_eq!(code(&diff), 0, "{what}: fmt changed the program: {diff:?}");
        let again = onsa(&["fmt", &path]);
        assert_eq!(code(&again), 0, "{what}: {again:?}");
        assert_eq!(read(&path), text, "{what}: fmt twice");
        let check = onsa(&["fmt", "--check", &path]);
        assert_eq!(code(&check), 0, "{what}: the output is not accepted by --check: {check:?}");
    }
}

#[test]
fn fmt_does_not_turn_one_symbol_into_the_other() {
    let d = Dir::new("fmt_symbol");
    for (symbol, other) in [("..<", "..="), ("..=", "..<")] {
        let src = loop_with(&format!("0{symbol}n"));
        let path = d.file("a.onsa", &src);
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 0, "{symbol}: {out:?}");
        let text = read(&path);
        assert!(text.contains(symbol), "{symbol}: the symbol is gone:\n{text}");
        assert!(!text.contains(other), "{symbol}: the other symbol appeared:\n{text}");
    }
}

// ---- diff --ast: the symbol and the ends are in the tree --------------------------------------------

/// (what the case says, one header, another header): the two files are different programs.
const DIFFERENT: &[(&str, &str, &str)] = &[
    ("half open and closed", "0..<n", "0..=n"),
    ("another start", "0..<n", "1..<n"),
    ("another end", "0..<n", "0..<hi"),
    ("a sum and its first operand", "0..<n + 1", "0..<n"),
    ("a sum and a difference", "0..<n + 1", "0..<n - 1"),
    ("the sum is in the start or in the end", "lo + 1..<hi", "lo..<hi + 1"),
    ("closed with a sum", "0..=n + 1", "0..<n + 1"),
];

/// (what, one header, another header): the same program written in two ways.
const SAME: &[(&str, &str, &str)] = &[
    ("spaces in the operators of the end", "0..<n + 1", "0..<n+1"),
    ("spaces in the operators of both ends", "lo + 1..<hi * 2", "lo+1..<hi*2"),
    ("a closed range", "0..=n - 1", "0..=n-1"),
];

#[test]
fn diff_ast_sees_the_symbol_and_the_ends_and_not_the_spaces_in_them() {
    let d = Dir::new("diff");
    for (what, one, other) in DIFFERENT {
        let a = d.file("a.onsa", &loop_with(one));
        let b = d.file("b.onsa", &loop_with(other));
        let out = onsa(&["diff", "--ast", &a, &b]);
        assert_eq!(code(&out), 1, "{what}: the programs differ: {out:?}");
    }
    for (what, one, other) in SAME {
        let a = d.file("a.onsa", &loop_with(one));
        let b = d.file("b.onsa", &loop_with(other));
        let out = onsa(&["diff", "--ast", &a, &b]);
        assert_eq!(code(&out), 0, "{what}: the programs are the same: {out:?}");
    }
}

// ---- the closed range is read and not lowered: E0200 (§18.1, S-224) -----------------------------------

#[test]
fn a_closed_range_in_a_for_header_stops_onsa_test_with_e0200() {
    // §18.2: `onsa test` stops at a check error and at an E0200 that does not depend on the target;
    // `tests` is an empty array then. The closed range is read (it is not a syntax error) and named
    // as the feature that this version does not lower. W8-03 removes this test.
    let src = "\
fn total(n: U32) -> U32 {
  var t: U32 = 0
  for i in 0..=n {
    t = t + i
  }
  t
}

test \"a closed range\" {
  assert total(3) == 6
}
";
    let d = Dir::new("closed");
    let path = d.file("a.onsa", src);
    let out = onsa(&["test", "--json", &path]);
    assert_eq!(code(&out), 1, "{out:?}");
    let text = String::from_utf8(out.stdout).expect("utf-8");
    let v: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("no JSON ({e}): {text}"));
    let diags = v["diagnostics"].as_array().expect("`diagnostics`");
    let codes: Vec<&str> = diags.iter().map(code_of).collect();
    assert_eq!(codes, ["E0200"], "one E0200 and no syntax error: {text}");
    assert_eq!(span_of(&diags[0]).0.0, 3, "the diagnostic is at the header: {text}");
    assert_eq!(v["tests"].as_array().map(Vec::len), Some(0), "no test ran: {text}");
}

#[test]
fn a_closed_range_is_not_a_syntax_error_for_fmt() {
    // §18.2: only the diagnostics of the syntax stage stop `fmt`. E0200 of the closed range cannot be
    // one of them: the candidate `a..=b` of E0020 (§7) must leave no diagnostic of the syntax stage in
    // the unit it touches (§18.1), and it leaves this E0200. So a file with a closed range header is
    // formatted (it is a program of the language).
    let d = Dir::new("closed_fmt");
    let text = loop_with("0..=n");
    let path = d.file("a.onsa", &text);
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
}
