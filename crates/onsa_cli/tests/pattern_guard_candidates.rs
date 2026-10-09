//! The guard-form candidates of the patterns (spec §7, §18.1; S-109, S-186, S-225, S-227, S-249,
//! S-251, S-253, S-278, S-317, S-319; R-156): W3-21/t.
//!
//! The case files in `tests/spec/` pin the code and the line of each diagnostic and the text of the
//! candidates whose text the spec fixes (`fixes/e0020_patterns_at_forms.onsa` and
//! `fixes/e0020_patterns_rest_forms.onsa` hold the `.fix1` of the forms that keep their names). The
//! candidate of a float literal, a range, a string with an interpolation and a `-` before a constant
//! puts a *new* binding in the pattern, and the spec does not say how it is named (S-253). These tests
//! say what those files cannot: the shape of every such candidate with the new names left open
//! (`$1`, `$2` are the new names in the order they appear), that the program after the candidate has no
//! diagnostic, that it keeps its meaning (the values that matched the pattern still do, and only those),
//! that the new names are not any visible name, that the edits are minimal, that a form with no
//! candidate has none, and what the notes and the messages say.
//!
//! Expected texts are written from the spec; none is taken from the output of the compiler. The
//! shapes follow the examples of §7 (`(0.0, 1.0)` is `(v, v2) if v == 0.0 && v2 == 1.0`,
//! `0.5 | 1.5` is `v if v == 0.5 || v == 1.5`, `n @ (1 | 1..<3)` is `n if n == 1 || (1 <= n && n < 3)`)
//! and the groups of §3.1 (a comparison is stronger than `&&`, `&&` and `||` do not mix without
//! parentheses, so a branch with a conjunction is in parentheses and so is a choice that the arm's own
//! guard follows).
//!
//! The behaviour is run with `onsa test` on a `match` written as a statement that sets a `var` (the
//! value of a `match` with a guard is E0200 until W8-06; a `Str` is E0200 in this version, so the
//! string cases are checked but not run).
//!
//! Every test uses only the binary (`onsa check --json`, `onsa test`, `onsa fmt`). The tests marked
//! `#[ignore]` do not pass with the code of 2026-10-09; each names the work that removes the mark (an
//! ignored test is not silenced by `tests/pending.toml`: it is skipped). Run them with
//! `cargo test -p onsa_cli --test pattern_guard_candidates -- --ignored`.

use std::collections::HashSet;
use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_guardpat_{}_{tag}", std::process::id()));
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

/// The diagnostics of `onsa check --json <path>`.
fn check(path: &str) -> Vec<Value> {
    let out = Command::new(ONSA).args(["check", "--json", path]).output().expect("run onsa");
    let code = out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"));
    assert!(
        code == 0 || code == 1,
        "onsa check {path}: exit code {code} (stderr: {})",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8(out.stdout).expect("utf-8 output");
    let v: Value =
        serde_json::from_str(&text).unwrap_or_else(|e| panic!("onsa check --json printed no JSON ({e}): {text}"));
    let diags = v["diagnostics"].as_array().unwrap_or_else(|| panic!("no `diagnostics` array: {v}")).clone();
    assert_eq!(code == 0, diags.is_empty(), "the exit code {code} and the diagnostics disagree: {diags:?}");
    diags
}

/// The exit code and the standard output of `onsa test <path>`.
fn run_tests(path: &str) -> (i32, String) {
    let out = Command::new(ONSA).args(["test", path]).output().expect("run onsa");
    let code = out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"));
    (code, String::from_utf8_lossy(&out.stdout).into_owned())
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

/// The byte offset of a (line, column in characters) position.
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

fn replaced_texts(text: &str, edits: &[Edit]) -> Vec<String> {
    edits.iter().map(|e| text[offset(text, e.start)..offset(text, e.end)].to_string()).collect()
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

fn with_fix(text: &str, diag: &Value, k: usize) -> String {
    let fixes = fixes_of(diag);
    let fix = fixes.get(k).unwrap_or_else(|| panic!("no candidate {k} for {diag}"));
    apply(text, &edits_of(fix))
}

// ---- Tokens: the shape of a candidate with its new names left open --------------------------------

/// The tokens of `text` without whitespace and comments. A name that starts with `$` is a placeholder.
fn tokens(text: &str) -> Vec<String> {
    const OPS: [&str; 13] = ["..<", "..=", "...", "..", "<=", ">=", "==", "!=", "&&", "||", "=>", "->", "::"];
    let cs: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '/' && cs.get(i + 1) == Some(&'/') {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if c == '"' || c == '\'' {
            let s = i;
            i += 1;
            while i < cs.len() && cs[i] != c {
                if cs[i] == '\\' {
                    i += 1;
                }
                i += 1;
            }
            i = (i + 1).min(cs.len());
            out.push(cs[s..i].iter().collect());
        } else if c.is_alphanumeric() || c == '_' || c == '$' {
            let s = i;
            let numeric = c.is_ascii_digit();
            i += 1;
            while i < cs.len() {
                let d = cs[i];
                if d.is_alphanumeric()
                    || d == '_'
                    || d == '$'
                    || (numeric && d == '.' && cs.get(i + 1).is_some_and(char::is_ascii_digit))
                {
                    i += 1;
                } else {
                    break;
                }
            }
            out.push(cs[s..i].iter().collect());
        } else if let Some(op) = OPS.iter().find(|op| cs[i..].iter().take(op.len()).collect::<String>() == **op) {
            out.push((*op).to_string());
            i += op.len();
        } else {
            out.push(c.to_string());
            i += 1;
        }
    }
    out
}

fn is_name(t: &str) -> bool {
    t != "_" && t != "if" && t.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
}

/// The tokens of `fixed` where a name that `original` does not have is `$1`, `$2`, ... in the order
/// of first appearance.
fn canonical(original: &str, fixed: &str) -> Vec<String> {
    let known: HashSet<String> = tokens(original).into_iter().filter(|t| is_name(t)).collect();
    let mut fresh: Vec<String> = Vec::new();
    tokens(fixed)
        .into_iter()
        .map(|t| {
            if is_name(&t) && !known.contains(&t) {
                let n = fresh.iter().position(|f| *f == t).unwrap_or_else(|| {
                    fresh.push(t.clone());
                    fresh.len() - 1
                });
                format!("${}", n + 1)
            } else {
                t
            }
        })
        .collect()
}

/// The pattern and the guard of the first arm: the tokens from the `{` after the first `match` to
/// the first `=>`.
fn first_arm_head(toks: &[String]) -> Vec<String> {
    let m = toks.iter().position(|t| t == "match").expect("a `match` in the program");
    let open = m + toks[m..].iter().position(|t| t == "{").expect("the `{` of the arms");
    let arrow = open + toks[open..].iter().position(|t| t == "=>").expect("the `=>` of the first arm");
    toks[open + 1..arrow].to_vec()
}

// ---- The programs ------------------------------------------------------------------------------------

/// `fn f` with a `match` written as a statement that sets `r`; the first arm is the wrong one.
fn prog(prelude: &str, params: &str, scrut: &str, arm: &str, body: &str, uses: &str) -> String {
    let m = if arm.starts_with("..") {
        // An arm that starts with a one-ended range is written on one line (a line that starts with
        // `..<` is not settled, §2.5: a gap in the report of W3-21/t).
        format!("  match {scrut} {{ {arm} => {{ r = {body} }}, _ => {{ r = 0 }} }}\n")
    } else {
        format!("  match {scrut} {{\n    {arm} => {{ r = {body} }},\n    _ => {{ r = 0 }},\n  }}\n")
    };
    format!("{prelude}pub fn f({params}) -> I32{uses} {{\n  var r = 0\n{m}  r\n}}\n")
}

struct Cand {
    /// The first arm after the candidate, with the new names as `$1`, `$2`; empty when not pinned.
    head: &'static str,
    /// The asserts that the program after the candidate must pass (the meaning of the pattern).
    asserts: &'static str,
}

struct Case {
    name: &'static str,
    program: String,
    cands: Vec<Cand>,
}

fn cand(head: &'static str, asserts: &'static str) -> Cand {
    Cand { head, asserts }
}

fn case(name: &'static str, params: &str, scrut: &str, arm: &str, body: &str, cands: Vec<Cand>) -> Case {
    Case { name, program: prog("", params, scrut, arm, body, ""), cands }
}

fn case_with(
    name: &'static str,
    prelude: &str,
    params: &str,
    scrut: &str,
    arm: &str,
    body: &str,
    cands: Vec<Cand>,
) -> Case {
    Case { name, program: prog(prelude, params, scrut, arm, body, ""), cands }
}

/// A string pattern: the function has `uses {Alloc}` (the interpolated string in the guard makes a
/// `Str`, §2.4), and the cases are not run (a `Str` is E0200 in this version).
fn string_case(name: &'static str, params: &str, scrut: &str, arm: &str, head: &'static str) -> Case {
    Case { name, program: prog("", params, scrut, arm, "1", " uses {Alloc}"), cands: vec![cand(head, "")] }
}

const LIMITS: &str = "const LIMIT: I32 = 4\nconst OTHER: I32 = 9\n\n";
const PT: &str = "pub struct Pt {\n  x: I32,\n  y: I32,\n}\n\n";

fn range_cases() -> Vec<Case> {
    let half = "assert f(0) == 0\nassert f(1) == 1\nassert f(2) == 1\nassert f(3) == 0";
    let closed = "assert f(0) == 0\nassert f(1) == 1\nassert f(3) == 1\nassert f(4) == 0";
    let choice = "$1 if (1 <= $1 && $1 < 3) || (5 <= $1 && $1 < 7)";
    vec![
        case("half_open", "n: I32", "n", "1..<3", "1", vec![cand("$1 if 1 <= $1 && $1 < 3", half)]),
        case("closed", "n: I32", "n", "1..=3", "1", vec![cand("$1 if 1 <= $1 && $1 <= 3", closed)]),
        case(
            "two_dots",
            "n: I32",
            "n",
            "1..3",
            "1",
            vec![cand("$1 if 1 <= $1 && $1 < 3", half), cand("$1 if 1 <= $1 && $1 <= 3", closed)],
        ),
        case(
            "three_dots",
            "n: I32",
            "n",
            "1...3",
            "1",
            vec![cand("$1 if 1 <= $1 && $1 < 3", half), cand("$1 if 1 <= $1 && $1 <= 3", closed)],
        ),
        case(
            "from",
            "n: I32",
            "n",
            "5..",
            "1",
            vec![cand("$1 if 5 <= $1", "assert f(4) == 0\nassert f(5) == 1\nassert f(100) == 1")],
        ),
        case(
            "up_to",
            "n: I32",
            "n",
            "..<5",
            "1",
            vec![cand("$1 if $1 < 5", "assert f(-100) == 1\nassert f(4) == 1\nassert f(5) == 0")],
        ),
        case(
            "through",
            "n: I32",
            "n",
            "..=5",
            "1",
            vec![cand("$1 if $1 <= 5", "assert f(-100) == 1\nassert f(5) == 1\nassert f(6) == 0")],
        ),
        case(
            "up_to_two_dots",
            "n: I32",
            "n",
            "..5",
            "1",
            vec![
                cand("$1 if $1 < 5", "assert f(4) == 1\nassert f(5) == 0"),
                cand("$1 if $1 <= 5", "assert f(5) == 1\nassert f(6) == 0"),
            ],
        ),
        case(
            "negative_ends",
            "n: I32",
            "n",
            "-5..<5",
            "1",
            vec![cand(
                "$1 if -5 <= $1 && $1 < 5",
                "assert f(-6) == 0\nassert f(-5) == 1\nassert f(4) == 1\nassert f(5) == 0",
            )],
        ),
        case(
            "chars",
            "c: Char",
            "c",
            "'a'..='z'",
            "1",
            vec![cand(
                "$1 if 'a' <= $1 && $1 <= 'z'",
                "assert f('a') == 1\nassert f('z') == 1\nassert f('A') == 0\nassert f('0') == 0",
            )],
        ),
        case(
            "floats",
            "x: F32",
            "x",
            "0.0..<1.0",
            "1",
            vec![cand(
                "$1 if 0.0 <= $1 && $1 < 1.0",
                "assert f(0.0) == 1\nassert f(0.5) == 1\nassert f(1.0) == 0\nassert f(-0.5) == 0",
            )],
        ),
        case(
            "inside_some",
            "o: Option[I32]",
            "o",
            "Some(1..<3)",
            "1",
            vec![cand(
                "Some($1) if 1 <= $1 && $1 < 3",
                "assert f(Some(2)) == 1\nassert f(Some(3)) == 0\nassert f(None) == 0",
            )],
        ),
        case(
            "inside_some_twice",
            "o: Option[Option[I32]]",
            "o",
            "Some(Some(1..=3))",
            "1",
            vec![cand(
                "Some(Some($1)) if 1 <= $1 && $1 <= 3",
                "assert f(Some(Some(3))) == 1\nassert f(Some(Some(4))) == 0\nassert f(Some(None)) == 0\nassert f(None) == 0",
            )],
        ),
        case(
            "inside_a_tuple",
            "t: (I32, I32)",
            "t",
            "(1..<3, n)",
            "n",
            vec![cand("($1, n) if 1 <= $1 && $1 < 3", "assert f((2, 7)) == 7\nassert f((3, 7)) == 0")],
        ),
        case_with(
            "inside_a_struct",
            PT,
            "p: Pt",
            "p",
            "Pt { x: 1..<3, y: _ }",
            "1",
            vec![cand(
                "Pt { x: $1, y: _ } if 1 <= $1 && $1 < 3",
                "let a = Pt { x: 2, y: 0 }\nlet b = Pt { x: 3, y: 0 }\nassert f(a) == 1\nassert f(b) == 0",
            )],
        ),
        case(
            "two_ranges",
            "t: (I32, I32)",
            "t",
            "(1..<3, 5..=7)",
            "1",
            vec![cand(
                "($1, $2) if 1 <= $1 && $1 < 3 && 5 <= $2 && $2 <= 7",
                "assert f((2, 6)) == 1\nassert f((2, 5)) == 1\nassert f((2, 7)) == 1\nassert f((3, 6)) == 0\nassert f((2, 8)) == 0",
            )],
        ),
        case(
            "choice_of_ranges",
            "n: I32",
            "n",
            "1..<3 | 5..<7",
            "1",
            vec![cand(
                choice,
                "assert f(2) == 1\nassert f(3) == 0\nassert f(5) == 1\nassert f(6) == 1\nassert f(7) == 0",
            )],
        ),
        case(
            "choice_of_three",
            "n: I32",
            "n",
            "1..<3 | 5..<7 | 9..=10",
            "1",
            vec![cand(
                "$1 if (1 <= $1 && $1 < 3) || (5 <= $1 && $1 < 7) || (9 <= $1 && $1 <= 10)",
                "assert f(2) == 1\nassert f(10) == 1\nassert f(11) == 0\nassert f(8) == 0",
            )],
        ),
        case(
            "choice_of_options",
            "o: Option[I32]",
            "o",
            "Some(1..<3) | Some(5..<7)",
            "1",
            vec![cand(
                "Some($1) if (1 <= $1 && $1 < 3) || (5 <= $1 && $1 < 7)",
                "assert f(Some(2)) == 1\nassert f(Some(6)) == 1\nassert f(Some(4)) == 0\nassert f(None) == 0",
            )],
        ),
        case(
            "choice_inside_some",
            "o: Option[I32]",
            "o",
            "Some(1..<3 | 5..<7)",
            "1",
            vec![cand(
                "Some($1) if (1 <= $1 && $1 < 3) || (5 <= $1 && $1 < 7)",
                "assert f(Some(2)) == 1\nassert f(Some(6)) == 1\nassert f(Some(4)) == 0\nassert f(None) == 0",
            )],
        ),
        case(
            "choice_that_shares_a_literal",
            "t: (I32, I32)",
            "t",
            "(1..<3, 1) | (5..<7, 1)",
            "1",
            vec![cand(
                "($1, 1) if (1 <= $1 && $1 < 3) || (5 <= $1 && $1 < 7)",
                "assert f((2, 1)) == 1\nassert f((6, 1)) == 1\nassert f((2, 2)) == 0\nassert f((4, 1)) == 0",
            )],
        ),
        case(
            "choice_that_shares_a_binding",
            "t: (I32, I32)",
            "t",
            "(1..<3, n) | (5..<7, n)",
            "n",
            vec![cand(
                "($1, n) if (1 <= $1 && $1 < 3) || (5 <= $1 && $1 < 7)",
                "assert f((2, 9)) == 9\nassert f((6, 9)) == 9\nassert f((4, 9)) == 0",
            )],
        ),
        case(
            "choice_of_one_ended_ranges",
            "n: I32",
            "n",
            "..<0 | 10..",
            "1",
            vec![cand(
                "$1 if $1 < 0 || 10 <= $1",
                "assert f(-1) == 1\nassert f(0) == 0\nassert f(9) == 0\nassert f(10) == 1",
            )],
        ),
        case(
            "with_the_arms_own_guard",
            "n: I32, flag: Bool",
            "n",
            "1..<3 if flag",
            "1",
            vec![cand(
                "$1 if 1 <= $1 && $1 < 3 && flag",
                "assert f(2, true) == 1\nassert f(2, false) == 0\nassert f(3, true) == 0",
            )],
        ),
        case(
            "guarded_choice",
            "n: I32, flag: Bool",
            "n",
            "1..<3 | 5..<7 if flag",
            "1",
            vec![cand(
                "$1 if ((1 <= $1 && $1 < 3) || (5 <= $1 && $1 < 7)) && flag",
                "assert f(6, true) == 1\nassert f(6, false) == 0\nassert f(4, true) == 0",
            )],
        ),
    ]
}

fn float_cases() -> Vec<Case> {
    vec![
        case(
            "float_negative",
            "x: F32",
            "x",
            "-1.0",
            "1",
            vec![cand("$1 if $1 == -1.0", "assert f(-1.0) == 1\nassert f(1.0) == 0")],
        ),
        case(
            "float_exponent",
            "x: F64",
            "x",
            "1e3",
            "1",
            vec![cand("$1 if $1 == 1e3", "assert f(1000.0) == 1\nassert f(1.0) == 0")],
        ),
        case(
            "float_choice",
            "x: F32",
            "x",
            "0.5 | 1.5",
            "1",
            vec![cand("$1 if $1 == 0.5 || $1 == 1.5", "assert f(0.5) == 1\nassert f(1.5) == 1\nassert f(1.0) == 0")],
        ),
        case(
            "float_pair",
            "t: (F32, F32)",
            "t",
            "(0.0, 1.0)",
            "1",
            vec![cand(
                "($1, $2) if $1 == 0.0 && $2 == 1.0",
                "assert f((0.0, 1.0)) == 1\nassert f((0.0, 2.0)) == 0\nassert f((1.0, 1.0)) == 0",
            )],
        ),
        case(
            "float_choice_that_shares_a_binding",
            "t: (F32, I32)",
            "t",
            "(0.5, n) | (1.5, n)",
            "n",
            vec![cand(
                "($1, n) if $1 == 0.5 || $1 == 1.5",
                "assert f((1.5, 7)) == 7\nassert f((0.5, 7)) == 7\nassert f((2.5, 7)) == 0",
            )],
        ),
        case(
            "float_choice_that_shares_a_literal",
            "t: (F32, I32)",
            "t",
            "(0.5, 1) | (1.5, 1)",
            "1",
            vec![cand(
                "($1, 1) if $1 == 0.5 || $1 == 1.5",
                "assert f((1.5, 1)) == 1\nassert f((1.5, 2)) == 0\nassert f((2.5, 1)) == 0",
            )],
        ),
        case(
            "float_choice_inside_some",
            "o: Option[F32]",
            "o",
            "Some(0.5 | 1.5)",
            "1",
            vec![cand(
                "Some($1) if $1 == 0.5 || $1 == 1.5",
                "assert f(Some(1.5)) == 1\nassert f(Some(2.5)) == 0\nassert f(None) == 0",
            )],
        ),
        case(
            "float_choice_of_options",
            "o: Option[F32]",
            "o",
            "Some(0.5) | Some(1.5)",
            "1",
            vec![cand(
                "Some($1) if $1 == 0.5 || $1 == 1.5",
                "assert f(Some(1.5)) == 1\nassert f(Some(2.5)) == 0\nassert f(None) == 0",
            )],
        ),
        case(
            "float_guarded_choice",
            "x: F32, flag: Bool",
            "x",
            "0.5 | 1.5 if flag",
            "1",
            vec![cand(
                "$1 if ($1 == 0.5 || $1 == 1.5) && flag",
                "assert f(0.5, true) == 1\nassert f(0.5, false) == 0\nassert f(2.5, true) == 0",
            )],
        ),
    ]
}

fn negated_constant_cases() -> Vec<Case> {
    vec![
        case_with(
            "negated_constant",
            LIMITS,
            "x: I32",
            "x",
            "-LIMIT",
            "1",
            vec![cand("$1 if $1 == -LIMIT", "assert f(-4) == 1\nassert f(4) == 0\nassert f(-3) == 0")],
        ),
        case_with(
            "negated_inside_some",
            LIMITS,
            "o: Option[I32]",
            "o",
            "Some(-LIMIT)",
            "1",
            vec![cand(
                "Some($1) if $1 == -LIMIT",
                "assert f(Some(-4)) == 1\nassert f(Some(4)) == 0\nassert f(None) == 0",
            )],
        ),
        case_with(
            "negated_choice",
            LIMITS,
            "x: I32",
            "x",
            "-LIMIT | -OTHER",
            "1",
            vec![cand("$1 if $1 == -LIMIT || $1 == -OTHER", "assert f(-4) == 1\nassert f(-9) == 1\nassert f(9) == 0")],
        ),
        case_with(
            "negated_pair",
            LIMITS,
            "t: (I32, I32)",
            "t",
            "(-LIMIT, -OTHER)",
            "1",
            vec![cand(
                "($1, $2) if $1 == -LIMIT && $2 == -OTHER",
                "assert f((-4, -9)) == 1\nassert f((-4, 9)) == 0\nassert f((4, -9)) == 0",
            )],
        ),
        case_with(
            "negated_beside_a_literal",
            LIMITS,
            "t: (I32, I32)",
            "t",
            "(-LIMIT, 3)",
            "1",
            vec![cand("($1, 3) if $1 == -LIMIT", "assert f((-4, 3)) == 1\nassert f((-4, 2)) == 0")],
        ),
        case_with(
            "negated_beside_a_range",
            LIMITS,
            "t: (I32, I32)",
            "t",
            "(-LIMIT, 1..<3)",
            "1",
            vec![cand(
                "($1, $2) if $1 == -LIMIT && 1 <= $2 && $2 < 3",
                "assert f((-4, 2)) == 1\nassert f((-4, 3)) == 0\nassert f((4, 2)) == 0",
            )],
        ),
        case_with(
            "negated_associated_constant",
            "",
            "x: I64",
            "x",
            "-I64.MAX",
            "1",
            vec![cand("$1 if $1 == -I64.MAX", "assert f(0) == 0")],
        ),
    ]
}

const COLOR: &str = "pub enum Color {\n  Red,\n  Green,\n}\n\n";

/// `@` with a constant on the right (S-352, decided 2026-10-09 after W3-21/t): the guard form
/// `k if k == LIMIT`, the `-` and the path too.
fn at_constant_cases() -> Vec<Case> {
    vec![
        case_with(
            "at_a_constant",
            LIMITS,
            "n: I32",
            "n",
            "k @ LIMIT",
            "k",
            vec![cand("k if k == LIMIT", "assert f(4) == 4\nassert f(3) == 0")],
        ),
        case_with(
            "at_a_negated_constant",
            LIMITS,
            "n: I32",
            "n",
            "k @ -LIMIT",
            "k",
            vec![cand("k if k == -LIMIT", "assert f(-4) == -4\nassert f(4) == 0")],
        ),
        case_with(
            "at_a_choice_of_constants",
            LIMITS,
            "n: I32",
            "n",
            "k @ (LIMIT | OTHER)",
            "k",
            vec![cand("k if k == LIMIT || k == OTHER", "assert f(4) == 4\nassert f(9) == 9\nassert f(5) == 0")],
        ),
        case_with(
            "at_an_associated_constant",
            "",
            "n: I64",
            "n",
            "k @ I64.MAX",
            "1",
            vec![cand("k if k == I64.MAX", "assert f(0) == 0")],
        ),
    ]
}

fn mixed_cases() -> Vec<Case> {
    vec![
        case(
            "range_and_float",
            "t: (I32, F32)",
            "t",
            "(1..<3, 0.5)",
            "1",
            vec![cand(
                "($1, $2) if 1 <= $1 && $1 < 3 && $2 == 0.5",
                "assert f((2, 0.5)) == 1\nassert f((3, 0.5)) == 0\nassert f((2, 0.6)) == 0",
            )],
        ),
        case(
            "at_and_float",
            "t: (I32, F32)",
            "t",
            "(k @ 1..<3, 0.5)",
            "k",
            vec![cand(
                "(k, $1) if 1 <= k && k < 3 && $1 == 0.5",
                "assert f((2, 0.5)) == 2\nassert f((3, 0.5)) == 0\nassert f((2, 0.6)) == 0",
            )],
        ),
        case(
            "two_at_bindings",
            "t: (I32, I32)",
            "t",
            "(a @ 1..<3, b @ 5)",
            "a + b",
            vec![cand(
                "(a, b) if 1 <= a && a < 3 && b == 5",
                "assert f((2, 5)) == 7\nassert f((2, 6)) == 0\nassert f((3, 5)) == 0",
            )],
        ),
        case(
            "at_with_the_arms_own_guard",
            "n: I32",
            "n",
            "k @ 1..<5 if k != 3",
            "k",
            vec![cand("k if 1 <= k && k < 5 && k != 3", "assert f(2) == 2\nassert f(3) == 0\nassert f(5) == 0")],
        ),
        case(
            "at_choice_with_the_arms_own_guard",
            "n: I32, flag: Bool",
            "n",
            "k @ (1 | 7..<9) if flag",
            "k",
            vec![cand(
                "k if (k == 1 || (7 <= k && k < 9)) && flag",
                "assert f(1, true) == 1\nassert f(8, true) == 8\nassert f(8, false) == 0\nassert f(9, true) == 0",
            )],
        ),
        case(
            "at_choice_of_two_arms_with_a_guard",
            "n: I32",
            "n",
            "k @ 1 | k @ 2 if k != 2",
            "k",
            vec![cand("k if (k == 1 || k == 2) && k != 2", "assert f(1) == 1\nassert f(2) == 0\nassert f(3) == 0")],
        ),
        case(
            "range_beside_a_float_in_a_choice",
            "t: (I32, F32)",
            "t",
            "(1..<3, 0.5) | (5..<7, 1.5)",
            "1",
            vec![cand(
                "($1, $2) if (1 <= $1 && $1 < 3 && $2 == 0.5) || (5 <= $1 && $1 < 7 && $2 == 1.5)",
                "assert f((2, 0.5)) == 1\nassert f((6, 1.5)) == 1\nassert f((2, 1.5)) == 0\nassert f((6, 0.5)) == 0",
            )],
        ),
    ]
}

fn string_cases() -> Vec<Case> {
    vec![
        string_case("string", "s: Str, x: U32", "s", "\"a{x}b\"", "$1 if $1 == \"a{x}b\""),
        string_case("string_alone", "s: Str, x: U32", "s", "\"{x}\"", "$1 if $1 == \"{x}\""),
        string_case(
            "string_pair",
            "t: (Str, Str), x: U32, y: U32",
            "t",
            "(\"{x}\", \"{y}\")",
            "($1, $2) if $1 == \"{x}\" && $2 == \"{y}\"",
        ),
        string_case(
            "string_choice",
            "s: Str, x: U32",
            "s",
            "\"a{x}\" | \"b{x}\"",
            "$1 if $1 == \"a{x}\" || $1 == \"b{x}\"",
        ),
        string_case(
            "string_with_a_guard",
            "s: Str, x: U32",
            "s",
            "\"a{x}b\" if x > 0",
            "$1 if $1 == \"a{x}b\" && x > 0",
        ),
        string_case(
            "string_beside_a_literal",
            "t: (Str, U32), x: U32",
            "t",
            "(\"a{x}\", 1)",
            "($1, 1) if $1 == \"a{x}\"",
        ),
        string_case(
            "string_inside_some",
            "o: Option[Str], x: U32",
            "o",
            "Some(\"a{x}b\")",
            "Some($1) if $1 == \"a{x}b\"",
        ),
        string_case(
            "string_choice_that_shares_a_binding",
            "t: (Str, U32), x: U32",
            "t",
            "(\"a{x}\", n) | (\"b{x}\", n)",
            "($1, n) if $1 == \"a{x}\" || $1 == \"b{x}\"",
        ),
        string_case(
            "string_beside_a_float",
            "t: (Str, F32), x: U32",
            "t",
            "(\"a{x}\", 0.5)",
            "($1, $2) if $1 == \"a{x}\" && $2 == 0.5",
        ),
    ]
}

/// Checks one case: the diagnostic, the number of the candidates, and for each candidate the shape,
/// the absence of diagnostics and the meaning.
fn check_case(d: &Dir, c: &Case) {
    let path = d.file(&format!("{}.onsa", c.name), &c.program);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{}: one diagnostic expected, got {diags:?}\n{}", c.name, c.program);
    assert_eq!(code_of(&diags[0]), "E0020", "{}: {}", c.name, diags[0]);
    assert!(!notes_of(&diags[0]).is_empty(), "{}: E0020 shows the rule in a note (§18.1): {}", c.name, diags[0]);
    assert_eq!(fixes_of(&diags[0]).len(), c.cands.len(), "{}: the number of the candidates (§7): {}", c.name, diags[0]);
    for (k, cd) in c.cands.iter().enumerate() {
        let fixed = with_fix(&c.program, &diags[0], k);
        if !cd.head.is_empty() {
            let got = first_arm_head(&canonical(&c.program, &fixed));
            assert_eq!(got, tokens(cd.head), "{}: candidate {}: the first arm is\n{}", c.name, k + 1, fixed);
        }
        let full = if cd.asserts.is_empty() {
            fixed.clone()
        } else {
            let body: String = cd.asserts.lines().map(|l| format!("  {l}\n")).collect();
            format!("{fixed}\ntest \"the meaning of the pattern\" {{\n{body}}}\n")
        };
        let fixed_path = d.file(&format!("{}_fixed{}.onsa", c.name, k + 1), &full);
        let after = check(&fixed_path);
        assert!(
            after.is_empty(),
            "{}: candidate {}: the program after it has diagnostics: {after:?}\n{full}",
            c.name,
            k + 1
        );
        if !cd.asserts.is_empty() {
            let (code, out) = run_tests(&fixed_path);
            assert_eq!(code, 0, "{}: candidate {}: the meaning of the pattern changed:\n{out}\n{full}", c.name, k + 1);
            assert!(out.contains("1 passed, 0 failed"), "{}: candidate {}: {out}", c.name, k + 1);
        }
    }
}

fn check_all(tag: &str, cases: Vec<Case>) {
    let d = Dir::new(tag);
    for c in &cases {
        check_case(&d, c);
    }
}

#[test]
fn a_range_pattern_is_e0020_and_its_candidate_is_the_guard_form_with_the_same_meaning() {
    // §7: `1..<3 =>` is `k if 1 <= k && k < 3 =>`, `1..=3` is `k <= 3`, `1..3` and `1...3` are the two,
    // a range with one end is one comparison (S-278); in `Some(..)`, a tuple, a struct and a choice
    // the same (a choice is one guard when the branches have one shape, S-317); the ends can be of
    // any type; the arm's own guard follows with `&&`.
    check_all("ranges", range_cases());
}

#[test]
fn a_float_pattern_candidate_has_the_shape_of_section_7_and_keeps_its_meaning() {
    // §7: `(0.0, 1.0)` is `(v, v2) if v == 0.0 && v2 == 1.0`, `0.5 | 1.5` is `v if v == 0.5 || v == 1.5`,
    // `(0.5, n) | (1.5, n)` is `(v, n) if ...`, `Some(0.5 | 1.5)` is `Some(v) if ...`, and the arm's own
    // guard follows with `&&` (the choice in parentheses, §3.1). This is W3-15's form; the exact
    // shapes and the meaning are checked here (foreign_candidates.rs checks that there is a guard).
    check_all("floats", float_cases());
}

#[test]
fn a_negated_constant_is_e0020_and_its_candidate_is_the_guard_form() {
    // §7: `-LIMIT` is E0020 with the candidate `x if x == -LIMIT`, in the syntax stage (S-319).
    check_all("negated", negated_constant_cases());
}

#[test]
fn the_guard_forms_of_one_arm_are_one_error_with_one_candidate_joined_with_and() {
    // §7, §18.1 (S-248, S-317, S-319): a range, a float, a name with `@`, a `-` before a constant in
    // one pattern are one error and one candidate; the conditions are joined with `&&`, the branches of
    // a choice with `||`, and the arm's own guard last.
    check_all("mixed", mixed_cases());
}

#[test]
fn an_at_binding_of_a_constant_is_e0020_and_its_candidate_is_the_guard_form() {
    // §7 (S-352): a name whose last segment is a constant's by its spelling, with or without `-`,
    // is a guard form on the right of `@`.
    check_all("at_constants", at_constant_cases());
}

#[test]
fn an_interpolated_string_pattern_is_e0020_and_its_candidate_is_the_guard_form() {
    // §7: the candidate is `v if v == "a{x}b"`. The guard makes a `Str` (§2.4), so the function has
    // `uses {Alloc}` and the program after the candidate has no diagnostic. A `Str` is E0200 in this
    // version, so the programs are checked and not run.
    check_all("strings", string_cases());
}

// ---- Fresh names (S-253): the new binding is not a visible name ------------------------------------

struct Crowd {
    name: &'static str,
    program: &'static str,
}

const CROWDS: &[Crowd] = &[
    Crowd {
        name: "parameters",
        // `x`, `v`, `v2`, `v3`, `w`, `k` and `val` are parameters: none of them may be the new name,
        // and the two new names of the pair are different.
        program: "pub fn f(t: (F32, F32), v: F32, v2: F32, v3: F32, w: F32, k: F32, val: F32, x: F32) -> I32 {\n  var r = 0\n  match t {\n    (0.0, 1.0) => { r = 1 },\n    _ => { r = 0 },\n  }\n  r\n}\n",
    },
    Crowd {
        name: "items_of_the_module",
        // Functions of the module are visible names too (§5.1).
        program: "pub fn v() -> I32 {\n  1\n}\n\npub fn v2() -> I32 {\n  2\n}\n\npub fn val() -> I32 {\n  3\n}\n\npub fn w() -> I32 {\n  4\n}\n\npub fn f(x: F32) -> I32 {\n  var r = 0\n  match x {\n    0.5 | 1.5 => { r = v() + v2() + val() + w() },\n    _ => { r = 0 },\n  }\n  r\n}\n",
    },
    Crowd {
        name: "a_binding_of_an_outer_arm",
        program: "pub fn f(o: Option[F32]) -> I32 {\n  var r = 0\n  match o {\n    Some(v) => {\n      match v {\n        0.5 => { r = 1 },\n        _ => { r = 0 },\n      }\n    },\n    None => { r = 2 },\n  }\n  r\n}\n",
    },
    Crowd {
        name: "a_local_and_a_loop_variable",
        program: "pub fn f(x: F32) -> I32 {\n  var r = 0\n  for v in 0..<3 {\n    let v2 = v\n    match x {\n      0.5 => { r = r + v2 },\n      _ => { r = r + 0 },\n    }\n  }\n  r\n}\n",
    },
    Crowd {
        name: "a_binding_of_the_same_pattern",
        // The pattern binds `v` itself.
        program: "pub fn f(t: (F32, I32)) -> I32 {\n  var r = 0\n  match t {\n    (0.5, v) => { r = v },\n    _ => { r = 0 },\n  }\n  r\n}\n",
    },
    Crowd {
        name: "a_range_with_the_names_of_the_template",
        // `r` is a `var` of the function, `i`, `j`, `k`, `n` and `v` are visible.
        program: "pub fn f(n: I32, i: I32, j: I32, k: I32, v: I32) -> I32 {\n  var r = 0\n  match n {\n    1..<3 => { r = i + j + k + v },\n    _ => { r = 0 },\n  }\n  r\n}\n",
    },
    Crowd {
        name: "a_negated_constant",
        program: "const LIMIT: I32 = 4\n\npub fn f(x: I32, v: I32, v2: I32) -> I32 {\n  var r = 0\n  match x {\n    -LIMIT => { r = v + v2 },\n    _ => { r = 0 },\n  }\n  r\n}\n",
    },
    Crowd {
        name: "an_interpolated_name",
        // `v` is interpolated (and a parameter): the guard `v == \"a{v}\"` must not bind it again.
        program: "pub fn f(s: Str, v: U32) -> I32 uses {Alloc} {\n  var r = 0\n  match s {\n    \"a{v}\" => { r = 1 },\n    _ => { r = 0 },\n  }\n  r\n}\n",
    },
    Crowd {
        name: "a_closure",
        program: "use std.array\n\npub fn f() -> [I32; 2] {\n  array.from_fn(fn(i) {\n    let v: F32 = 0.5\n    var r = 0\n    match v {\n      0.5 => { r = 1 },\n      _ => { r = 0 },\n    }\n    r\n  })\n}\n",
    },
    Crowd {
        name: "two_arms",
        // The first arm binds `v`; the second arm is another scope, but the first candidate must not
        // make the second one collide.
        program: "pub fn f(o: Option[I32], x: F32) -> I32 {\n  var r = 0\n  match o {\n    Some(v) => { r = v },\n    None => {\n      match x {\n        1.5 => { r = 2 },\n        _ => { r = 3 },\n      }\n    },\n  }\n  r\n}\n",
    },
];

#[test]
fn the_new_binding_of_a_candidate_is_not_a_visible_name() {
    // §7 (S-253): the name of the new binding is not decided, but it is not a name that is visible at
    // the arm (a parameter, an item of the module, a local, a loop variable, a binding of an outer arm
    // or of the same pattern, an interpolated name), and after the candidate there is no E0304 (§5.1).
    let d = Dir::new("crowds");
    for c in CROWDS {
        let path = d.file(&format!("{}.onsa", c.name), c.program);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{}: one diagnostic expected, got {diags:?}", c.name);
        assert_eq!(code_of(&diags[0]), "E0020", "{}: {}", c.name, diags[0]);
        let fixes = fixes_of(&diags[0]);
        assert!(!fixes.is_empty(), "{}: no candidate: {}", c.name, diags[0]);
        for k in 0..fixes.len() {
            let fixed = with_fix(c.program, &diags[0], k);
            let after = check(&d.file(&format!("{}_fixed{}.onsa", c.name, k + 1), &fixed));
            assert!(
                after.is_empty(),
                "{}: candidate {}: the program after it has diagnostics: {after:?}\n{fixed}",
                c.name,
                k + 1
            );
        }
    }
}

// ---- Minimal edits (S-251), the comments, the main span --------------------------------------------

const COMMENTS: &str = "\
pub fn f(t: (F32, I32)) -> I32 {
  var r = 0
  match t {
    (0.5, // keep this
     n) => { r = n }, // and this
    _ => { r = 0 },
  }
  r
}

test \"the meaning\" {
  assert f((0.5, 7)) == 7
  assert f((1.5, 7)) == 0
}
";

const COMMENTS_RANGE: &str = "\
pub fn f(t: (I32, I32)) -> I32 {
  var r = 0
  match t {
    (1..<3, // keep this
     n) => { r = n }, // and this
    _ => { r = 0 },
  }
  r
}

test \"the meaning\" {
  assert f((2, 7)) == 7
  assert f((3, 7)) == 0
}
";

#[test]
fn a_guard_form_candidate_keeps_the_comments_and_the_other_tokens() {
    // §18.1 (S-251): an edit replaces the tokens it changes and never a comment between them; the
    // tokens outside the form (`n`) and the comments stay where they were; the program after the
    // candidate has no diagnostic and keeps its meaning.
    let d = Dir::new("comments");
    for (name, src) in [("float", COMMENTS), ("range", COMMENTS_RANGE)] {
        let path = d.file(&format!("{name}.onsa"), src);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{name}: {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0020", "{name}: {}", diags[0]);
        assert_eq!(fixes_of(&diags[0]).len(), 1, "{name}: {}", diags[0]);
        let edits = edits_of(fixes_of(&diags[0])[0]);
        for old in replaced_texts(src, &edits) {
            assert!(!old.contains("//"), "{name}: an edit replaces a comment: `{old}`");
            assert!(
                !old.contains("n)"),
                "{name}: an edit replaces the token `n` that is not part of the form: `{old}`"
            );
        }
        let fixed = with_fix(src, &diags[0], 0);
        assert_eq!(
            fixed.matches("// keep this").count(),
            1,
            "{name}: the comment inside the pattern is kept:\n{fixed}"
        );
        assert_eq!(fixed.matches("// and this").count(), 1, "{name}: the comment after the arm is kept:\n{fixed}");
        assert!(
            tokens(&fixed).windows(3).any(|w| w[0] == "," && w[1] == "n" && w[2] == ")"),
            "{name}: the token `n` stays after the `,`:\n{fixed}"
        );
        let after_path = d.file(&format!("{name}_fixed.onsa"), &fixed);
        assert!(check(&after_path).is_empty(), "{name}: the program after the candidate has diagnostics:\n{fixed}");
        let (code, out) = run_tests(&after_path);
        assert_eq!(code, 0, "{name}: the meaning changed:\n{out}\n{fixed}");
    }
}

#[test]
fn the_candidate_for_the_rest_of_a_struct_pattern_replaces_the_dots_only() {
    // §7, §18.1 (S-109, S-251): the candidate lists the remaining fields with `_` in the order of the
    // declaration, in place of `..`: one edit, and it replaces `..` and nothing else. (The text of the
    // candidate is pinned in fixes/e0020_patterns_rest_forms.onsa.)
    let src = "pub struct P3 {\n  x: I32,\n  y: I32,\n  z: I32,\n}\n\npub fn f(p: P3) -> I32 {\n  match p {\n    P3 { z: c, .. } => c,\n  }\n}\n";
    let d = Dir::new("rest");
    let path = d.file("rest.onsa", src);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!(code_of(&diags[0]), "E0020", "{}", diags[0]);
    assert!(!notes_of(&diags[0]).is_empty(), "no note with the rule: {}", diags[0]);
    let fixes = fixes_of(&diags[0]);
    assert_eq!(fixes.len(), 1, "{}", diags[0]);
    let edits = edits_of(fixes[0]);
    assert_eq!(edits.len(), 1, "one edit: {}", diags[0]);
    assert_eq!(replaced_texts(src, &edits), vec!["..".to_string()], "the edit replaces `..` and nothing else");
    let span = &diags[0]["span"];
    assert_eq!(
        (span["line"].as_u64(), span["col"].as_u64()),
        (Some(9), Some(16)),
        "the main span starts at `..` (S-316): {}",
        diags[0]
    );
    assert_eq!(
        (span["end_line"].as_u64(), span["end_col"].as_u64()),
        (Some(9), Some(18)),
        "and ends after it: {}",
        diags[0]
    );
    let fixed = with_fix(src, &diags[0], 0);
    assert!(
        check(&d.file("rest_fixed.onsa", &fixed)).is_empty(),
        "the program after the candidate has diagnostics:\n{fixed}"
    );
}

#[test]
fn the_main_span_of_a_string_pattern_and_of_a_negated_constant_is_the_form() {
    // §18.1 (S-316): the main range is the range of the foreign form, from its first token to its last:
    // the string for an interpolated string, `-LIMIT` for a negated constant.
    let d = Dir::new("spans");
    let string =
        "pub fn f(s: Str, x: U32) -> I32 uses {Alloc} {\n  match s {\n    \"a{x}b\" => 1,\n    _ => 0,\n  }\n}\n";
    let negated =
        "const LIMIT: I32 = 4\n\npub fn f(x: I32) -> I32 {\n  match x {\n    -LIMIT => 1,\n    _ => 0,\n  }\n}\n";
    for (name, src, line, col, end_col) in [("string", string, 3, 5, 12), ("negated", negated, 5, 5, 11)] {
        let diags = check(&d.file(&format!("{name}.onsa"), src));
        assert_eq!(diags.len(), 1, "{name}: {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0020", "{name}: {}", diags[0]);
        let s = &diags[0]["span"];
        let got = (s["line"].as_u64(), s["col"].as_u64(), s["end_line"].as_u64(), s["end_col"].as_u64());
        assert_eq!(got, (Some(line), Some(col), Some(line), Some(end_col)), "{name}: {}", diags[0]);
    }
}

// ---- Forms with no candidate: E0002 (S-317, S-319, §7) ---------------------------------------------

/// A function with the wrong first arm, for the E0002 tests.
fn bad(prelude: &str, params: &str, scrut: &str, arm: &str, body: &str) -> String {
    prog(prelude, params, scrut, arm, body, " uses {Alloc}")
}

fn differing_branches(tag: &str, strings: bool) {
    // §7 (S-317, S-319): a choice is one guard only when every branch has the same shape once the
    // ranges, floats, strings, constants with `-` and `@` bindings are replaced; any other is E0002 and
    // the guard has no candidate (it would match other values).
    let l = LIMITS;
    let forms: Vec<(&str, String)> = vec![
        ("range_and_none", bad("", "o: Option[I32]", "o", "Some(1..<3) | None", "1")),
        ("range_with_other_literals", bad("", "t: (I32, I32)", "t", "(1..<3, 1) | (5..<7, 2)", "1")),
        ("range_and_a_literal", bad("", "n: I32", "n", "1..<3 | 7", "1")),
        ("range_and_a_wildcard", bad("", "n: I32", "n", "1..<3 | _", "1")),
        ("range_and_a_binding", bad("", "o: Option[I32]", "o", "Some(1..<3) | Some(x)", "x")),
        ("ranges_in_other_places", bad("", "t: (I32, I32)", "t", "(1..<3, _) | (_, 5..<7)", "1")),
        ("one_ended_range_and_a_literal", bad("", "n: I32", "n", "..<3 | 7", "1")),
        ("string_and_a_literal", bad("", "s: Str, x: U32", "s", "\"a\" | \"b{x}\"", "1")),
        ("string_and_an_escape", bad("", "s: Str, x: U32", "s", "\"a{x}\" | \"{{\"", "1")),
        ("string_and_none", bad("", "o: Option[Str], x: U32", "o", "Some(\"a{x}\") | None", "1")),
        ("string_with_other_literals", bad("", "t: (Str, U32), x: U32", "t", "(\"a{x}\", 1) | (\"b{x}\", 2)", "1")),
        ("negated_and_the_constant", bad(l, "x: I32", "x", "-LIMIT | LIMIT", "1")),
        ("negated_and_a_literal", bad(l, "x: I32", "x", "-LIMIT | 1", "1")),
        ("negated_and_a_wildcard", bad(l, "x: I32", "x", "-LIMIT | _", "1")),
        ("negated_with_other_literals", bad(l, "t: (I32, I32)", "t", "(-LIMIT, 1) | (-OTHER, 2)", "1")),
        ("at_before_the_bar", bad("", "n: I32", "n", "k @ 1 | 2", "k")),
        ("at_with_two_names", bad("", "n: I32", "n", "a @ 1 | b @ 2", "1")),
        ("at_and_a_wildcard", bad("", "n: I32", "n", "k @ 1 | _", "1")),
        ("at_and_a_literal_in_a_tuple", bad("", "t: (I32, F32)", "t", "(k @ 1..<3, 0.5) | (5, 1.5)", "k")),
        ("string_and_a_float_elsewhere", bad("", "t: (F32, Str), x: U32", "t", "(0.5, \"a{x}\") | (1.5, \"b\")", "1")),
        ("range_and_a_binding_beside_a_float", bad("", "t: (F32, I32)", "t", "(0.5, 1..<3) | (1.5, n)", "n")),
    ];
    let d = Dir::new(tag);
    for (name, src) in forms.iter().filter(|(n, _)| n.contains("string") == strings) {
        let path = d.file(&format!("{name}.onsa"), src);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{name}: one diagnostic expected, got {diags:?}\n{src}");
        assert_eq!(code_of(&diags[0]), "E0002", "{name}: {}", diags[0]);
        assert!(fixes_of(&diags[0]).is_empty(), "{name}: a candidate for a choice whose branches differ: {}", diags[0]);
    }
}

#[test]
fn branches_that_differ_once_the_forms_are_replaced_are_e0002_with_no_candidate() {
    differing_branches("noshape", false);
}

#[test]
fn branches_that_differ_once_the_strings_are_replaced_are_e0002_with_no_candidate() {
    differing_branches("noshape_str", true);
}

fn comment_in_a_branch(tag: &str, strings: bool) {
    // §18.1 (S-251, S-317): to make one guard of a choice the branches are joined, and a comment in
    // the part that goes cannot be kept by an edit that does not touch comments, so there is no
    // candidate: E0002. (A float is in negative/foreign_float_pattern.onsa.)
    let l = LIMITS;
    let forms: Vec<(&str, String)> = vec![
        ("range", bad("", "n: I32", "n", "1..<3 | // the second range\n    5..<7", "1")),
        ("string", bad("", "s: Str, x: U32", "s", "\"a{x}\" | // the second string\n    \"b{x}\"", "1")),
        ("negated", bad(l, "x: I32", "x", "-LIMIT | // the second constant\n    -OTHER", "1")),
        ("at", bad("", "n: I32", "n", "k @ 1 | // the second arm\n    k @ 2", "k")),
    ];
    let d = Dir::new(tag);
    for (name, src) in forms.iter().filter(|(n, _)| (*n == "string") == strings) {
        let diags = check(&d.file(&format!("{name}.onsa"), src));
        assert_eq!(diags.len(), 1, "{name}: one diagnostic expected, got {diags:?}\n{src}");
        assert_eq!(code_of(&diags[0]), "E0002", "{name}: {}", diags[0]);
        assert!(fixes_of(&diags[0]).is_empty(), "{name}: a candidate that deletes a comment: {}", diags[0]);
    }
}

#[test]
fn a_comment_in_a_branch_that_the_candidate_would_delete_leaves_no_candidate() {
    comment_in_a_branch("comment_branch", false);
}

#[test]
fn a_comment_in_a_branch_of_strings_leaves_no_candidate() {
    comment_in_a_branch("comment_branch_str", true);
}

#[test]
fn an_at_binding_that_is_not_a_literal_or_a_range_is_e0002_with_a_note_and_no_candidate() {
    // §7: `s @ Some(_)` is E0002, and a note shows that the guard or a nested `match` is the way to
    // write it. The right side is not a literal, a constant, a range or a choice of them (S-352: a
    // constant by its spelling, `k @ LIMIT`, has the guard form, in `at_cases`).
    let forms: Vec<(&str, String)> = vec![
        ("an_enum_pattern", bad("", "o: Option[I32]", "o", "s @ Some(_)", "1")),
        ("an_enum_pattern_with_a_literal", bad("", "o: Option[I32]", "o", "s @ Some(1)", "1")),
        ("a_tuple", bad("", "t: (I32, I32)", "t", "u @ (1, 2)", "1")),
        ("a_binding", bad("", "n: I32", "n", "k @ m", "1")),
        ("a_wildcard_in_the_choice", bad("", "n: I32", "n", "k @ (1 | _)", "k")),
        // An enum variant is no constant by its spelling (S-352): E0002.
        ("an_enum_variant", bad(COLOR, "c: Color", "c", "k @ Color.Red", "1")),
        ("another_at", bad("", "n: I32", "n", "a @ b @ 1", "a")),
    ];
    let d = Dir::new("at_note");
    for (name, src) in &forms {
        let diags = check(&d.file(&format!("{name}.onsa"), src));
        assert_eq!(diags.len(), 1, "{name}: one diagnostic expected, got {diags:?}\n{src}");
        assert_eq!(code_of(&diags[0]), "E0002", "{name}: {}", diags[0]);
        assert!(
            fixes_of(&diags[0]).is_empty(),
            "{name}: a candidate for an `@` binding with no guard form: {}",
            diags[0]
        );
        let notes = notes_of(&diags[0]);
        assert!(!notes.is_empty(), "{name}: no note that shows the guard or a nested `match` (§7): {}", diags[0]);
        assert!(
            notes.iter().all(|n| n["message"].as_str().is_some_and(|m| !m.is_empty())),
            "{name}: an empty note: {}",
            diags[0]
        );
    }
}

// ---- `-(-1)` (S-227, R-156) -------------------------------------------------------------------------

#[test]
fn a_negated_negative_literal_in_a_pattern_is_e0002_and_the_message_is_not_about_floats() {
    // §7 (S-227): `-(-1)` is not a literal, so it cannot be a pattern: E0002. R-156: the message said
    // "float literals cannot be patterns", which is another rule; it must not talk about floats. The
    // spec does not fix the words, so only this is checked.
    let forms = ["-(-1)", "-(-128)", "-(-(1))", "Some(-(-1))", "(-(-2), _)", "1 | -(-2)"];
    let d = Dir::new("negneg");
    for (i, pat) in forms.iter().enumerate() {
        let scrut = if pat.starts_with("Some") {
            "o"
        } else if pat.starts_with('(') {
            "t"
        } else {
            "n"
        };
        let params = match scrut {
            "o" => "o: Option[I32]",
            "t" => "t: (I32, I32)",
            _ => "n: I32",
        };
        let src = prog("", params, scrut, pat, "1", "");
        let diags = check(&d.file(&format!("neg{i}.onsa"), &src));
        assert_eq!(diags.len(), 1, "{pat}: one diagnostic expected, got {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0002", "{pat}: {}", diags[0]);
        let message = diags[0]["message"].as_str().unwrap_or_default().to_lowercase();
        assert!(!message.contains("float"), "{pat}: the message is about floats (R-156): {}", diags[0]);
        assert!(fixes_of(&diags[0]).is_empty(), "{pat}: a candidate: {}", diags[0]);
    }
}

// ---- A range with one end in the header of a loop (S-278) -----------------------------------------------

#[test]
#[ignore = "W3-09: the cases of `par` declare a flow, whose inputs are written with `at`"]
fn a_range_with_one_end_in_a_header_is_e0002_with_a_note_and_no_candidate() {
    // §7 (S-278): `for i in 0.. {` and `for i in ..<n {` are E0002 and a note shows the two-ended
    // spelling; no candidate (what the missing end is, nothing says). The same in the header of a
    // `par` (§11.5). (A `{` after the range symbol that opens a block expression is another error, S-338, in the
    // last test.)
    let loops = [
        ("from", "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for _ in 5.. {\n    c = c + 1\n  }\n  c\n}\n"),
        ("from_zero", "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for _ in 0.. {\n    c = c + 1\n  }\n  c\n}\n"),
        ("up_to", "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for _ in ..<n {\n    c = c + 1\n  }\n  c\n}\n"),
        ("through", "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for _ in ..=n {\n    c = c + 1\n  }\n  c\n}\n"),
        (
            "up_to_two_dots",
            "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for _ in ..n {\n    c = c + 1\n  }\n  c\n}\n",
        ),
        (
            "par_from",
            "pub flow f(x: F32 at sample) -> [F32; 4] at sample {\n  par i in 0.. {\n    x * i.round_f32()\n  }\n}\n",
        ),
        (
            "par_up_to",
            "pub flow f(x: F32 at sample) -> [F32; 4] at sample {\n  par i in ..<4 {\n    x * i.round_f32()\n  }\n}\n",
        ),
    ];
    let d = Dir::new("header");
    for (name, src) in loops {
        let diags = check(&d.file(&format!("{name}.onsa"), src));
        assert_eq!(diags.len(), 1, "{name}: one diagnostic expected, got {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0002", "{name}: {}", diags[0]);
        assert!(
            fixes_of(&diags[0]).is_empty(),
            "{name}: a candidate for a range with one end in a header: {}",
            diags[0]
        );
        let notes = notes_of(&diags[0]);
        assert!(!notes.is_empty(), "{name}: no note: {}", diags[0]);
        assert!(
            notes.iter().all(|n| n["message"].as_str().is_some_and(|m| !m.is_empty())),
            "{name}: an empty note: {}",
            diags[0]
        );
    }
}

// ---- `onsa fmt` stops at the syntax stage (§18.2) ---------------------------------------------------

#[test]
fn fmt_does_not_rewrite_a_file_with_a_guard_form_pattern() {
    // §18.2: `onsa fmt` and `fmt --check` do not rewrite a file with a diagnostic of the syntax stage
    // and exit with 2. The forms of §7 that have the guard form as a candidate and the E0002 of a
    // choice with no candidate are all found in the syntax stage. `g` is badly spaced, so a formatter
    // that went on would change the file. (The `..` of a struct pattern is found where the fields are
    // counted, S-366: the next test.)
    let forms: Vec<(&str, String)> = vec![
        ("range", prog("", "n: I32", "n", "1..<3", "1", "")),
        ("range_one_ended", prog("", "n: I32", "n", "5..", "1", "")),
        ("at", prog("", "n: I32", "n", "k @ 1..<3", "k", "")),
        ("string", prog("", "s: Str, x: U32", "s", "\"a{x}\"", "1", " uses {Alloc}")),
        ("negated", prog(LIMITS, "x: I32", "x", "-LIMIT", "1", "")),
        ("choice_without_a_shape", prog("", "o: Option[I32]", "o", "Some(1..<3) | None", "1", "")),
        ("negated_negative", prog("", "n: I32", "n", "-(-1)", "1", "")),
    ];
    let d = Dir::new("fmt");
    for (name, f) in &forms {
        let src = format!("{f}\npub fn g()->I32{{\n  2\n}}\n");
        let path = d.file(&format!("{name}.onsa"), &src);
        for args in [vec!["fmt", path.as_str()], vec!["fmt", "--check", path.as_str()]] {
            let out = Command::new(ONSA).args(&args).output().expect("run onsa");
            assert_eq!(out.status.code(), Some(2), "{name}: onsa {args:?}: {out:?}");
            assert_eq!(std::fs::read_to_string(&path).unwrap(), src, "{name}: onsa {args:?} wrote the file");
        }
    }
}

#[test]
fn fmt_formats_a_file_with_the_rest_of_a_struct_pattern_and_keeps_it() {
    // S-366 (decided 2026-10-09): the `..` of a struct pattern is read by the syntax stage and is
    // E0020 where the fields are counted, so `onsa fmt` formats the file and writes the `..` back.
    let d = Dir::new("fmt_rest");
    let src = "pub struct P3 {\n  x: I32,\n  y: I32,\n}\n\npub fn f(p: P3) -> I32 {\n  match p {\n    P3 { x: a,   .. } => a,\n  }\n}\n\npub fn g()->I32{\n  2\n}\n";
    let path = d.file("rest.onsa", src);
    let out = Command::new(ONSA).args(["fmt", path.as_str()]).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "onsa fmt: {out:?}");
    let formatted = std::fs::read_to_string(&path).unwrap();
    assert!(formatted.contains("P3 { x: a, .. } => a"), "the `..` is written back:\n{formatted}");
    assert!(formatted.contains("pub fn g() -> I32 {"), "the file is formatted:\n{formatted}");
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!(code_of(&diags[0]), "E0020", "{}", diags[0]);
}

// ---- A `{` at the start of an expression in a header is the body (S-338) -------------------------------

#[test]
#[ignore = "W3-09: the cases of `par` declare a flow, whose inputs are written with `at`"]
fn a_block_at_the_start_of_an_expression_in_a_header_is_e0002_with_a_note_and_no_candidate() {
    // §3.1, §4.4 (S-338, decided 2026-10-09): in the header of an `if`, `while`, `match`, `for` or
    // `par`, a `{` at the start of an expression outside parentheses starts the body, so a block
    // expression is written in parentheses, like a struct literal. The violation is E0002 with a note and
    // no candidate. It is not the range with one end (`for i in 0.. {`, S-278, in the test above): both
    // are E0002 with a note, and the body that follows a range with one end is not a block expression.
    let bad = [
        (
            "for_end",
            "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for i in 0..<{ n } {\n    c = c + i\n  }\n  c\n}\n",
        ),
        ("if_condition", "pub fn f(c: Bool) -> U32 {\n  if { c } {\n    1\n  } else {\n    2\n  }\n}\n"),
        (
            "while_comparison",
            "pub fn f(x: U32, n: U32) -> U32 {\n  var t: U32 = 0\n  while x < { n } {\n    t = t + 1\n    break\n  }\n  t\n}\n",
        ),
        ("match_scrutinee", "pub fn f(n: U32) -> U32 {\n  match { n } {\n    _ => 1,\n  }\n}\n"),
        (
            "for_iterated",
            "pub fn f(xs: [U32; 3]) -> U32 {\n  var t: U32 = 0\n  for x in { xs } {\n    t = t + x\n  }\n  t\n}\n",
        ),
        (
            "for_end_after_an_operator",
            "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for i in 0..<n + { 1 } {\n    c = c + i\n  }\n  c\n}\n",
        ),
        (
            "par_end",
            "pub flow f(x: F32 at sample) -> [F32; 4] at sample {\n  par i in 0..<{ 4 } {\n    x * i.round_f32()\n  }\n}\n",
        ),
    ];
    let good = [
        (
            "for_end",
            "pub fn f(n: U32) -> U32 {\n  var c: U32 = 0\n  for i in 0..<({ n }) {\n    c = c + i\n  }\n  c\n}\n",
        ),
        ("if_condition", "pub fn f(c: Bool) -> U32 {\n  if ({ c }) {\n    1\n  } else {\n    2\n  }\n}\n"),
        (
            "while_comparison",
            "pub fn f(x: U32, n: U32) -> U32 {\n  var t: U32 = 0\n  while x < ({ n }) {\n    t = t + 1\n    break\n  }\n  t\n}\n",
        ),
        (
            "an_if_as_the_end",
            "pub fn f(c: Bool) -> U32 {\n  var t: U32 = 0\n  for i in 0..<if c { 4 } else { 8 } {\n    t = t + i\n  }\n  t\n}\n",
        ),
        (
            "an_if_as_the_condition",
            "pub fn f(a: Bool, b: Bool) -> U32 {\n  if if a { b } else { false } {\n    1\n  } else {\n    2\n  }\n}\n",
        ),
    ];
    let d = Dir::new("header_block");
    for (name, src) in bad {
        let diags = check(&d.file(&format!("bad_{name}.onsa"), src));
        assert_eq!(diags.len(), 1, "{name}: one diagnostic expected, got {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0002", "{name}: {}", diags[0]);
        assert!(fixes_of(&diags[0]).is_empty(), "{name}: a candidate: {}", diags[0]);
        let notes = notes_of(&diags[0]);
        assert!(!notes.is_empty(), "{name}: no note (S-338): {}", diags[0]);
        assert!(
            notes.iter().all(|n| n["message"].as_str().is_some_and(|m| !m.is_empty())),
            "{name}: an empty note: {}",
            diags[0]
        );
    }
    for (name, src) in good {
        let diags = check(&d.file(&format!("good_{name}.onsa"), src));
        assert!(diags.is_empty(), "{name}: a block in parentheses, or after a keyword, is not an error: {diags:?}");
    }
}
