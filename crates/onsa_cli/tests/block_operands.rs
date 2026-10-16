//! Block-like expressions as the operands of an operator (spec §3.1, §2.5, §6.1, §18.1, §18.2; S-537; W3-13/t U1).
//!
//! The case files in `tests/spec/` pin the code and the line of each diagnostic and the text after each
//! candidate (`negative/block_operand_*.onsa`, `fixes/block_operand_*.onsa`), and the values of the forms in
//! parentheses are in `ops/block_operand_*.onsa`. These tests say what those cannot: that a candidate of an E0013
//! is made of insertions of `(` and `)` and nothing else (§18.1: an edit changes only the token it changes), that
//! one E0013 covers every block-like operand of an expression, that applying the first candidate over and over to
//! a file with an error in each of several units reaches a file with no diagnostic, that the candidates of the
//! other diagnostics (a line that starts with an operator, a call of a block-like expression) end with
//! a clean program, that the arm list `{ 1 } - 1 =>` is an E0002 with no candidate and no E0013 (§2.5), and that
//! `onsa fmt` writes no file that has an E0013 (exit code 2, §18.2) and keeps the parentheses of an operand
//! (docs/onsa-tools.md §3.3).
//!
//! The main position of an E0013 is the first token of the first block-like operand with no parentheses
//! (§3.1), so the position is asserted where the expression is on one line. Every expected text is written from the
//! spec; none is taken from the output of the compiler. A test that needs the E0013 runs ignored until W3-13/i; each
//! ignore names the work that removes it (a test cannot be silenced by `tests/pending.toml`).

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_block_operands_{}_{tag}", std::process::id()));
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

fn span_start(d: &Value) -> Pos {
    let s = &d["span"];
    let get = |k: &str| usize::try_from(s[k].as_u64().unwrap_or_else(|| panic!("no `{k}` in {s}"))).unwrap();
    (get("line"), get("col"))
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

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// A file with a struct, a function that takes two numbers and `pub fn f(params) -> ret { expr }`.
fn wrap(params: &str, ret: &str, expr: &str) -> String {
    format!(
        "pub struct Pt {{\n  x: I32,\n}}\n\npub fn add(a: I32, b: I32) -> I32 {{\n  a + b\n}}\n\npub fn f({params}) -> {ret} {{\n  {expr}\n}}\n"
    )
}

// ---- E0013: one diagnostic, one candidate, made of parentheses (§3.1, §18.1) ---------------------------

/// (the parameters, the result, the expression with no parentheses, the same with the candidate applied).
type Form = (&'static str, &'static str, &'static str, &'static str);

const FORMS: &[Form] = &[
    ("c: Bool", "I32", "if c { 1 } else { 2 } + 10", "(if c { 1 } else { 2 }) + 10"),
    ("c: Bool", "I32", "10 + if c { 1 } else { 2 }", "10 + (if c { 1 } else { 2 })"),
    ("o: Option[I32]", "I32", "match o { Some(n) => n, None => 0 } * 2", "(match o { Some(n) => n, None => 0 }) * 2"),
    ("n: I32", "I32", "{ n } - 10", "({ n }) - 10"),
    ("c: Bool", "I32", "-if c { 1 } else { 2 }", "-(if c { 1 } else { 2 })"),
    ("c: Bool", "Bool", "!if c { true } else { false }", "!(if c { true } else { false })"),
    ("c: Bool, xs: [I32; 2], ys: [I32; 2]", "I32", "if c { xs } else { ys }[1]", "(if c { xs } else { ys })[1]"),
    ("c: Bool, p: Pt, q: Pt", "I32", "if c { p } else { q }.x", "(if c { p } else { q }).x"),
    ("c: Bool, xs: [I32; 2], ys: [I32; 2]", "U32", "if c { xs } else { ys }.len()", "(if c { xs } else { ys }).len()"),
    ("c: Bool, a: I32, b: I32", "F64", "if c { a } else { b } as F64", "(if c { a } else { b }) as F64"),
    (
        "a: Bool, b: Bool, c: Bool",
        "I32",
        "if a { 1 } else { 2 } + if b { 10 } else { 20 } + if c { 100 } else { 200 }",
        "(if a { 1 } else { 2 }) + (if b { 10 } else { 20 }) + (if c { 100 } else { 200 })",
    ),
    (
        "c: Bool, o: Option[I32]",
        "I32",
        "if c { 1 } else { 2 } + match o { Some(n) => n, None => 0 }",
        "(if c { 1 } else { 2 }) + (match o { Some(n) => n, None => 0 })",
    ),
    (
        "a: Bool, b: Bool",
        "I32",
        "-if a { 1 } else { 2 } + if b { 3 } else { 4 }",
        "-(if a { 1 } else { 2 }) + (if b { 3 } else { 4 })",
    ),
    (
        "a: Bool, b: Bool",
        "I32",
        "if a { 1 } else { 2 } + (if b { 3 } else { 4 })",
        "(if a { 1 } else { 2 }) + (if b { 3 } else { 4 })",
    ),
];

#[test]
fn an_expression_with_block_like_operands_is_one_e0013_with_one_candidate() {
    let d = Dir::new("one");
    for (params, ret, expr, fixed) in FORMS {
        let src = wrap(params, ret, expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0013", expr);
        let fixes = fixes_of(diag);
        assert_eq!(fixes.len(), 1, "{expr}: one candidate (§3.1): {diag}");
        let after = apply(&src, &edits_of(fixes[0]));
        assert_eq!(after, wrap(params, ret, fixed), "{expr}: the text after the candidate");
    }
}

#[test]
fn the_candidate_of_an_e0013_inserts_only_parentheses_and_leaves_no_diagnostic() {
    // §18.1: an edit changes only the token it changes, so the candidate is made of insertions of `(` and
    // `)` (empty ranges), one pair for each operand; and these forms type check, so nothing is left.
    let d = Dir::new("parens");
    for (params, ret, expr, fixed) in FORMS {
        let src = wrap(params, ret, expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0013", expr);
        let edits = edits_of(fixes_of(diag)[0]);
        let pairs = fixed.matches('(').count() - expr.matches('(').count();
        assert_eq!(edits.len(), 2 * pairs, "{expr}: two edits for each operand put in parentheses");
        for e in &edits {
            assert_eq!(e.start, e.end, "{expr}: an insertion has an empty range");
            assert!(e.replace == "(" || e.replace == ")", "{expr}: only parentheses are inserted: {:?}", e.replace);
        }
        let after = d.file("b.onsa", &apply(&src, &edits));
        let again = check(&after);
        assert!(again.is_empty(), "{expr}: the candidate leaves {again:?}");
    }
}

#[test]
fn the_main_position_is_the_first_token_of_the_first_operand_without_parentheses() {
    // §3.1: the main position is the first block-like operand with no parentheses of the expression.
    let d = Dir::new("position");
    let cases: [(&str, &str, &str, usize); 4] = [
        ("c: Bool", "I32", "if c { 1 } else { 2 } + 10", 3),
        ("c: Bool", "I32", "10 + if c { 1 } else { 2 }", 8),
        ("a: Bool, b: Bool", "I32", "(if a { 1 } else { 2 }) + if b { 3 } else { 4 }", 29),
        ("a: Bool, b: Bool", "I32", "if a { 1 } else { 2 } + if b { 3 } else { 4 }", 3),
    ];
    for (params, ret, expr, col) in cases {
        let src = wrap(params, ret, expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0013", expr);
        assert_eq!(span_start(diag), (10, col), "{expr}: the line and the column of the main position");
    }
}

#[test]
fn the_first_candidate_applied_over_and_over_reaches_a_file_with_no_diagnostic() {
    // One E0013 in each of several units, and the same unit twice over (an `if` at the end of a line that
    // starts with an operator): applying the first candidate of the first diagnostic until none is left ends in
    // a few steps with a clean file, and the number of diagnostics never goes up (§18.1).
    let src = "pub fn a(c: Bool) -> I32 {\n  if c { 1 } else { 2 } + 10\n}\n\n\
               pub fn b(o: Option[I32]) -> I32 {\n  -match o { Some(n) => n, None => 0 }\n}\n\n\
               pub fn d(c: Bool, xs: [I32; 2], ys: [I32; 2]) -> I32 {\n  if c { xs } else { ys }[0] + if c { 1 } else { 2 }\n}\n\n\
               pub fn e(c: Bool) -> I32 {\n  let r = if c { 1 } else { 2 }\n    + 1\n  r\n}\n";
    let dir = Dir::new("loop");
    let mut text = src.to_string();
    let mut last = usize::MAX;
    for step in 0..8 {
        let path = dir.file("a.onsa", &text);
        let diags = check(&path);
        if diags.is_empty() {
            assert!(step >= 4, "four units have an error: {step} steps");
            return;
        }
        assert!(diags.len() < last, "step {step}: the diagnostics do not go down: {diags:?}");
        last = diags.len();
        let first = &diags[0];
        let fixes = fixes_of(first);
        assert!(!fixes.is_empty(), "step {step}: no candidate for {first}");
        text = apply(&text, &edits_of(fixes[0]));
    }
    panic!("no clean file after 8 candidates:\n{text}");
}

// ---- the candidates of other diagnostics (§2.5, §6.1, §3.1) -------------------------------------------

#[test]
fn the_candidate_of_a_line_that_starts_with_an_operator_leaves_a_clean_program() {
    let d = Dir::new("leading");
    // (the expression on two lines, the text after the candidate).
    let cases: [(&str, &str); 2] = [
        ("if c { 1 } else { 2 }\n  + 10", "(if c { 1 } else { 2 }) +\n  10"),
        ("match o { Some(n) => n, None => 0 }\n  * 2", "(match o { Some(n) => n, None => 0 }) *\n  2"),
    ];
    for (expr, fixed) in cases {
        let src = wrap("c: Bool, o: Option[I32]", "I32", expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0020", expr);
        let fixes = fixes_of(diag);
        assert_eq!(fixes.len(), 1, "{expr}: one candidate: {diag}");
        let after = apply(&src, &edits_of(fixes[0]));
        assert_eq!(after, wrap("c: Bool, o: Option[I32]", "I32", fixed), "{expr}");
        let again = check(&d.file("b.onsa", &after));
        assert!(again.is_empty(), "{expr}: the candidate leaves {again:?}");
    }
}

#[test]
fn the_call_of_a_block_like_expression_is_an_e0020_with_the_parenthesized_dot_call_as_its_candidate() {
    // §6.1, §3.1: `if c { h } else { g }(1)` is `(if c { h } else { g }).(1)`; the call `(` is not
    // a postfix symbol of the E0013 list, so the original is one E0020.
    let d = Dir::new("call");
    let src = "pub fn f(c: Bool, h: fn(I32) -> I32, g: fn(I32) -> I32) -> I32 {\n  if c { h } else { g }(1)\n}\n";
    let path = d.file("a.onsa", src);
    let diags = check(&path);
    let diag = expect_one(&diags, "E0020", "the call of an if");
    let fixes = fixes_of(diag);
    assert_eq!(fixes.len(), 1, "one candidate: {diag}");
    let after = apply(src, &edits_of(fixes[0]));
    assert_eq!(
        after,
        "pub fn f(c: Bool, h: fn(I32) -> I32, g: fn(I32) -> I32) -> I32 {\n  (if c { h } else { g }).(1)\n}\n"
    );
    assert!(check(&d.file("b.onsa", &after)).is_empty(), "the candidate leaves a diagnostic");
}

// ---- the arm list (§2.5) ---------------------------------------------------------------------------------

#[test]
fn a_block_body_then_a_spaced_minus_and_an_arrow_is_an_e0002_with_no_candidate_and_no_e0013() {
    // §2.5: `{ 1 } - 1 =>` is a missing `,` between two arms (the `=>` before the next `,` or `}`), and the
    // candidate would leave the E0020 of the space after the prefix `-`, so there is none; the block-like
    // expression is not read as an operand, so there is no E0013.
    let d = Dir::new("arms");
    let src = "pub fn f(x: I32) -> I32 {\n  match x {\n    0 => { 1 } - 1 => 2,\n    _ => 0,\n  }\n}\n";
    let path = d.file("a.onsa", src);
    let diags = check(&path);
    let diag = expect_one(&diags, "E0002", "the arm list");
    assert!(fixes_of(diag).is_empty(), "no candidate: {diag}");
    assert_eq!(span_start(diag).0, 3, "the diagnostic is on the line of the arm");
}

// ---- onsa fmt (§18.2, docs/onsa-tools.md §3.3) -----------------------------------------------------------

/// `f` has an E0013; `g` is fine and badly spaced.
const E0013_FILE: &str = "\
pub fn f(c: Bool) -> I32 {
  if c { 1 } else { 2 } + 10
}

pub fn g()->I32{
  2
}
";

#[test]
fn fmt_does_not_write_a_file_with_an_e0013_and_ends_with_the_exit_code_2() {
    // §18.2: a diagnostic of the syntax stage stops `fmt` (and `fmt --check`, and `diff --ast`) with 2.
    let d = Dir::new("fmt_error");
    let path = d.file("a.onsa", E0013_FILE);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 2, "fmt: {out:?}");
    assert_eq!(read(&path), E0013_FILE, "the file is not written");
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("E0013"),
        "the diagnostic is on the standard output: {out:?}"
    );
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 2, "fmt --check: {out:?}");
    let out = onsa(&["diff", "--ast", &path]);
    assert_eq!(code(&out), 2, "diff --ast: {out:?}");
    assert_eq!(read(&path), E0013_FILE);
}

/// The forms in parentheses, badly spaced, and the text that `fmt` writes: the parentheses stay.
const MESSY: &str = "\
pub fn f(c:Bool)->I32{
  (if c {1} else {2})+10
}

pub fn g(o:Option[I32])->I32{
  -(match o {Some(n)=>n,None=>0})
}

pub fn h(c:Bool,xs:[I32;2],ys:[I32;2])->I32{
  (if c {xs} else {ys})[1]
}
";

const MESSY_FORMATTED: &str = "\
pub fn f(c: Bool) -> I32 {
  (if c { 1 } else { 2 }) + 10
}

pub fn g(o: Option[I32]) -> I32 {
  -(match o { Some(n) => n, None => 0 })
}

pub fn h(c: Bool, xs: [I32; 2], ys: [I32; 2]) -> I32 {
  (if c { xs } else { ys })[1]
}
";

#[test]
fn fmt_keeps_the_parentheses_of_a_block_like_operand() {
    // docs/onsa-tools.md §3.3: the parentheses of `(if c { 1 } else { 2 }) + 1` are not redundant (E0013 without
    // them), so `fmt` does not take them off.
    let d = Dir::new("fmt_keep");
    let path = d.file("a.onsa", MESSY);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "fmt: {out:?}");
    assert_eq!(read(&path), MESSY_FORMATTED);
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "the formatted file is canonical: {out:?}");
    assert!(check(&path).is_empty(), "the formatted file has no diagnostic");
}
