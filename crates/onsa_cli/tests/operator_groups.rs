//! The groups of the binary operators (spec §3.1, §3.3, §18.1; S-45, S-60, S-61, S-118, S-320; W3-07/t).
//!
//! The case files in `tests/spec/` pin the code and the line of each diagnostic and the text after
//! each candidate (`fixes/e0010_candidates*.onsa`, `fixes/e0010_layout.onsa`,
//! `fixes/e0010_nesting_boundary.onsa`, `fixes/e0020_binary_minus.onsa`, `negative/operator_groups.onsa`,
//! `negative/cast_operands.onsa`, `negative/const_arg_groups.onsa`), and the values of the expressions
//! are in `tests/spec/semantics/precedence*.onsa`. These tests say what those cannot: that the message
//! of an E0010 names the operators that clash, that a candidate is made of insertions of `(` and `)` and
//! nothing else (an edit changes only the token it changes, §18.1), that equal forms are listed once, that
//! more than three forms give no candidate and a note, that a comparison chain with a middle operand that
//! is not a name, a literal or a field path gives no candidate and a note with the `let`, that one E0010
//! does not hide another unit and hides a later stage of its own unit, and the main span and the edit of
//! the E0020 of `a--b`.
//!
//! What is not here: the text of the message beyond the names of the operators (§18.1 says "メッセージには、
//! 衝突している演算子とそれぞれの読みを示す" and does not give the form of a reading), and the main span of
//! an E0010 (the spec does not say where it starts). Neither is asserted.
//!
//! Every test uses only the binary (`onsa check`). Expected texts are written from the spec and the
//! decision of S-60 (`tests/review-phase1/parent/r72.onsa`); none is taken from the output of the compiler.
//!
//! A test that needs the reading of §3.1 (the partial order of the groups) ran ignored until W3-07/i; each
//! ignore names the work that removes it (a test cannot be silenced by `tests/pending.toml`).

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_groups_{}_{tag}", std::process::id()));
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

fn notes_of(d: &Value) -> Vec<&Value> {
    d.get("notes").and_then(Value::as_array).map(|a| a.iter().collect()).unwrap_or_default()
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

/// A file with a struct, an identity function and `pub fn f(params) -> ret { expr }`.
fn wrap(params: &str, ret: &str, expr: &str) -> String {
    format!(
        "pub struct Pt {{\n  x: I32,\n}}\n\npub fn id(a: I32) -> I32 {{\n  a\n}}\n\npub fn f({params}) -> {ret} {{\n  {expr}\n}}\n"
    )
}

// ---- E0010: the message names the operators that clash (§18.1) ----------------------------------------

/// (the parameters, the result, the expression, the operators that clash).
type Clash = (&'static str, &'static str, &'static str, &'static [&'static str]);

const CLASHES: &[Clash] = &[
    ("w: U32, n: U32", "U32", "w + 1 % n", &["+", "%"]),
    ("a: U32, b: U32, c: U32", "U32", "a * b % c", &["*", "%"]),
    ("p: Bool, q: Bool, r: Bool", "Bool", "p && q || r", &["&&", "||"]),
    ("x: U32", "Bool", "x & 1 == 0", &["&", "=="]),
    ("a: U32, b: U32, c: U32", "U32", "a & b | c", &["&", "|"]),
    ("x: U32, y: U32", "U32", "x << 1 + y", &["<<", "+"]),
];

#[test]
fn the_message_of_e0010_names_the_operators_that_clash() {
    let d = Dir::new("message");
    for (params, ret, expr, ops) in CLASHES {
        let path = d.file("a.onsa", &wrap(params, ret, expr));
        let diags = check(&path);
        let diag = expect_one(&diags, "E0010", expr);
        let message = diag["message"].as_str().expect("`message` is a string");
        for op in *ops {
            assert!(message.contains(op), "{expr}: the message does not name `{op}`: {message}");
        }
    }
}

#[test]
fn the_message_of_a_chain_of_comparisons_names_the_comparison() {
    let d = Dir::new("chain_message");
    for (expr, op) in [("a < b < c", "<"), ("a == b == c", "=="), ("a != b != c", "!="), ("a >= b >= c", ">=")] {
        let path = d.file("a.onsa", &wrap("a: I32, b: I32, c: I32", "Bool", expr));
        let diags = check(&path);
        let diag = expect_one(&diags, "E0010", expr);
        let message = diag["message"].as_str().expect("`message` is a string");
        assert!(message.contains(op), "{expr}: the message does not name `{op}`: {message}");
    }
}

// ---- E0010: the candidates (§18.1, S-60) ---------------------------------------------------------------

/// (the parameters, the result, the expression, the candidates in order). The order is the one of §18.1
/// ("式の中で先に現れる群を強いとした読みを先に") and of the decision of S-60; equal forms are listed once.
type Cands = (&'static str, &'static str, &'static str, &'static [&'static str]);

const CANDIDATES: &[Cands] = &[
    ("w: U32, n: U32", "U32", "w + 1 % n", &["(w + 1) % n", "w + (1 % n)"]),
    ("a: U32, b: U32, c: U32", "U32", "a % b * c", &["(a % b) * c", "a % (b * c)"]),
    ("p: Bool, q: Bool, r: Bool", "Bool", "p && q || r", &["(p && q) || r", "p && (q || r)"]),
    ("a: Bool, b: Bool, c: Bool, d: Bool", "Bool", "a && b || c && d", &["(a && b) || (c && d)", "a && (b || c) && d"]),
    ("x: U32", "Bool", "x & 1 == 0", &["(x & 1) == 0", "x & (1 == 0)"]),
    ("x: U32, y: U32", "U32", "x << 1 + y", &["(x << 1) + y", "x << (1 + y)"]),
    ("a: U32, b: U32, c: U32", "U32", "a & b | c", &["(a & b) | c", "a & (b | c)"]),
    (
        "a: U32, b: U32, c: U32, d: U32, e: U32",
        "U32",
        "a + b + c % d + e",
        &["(a + b + c) % (d + e)", "a + b + (c % d) + e"],
    ),
    ("i: U32, n: U32, m: U32", "Bool", "i + 1 % n < m", &["(i + 1) % n < m", "i + (1 % n) < m"]),
    // three groups, the order of tests/review-phase1/parent/r72.onsa
    (
        "x: U32, ok: Bool",
        "Bool",
        "x & 1 == 0 && ok",
        &["(x & 1) == 0 && ok", "(x & (1 == 0)) && ok", "x & (1 == 0 && ok)"],
    ),
    // three groups that give two forms (the strength between the bit group and the others is only
    // temporary, so the same form is not listed twice)
    ("x: U32, m: U32, a: U32, b: U32", "U32", "x & m + a * b", &["(x & m) + a * b", "x & (m + a * b)"]),
    ("a: U32, b: U32, c: U32, d: U32", "Bool", "a & b == c + d", &["(a & b) == c + d", "a & (b == c + d)"]),
    // the comparison chain: one candidate, only when every middle operand is a name, a literal or a
    // field path
    ("a: I32, b: I32, c: I32", "Bool", "a < b < c", &["a < b && b < c"]),
    ("a: I32, b: I32, c: I32", "Bool", "a == b != c", &["a == b && b != c"]),
    ("a: I32, c: I32", "Bool", "a < 0 < c", &["a < 0 && 0 < c"]),
    ("a: I32, p: Pt, c: I32", "Bool", "a <= p.x < c", &["a <= p.x && p.x < c"]),
];

#[test]
fn the_candidates_of_e0010_are_the_readings_in_the_order_of_the_rule() {
    let d = Dir::new("candidates");
    for (params, ret, expr, want) in CANDIDATES {
        let src = wrap(params, ret, expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0010", expr);
        let fixes = fixes_of(diag);
        assert_eq!(fixes.len(), want.len(), "{expr}: the number of candidates: {diag}");
        for (k, (fix, text)) in fixes.iter().zip(*want).enumerate() {
            assert_eq!(apply(&src, &edits_of(fix)), wrap(params, ret, text), "{expr}: candidate {}", k + 1);
        }
        assert!(!fixes.is_empty());
    }
}

#[test]
fn a_parenthesis_candidate_inserts_only_parentheses() {
    // §18.1: an edit replaces only the token it changes and the tokens and comments between are not in
    // its range; the parentheses are inserted, each edit with an empty range, so a candidate has as
    // many `(` as `)`, and every edit is an insertion of `(` only or `)` only (one or more).
    // Changed by the parent (W3-07): two insertions at one position overlap (§18.1), so the parentheses
    // one position needs are one insertion (`))`), as in E0012.
    let d = Dir::new("insertions");
    for (params, ret, expr, want) in CANDIDATES {
        if want.iter().any(|w| !w.contains('(')) {
            continue; // the comparison chain makes `&&` out of nothing; it is not a parenthesis candidate
        }
        let path = d.file("a.onsa", &wrap(params, ret, expr));
        let diags = check(&path);
        let diag = expect_one(&diags, "E0010", expr);
        for (k, fix) in fixes_of(diag).iter().enumerate() {
            let edits = edits_of(fix);
            assert!(!edits.is_empty(), "{expr}: candidate {} has no edit", k + 1);
            let mut open = 0;
            let mut close = 0;
            for e in &edits {
                assert_eq!(e.start, e.end, "{expr}: candidate {}: an edit that replaces text: {fix}", k + 1);
                let r = e.replace.as_str();
                if !r.is_empty() && r.chars().all(|c| c == '(') {
                    open += r.len();
                } else if !r.is_empty() && r.chars().all(|c| c == ')') {
                    close += r.len();
                } else {
                    panic!("{expr}: candidate {}: an edit inserts `{r}`: {fix}", k + 1);
                }
            }
            assert_eq!(open, close, "{expr}: candidate {}: unbalanced parentheses: {fix}", k + 1);
        }
    }
}

#[test]
fn a_comparison_chain_candidate_inserts_the_middle_operand_and_the_and() {
    // `a < b < c` -> `a < b && b < c`: the edit changes no token that is already there (the operands and
    // the symbols stay), it inserts `&& b ` after the first comparison.
    let d = Dir::new("chain_edit");
    let src = wrap("a: I32, b: I32, c: I32", "Bool", "a < b < c");
    let path = d.file("a.onsa", &src);
    let diags = check(&path);
    let diag = expect_one(&diags, "E0010", "a < b < c");
    let fixes = fixes_of(diag);
    assert_eq!(fixes.len(), 1, "{diag}");
    let edits = edits_of(fixes[0]);
    assert!(edits.iter().all(|e| e.start == e.end), "an edit replaces text: {}", fixes[0]);
    assert_eq!(apply(&src, &edits), wrap("a: I32, b: I32, c: I32", "Bool", "a < b && b < c"));
}

/// Expressions with more than three different readings, and a chain of comparisons whose middle operand
/// is not a name, a literal or a field path: no candidate, and a note.
const NO_CANDIDATE: &[(&str, &str, &str, &str)] = &[
    ("four groups", "x: U32, a: Bool, b: Bool", "Bool", "x & 1 == 0 && a || b"),
    ("three operators of the bit group", "a: U32, b: U32, c: U32, d: U32", "U32", "a & b | c ^ d"),
    ("three groups, five forms", "x: U32", "U32", "x & 1 + 2 % 3"),
    ("a call in the middle", "a: I32, b: I32, c: I32", "Bool", "a < id(b) < c"),
    ("a sum in the middle", "a: I32, b: I32, c: I32", "Bool", "a < b + 1 < c"),
    ("an index in the middle", "a: I32, xs: [I32; 2], c: I32", "Bool", "a < xs[0] < c"),
];

#[test]
fn more_than_three_readings_or_a_middle_that_is_evaluated_twice_give_no_candidate_and_a_note() {
    let d = Dir::new("none");
    for (what, params, ret, expr) in NO_CANDIDATE {
        let path = d.file("a.onsa", &wrap(params, ret, expr));
        let diags = check(&path);
        let diag = expect_one(&diags, "E0010", what);
        assert!(fixes_of(diag).is_empty(), "{what}: a candidate: {diag}");
        let notes = notes_of(diag);
        assert!(
            notes.iter().any(|n| n["message"].as_str().is_some_and(|m| !m.is_empty())),
            "{what}: no note that shows how to write it: {diag}"
        );
    }
}

#[test]
fn the_note_of_a_chain_with_a_middle_that_is_not_a_path_shows_let() {
    // §18.1: "それ以外は 2 回評価されるので、`let` に取る書き方を note で示す".
    let d = Dir::new("let_note");
    for expr in ["a < id(b) < c", "a < b + 1 < c"] {
        let path = d.file("a.onsa", &wrap("a: I32, b: I32, c: I32", "Bool", expr));
        let diags = check(&path);
        let diag = expect_one(&diags, "E0010", expr);
        let shown = notes_of(diag).iter().any(|n| n["message"].as_str().is_some_and(|m| m.contains("let")));
        assert!(shown, "{expr}: no note shows `let`: {diag}");
    }
}

#[test]
fn the_candidates_that_type_check_leave_the_program_without_a_diagnostic() {
    // §18.1: a candidate leaves no diagnostic of the stage of the error or an earlier one in the unit;
    // here both readings of these expressions also type check, so the whole check is silent.
    let d = Dir::new("clean");
    let cases: [(&str, &str, &str); 6] = [
        ("w: U32, n: U32", "U32", "w + 1 % n"),
        ("a: U32, b: U32, c: U32", "U32", "a * b % c"),
        ("p: Bool, q: Bool, r: Bool", "Bool", "p && q || r"),
        ("a: U32, b: U32, c: U32", "U32", "a & b | c"),
        ("a: I32, b: I32, c: I32", "Bool", "a < b < c"),
        ("i: U32, n: U32, m: U32", "Bool", "i + 1 % n < m"),
    ];
    for (params, ret, expr) in cases {
        let src = wrap(params, ret, expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0010", expr);
        for (k, fix) in fixes_of(diag).iter().enumerate() {
            let after = d.file("b.onsa", &apply(&src, &edits_of(fix)));
            let again = check(&after);
            assert!(again.is_empty(), "{expr}: candidate {} leaves {again:?}", k + 1);
        }
    }
}

// ---- the constant arguments (§4.5, from W3-19) ---------------------------------------------------------

/// Where a constant argument stands: an array length, the arguments of a type, the length of `[e; N]`,
/// the `::[…]` of an expression. Each is written with a product in a sum, which §3.1 allows.
const CONST_ARGS: &[(&str, &str)] = &[
    ("an array length in a parameter", "pub fn f(a: [F32; TABLE_SIZE * 2 + 1]) -> U32 {\n  1\n}\n"),
    ("an array length in a result", "pub fn f() -> [F32; N * 2 - 1] {\n  [0.0; 3]\n}\n"),
    ("the length of a repeat", "pub fn f() -> U32 {\n  let a = [0.0; TABLE_SIZE * 2 + 1]\n  1\n}\n"),
    ("an annotation", "pub fn f() -> U32 {\n  let a: [F32; N / 2 + 4 * 3 - 1] = [0.0; 5]\n  1\n}\n"),
    ("the arguments of a type", "pub fn f(r: Rg[F32, TABLE_SIZE * 2 + 1]) -> U32 {\n  1\n}\n"),
    ("the arguments of a type in a tuple", "pub fn f(t: (Rg[F32, 2 * 3 + 1], U8)) -> U8 {\n  t.1\n}\n"),
    ("the arguments of an associated constant", "pub fn f() -> U32 {\n  Rg::[F32, TABLE_SIZE * 2 + 1].CAP\n}\n"),
    ("the arguments of a function", "pub fn f() -> U32 {\n  pair::[U8, N * 2 - 1](1, 2)\n}\n"),
    (
        "the arguments of a struct literal",
        "pub fn f() -> U32 {\n  let r = Rg::[F32, 2 * 3 + 1] { data: [0.0; 7], head: 0 }\n  1\n}\n",
    ),
];

#[test]
fn a_product_in_a_sum_in_a_constant_argument_is_not_a_syntax_error() {
    // §4.5: a constant argument is a constant expression read like any expression, and §3.1 gives the
    // product a strength over the sum, so `TABLE_SIZE * 2 + 1` needs no parentheses. The names, the
    // types and what this version does not lower (E0200 for an expression as an array length and for
    // the arguments written in an expression) are for the stages after the syntax; here only the syntax
    // stage is looked at: no E0010, E0002 or E0001.
    let d = Dir::new("const_args");
    for (what, src) in CONST_ARGS {
        let path = d.file("a.onsa", src);
        let diags = check(&path);
        let syntax: Vec<&str> =
            diags.iter().map(code_of).filter(|c| matches!(*c, "E0010" | "E0002" | "E0001")).collect();
        assert!(syntax.is_empty(), "{what}: a syntax error {syntax:?} in {src}\n{diags:?}");
    }
}

#[test]
fn the_remainder_with_a_sum_in_a_constant_argument_is_e0010() {
    // §4.5 "普通の式と同じ規則" and §3.1: `N % 2 + 1` has two groups without a strength between them.
    let d = Dir::new("const_args_e0010");
    for (what, src) in [
        ("an array length", "pub fn f(a: [F32; N % 2 + 1]) -> U32 {\n  1\n}\n"),
        ("the arguments of a type", "pub fn f(r: Rg[F32, N % 2 + 1]) -> U32 {\n  1\n}\n"),
        ("an expression", "pub fn f() -> U32 {\n  Rg::[F32, N % 2 + 1].CAP\n}\n"),
    ] {
        let path = d.file("a.onsa", src);
        let diags = check(&path);
        assert!(diags.iter().any(|x| code_of(x) == "E0010"), "{what}: no E0010: {diags:?}");
    }
}

// ---- the units of a file (§18.1) ------------------------------------------------------------------------

#[test]
fn an_e0010_hides_the_later_stages_of_its_unit_but_not_the_other_units() {
    // §18.1: within a unit the first error stops the check and the stages run in an order (the syntax
    // before the types); the units are checked independently and all their errors are reported.
    let d = Dir::new("units");
    let src = "pub fn a(w: U32, n: U32) -> U32 {\n  let bad: Bool = 1\n  w + 1 % n\n}\n\n\
               pub fn b() -> Bool {\n  1\n}\n\n\
               pub fn c(p: Bool, q: Bool, r: Bool) -> Bool {\n  p && q || r\n}\n";
    let path = d.file("a.onsa", src);
    let diags = check(&path);
    let found: Vec<(&str, u64)> =
        diags.iter().map(|x| (code_of(x), x["span"]["line"].as_u64().expect("a line"))).collect();
    assert_eq!(found, vec![("E0010", 3), ("E0401", 7), ("E0010", 11)], "{diags:?}");
}

// ---- E0020: `a--b` (S-320) -----------------------------------------------------------------------------

#[test]
fn a_binary_minus_followed_by_a_prefix_minus_is_one_e0020_with_the_spaced_form_as_its_candidate() {
    // S-320: `a--b` and `5--3` are E0020 and the candidate is `a - -b`. The edit changes the token `--`
    // and no other (§18.1), and the main span starts at it. A note shows the rule.
    let d = Dir::new("minus");
    let cases: [(&str, &str, &str, &str); 4] = [
        ("a: I32, b: I32", "I32", "a--b", "a - -b"),
        ("", "I32", "5--3", "5 - -3"),
        ("x: F32", "F32", "x--1.5", "x - -1.5"),
        ("p: Pt, b: I32", "I32", "p.x--b", "p.x - -b"),
    ];
    for (params, ret, expr, want) in cases {
        let src = wrap(params, ret, expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0020", expr);
        let at = src.find("--").expect("the symbol is in the source");
        let line = 1 + src[..at].matches('\n').count();
        let col = 1 + src[src[..at].rfind('\n').map_or(0, |i| i + 1)..at].chars().count();
        let (start, _) = span_of(diag);
        assert_eq!(start, (line, col), "{expr}: the main span starts at `--`: {diag}");
        let fixes = fixes_of(diag);
        assert_eq!(fixes.len(), 1, "{expr}: one candidate: {diag}");
        let edits = edits_of(fixes[0]);
        for e in &edits {
            assert!(
                (line, col) <= e.start && e.end <= (line, col + 2),
                "{expr}: the edit {:?}..{:?} is outside the token `--`",
                e.start,
                e.end
            );
        }
        assert_eq!(apply(&src, &edits), wrap(params, ret, want), "{expr}");
        assert!(!notes_of(diag).is_empty(), "{expr}: no note with the rule: {diag}");
    }
}

#[test]
fn the_spaced_candidate_of_a_binary_minus_and_a_prefix_minus_leaves_no_diagnostic() {
    let d = Dir::new("minus_clean");
    for (params, ret, expr) in [("a: I32, b: I32", "I32", "a--b"), ("x: I32, a: I32, b: I32", "I32", "x * a--b")] {
        let src = wrap(params, ret, expr);
        let path = d.file("a.onsa", &src);
        let diags = check(&path);
        let diag = expect_one(&diags, "E0020", expr);
        let after = d.file("b.onsa", &apply(&src, &edits_of(fixes_of(diag)[0])));
        let again = check(&after);
        assert!(again.is_empty(), "{expr}: the candidate leaves {again:?}");
    }
}

#[test]
fn a_binary_operator_other_than_minus_followed_by_a_prefix_minus_is_not_the_form() {
    // S-320 is about `--`, one token. `a+-b`, `a*-b`, `a/-b` and `a - -b` are separate tokens and no
    // form of the closed list of docs/foreign-forms.toml (§18.1: a form that is not in the list is not
    // an E0020).
    let d = Dir::new("minus_other");
    for expr in ["a+-b", "a*-b", "a/-b", "a - -b", "a-b", "a-(-b)"] {
        let path = d.file("a.onsa", &wrap("a: I32, b: I32", "I32", expr));
        let diags = check(&path);
        assert!(diags.iter().all(|x| code_of(x) != "E0020"), "{expr}: an E0020: {diags:?}");
    }
}
