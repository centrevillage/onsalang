//! The decisions of the 14th group of the syntax of a flow (spec §2.2, §2.6, §11.3, §11.5, §18.1;
//! S-354, S-355, S-356, S-357, S-358, S-363; W3-09/t2): the space between `if` / `match` and `~`, the
//! `~` on a later `if` of a chain and the missing `else` of an `if~`, the `at` inside a type and after the
//! type of a declaration that is not an input or an output of a flow, the keyword after a `.`, the `^`
//! that no name follows, and the prefix `~` with and without a space.
//!
//! The case files in `tests/spec/` pin the code and the line of each error and the text after each
//! candidate (`fixes/e0020_if_tilde_gap.onsa`, `fixes/e0020_else_if_tilde.onsa`,
//! `fixes/e0020_else_if_tilde_chain.onsa`, `fixes/e0020_clock_in_types.onsa`,
//! `fixes/e0020_clock_in_types_multi.onsa`, `fixes/e0020_prefix_tilde_contrast.onsa`,
//! `fixes/e0003_if_tilde_else_line.onsa`, `negative/syntax_if_tilde_no_else.onsa`,
//! `negative/syntax_caret_not_a_name.onsa`, `negative/syntax_tilde_no_candidate.onsa`,
//! `negative/syntax_clock_in_types_values.onsa`, `negative/member_keyword_names.onsa`,
//! `negative/names_clock_in_fn_head.onsa`, and `flow_syntax/tilde_clock_boundaries.onsa` for the right
//! forms next to them). These tests say what those cannot: that the number of candidates is what the
//! spec says and that none is offered where the spec offers none (an error with no candidate has a note
//! that shows the rule, §18.1), that applying the first candidate again and again ends in a chain or a
//! type with no error of the syntax stage (the errors of one chain or one type are separate, one at a time),
//! the normal form `onsa fmt` writes for `if~c`, that a tab between `if` and `~` is the space of the
//! error (§2.5: the blanks are the space and the tab), that `fmt` and `diff --ast` stop at these errors,
//! and that the keyword after a `.` reaches the type stage.
//!
//! What is not here: the text of a message, the main position of the new E0020 forms (`else if~`, the
//! `at` of a type and the space of `if ~ c` are not given a position by the spec; the cases in
//! `fixes/e0020_else_if_tilde_chain.onsa` and `fixes/e0020_clock_in_types_multi.onsa` assume the first
//! token of the wrong mark, `~` and `at`), what the unreported second error of a unit says, and the
//! forms the spec leaves open (a clock name that is unknown, S-359; the arguments of a delay, S-360).
//! The `at` after the result of a function type (S-367) is in `fixes/e0020_clock_after_fn_type.onsa`.
//!
//! Every test uses only the binary (`onsa check --json`, `onsa fmt`, `onsa diff --ast`). Expected
//! texts are written from the spec; none is taken from the output of the compiler.
//!
//! The tests were written before W3-09 and ran ignored until W3-09/i (the parser did not read `at`
//! and `if~`; an ignored test is not silenced by `tests/pending.toml`).

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_flow_decisions_{}_{tag}", std::process::id()));
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

/// A flow whose body is `body` (lines already indented by two spaces).
fn in_a_flow(body: &str) -> String {
    format!(
        "pub flow f(x: F32 at sample, c: Bool at sample, d: Bool at sample, e: Bool at sample, k: U32 at sample) -> F32 at sample {{\n{body}\n}}\n"
    )
}

/// A function whose body is `body` (lines already indented by two spaces).
fn in_a_fn(body: &str) -> String {
    format!("pub fn f(c: Bool, d: Bool, k: U32, m: U32, xs: [I32; 2]) -> U32 {{\n{body}\n}}\n")
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

fn array_of<'a>(d: &'a Value, key: &str) -> Vec<&'a Value> {
    d.get(key).and_then(Value::as_array).map(|a| a.iter().collect()).unwrap_or_default()
}

/// One edit of a candidate: a range as (line, column, end line, end column), 1-based, columns in
/// characters, and the text that replaces it.
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

/// The text without the blanks of each line and without the empty lines. The spec fixes the tokens
/// and the line breaks of a candidate, not the amount of blank (the normal form is `onsa fmt`'s).
fn squeeze(s: &str) -> String {
    s.lines()
        .map(|l| l.chars().filter(|c| *c != ' ' && *c != '\t').collect::<String>())
        .filter(|l| !l.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

/// The only diagnostic of `text` (a unit holds one error, §18.1), with its code asserted.
fn only_diagnostic(d: &Dir, what: &str, text: &str, wanted_code: &str) -> Value {
    let path = d.file("a.onsa", text);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{what}: one error in the unit, got {diags:?}\n{text}");
    assert_eq!(code_of(&diags[0]), wanted_code, "{what}: {}\n{text}", diags[0]);
    diags[0].clone()
}

/// The texts after each candidate of the only diagnostic of `text`, one at a time.
fn candidates_applied(d: &Dir, what: &str, text: &str, wanted_code: &str) -> Vec<String> {
    let diag = only_diagnostic(d, what, text, wanted_code);
    array_of(&diag, "fixes").into_iter().map(|f| apply(text, &edits_of(f))).collect()
}

/// A case: what it says, the source, the sources after the candidates, in the order of the spec.
struct Case {
    what: &'static str,
    source: String,
    fixed: Vec<String>,
}

fn case(what: &'static str, source: String, fixed: &[String]) -> Case {
    Case { what, source, fixed: fixed.to_vec() }
}

fn check_cases(tag: &str, wanted_code: &str, cases: &[Case]) {
    let d = Dir::new(tag);
    for c in cases {
        let after = candidates_applied(&d, c.what, &c.source, wanted_code);
        assert_eq!(after.len(), c.fixed.len(), "{}: number of candidates\n{}", c.what, c.source);
        for (i, (got, want)) in after.iter().zip(&c.fixed).enumerate() {
            assert_eq!(
                squeeze(got),
                squeeze(want),
                "{}: candidate {}\nsource:\n{}\ngot:\n{got}",
                c.what,
                i + 1,
                c.source
            );
        }
    }
}

/// Apply the first candidate of the first diagnostic until the syntax stage reports nothing. Returns
/// the texts after each step (at most `limit`).
fn converge(d: &Dir, what: &str, text: &str, limit: usize) -> Vec<String> {
    let mut steps = Vec::new();
    let mut current = text.to_string();
    for _ in 0..limit {
        let path = d.file("a.onsa", &current);
        let diags = check(&path);
        let Some(first) = diags.iter().find(|x| matches!(code_of(x), "E0020" | "E0002" | "E0003")) else {
            return steps;
        };
        let fixes = array_of(first, "fixes");
        assert!(!fixes.is_empty(), "{what}: no candidate for {first}\n{current}");
        current = apply(&current, &edits_of(fixes[0]));
        steps.push(current.clone());
    }
    panic!("{what}: the candidates do not end in {limit} steps; last text:\n{current}");
}

#[test]
fn the_one_at_a_time_helper_follows_separate_errors_of_a_unit() {
    // The helper of the tests of S-355 and S-356 (`converge`) on a form that is read today: the `;` that end
    // different statements are separate errors (§18.1, S-248), a unit reports its first, and applying the first
    // candidate again and again ends with none. (It shows that the helper checks what the later tests rely on.)
    let d = Dir::new("helper");
    let written = in_a_fn("  let a = 1; let b = 2; let c = 3\n  m");
    let got = converge(&d, "separate semicolons", &written, 6);
    assert_eq!(got.len(), 2, "number of steps");
    assert_eq!(squeeze(got.last().unwrap()), squeeze(&in_a_fn("  let a = 1\n  let b = 2\n  let c = 3\n  m")));
    let diags = check(&d.file("first.onsa", &written));
    assert_eq!(diags.len(), 1, "a unit reports its first error only: {diags:?}");
}

// ---- S-354: the space between `if` / `match` and `~` ---------------------------------------------

#[test]
fn a_space_between_if_or_match_and_the_tilde_is_e0020_with_the_space_removed() {
    // §2.6: "`if~` / `match~` は、`if` / `match` の直後に空白を空けずに `~` を書く（空白を空けると E0020 で、
    // 修正候補は空白を除く形。`if ~c` のように `~` が被演算子に接するときは、前置の `~` の読みの `if !c` を二つ目に
    // 並べる）". The first candidate is the one without the space, in every case; the second exists only when the
    // `~` touches the operand.
    let cases = vec![
        case("if, a space", in_a_flow("  if ~ c { 1.0 } else { 2.0 }"), &[in_a_flow("  if~ c { 1.0 } else { 2.0 }")]),
        case(
            "if, wide space",
            in_a_flow("  if    ~ c { 1.0 } else { 2.0 }"),
            &[in_a_flow("  if~ c { 1.0 } else { 2.0 }")],
        ),
        case(
            "match, a space",
            in_a_flow("  match ~ k { 0 => 1.0, _ => 2.0 }"),
            &[in_a_flow("  match~ k { 0 => 1.0, _ => 2.0 }")],
        ),
        case(
            "if, in a let",
            in_a_flow("  let a = if ~ c { 1.0 } else { 2.0 }\n  a"),
            &[in_a_flow("  let a = if~ c { 1.0 } else { 2.0 }\n  a")],
        ),
        case(
            "if, a space and an operator",
            in_a_flow("  if ~ c && d { 1.0 } else { 2.0 }"),
            &[in_a_flow("  if~ c && d { 1.0 } else { 2.0 }")],
        ),
        case(
            "if, the tilde touches the operand",
            in_a_flow("  if ~c { 1.0 } else { 2.0 }"),
            &[in_a_flow("  if~ c { 1.0 } else { 2.0 }"), in_a_flow("  if !c { 1.0 } else { 2.0 }")],
        ),
        case(
            "match, the tilde touches the operand",
            in_a_flow("  match ~k { 0 => 1.0, _ => 2.0 }"),
            &[in_a_flow("  match~ k { 0 => 1.0, _ => 2.0 }"), in_a_flow("  match !k { 0 => 1.0, _ => 2.0 }")],
        ),
        case(
            "if, the tilde touches the first operand of an operator",
            in_a_flow("  if ~c && d { 1.0 } else { 2.0 }"),
            &[in_a_flow("  if~ c && d { 1.0 } else { 2.0 }"), in_a_flow("  if !c && d { 1.0 } else { 2.0 }")],
        ),
        case("if in a fn", in_a_fn("  if ~ c { 1 } else { 2 }"), &[in_a_fn("  if~ c { 1 } else { 2 }")]),
    ];
    check_cases("if_tilde_gap", "E0020", &cases);
}

#[test]
fn a_tab_between_if_and_the_tilde_is_the_space_of_the_error() {
    // §2.5: the blanks are the space and the tab. A tab is the same mistake as a space.
    let cases = vec![
        case("a tab", in_a_flow("  if\t~ c { 1.0 } else { 2.0 }"), &[in_a_flow("  if~ c { 1.0 } else { 2.0 }")]),
        case(
            "a tab and the tilde touching the operand",
            in_a_flow("  if\t~c { 1.0 } else { 2.0 }"),
            &[in_a_flow("  if~ c { 1.0 } else { 2.0 }"), in_a_flow("  if !c { 1.0 } else { 2.0 }")],
        ),
    ];
    check_cases("if_tilde_tab", "E0020", &cases);
}

#[test]
fn if_with_the_tilde_glued_to_the_condition_is_read_and_fmt_spaces_it() {
    // S-354: `if~c` is accepted (the `~` is right after the keyword), and `onsa fmt` writes the condition after one
    // space (docs/onsa-tools.md §3.2: `if~ c`).
    let d = Dir::new("if_glued");
    let cases = [
        ("if~c", "  if~c { 1.0 } else { 2.0 }", "  if~ c { 1.0 } else { 2.0 }"),
        ("match~k", "  match~k { 0 => 1.0, _ => 2.0 }", "  match~ k { 0 => 1.0, _ => 2.0 }"),
        (
            "if~c in a chain",
            "  if~c { 1.0 } else if d { 2.0 } else { 3.0 }",
            "  if~ c { 1.0 } else if d { 2.0 } else { 3.0 }",
        ),
        ("if~c with an operator", "  if~c && d { 1.0 } else { 2.0 }", "  if~ c && d { 1.0 } else { 2.0 }"),
    ];
    for (what, written, normal) in cases {
        let path = d.file("a.onsa", &in_a_flow(written));
        let diags = check(&path);
        assert!(
            diags.iter().all(|x| !matches!(code_of(x), "E0001" | "E0002" | "E0003" | "E0020")),
            "{what}: the syntax stage reports {diags:?}"
        );
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        assert_eq!(read(&path), in_a_flow(normal), "{what}");
        let again = onsa(&["fmt", "--check", &path]);
        assert_eq!(code(&again), 0, "{what}: the normal form is not accepted by --check: {again:?}");
    }
    // The program does not change (`diff --ast`, §18.2): the `~` is kept.
    let a = d.file("a1.onsa", &in_a_flow("  if~c { 1.0 } else { 2.0 }"));
    let b = d.file("b1.onsa", &in_a_flow("  if~ c { 1.0 } else { 2.0 }"));
    let diff = onsa(&["diff", "--ast", &a, &b]);
    assert_eq!(code(&diff), 0, "fmt of `if~c` changed the program: {diff:?}");
    let plain = d.file("c1.onsa", &in_a_flow("  if c { 1.0 } else { 2.0 }"));
    let diff = onsa(&["diff", "--ast", &a, &plain]);
    assert_ne!(code(&diff), 0, "the tree of `if~ c` is the tree of `if c`: the `~` is dropped");
}

#[test]
fn while_with_a_prefix_tilde_stays_the_bit_negation_with_one_candidate() {
    // S-354 limits the rule to `if` and `match`: `while ~c` is the prefix `~` of S-123 (the candidate is the `!`,
    // §2.6), and there is no second reading, so the candidate is the only one. With a space (`while ~ c`) it is the
    // general error of S-363.
    let cases = vec![case(
        "while, the tilde touches the operand",
        in_a_fn("  while ~c {\n    break\n  }\n  1"),
        &[in_a_fn("  while !c {\n    break\n  }\n  1")],
    )];
    check_cases("while_tilde", "E0020", &cases);
    let d = Dir::new("while_tilde_spaced");
    let diag = only_diagnostic(&d, "while ~ c", &in_a_fn("  while ~ c {\n    break\n  }\n  1"), "E0002");
    assert!(array_of(&diag, "fixes").is_empty(), "`while ~ c` has no candidate: {diag}");
}

// ---- S-363: the prefix `~` with and without a space ----------------------------------------------

#[test]
fn a_prefix_tilde_with_a_space_is_e0002_and_without_a_space_e0020_with_the_bang() {
    // §2.6 and S-363: `~m` (touching the operand) is the C-family bit negation, E0020 with the candidate `!m`; `~ m`
    // (a space) is E0002 with no candidate, because removing the space would write `~m`, which is an error itself.
    // The scope is a `~` after neither a name nor `if` / `match`.
    let d = Dir::new("prefix_tilde");
    let touching = [
        ("let", "  let n = ~m\n  n", "  let n = !m\n  n"),
        ("an argument", "  id(~m)", "  id(!m)"),
        ("an operand", "  m + ~m", "  m + !m"),
        ("a tuple element", "  let t = (m, ~m)\n  t.0", "  let t = (m, !m)\n  t.0"),
    ];
    let head = "pub fn id(m: U32) -> U32 {\n  m\n}\n\n";
    for (what, body, fixed) in touching {
        let text = format!("{head}{}", in_a_fn(body));
        let after = candidates_applied(&d, what, &text, "E0020");
        assert_eq!(after.len(), 1, "{what}: one candidate");
        assert_eq!(squeeze(&after[0]), squeeze(&format!("{head}{}", in_a_fn(fixed))), "{what}");
    }
    let spaced = [
        ("let", "  let n = ~ m\n  n"),
        ("an argument", "  id(~ m)"),
        ("an operand", "  m + ~ m"),
        ("a tuple element", "  let t = (m, ~ m)\n  t.0"),
        ("return", "  return ~ m"),
    ];
    for (what, body) in spaced {
        let text = format!("{head}{}", in_a_fn(body));
        let diag = only_diagnostic(&d, what, &text, "E0002");
        assert!(array_of(&diag, "fixes").is_empty(), "{what}: a space after the prefix `~` has no candidate: {diag}");
    }
}

#[test]
fn an_if_followed_by_a_line_break_is_e0002_not_the_space_of_the_tilde() {
    // S-354 is "right after the keyword, on the same line". §2.5: a line goes on after a binary operator, a range mark,
    // `=`, `->`, an attribute, a leading `.` or `uses`; `if` is none of these, so the `if` has no condition.
    let d = Dir::new("if_break");
    for (what, body) in [
        ("if", "  let a = if\n    ~c { 1 } else { 2 }\n  a"),
        ("match", "  match\n    ~k {\n    0 => 1,\n    _ => 2,\n  }"),
    ] {
        let diag = only_diagnostic(&d, what, &in_a_fn(body), "E0002");
        assert!(array_of(&diag, "fixes").is_empty(), "{what}: {diag}");
        assert_eq!(diag["span"]["line"].as_u64(), Some(2), "{what}: on the keyword's line");
    }
}

// ---- S-355: an `if~` with no `else` and `else if~` ----------------------------------------------

#[test]
fn an_if_tilde_with_no_else_is_e0002_with_a_note_and_no_candidate() {
    // §11.5: "`else` は省けない（省くと構文の段の E0002 で、修正候補は無く、全ての枝を評価して一つを選ぶので
    // `else` が要ることを note で示す）".
    let d = Dir::new("no_else");
    let bodies = [
        ("a last expression", "  if~ c { 1.0 }"),
        ("a let", "  let a = if~ c { 1.0 }\n  a"),
        ("a chain with no final else", "  if~ c { 1.0 } else if d { 2.0 }"),
        ("in lines", "  if~ c {\n    1.0\n  }"),
        ("an arm", "  if~ c {\n    if~ d { 1.0 }\n  } else {\n    2.0\n  }"),
        ("a par", "  par i in 0..<2 {\n    if~ c { 1.0 }\n  }"),
        ("an argument", "  mix(if~ c { x }, 0.5)"),
    ];
    for (what, body) in bodies {
        let diag = only_diagnostic(&d, what, &in_a_flow(body), "E0002");
        assert!(array_of(&diag, "fixes").is_empty(), "{what}: an `if~` with no `else` has no candidate: {diag}");
        assert!(!array_of(&diag, "notes").is_empty(), "{what}: the note of the rule is missing: {diag}");
    }
    let diag = only_diagnostic(&d, "in a fn", &in_a_fn("  if~ c { 1 }"), "E0002");
    assert!(array_of(&diag, "fixes").is_empty(), "in a fn: {diag}");
}

#[test]
fn an_else_on_the_next_line_of_an_if_tilde_is_e0003_and_not_the_missing_else() {
    // §2.5: `else` is written on the line of the `}` before it; the error is E0003 and the candidate joins the lines.
    // The `else` is there, so it is not the E0002 of §11.5.
    let cases = vec![
        case(
            "if~ and an else on the next line",
            in_a_flow("  if~ c {\n    1.0\n  }\n  else {\n    2.0\n  }"),
            &[in_a_flow("  if~ c {\n    1.0\n  } else {\n    2.0\n  }")],
        ),
        case(
            "a chain and an else on the next line",
            in_a_flow("  if~ c {\n    1.0\n  } else if d {\n    2.0\n  }\n  else {\n    3.0\n  }"),
            &[in_a_flow("  if~ c {\n    1.0\n  } else if d {\n    2.0\n  } else {\n    3.0\n  }")],
        ),
    ];
    check_cases("else_line", "E0003", &cases);
}

#[test]
fn a_tilde_on_a_later_if_of_a_chain_is_e0020_with_one_candidate() {
    // §11.5: "`~` は連鎖の最初の `if` にだけ書く。後ろの `if` に付けた `~`（`else if~`）は E0020 で、修正候補は、連鎖の頭に
    // `~` があれば後ろの `~` を除く形、無ければ `~` を頭の `if` へ移す形". With a space (`else if ~ d`) the candidate is
    // the same one (the space-removing reading would write `else if~ d` again); with the tilde touching the operand
    // (`else if ~d`) the prefix reading `else if !d` is the second.
    let move_to_head = "  if~ c { 1.0 } else if d { 2.0 } else { 3.0 }";
    let remove_later = "  if~ c { 1.0 } else if d { 2.0 } else { 3.0 }";
    let cases = vec![
        case(
            "the head has no tilde",
            in_a_flow("  if c { 1.0 } else if~ d { 2.0 } else { 3.0 }"),
            &[in_a_flow(move_to_head)],
        ),
        case(
            "the head has the tilde",
            in_a_flow("  if~ c { 1.0 } else if~ d { 2.0 } else { 3.0 }"),
            &[in_a_flow(remove_later)],
        ),
        case(
            "a space, the head has no tilde",
            in_a_flow("  if c { 1.0 } else if ~ d { 2.0 } else { 3.0 }"),
            &[in_a_flow(move_to_head)],
        ),
        case(
            "a space, the head has the tilde",
            in_a_flow("  if~ c { 1.0 } else if ~ d { 2.0 } else { 3.0 }"),
            &[in_a_flow(remove_later)],
        ),
        case(
            "touching the operand, the head has no tilde",
            in_a_flow("  if c { 1.0 } else if ~d { 2.0 } else { 3.0 }"),
            &[in_a_flow(move_to_head), in_a_flow("  if c { 1.0 } else if !d { 2.0 } else { 3.0 }")],
        ),
        case(
            "touching the operand, the head has the tilde",
            in_a_flow("  if~ c { 1.0 } else if ~d { 2.0 } else { 3.0 }"),
            &[in_a_flow(remove_later), in_a_flow("  if~ c { 1.0 } else if !d { 2.0 } else { 3.0 }")],
        ),
        case(
            "the third link",
            in_a_flow("  if c { 1.0 } else if d { 2.0 } else if~ e { 3.0 } else { 4.0 }"),
            &[in_a_flow("  if~ c { 1.0 } else if d { 2.0 } else if e { 3.0 } else { 4.0 }")],
        ),
        case(
            "in lines",
            in_a_flow("  if c {\n    1.0\n  } else if~ d {\n    2.0\n  } else {\n    3.0\n  }"),
            &[in_a_flow("  if~ c {\n    1.0\n  } else if d {\n    2.0\n  } else {\n    3.0\n  }")],
        ),
        case(
            "in a fn",
            in_a_fn("  if c { 1 } else if~ d { 2 } else { 3 }"),
            &[in_a_fn("  if~ c { 1 } else if d { 2 } else { 3 }")],
        ),
    ];
    check_cases("else_if_tilde", "E0020", &cases);
}

#[test]
fn the_tildes_of_one_chain_are_separate_errors_fixed_one_at_a_time() {
    // §11.5: "一つの連鎖に複数あれば `~` ごとの誤り"; §18.1: a unit stops at its first error. Applying the first candidate
    // again and again ends in the chain with the `~` on the head and nowhere else.
    let d = Dir::new("tilde_chain");
    let cases = [
        (
            "two links, no tilde on the head",
            "  if c { 1.0 } else if~ d { 2.0 } else if~ e { 3.0 } else { 4.0 }",
            "  if~ c { 1.0 } else if d { 2.0 } else if e { 3.0 } else { 4.0 }",
            2,
        ),
        (
            "two links, the head has the tilde",
            "  if~ c { 1.0 } else if~ d { 2.0 } else if~ e { 3.0 } else { 4.0 }",
            "  if~ c { 1.0 } else if d { 2.0 } else if e { 3.0 } else { 4.0 }",
            2,
        ),
        (
            "a space on the head and a link",
            "  if ~ c { 1.0 } else if~ d { 2.0 } else { 3.0 }",
            "  if~ c { 1.0 } else if d { 2.0 } else { 3.0 }",
            2,
        ),
        (
            "three links in lines",
            "  if c {\n    1.0\n  } else if~ d {\n    2.0\n  } else if~ e {\n    3.0\n  } else if~ x > 0.5 {\n    4.0\n  } else {\n    5.0\n  }",
            "  if~ c {\n    1.0\n  } else if d {\n    2.0\n  } else if e {\n    3.0\n  } else if x > 0.5 {\n    4.0\n  } else {\n    5.0\n  }",
            3,
        ),
    ];
    for (what, written, end, steps) in cases {
        let got = converge(&d, what, &in_a_flow(written), 6);
        assert_eq!(got.len(), steps, "{what}: number of steps");
        assert_eq!(squeeze(got.last().unwrap()), squeeze(&in_a_flow(end)), "{what}");
        // Only the first error of the unit is reported at each step (§18.1).
        let path = d.file("first.onsa", &in_a_flow(written));
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{what}: a unit reports its first error only: {diags:?}");
    }
}

// ---- S-356: an `at` in a type, and after the type of a declaration that is not an input or an output of a flow ----

fn fn_with_param(ty: &str) -> String {
    format!("pub fn f(x: {ty}) -> F32 {{\n  0.5\n}}\n")
}

#[test]
fn an_at_inside_a_type_or_after_the_type_of_a_plain_declaration_is_e0020() {
    // §11.3: "型の中（型引数、配列とタプルの要素、関数型の引数と返り値）と、入出力でない宣言の型（struct のフィールド、
    // enum の列挙子の要素、`type` の右辺、`const` の型）の後ろの `at` は、flow の中でも外でも構文の段の E0020 で、修正候補は
    // クロックを書ける場所へ移す形（クロックの無い flow の入出力の型の後ろ、束縛では値の式）か、場所が無ければ除く形".
    let wrap = "pub struct Wrap[T] {\n  v: T,\n}\n\n";
    let with_wrap = |s: &str| format!("{wrap}{s}");
    let cases = vec![
        // removed
        case("a type argument of an fn", fn_with_param("Option[F32 at sample]"), &[fn_with_param("Option[F32]")]),
        case("an array element", fn_with_param("[F32 at sample; 2]"), &[fn_with_param("[F32; 2]")]),
        case("a tuple element", fn_with_param("(F32 at sample, F32)"), &[fn_with_param("(F32, F32)")]),
        case(
            "an argument of a function type",
            fn_with_param("fn(F32 at sample) -> F32"),
            &[fn_with_param("fn(F32) -> F32")],
        ),
        case(
            "a nested type argument",
            fn_with_param("Option[Option[F32 at block]]"),
            &[fn_with_param("Option[Option[F32]]")],
        ),
        case(
            "the return type of an fn",
            "pub fn f(x: F32) -> Option[F32 at sample] {\n  Some(x)\n}\n".to_string(),
            &["pub fn f(x: F32) -> Option[F32] {\n  Some(x)\n}\n".to_string()],
        ),
        case(
            "a field",
            "pub struct S {\n  a: F32 at sample,\n}\n".to_string(),
            &["pub struct S {\n  a: F32,\n}\n".to_string()],
        ),
        case(
            "a field, an array",
            "pub struct S {\n  a: [F32 at block; 2],\n}\n".to_string(),
            &["pub struct S {\n  a: [F32; 2],\n}\n".to_string()],
        ),
        case(
            "an element of a variant",
            "pub enum E {\n  Gain(F32 at sample),\n  Off,\n}\n".to_string(),
            &["pub enum E {\n  Gain(F32),\n  Off,\n}\n".to_string()],
        ),
        case(
            "the right side of a type",
            "pub type T = F32 at sample\n".to_string(),
            &["pub type T = F32\n".to_string()],
        ),
        case(
            "the right side of a type, a type argument",
            "pub type T = Option[F32 at init]\n".to_string(),
            &["pub type T = Option[F32]\n".to_string()],
        ),
        case(
            "the type of a const",
            "pub const K: F32 at sample = 1.0\n".to_string(),
            &["pub const K: F32 = 1.0\n".to_string()],
        ),
        case(
            "the type of a const, an array",
            "pub const K: [F32 at init; 2] = [1.0, 2.0]\n".to_string(),
            &["pub const K: [F32; 2] = [1.0, 2.0]\n".to_string()],
        ),
        // moved to the value of a let or a var
        case(
            "the type of a let, in a fn",
            "pub fn f(x: Option[F32]) -> F32 {\n  let y: Option[F32 at sample] = x\n  0.5\n}\n".to_string(),
            &["pub fn f(x: Option[F32]) -> F32 {\n  let y: Option[F32] = x at sample\n  0.5\n}\n".to_string()],
        ),
        case(
            "the type of a var, in a fn",
            "pub fn f(x: F32) -> F32 {\n  var y: F32 at sample = x\n  y\n}\n".to_string(),
            &["pub fn f(x: F32) -> F32 {\n  var y: F32 = x at sample\n  y\n}\n".to_string()],
        ),
        case(
            "the type of a let, in a flow",
            "pub flow f(x: [F32; 2] at sample) -> F32 at sample {\n  let y: [F32 at sample; 2] = x\n  y[0]\n}\n"
                .to_string(),
            &["pub flow f(x: [F32; 2] at sample) -> F32 at sample {\n  let y: [F32; 2] = x at sample\n  y[0]\n}\n"
                .to_string()],
        ),
        // moved to the type of an input or an output of a flow
        case(
            "an input of a flow with no clock",
            "pub flow f(x: Option[F32 at sample]) -> F32 at sample {\n  0.5\n}\n".to_string(),
            &["pub flow f(x: Option[F32] at sample) -> F32 at sample {\n  0.5\n}\n".to_string()],
        ),
        case(
            "an output of a flow with no clock",
            "pub flow f(x: F32 at sample) -> (F32 at sample, F32) {\n  (x, x)\n}\n".to_string(),
            &["pub flow f(x: F32 at sample) -> (F32, F32) at sample {\n  (x, x)\n}\n".to_string()],
        ),
        case(
            "an input of a flow, a user type",
            with_wrap("pub flow f(x: Wrap[F32 at sample]) -> F32 at sample {\n  x.v\n}\n"),
            &[with_wrap("pub flow f(x: Wrap[F32] at sample) -> F32 at sample {\n  x.v\n}\n")],
        ),
        // removed: the input or the output of the flow has its clock already
        case(
            "an input of a flow with a clock",
            "pub flow f(x: Option[F32 at sample] at block) -> F32 at sample {\n  0.5\n}\n".to_string(),
            &["pub flow f(x: Option[F32] at block) -> F32 at sample {\n  0.5\n}\n".to_string()],
        ),
        case(
            "an output of a flow with a clock",
            "pub flow f(x: F32 at sample) -> [F32 at block; 2] at sample {\n  [x, x]\n}\n".to_string(),
            &["pub flow f(x: F32 at sample) -> [F32; 2] at sample {\n  [x, x]\n}\n".to_string()],
        ),
    ];
    check_cases("type_clock", "E0020", &cases);
}

#[test]
fn the_ats_of_one_type_are_separate_errors_fixed_one_at_a_time() {
    // S-356: "一つの型に複数の `at` は位置ごとの誤り". A unit stops at its first error (§18.1); the candidate of the first
    // removes it, the next is reported by the next check, and the first candidate again and again ends in a type with
    // no `at` inside it.
    let d = Dir::new("type_clock_multi");
    let pair = "pub struct Pair[A, B] {\n  first: A,\n  second: B,\n}\n\n";
    let cases = [
        (
            "a tuple",
            "pub fn f(x: (F32 at sample, F32 at block)) -> F32 {\n  0.5\n}\n".to_string(),
            "pub fn f(x: (F32, F32)) -> F32 {\n  0.5\n}\n".to_string(),
            2,
        ),
        (
            "three elements",
            "pub fn f(x: (F32 at sample, F32 at block, F32 at init)) -> F32 {\n  0.5\n}\n".to_string(),
            "pub fn f(x: (F32, F32, F32)) -> F32 {\n  0.5\n}\n".to_string(),
            3,
        ),
        (
            "type arguments of an fn",
            format!("{pair}pub fn f(x: Pair[F32 at sample, F32 at block]) -> F32 {{\n  0.5\n}}\n"),
            format!("{pair}pub fn f(x: Pair[F32, F32]) -> F32 {{\n  0.5\n}}\n"),
            2,
        ),
        (
            "type arguments of an input of a flow with no clock",
            format!("{pair}pub flow f(x: Pair[F32 at sample, F32 at block]) -> F32 at sample {{\n  0.5\n}}\n"),
            format!("{pair}pub flow f(x: Pair[F32, F32] at sample) -> F32 at sample {{\n  0.5\n}}\n"),
            2,
        ),
        (
            "a field",
            "pub struct S {\n  a: (F32 at sample, F32 at block),\n}\n".to_string(),
            "pub struct S {\n  a: (F32, F32),\n}\n".to_string(),
            2,
        ),
    ];
    for (what, written, end, steps) in cases {
        let got = converge(&d, what, &written, 6);
        assert_eq!(got.len(), steps, "{what}: number of steps");
        assert_eq!(squeeze(got.last().unwrap()), squeeze(&end), "{what}");
        let path = d.file("first.onsa", &written);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{what}: a unit reports its first error only: {diags:?}");
    }
}

#[test]
fn an_error_of_a_clock_in_a_type_has_its_note_and_one_candidate() {
    // §18.1: an E0020 shows the correct rule in a note (the clock belongs to a value; where it goes), and the candidate
    // is one (the place is decided: S-356 moves it where a clock can be written, and removes it where there is none).
    let d = Dir::new("type_clock_note");
    for (what, text) in [
        ("a type argument", fn_with_param("Option[F32 at sample]")),
        ("a field", "pub struct S {\n  a: F32 at sample,\n}\n".to_string()),
        ("a const", "pub const K: F32 at sample = 1.0\n".to_string()),
        ("an input of a flow", "pub flow f(x: Option[F32 at sample]) -> F32 at sample {\n  0.5\n}\n".to_string()),
    ] {
        let diag = only_diagnostic(&d, what, &text, "E0020");
        assert_eq!(array_of(&diag, "fixes").len(), 1, "{what}: {diag}");
        assert!(!array_of(&diag, "notes").is_empty(), "{what}: the note of the rule is missing: {diag}");
    }
}

#[test]
fn fmt_and_diff_stop_at_the_new_errors_and_do_not_change_the_file() {
    // §18.2: `onsa fmt` does not rewrite a file that has an error of the syntax stage; `diff --ast` stops with the same code.
    let d = Dir::new("stop");
    let sources = [
        in_a_flow("  if ~ c { 1.0 } else { 2.0 }"),
        in_a_flow("  if c { 1.0 } else if~ d { 2.0 } else { 3.0 }"),
        in_a_flow("  if~ c { 1.0 }"),
        fn_with_param("Option[F32 at sample]"),
        "pub struct S {\n  a: F32 at sample,\n}\n".to_string(),
        in_a_flow("  let y = x + prev~(^(y))\n  y"),
    ];
    for text in sources {
        let path = d.file("a.onsa", &text);
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 2, "fmt on an error of the syntax stage: {out:?}\n{text}");
        assert_eq!(read(&path), text, "fmt rewrote a file with a syntax error:\n{text}");
        let diff = onsa(&["diff", "--ast", &path, &path]);
        assert_eq!(code(&diff), 2, "diff --ast on an error of the syntax stage: {diff:?}\n{text}");
    }
}

// ---- S-357: a keyword after a `.` is a name ----------------------------------------------------

#[test]
fn a_keyword_after_a_dot_is_read_and_rejected_by_the_type_stage() {
    // §2.2: "`.` の直後のキーワードは名前として読み、フィールドとメソッドの名前にはキーワードを宣言できないので、
    // `xs.at(0)` のような形は後の段で解決できない誤りになる". Once `at` is a keyword, the syntax stage still reads `xs.at(0)` and
    // `s.at`; the type stage reports E0413 (no such method or field), and there is no E0002.
    let d = Dir::new("member_keyword");
    let head = "pub struct S {\n  a: F32,\n}\n\n";
    let cases = [
        ("a method", "pub fn f(xs: [I32; 2]) -> I32 {\n  xs.at(0)\n}\n"),
        ("a field", "pub fn f(s: S) -> F32 {\n  s.at\n}\n"),
        ("a method on the next line", "pub fn f(xs: [I32; 2]) -> I32 {\n  xs\n    .at(0)\n}\n"),
        ("a field and a field", "pub fn f(s: S) -> F32 {\n  s.at.a\n}\n"),
        ("another keyword", "pub fn f(s: S) -> F32 {\n  s.if\n}\n"),
        ("fn as a field", "pub fn f(s: S) -> F32 {\n  s.fn\n}\n"),
    ];
    for (what, body) in cases {
        let text = format!("{head}{body}");
        only_diagnostic(&d, what, &text, "E0413");
        let path = d.file("a.onsa", &text);
        // The syntax stage reads it: `diff --ast` of the file with itself is 0 (exit code 2 would be a syntax error).
        let diff = onsa(&["diff", "--ast", &path, &path]);
        assert_eq!(code(&diff), 0, "{what}: {diff:?}");
    }
}

#[test]
fn a_keyword_as_a_declared_name_is_still_rejected() {
    // §2.2: the keywords cannot be declared as a field or a method name, so only a `.` makes a keyword a name.
    // (A new `at` is covered in negative/syntax_at_keyword.onsa; `if` is a keyword today.)
    let d = Dir::new("declared_keyword");
    let has_e0002 = |what: &str, text: &str| {
        let path = d.file("a.onsa", text);
        let diags = check(&path);
        assert!(diags.iter().any(|x| code_of(x) == "E0002"), "{what}: expected E0002, got {diags:?}");
    };
    has_e0002("a field named if", "pub struct S {\n  if: F32,\n}\n");
    has_e0002("a function named match", "pub fn match(x: F32) -> F32 {\n  x\n}\n");
}

// ---- S-358: a `^` that no name follows ---------------------------------------------------------

#[test]
fn a_caret_with_no_name_after_it_is_e0002_with_a_note_and_no_candidate() {
    // §2.6: "名前の続かない `^`（`^(y)`、`^1.0`、`^^y`）は構文の段の E0002 で、`^` は `let` の名前の直前にだけ書くことを
    // note で示す". The `^` is a part of the name, not an operator.
    let d = Dir::new("caret");
    let bodies = [
        "  let y = x + prev~(^(y))\n  y",
        "  let y = x + prev~(^1.0)\n  y",
        "  let y = x + prev~(^1)\n  y",
        "  let y = x + prev~(^^y)\n  y",
        "  let y = x + prev~(^-y)\n  y",
        "  let y = x + prev~(^true)\n  y",
        "  let y = x + delay~(^(y), 4)\n  y",
        "  let y = x + vdelay~(^1.0, 0.5, 64)\n  y",
        "  let y = x + 0.5 * prev~(x + ^(y))\n  y",
        "  let y = x + ^(y)\n  y",
        "  let y = ^1.0\n  y",
    ];
    for body in bodies {
        let diag = only_diagnostic(&d, body, &in_a_flow(body), "E0002");
        assert!(array_of(&diag, "fixes").is_empty(), "no candidate for a caret with no name: {diag}\n{body}");
        assert!(!array_of(&diag, "notes").is_empty(), "the note of the rule is missing: {diag}\n{body}");
    }
    let diag = only_diagnostic(&d, "in a fn", &in_a_fn("  let y = ^(m)\n  y"), "E0002");
    assert!(array_of(&diag, "fixes").is_empty() && !array_of(&diag, "notes").is_empty(), "in a fn: {diag}");
}

#[test]
fn a_caret_before_a_name_and_the_binary_caret_are_read() {
    // The boundary of S-358: `^y` is the reference (a part of the name), `^` between two operands is the exclusive or.
    let d = Dir::new("caret_ok");
    let bodies = [
        "  let y = x + prev~(^y)\n  y",
        "  let y = x + prev~(^y.v)\n  y",
        "  let z = c ^ d\n  let y = z + prev~(^y)\n  y",
        "  let z = c ^ ^y\n  let y = z + prev~(^y)\n  y",
    ];
    for body in bodies {
        let path = d.file("a.onsa", &in_a_flow(body));
        let diags = check(&path);
        assert!(
            diags.iter().all(|x| !matches!(code_of(x), "E0001" | "E0002" | "E0003" | "E0020")),
            "the syntax stage reports {diags:?}\n{body}"
        );
    }
}
