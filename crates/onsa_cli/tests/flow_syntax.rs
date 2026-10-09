//! The syntax of a flow (spec §2.2, §2.5, §2.6, §3.1, §11.2 to §11.5, §18.1, §18.2; S-102, S-44, S-116,
//! S-101, S-110, S-29, S-118, R-132; W3-09/t): the clock `at` on the inputs and the output of a flow
//! and on an expression, the reference `^name`, the built-in delays with and without `init`, `if~`
//! and `match~`, and the errors of the syntax stage around them.
//!
//! The case files in `tests/spec/` pin what is read (`flow_syntax/*.onsa`, `mode = "parse"`), the code
//! and the line of each error (`negative/syntax_flow_at.onsa`, `negative/syntax_clock_operands.onsa`,
//! `negative/syntax_flow_caret.onsa`, `negative/syntax_at_keyword.onsa`,
//! `negative/syntax_flow_clock_binding.onsa`, `negative/nesting_boundary_clock.onsa`) and the round trip
//! of the CST (`tests/cst/`); `docs/foreign-forms.toml` lists the forms of other languages. These tests
//! say what those cannot: the normal form of the forms that `onsa fmt` writes (`docs/onsa-tools.md`
//! §3.2), that each part of the syntax is kept in the tree and not dropped (R-81: `diff --ast` sees it),
//! the shape of the tree through the levels of `onsa dump --levels` (§2.5 counts the levels of every
//! form, so the levels tell what `at`, `^name` and the postfix forms bind to), that fmt and
//! `diff --ast` stop at the errors of the syntax stage and do not stop at the flow syntax written
//! outside a flow (E0821 belongs to the names stage, §18.1), the position of E0006 for `at`, and the
//! text of the candidate of the clock on a binding.
//!
//! What is not here: the text of a message, the main span of E0011 (the spec does not say where it
//! starts), the candidates of E0011 (the runner checks the promise of §18.1 on them in the case
//! files), and the forms the spec leaves open (a `^` followed by something that is not a name, `if ~ c`
//! with a space, an `if~` with no `else`, `at` after a `.`, the clock of a type that is not the input
//! or output of a flow).
//!
//! Every test uses only the binary (`onsa fmt`, `onsa diff --ast`, `onsa check --json`, `onsa dump`).
//! Expected texts are written from the spec; none is taken from the output of the compiler.
//!
//! The tests were written before the syntax of W3-09 and ran ignored until W3-09/i (a test cannot be
//! silenced by `tests/pending.toml`).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_flow_syntax_{}_{tag}", std::process::id()));
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

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The directory `tests/spec` of the repository.
fn spec_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec")
}

/// The `.onsa` files of a directory of `tests/spec`, in the order of their names.
fn case_files(dir: &str) -> Vec<String> {
    let mut files: Vec<String> = std::fs::read_dir(spec_dir().join(dir))
        .unwrap_or_else(|e| panic!("tests/spec/{dir}: {e}"))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "onsa"))
        .map(|p| p.to_string_lossy().into_owned())
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no case file in tests/spec/{dir}");
    files
}

/// A flow whose body is `body` (lines already indented by two spaces).
fn in_a_flow(body: &str) -> String {
    format!("pub flow f(x: F32 at sample, p: F32 at block, c: Bool at sample) -> F32 at sample {{\n{body}\n}}\n")
}

/// A flow with the given inputs and output.
fn with_head(inputs: &str, output: &str, body: &str) -> String {
    format!("pub flow f({inputs}) -> {output} {{\n{body}\n}}\n")
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

fn line_of(d: &Value) -> u64 {
    d["span"]["line"].as_u64().expect("`span.line`")
}

fn col_of(d: &Value) -> u64 {
    d["span"]["col"].as_u64().expect("`span.col`")
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

/// The levels `onsa dump --levels <path>` prints: a line for each declaration (§2.5).
fn levels(path: &str) -> Vec<usize> {
    let out = onsa(&["dump", "--levels", path]);
    assert_eq!(code(&out), 0, "dump --levels {path}: {out:?}");
    stdout(&out)
        .lines()
        .map(|l| l.trim().parse().unwrap_or_else(|_| panic!("a line of dump --levels is not a number: {l:?}")))
        .collect()
}

// ---- the case files are in the normal form and read by the syntax stage ----------------------------

#[test]
fn the_syntax_cases_are_in_the_normal_form_and_have_no_syntax_error() {
    // The files of `tests/spec/flow_syntax/` are written the way `onsa fmt` writes them, and the
    // syntax stage reports nothing for them (`diff --ast` of a file with itself is 0, and exit code 2
    // would be a diagnostic of the syntax stage, §18.2). Their text is also what the CST gives back.
    for path in case_files("flow_syntax") {
        let out = onsa(&["fmt", "--check", &path]);
        assert_eq!(code(&out), 0, "{path} is not in the normal form or has a syntax error: {out:?}");
        let diff = onsa(&["diff", "--ast", &path, &path]);
        assert_eq!(code(&diff), 0, "{path}: {diff:?}");
        let cst = onsa(&["dump", "--cst", &path]);
        assert_eq!(code(&cst), 0, "{path}: {cst:?}");
        assert_eq!(String::from_utf8_lossy(&cst.stdout), read(&path), "{path}: the CST gives the file back");
    }
}

#[test]
fn the_error_cases_give_the_file_back_through_the_cst() {
    // The round trip holds with and without syntax errors (R-86): the files with errors too. (This
    // passes before W3-09 too: the CST keeps the text of what it cannot read.)
    for dir in ["negative", "nesting"] {
        for path in case_files(dir) {
            let name = Path::new(&path).file_name().unwrap().to_string_lossy().into_owned();
            let wanted =
                ["syntax_flow_", "syntax_clock_", "syntax_at_keyword", "nesting_boundary_clock", "boundary_clock"];
            if !wanted.iter().any(|w| name.contains(w)) {
                continue;
            }
            let cst = onsa(&["dump", "--cst", &path]);
            assert_eq!(code(&cst), 0, "{path}: {cst:?}");
            assert_eq!(String::from_utf8_lossy(&cst.stdout), read(&path), "{path}: the CST gives the file back");
        }
    }
}

// ---- fmt: the normal form (docs/onsa-tools.md §3.2) -----------------------------------------------

/// (what the case says, the body as written, the body `onsa fmt` writes). §3.2: one space on both sides of
/// `at` and of a binary operator, none inside brackets, none after a prefix mark or `^`; `,` followed by
/// one space. No `init` below is a default value (`onsa fmt` takes that one out, §11.4).
const NORMAL_FORMS: &[(&str, &str, &str)] = &[
    ("spaces round the clock", "  let a = p   at   sample\n  a", "  let a = p at sample\n  a"),
    ("tabs round the clock", "  let a = p\tat\tsample\n  a", "  let a = p at sample\n  a"),
    ("the clock of the last expression", "  p  at  sample", "  p at sample"),
    ("the clock in the arguments", "  g(p  at sample,q at   block)", "  g(p at sample, q at block)"),
    ("the clock after a call", "  let a = g(p)   at   block\n  a", "  let a = g(p) at block\n  a"),
    ("the clock after a prefix operator", "  let a = -p  at  sample\n  a", "  let a = -p at sample\n  a"),
    ("the clock round a parenthesis", "  let a = (p   at   sample) * x\n  a", "  let a = (p at sample) * x\n  a"),
    (
        "the clock in the heading of an if",
        "  if c   at   sample { 1.0 } else { 2.0 }",
        "  if c at sample { 1.0 } else { 2.0 }",
    ),
    ("a space after the parenthesis of a delay", "  prev~( ^y )", "  prev~(^y)"),
    ("the comma of a delay with an init", "  prev~(^y,1.0)", "  prev~(^y, 1.0)"),
    ("the comma of a delay line", "  delay~(^y,4)", "  delay~(^y, 4)"),
    ("the commas of a variable delay", "  vdelay~(^y,d,64,0.5)", "  vdelay~(^y, d, 64, 0.5)"),
    ("a space before a comma of a delay", "  prev~(^y , 1.0)", "  prev~(^y, 1.0)"),
    ("a binary caret with a space before only", "  let z = a ^b\n  z", "  let z = a ^ b\n  z"),
    ("a binary caret with no space", "  let z = a^b\n  z", "  let z = a ^ b\n  z"),
    ("a binary caret with wide spaces", "  let z = a   ^    b\n  z", "  let z = a ^ b\n  z"),
    ("the mark after a binary operator", "  let z = a +   ^y\n  z", "  let z = a + ^y\n  z"),
    ("the mark after a binary caret", "  let z = a ^   ^y\n  z", "  let z = a ^ ^y\n  z"),
    ("the mark after a minus", "  prev~(-^y)", "  prev~(-^y)"),
    ("if with a tilde", "  let a = if~   c { 1.0 } else { 2.0 }\n  a", "  let a = if~ c { 1.0 } else { 2.0 }\n  a"),
    (
        "match with a tilde",
        "  match~   k {\n    0 => 1.0,\n    _ => 2.0,\n  }",
        "  match~ k {\n    0 => 1.0,\n    _ => 2.0,\n  }",
    ),
    (
        "an else if chain with a tilde",
        "  if~   c {\n    1.0\n  } else if   d {\n    2.0\n  } else {\n    3.0\n  }",
        "  if~ c {\n    1.0\n  } else if d {\n    2.0\n  } else {\n    3.0\n  }",
    ),
    ("a flow call is not changed", "  lp~(x)", "  lp~(x)"),
];

#[test]
fn fmt_writes_the_flow_syntax_in_the_normal_form() {
    let d = Dir::new("normal");
    for (what, written, normal) in NORMAL_FORMS {
        let path = d.file("a.onsa", &in_a_flow(written));
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        assert_eq!(read(&path), in_a_flow(normal), "{what}");
        // The normal form is a fixed point of `fmt`, and `fmt --check` accepts it (§18.2).
        let check = onsa(&["fmt", "--check", &path]);
        assert_eq!(code(&check), 0, "{what}: the normal form is not accepted by --check: {check:?}");
        let again = onsa(&["fmt", &path]);
        assert_eq!(code(&again), 0, "{what}: {again:?}");
        assert_eq!(read(&path), in_a_flow(normal), "{what}: fmt twice");
    }
}

#[test]
fn fmt_does_not_change_the_program_that_has_flow_syntax() {
    // §18.2: fmt keeps the meaning; the file as written and the file as formatted are the same program
    // (`diff --ast` finds nothing). A change that drops the clock, the mark or the tilde would show.
    let d = Dir::new("fmt_same");
    for (what, written, _) in NORMAL_FORMS {
        let a = d.file("a.onsa", &in_a_flow(written));
        let b = d.file("b.onsa", &in_a_flow(written));
        let out = onsa(&["fmt", &b]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        let diff = onsa(&["diff", "--ast", &a, &b]);
        assert_eq!(code(&diff), 0, "{what}: the program changed: {diff:?}");
    }
}

/// (what, the file as written, the file `onsa fmt` writes): the heads of §11.2.
const HEADS: &[(&str, &str, &str)] = &[
    (
        "spaces round the clocks of a head",
        "pub flow g(x: F32   at   sample,p: F32 at\tblock) ->   F32   at   sample {\n  x\n}\n",
        "pub flow g(x: F32 at sample, p: F32 at block) -> F32 at sample {\n  x\n}\n",
    ),
    (
        "the clock of an array type",
        "pub flow g(x: [F32; 2]   at   sample) -> [F32; 2]  at  sample {\n  x\n}\n",
        "pub flow g(x: [F32; 2] at sample) -> [F32; 2] at sample {\n  x\n}\n",
    ),
    (
        "the block form of the inputs, indented wrongly",
        "pub flow g(\n    x: F32 at sample,\n  p: F32   at block,\n) -> F32 at sample {\n  x\n}\n",
        "pub flow g(\n  x: F32 at sample,\n  p: F32 at block,\n) -> F32 at sample {\n  x\n}\n",
    ),
    (
        "a doc comment and an attribute before an input",
        "pub flow g(\n  x: F32 at sample,\n  /// the level\n  @param(min: 0.0, max: 1.0, default: 0.5)\n  level: F32   at   block,\n) -> F32 at sample {\n  x\n}\n",
        "pub flow g(\n  x: F32 at sample,\n  /// the level\n  @param(min: 0.0, max: 1.0, default: 0.5)\n  level: F32 at block,\n) -> F32 at sample {\n  x\n}\n",
    ),
    (
        "the clock in the head of a fn (E0821 is the names stage's)",
        "pub fn g(x: F32   at   sample) -> F32  at  sample {\n  x\n}\n",
        "pub fn g(x: F32 at sample) -> F32 at sample {\n  x\n}\n",
    ),
];

#[test]
fn fmt_writes_the_head_of_a_flow_in_the_normal_form() {
    let d = Dir::new("heads");
    for (what, written, normal) in HEADS {
        let path = d.file("a.onsa", written);
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        assert_eq!(read(&path), *normal, "{what}");
        let check = onsa(&["fmt", "--check", &path]);
        assert_eq!(code(&check), 0, "{what}: {check:?}");
        let before = d.file("before.onsa", written);
        let diff = onsa(&["diff", "--ast", &before, &path]);
        assert_eq!(code(&diff), 0, "{what}: the program changed: {diff:?}");
    }
}

#[test]
fn fmt_formats_flow_syntax_outside_a_flow() {
    // §11.1: flow syntax in a fn, a test or a const is E0821, and E0821 is of the names stage (§18.1),
    // which `fmt` does not report (§18.2: only the syntax stage stops it). So fmt reads and formats such a
    // file, and `diff --ast` compares it.
    let written = "\
pub fn f(x: F32, c: Bool) -> F32 {
  let a = x   at   sample
  let b = prev~( ^b )
  let d = if~   c { a } else { b }
  d
}

const K: F32 = 1.0   at   init

test \"flow syntax in a test\" {
  let y = saw~(1.0)  at  sample
  let z = prev~(^z)
  assert y == z
}
";
    let normal = "\
pub fn f(x: F32, c: Bool) -> F32 {
  let a = x at sample
  let b = prev~(^b)
  let d = if~ c { a } else { b }
  d
}

const K: F32 = 1.0 at init

test \"flow syntax in a test\" {
  let y = saw~(1.0) at sample
  let z = prev~(^z)
  assert y == z
}
";
    let d = Dir::new("outside");
    let path = d.file("a.onsa", written);
    let before = d.file("before.onsa", written);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&path), normal);
    let diff = onsa(&["diff", "--ast", &before, &path]);
    assert_eq!(code(&diff), 0, "{diff:?}");
}

// ---- diff --ast: each part of the syntax is in the tree (R-81) ------------------------------------

/// (what the case says, one file, another file): the two files are different programs.
fn different() -> Vec<(&'static str, String, String)> {
    let b = |one: &str, other: &str| (in_a_flow(one), in_a_flow(other));
    let mut cases: Vec<(&'static str, String, String)> = Vec::new();
    let mut add = |what: &'static str, (one, other): (String, String)| cases.push((what, one, other));
    add(
        "the clock of an input",
        (with_head("x: F32 at sample", "F32 at sample", "  x"), with_head("x: F32 at block", "F32 at sample", "  x")),
    );
    add(
        "init and block for an input",
        (with_head("x: F32 at init", "F32 at sample", "  x"), with_head("x: F32 at block", "F32 at sample", "  x")),
    );
    add(
        "the clock of the output",
        (with_head("x: F32 at sample", "F32 at sample", "  x"), with_head("x: F32 at sample", "F32 at block", "  x")),
    );
    add("a clock on an expression and none", b("  let a = p at sample\n  a", "  let a = p\n  a"));
    add("one clock and another on an expression", b("  let a = p at sample\n  a", "  let a = p at block\n  a"));
    add("a clock on the last expression and none", b("  p at sample", "  p"));
    add(
        "a clock on a fn expression and none",
        (
            "pub fn f(x: F32) -> F32 {\n  let a = x at sample\n  a\n}\n".to_string(),
            "pub fn f(x: F32) -> F32 {\n  let a = x\n  a\n}\n".to_string(),
        ),
    );
    add("a mark and none", b("  prev~(^y)", "  prev~(y)"));
    add("a mark on one of two names", b("  prev~(^a + b)", "  prev~(a + ^b)"));
    add("an init and none", b("  prev~(x)", "  prev~(x, 1.0)"));
    add("another init", b("  prev~(x, 1.0)", "  prev~(x, 2.0)"));
    add("another length", b("  delay~(x, 4)", "  delay~(x, 8)"));
    add("a delay and another", b("  prev~(x)", "  delay~(x, 2)"));
    add("a tilde on if", b("  let a = if~ c { 1.0 } else { 2.0 }\n  a", "  let a = if c { 1.0 } else { 2.0 }\n  a"));
    add(
        "a tilde on match",
        b("  match~ k {\n    0 => 1.0,\n    _ => 2.0,\n  }", "  match k {\n    0 => 1.0,\n    _ => 2.0,\n  }"),
    );
    add(
        "a tilde on the whole else if chain",
        b(
            "  if~ c {\n    1.0\n  } else if d {\n    2.0\n  } else {\n    3.0\n  }",
            "  if c {\n    1.0\n  } else if d {\n    2.0\n  } else {\n    3.0\n  }",
        ),
    );
    // §3.1: `at` is looser than a prefix operator, so `-p at sample` is `(-p) at sample` and
    // differs from `-(p at sample)`.
    add(
        "the clock over a prefix operator and under it",
        b("  let a = -p at sample\n  a", "  let a = -(p at sample)\n  a"),
    );
    // §3.1: `at` is tighter than a binary operator.
    add(
        "the clock over a sum and under one of its operands",
        b("  let a = (x + p) at sample\n  a", "  let a = x + (p at sample)\n  a"),
    );
    add(
        "a postfix inside the clock and outside it",
        b("  let a = g(p at sample)\n  a", "  let a = g(p) at sample\n  a"),
    );
    // §2.5: the `^` is binary after an operand, and the mark where an operand is expected; a line break
    // ends the statement.
    add("a binary caret and the mark of a new statement", b("  let z = a ^ b\n  z", "  let z = a\n  ^b\n  z"));
    add("a binary caret and a mark after a plus", b("  let z = a ^ b\n  z", "  let z = a + ^b\n  z"));
    add("a field of the reference and a field of the delay", b("  prev~(^y.l)", "  prev~(^y).l"));
    cases
}

#[test]
fn diff_ast_sees_each_part_of_the_flow_syntax() {
    let d = Dir::new("diff");
    for (what, one, other) in different() {
        let a = d.file("a.onsa", &one);
        let b = d.file("b.onsa", &other);
        let out = onsa(&["diff", "--ast", &a, &b]);
        assert_eq!(
            code(&out),
            1,
            "{what}: the programs differ ({}): {out:?}",
            if code(&out) == 2 { "a file has a syntax error" } else { "diff found nothing" }
        );
    }
}

// ---- the levels (§2.5): the shape of the tree -------------------------------------------------------

/// (what, the file, the levels of its one declaration). §2.5: the body block is level 1; a
/// parenthesis, a prefix operator, a binary operator, `as` / `at`, a postfix call, `.name`, an index,
/// `if` (its blocks and the `if` of an `else if` below it), `match` and `par` (with its block) are a level each;
/// names, literals and the mark `^` of a name (`^name` is part of the name, §3.1) are none.
const LEVELS: &[(&str, &str, usize)] = &[
    ("a name", "  x", 1),
    ("a clock", "  x at sample", 2),
    ("a clock over a prefix operator", "  -x at sample", 3),
    ("a prefix operator over a parenthesized clock", "  -(x at sample)", 4),
    ("a clock in a parenthesis under a sum", "  (x at sample) + p", 4),
    ("a clock over a call", "  g(x) at sample", 3),
    ("a clock in an argument", "  g(x at sample)", 3),
    ("a clock over a flow call", "  lp~(x) at sample", 3),
    ("a flow call", "  lp~(x)", 2),
    ("a feedback", "  prev~(^y)", 2),
    ("a feedback with a field", "  prev~(^y.l)", 3),
    ("a feedback with a postfix chain", "  prev~(^ys[0].l)", 4),
    ("a feedback in a sum", "  prev~(0.5 * ^y + x)", 4),
    ("an exclusive or", "  a ^ b", 2),
    ("an exclusive or and a mark", "  prev~(a ^ ^b)", 3),
    ("if with a tilde", "  if~ c { x } else { y }", 3),
    ("if with a tilde and a clock in the condition", "  if~ c at sample { x } else { y }", 3),
    ("if with a tilde and a parenthesized clock in the condition", "  if~ (c at sample) { x } else { y }", 4),
    ("an else if chain", "  if~ c { x } else if d { y } else { z }", 4),
    ("match with a tilde", "  match~ k {\n    0 => x,\n    _ => y,\n  }", 2),
    ("match with a tilde and a clock in an arm", "  match~ k {\n    0 => x at sample,\n    _ => y,\n  }", 3),
    ("par and a clock in its block", "  par i in 0..<4 { x at sample }", 4),
    ("a delay with an init", "  prev~(x, 1.0)", 2),
    ("a clock in the first argument of a delay", "  delay~(x at sample, 4)", 3),
];

#[test]
fn the_levels_of_the_flow_syntax_are_those_of_section_2_5() {
    let d = Dir::new("levels");
    for (what, body, want) in LEVELS {
        let path = d.file("a.onsa", &in_a_flow(body));
        assert_eq!(levels(&path), vec![*want], "{what}: {body:?}");
    }
}

// ---- the nesting limit and `at` (§2.5, §18.1) ---------------------------------------------------------

/// `n` parentheses round `x at sample` in the body of a flow: the body is level 1, the parentheses are
/// levels 2 to n + 1 and the `at` is level n + 2.
fn nested_clock(n: usize) -> String {
    format!("pub flow f(x: F32 at block) -> F32 at sample {{\n  {}x at sample{}\n}}\n", "(".repeat(n), ")".repeat(n))
}

#[test]
fn a_clock_makes_the_level_256_and_is_accepted() {
    // 254 parentheses: the `at` is level 256, the limit (§2.5). The syntax stage reports nothing.
    let d = Dir::new("nest_ok");
    let path = d.file("a.onsa", &nested_clock(254));
    assert_eq!(levels(&path), vec![256]);
    let diff = onsa(&["diff", "--ast", &path, &path]);
    assert_eq!(code(&diff), 0, "{diff:?}");
}

#[test]
fn a_clock_makes_the_level_257_and_is_e0006_at_the_at() {
    // 255 parentheses: the `at` is level 257. E0006 is reported at the token that makes the level,
    // the `at` (§2.5: "その段を作るトークン（… キーワード）"), and the unit is not read further.
    let d = Dir::new("nest_over");
    let text = nested_clock(255);
    let path = d.file("a.onsa", &text);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "one diagnostic: {diags:?}");
    assert_eq!(code_of(&diags[0]), "E0006", "{diags:?}");
    assert_eq!(line_of(&diags[0]), 2, "{diags:?}");
    // two spaces, 255 parentheses, `x`, a space: the `at` is column 2 + 255 + 1 + 1 + 1.
    assert_eq!(col_of(&diags[0]), 260, "the `at`: {diags:?}");
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 2, "E0006 is of the syntax stage, fmt stops: {out:?}");
}

// ---- errors of the syntax stage stop fmt and diff --ast (§18.2) -----------------------------------------

/// Files with an error of the syntax stage in the flow syntax: (what, the file, the code of the error).
fn syntax_errors() -> Vec<(&'static str, String, &'static str)> {
    let f = |body: &str| in_a_flow(body);
    vec![
        ("a clock as the operand of a sum", f("  p at sample + x"), "E0011"),
        ("a clock as the right operand of a sum", f("  x + p at sample"), "E0011"),
        ("two clocks", f("  p at block at sample"), "E0011"),
        ("a cast and a clock", f("  n as F32 at sample"), "E0011"),
        ("a clock and a cast", f("  n at sample as F32"), "E0011"),
        (
            "a clock in a fn is read first as a syntax error",
            "pub fn f(x: F32) -> F32 {\n  x at sample + 1.0\n}\n".to_string(),
            "E0011",
        ),
        ("a missing clock in an input", with_head("x: F32 at, p: F32 at block", "F32 at sample", "  x"), "E0002"),
        ("a missing clock in the output", with_head("x: F32 at sample", "F32 at", "  x"), "E0002"),
        ("a clock that is a number", f("  let a = p at 1\n  a"), "E0002"),
        ("a mark with no name", f("  prev~(^)"), "E0002"),
        ("the keyword at as a name", f("  let at = 1\n  at"), "E0002"),
        ("the clock on a binding", f("  let y: F32 at sample = x\n  y"), "E0020"),
        ("the clock on a binding of another clock", f("  let y: F32 at block = p\n  y"), "E0020"),
        // The value is cut by a syntax error (W3-09/b2): that error is the unit's, not the
        // clock's E0020 with a candidate on the part that was read.
        ("the clock on a binding of a cut value", f("  let y: F32 at sample = 0..<3\n  x"), "E0002"),
    ]
}

#[test]
fn fmt_and_diff_stop_at_an_error_of_the_syntax_stage_in_the_flow_syntax() {
    // §18.2: a file with a diagnostic of the syntax stage is not rewritten (exit code 2) and `diff --ast`
    // does not compare it (exit code 2); the diagnostic goes to the standard output
    // (docs/onsa-tools.md §3.1, §4). E0011 is of the syntax stage as every E00xx is (§18.2), so it
    // stops them too.
    let d = Dir::new("syntax_errors");
    let other = d.file("other.onsa", &in_a_flow("  x"));
    for (what, text, want) in syntax_errors() {
        let path = d.file("a.onsa", &text);
        for args in [vec!["fmt"], vec!["fmt", "--check"]] {
            let mut full = args.clone();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what}: onsa {args:?}: {out:?}");
            assert_eq!(read(&path), text, "{what}: the file is not rewritten");
            let shown = stdout(&out);
            assert!(
                shown.contains(&format!("error[{want}]")),
                "{what}: the diagnostic {want} is on the standard output: {out:?}"
            );
        }
        let diff = onsa(&["diff", "--ast", &path, &other]);
        assert_eq!(code(&diff), 2, "{what}: diff --ast: {diff:?}");
        assert!(stdout(&diff).contains(&format!("error[{want}]")), "{what}: diff --ast shows {want}: {diff:?}");
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{what}: one diagnostic for the one unit: {diags:?}");
        assert_eq!(code_of(&diags[0]), want, "{what}: {diags:?}");
    }
}

// ---- the clock on a binding (§11.3, §18.1) ----------------------------------------------------------------

#[test]
fn the_clock_on_a_binding_has_a_candidate_that_moves_it_and_a_note() {
    // §11.3: `let y: F32 at sample = x` is E0020 and the candidate is `let y: F32 = x at sample`.
    // §18.1: the E0020 gives the right rule in a note; an edit changes only the tokens it changes (the
    // `at` and the clock are taken out, `at` and the clock are put after the value), so no edit
    // contains the type, the `=` or the value.
    let d = Dir::new("binding");
    let text = in_a_flow("  let y: F32 at sample = x\n  y");
    let path = d.file("a.onsa", &text);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{diags:?}");
    let diag = &diags[0];
    assert_eq!(code_of(diag), "E0020", "{diags:?}");
    assert_eq!(line_of(diag), 2, "{diags:?}");
    assert!(!array_of(diag, "notes").is_empty(), "the note that shows the rule: {diag}");
    let fixes = array_of(diag, "fixes");
    assert!(!fixes.is_empty(), "a candidate: {diag}");
    let edits = edits_of(fixes[0]);
    for (replaced, edit) in replaced_texts(&text, &edits).iter().zip(&edits) {
        assert!(
            !replaced.contains("F32") && !replaced.contains('=') && !replaced.contains('x') && !replaced.contains('y'),
            "an edit reaches a token it does not change: {replaced:?} (edit to {:?})",
            edit.replace
        );
    }
    // The runner compares the text after a candidate by its tokens, not by the amount of space (S-251).
    let squash = |t: &str| t.split(' ').filter(|w| !w.is_empty()).collect::<Vec<_>>().join(" ");
    let fixed = apply(&text, &edits);
    assert_eq!(squash(&fixed), squash(&in_a_flow("  let y: F32 = x at sample\n  y")));
}

#[test]
fn the_clock_on_a_binding_of_a_sum_is_written_in_parentheses_by_the_candidate() {
    // §3.1: `x + 1.0 at sample` is E0011, so the candidate does not write it; the value is in
    // parentheses (the spec gives the one example `let y: F32 = x at sample` and the promise of §18.1:
    // no error of the syntax stage is left in the unit). The text after the candidate is read by the
    // syntax stage and the clock stands over the whole sum.
    let d = Dir::new("binding_sum");
    let text = in_a_flow("  let y: F32 at sample = x + 1.0\n  y");
    let path = d.file("a.onsa", &text);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!(code_of(&diags[0]), "E0020", "{diags:?}");
    let fixes = array_of(&diags[0], "fixes");
    assert!(!fixes.is_empty(), "a candidate: {}", diags[0]);
    let fixed = apply(&text, &edits_of(fixes[0]));
    let fixed_path = d.file("fixed.onsa", &fixed);
    let out = onsa(&["fmt", "--check", &fixed_path]);
    assert_ne!(code(&out), 2, "the text after the candidate has a syntax error: {fixed:?}: {out:?}");
    // The sum is the operand of the clock: its tree is that of the written parentheses, so `diff --ast`
    // against the same program written with them finds nothing.
    let by_hand = d.file("by_hand.onsa", &in_a_flow("  let y: F32 = (x + 1.0) at sample\n  y"));
    let diff = onsa(&["diff", "--ast", &fixed_path, &by_hand]);
    assert_eq!(code(&diff), 0, "{fixed:?}: {diff:?}");
}

// ---- `at` does not continue a line (§2.5) -----------------------------------------------------------------------------

#[test]
fn a_clock_is_not_continued_on_the_next_line() {
    // §2.5: a line continues when it ends with a binary operator, a range symbol, `=`, `->` or an
    // attribute; `at` is none of them, so `x at` and `sample` on the next line are two statements and
    // the first is cut after `at` (E0002). One diagnostic for the unit; the line is that of the `at`
    // or the one after it.
    let d = Dir::new("continue");
    let text = in_a_flow("  let y = x at\n  sample\n  y");
    let path = d.file("a.onsa", &text);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!(code_of(&diags[0]), "E0002", "{diags:?}");
    let line = line_of(&diags[0]);
    assert!(line == 2 || line == 3, "the error is at the cut: line {line}");
}

// ---- E0011 and the units around it (§18.1) --------------------------------------------------------------------------------

#[test]
fn e0011_of_a_clock_is_one_error_per_unit_and_hides_nothing_in_the_next_unit() {
    // §18.1: a unit stops at its first error and units are independent. Two flows with a bare `at`
    // give two E0011; the names error of the unit after them is still reported; the names in the
    // unit with E0011 are not looked up.
    let d = Dir::new("units");
    let text = "\
pub flow first(p: F32 at block, x: F32 at sample) -> F32 at sample {
  nope(p at sample + x)
}

pub flow second(p: F32 at block, x: F32 at sample) -> F32 at sample {
  p at block at sample
}

pub fn third() -> I32 {
  missing
}
";
    let path = d.file("a.onsa", text);
    let diags = check(&path);
    let found: Vec<(&str, u64)> = diags.iter().map(|x| (code_of(x), line_of(x))).collect();
    assert_eq!(found, vec![("E0011", 2), ("E0011", 6), ("E0302", 10)], "{diags:?}");
}
