//! Calls and the shapes of expressions (W3-20/t): `.(` for a function value (S-191, spec §6.1),
//! the callee that is no path of names (E0020 of the syntax stage), the operand of `move` and
//! `inout` (R-42, §5.2), the one-element tuple (R-43, §2.4), `move` on the last expression of a
//! block (S-100, §5.2) and the type brackets that hold commas (R-196, §4.5).
//!
//! The case files in `tests/spec/` pin the diagnostics and the text after each candidate:
//! `fixes/e0020_call_forms_syntax.onsa` (the callee), `fixes/e0020_value_call_spacing.onsa` (a space
//! around the `.` of `.(`), `fixes/e0020_compound_assign_tuple.onsa` (S-322), `fn/value_calls.onsa`
//! and `fn/value_calls_pkg/` (the forms that are read), `negative/syntax_move_operand.onsa` (R-42),
//! `negative/syntax_one_tuple.onsa` and `semantics/paren_group.onsa` (R-43),
//! `values/move_tail_syntax.onsa` (S-100). These tests say what those cannot: the normal form that
//! `onsa fmt` writes for `.(` (`docs/onsa-tools.md` §3.2), that `.(` is in the tree (`diff --ast`
//! sees it), that fmt and `diff --ast` stop at an error of the syntax stage, how the edits of a
//! candidate are cut (the tokens that change and no others, §18.1), that every E0020 of the callee
//! form has a note that shows `.(` (§18.1), and the forms that cannot be in a case file that has to be
//! canonical under `fmt` (a `move` on a returned value is removed by `fmt`, §5.2).
//!
//! Every test uses only the binary (`onsa check --json`, `onsa fmt`, `onsa diff --ast`). Expected
//! texts are written from the spec; none is taken from the output of the compiler.
//!
//! The tests marked `#[ignore]` do not pass with the code of 2026-10-09 (the parser does not read
//! `.(`, accepts the forms of R-42 and R-43, and rejects a `move` on a block's last expression). Each
//! names the work that removes the mark (an ignored test is not silenced by `tests/pending.toml`: it
//! is skipped). Run them with `cargo test -p onsa_cli --test call_forms_syntax -- --ignored`.

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_call_forms_{}_{tag}", std::process::id()));
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

/// A function with `body` (lines already indented by two spaces) as its body.
fn in_a_function(body: &str) -> String {
    format!("pub fn f() -> U8 {{\n{body}\n}}\n")
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

fn notes_of(d: &Value) -> Vec<String> {
    d.get("notes")
        .and_then(Value::as_array)
        .map(|a| a.iter().map(|n| n["message"].as_str().unwrap_or("").to_string()).collect())
        .unwrap_or_default()
}

fn start_of(d: &Value) -> (u64, u64) {
    (d["span"]["line"].as_u64().expect("line"), d["span"]["col"].as_u64().expect("col"))
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

/// The text each edit replaces, in the order of the edits.
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

// ---- fmt: the normal form of a call through a function value (docs/onsa-tools.md §3.2) ---------

/// (what the case says, the body as written, the body `onsa fmt` writes). §3.2: no space round the
/// `.` of `.(` or inside the parentheses, `, ` between the arguments, a space on both sides of a
/// binary operator; a line that starts with `.` continues the previous one, one level deeper.
const NORMAL_FORMS: &[(&str, &str, &str)] = &[
    ("spaces inside the arguments", "  f.( x )", "  f.(x)"),
    ("no space after the comma", "  f.(1,2)", "  f.(1, 2)"),
    ("space before the comma", "  f.( 1 ,2 )", "  f.(1, 2)"),
    ("no arguments", "  f.( )", "  f.()"),
    ("a field", "  s.curve.( x )", "  s.curve.(x)"),
    ("an element", "  ops[ i ].( x )", "  ops[i].(x)"),
    ("a result", "  pick( true ).( 5 )", "  pick(true).(5)"),
    ("a result called again", "  h.( 1 ).( 2 )", "  h.(1).(2)"),
    ("a tuple element", "  t.0.( t.1 )", "  t.0.(t.1)"),
    ("a nested tuple element", "  t.0.1.( x )", "  t.0.1.(x)"),
    ("binary operators round the calls", "  f.(x)+g.(y)-f.(g.(x))", "  f.(x) + g.(y) - f.(g.(x))"),
    ("the marks of the arguments", "  f.( inout   v , move  a )", "  f.(inout v, move a)"),
    ("a call in the argument", "  f.( g.( x ) )", "  f.(g.(x))"),
    ("a field of the result", "  f.(x).0 + f.(x).1", "  f.(x).0 + f.(x).1"),
    ("an element of the result", "  f.(x)[0]", "  f.(x)[0]"),
    ("a method of the result", "  f.(x).abs()", "  f.(x).abs()"),
    ("a conversion of the result", "  f.(x)   as I64", "  f.(x) as I64"),
    ("a try of the result", "  f.( x )?", "  f.(x)?"),
    ("a prefix before the call", "  -f.( x )", "  -f.(x)"),
    ("a line that continues with `.(`", "  let r = pick(up)\n.(5)\n  r", "  let r = pick(up)\n    .(5)\n  r"),
    ("the arguments in the block form are kept", "  f.(\n    1,\n    2,\n  )", "  f.(\n    1,\n    2,\n  )"),
    ("the arguments in the continuation form are kept", "  f.(1,\n     2)", "  f.(1,\n     2)"),
    ("the item call is not rewritten", "  inc(x)", "  inc(x)"),
    ("an item call and a value call", "  inc(x) + f.(x)", "  inc(x) + f.(x)"),
];

#[test]
fn fmt_writes_a_value_call_in_the_normal_form() {
    let d = Dir::new("normal");
    for (what, written, normal) in NORMAL_FORMS {
        let path = d.file("a.onsa", &in_a_function(written));
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        assert_eq!(read(&path), in_a_function(normal), "{what}");
        // The normal form is a fixed point of `fmt`, and `fmt --check` accepts it (§18.2).
        let check = onsa(&["fmt", "--check", &path]);
        assert_eq!(code(&check), 0, "{what}: the normal form is not accepted by --check: {check:?}");
        let again = onsa(&["fmt", &path]);
        assert_eq!(code(&again), 0, "{what}: {again:?}");
        assert_eq!(read(&path), in_a_function(normal), "{what}: fmt twice");
    }
}

#[test]
fn fmt_check_names_the_file_that_has_a_value_call_out_of_form() {
    // §18.2: `fmt --check` exits with 1 and writes nothing for a file that is not in the normal form.
    let d = Dir::new("check");
    let text = in_a_function("  f.( x )");
    let path = d.file("a.onsa", &text);
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 1, "{out:?}");
    assert_eq!(read(&path), text, "--check writes nothing");
    assert!(String::from_utf8_lossy(&out.stdout).contains("a.onsa"), "the file is named: {out:?}");
}

#[test]
fn a_file_in_the_normal_form_is_kept_whatever_the_calls_in_it() {
    // One file with every kind of call of §6.1 in the normal form: fmt changes nothing.
    let text = "\
pub struct Shaper {
  gain: F32,
  curve: fn(F32) -> F32,
}

pub fn f(s: Shaper, ops: [fn(I32) -> I32; 2], t: (fn(I32) -> I32, I32), g: fn(I32) -> I32) -> I32 {
  let a = inc(1)
  let b = g.(a)
  let c = s.curve.(1.0).trunc_i32()
  let d = ops[0].(b) + ops[1].(c)
  let e = t.0.(t.1)
  let r = pick(true).(d)
  let q = Point.new(1.0, 2.0)
  let p = Some(r)
  a + b + c + d + e + r
}
";
    let d = Dir::new("kept");
    let path = d.file("a.onsa", text);
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&path), text);
}

// ---- diff --ast: `.(` is in the tree ------------------------------------------------------------

/// (what the case says, one body, another body): the two files are different programs.
const DIFFERENT: &[(&str, &str, &str)] = &[
    ("a value call and an item call", "  f.(x)", "  f(x)"),
    ("a value call and the value", "  f.(x)", "  f"),
    ("another callee", "  f.(x)", "  g.(x)"),
    ("another argument", "  f.(x)", "  f.(y)"),
    ("another number of arguments", "  f.(x, y)", "  f.(x)"),
    ("a field and its call", "  s.f.(x)", "  s.f"),
    ("the callee and its result", "  g.(x).(y)", "  g.(x)"),
    ("a call of a field and a call of the object", "  s.f.(x)", "  s.(x)"),
    ("an element and its call", "  ops[i].(x)", "  ops[i]"),
    ("a value call and a method call", "  s.f.(x)", "  s.f(x)"),
    ("the mark of the argument", "  f.(inout v)", "  f.(v)"),
];

/// (what, one body, another body): the same program written in two ways.
const SAME: &[(&str, &str, &str)] = &[
    ("spaces inside the arguments", "  f.(x)", "  f.( x )"),
    ("spaces round the comma", "  f.(x, y)", "  f.(x ,y)"),
    ("a result called again", "  g.(x).(y)", "  g.( x ).( y )"),
    ("an operator round the calls", "  f.(x) + g.(y)", "  f.(x)+g.(y)"),
];

#[test]
fn diff_ast_sees_a_value_call_and_does_not_see_its_spaces() {
    let d = Dir::new("diff");
    for (what, one, other) in DIFFERENT {
        let a = d.file("a.onsa", &in_a_function(one));
        let b = d.file("b.onsa", &in_a_function(other));
        let out = onsa(&["diff", "--ast", &a, &b]);
        assert_eq!(code(&out), 1, "{what}: the programs differ: {out:?}");
    }
    for (what, one, other) in SAME {
        let a = d.file("a.onsa", &in_a_function(one));
        let b = d.file("b.onsa", &in_a_function(other));
        let out = onsa(&["diff", "--ast", &a, &b]);
        assert_eq!(code(&out), 0, "{what}: the programs are the same: {out:?}");
    }
}

// ---- fmt and diff --ast stop at the errors of the syntax stage (§18.2) -------------------------

/// Files with an error of the syntax stage in the forms of this work: (what, the file, the code of
/// the error). `fmt` and `diff --ast` stop at each of them. A callee that is no path of names is an
/// E0020 that `fmt` does not repair by removing the parentheses (§6.1: the parentheses stay).
const SYNTAX_ERRORS: &[(&str, &str, &str)] = &[
    ("a parenthesized field as the callee", "pub fn f(s: S) -> U8 {\n  (s.f)(1)\n}\n", "E0020"),
    ("a parenthesized tuple element as the callee", "pub fn f(t: T) -> U8 {\n  (t.0)(1)\n}\n", "E0020"),
    ("the result of a call as the callee", "pub fn f() -> U8 {\n  pick(true)(5)\n}\n", "E0020"),
    ("the result of a value call as the callee", "pub fn f(h: H) -> U8 {\n  h.(1)(2)\n}\n", "E0020"),
    ("a space before the dot of the call", "pub fn f(g: G) -> U8 {\n  g .(1)\n}\n", "E0020"),
    ("a space after the dot of the call", "pub fn f(g: G) -> U8 {\n  g. (1)\n}\n", "E0020"),
    ("a sum as the operand of move", "pub fn f(y: U8) -> U8 {\n  take(move y + 1)\n}\n", "E0002"),
    ("a sum as the operand of inout", "pub fn f(v: U8) -> U8 {\n  bump(inout v + 1)\n  v\n}\n", "E0002"),
    ("a parenthesized mark as an operand", "pub fn f(y: U8) -> U8 {\n  1 + (move y)\n}\n", "E0002"),
    ("a one-element tuple", "pub fn f() -> U8 {\n  let t = (1,)\n  1\n}\n", "E0002"),
    ("a one-element tuple type", "pub fn f(t: (U8,)) -> U8 {\n  1\n}\n", "E0002"),
    ("a one-element tuple pattern", "pub fn f(v: U8) -> U8 {\n  let (a,) = v\n  a\n}\n", "E0002"),
    ("a call whose arguments are not closed", "pub fn f(g: G) -> U8 {\n  g.(1\n}\n", "E0002"),
    ("a call with no callee", "pub fn f() -> U8 {\n  .(1)\n}\n", "E0002"),
    ("a call with two commas", "pub fn f(g: G) -> U8 {\n  g.(1,, 2)\n}\n", "E0002"),
];

#[test]
fn fmt_and_diff_stop_at_an_error_of_the_syntax_stage_of_these_forms() {
    // §18.2: a file with a diagnostic of the syntax stage is not rewritten (exit code 2) and
    // `diff --ast` does not compare it (exit code 2); the diagnostic goes to the standard output
    // (docs/onsa-tools.md §3.1, §4). R-43 was `fmt` rewriting `(1,)` into `(1)`: another program.
    let d = Dir::new("syntax_errors");
    let other = d.file("other.onsa", "pub fn f() -> U8 {\n  250\n}\n");
    for (what, text, expected) in SYNTAX_ERRORS {
        let path = d.file("a.onsa", text);
        for args in [vec!["fmt"], vec!["fmt", "--check"]] {
            let mut full = args.clone();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what}: onsa {args:?}: {out:?}");
            assert_eq!(read(&path), *text, "{what}: the file is not rewritten");
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(
                stdout.contains(&format!("error[{expected}]")),
                "{what}: the diagnostic {expected} is on the standard output: {out:?}"
            );
        }
        let diff = onsa(&["diff", "--ast", &path, &other]);
        assert_eq!(code(&diff), 2, "{what}: diff --ast: {diff:?}");
    }
}

// ---- the E0020 of a callee that is no path of names: the candidate and the note (§6.1, §18.1) ----

/// (what, the body of the function, the callee as written, the first token of the call in the body
/// as (line, column) counted in the file, the replaced texts, the replacements, the body after the
/// candidate). The file is `in_a_function(body)`, so the body starts on line 2.
#[allow(clippy::type_complexity)]
const CALLEE_FORMS: &[(&str, &str, (u64, u64), &[&str], &[&str], &str)] = &[
    (
        "a parenthesized field: the parentheses go, the dot comes",
        "  (s.curve)(x)",
        (2, 3),
        &["(", ")"],
        &["", "."],
        "  s.curve.(x)",
    ),
    ("a parenthesized tuple element", "  (t.0)(t.1)", (2, 3), &["(", ")"], &["", "."], "  t.0.(t.1)"),
    ("a parenthesized nested field", "  (r.shaper.curve)(x)", (2, 3), &["(", ")"], &["", "."], "  r.shaper.curve.(x)"),
    ("the result of a call: the dot is inserted", "  pick(true)(5)", (2, 3), &[""], &["."], "  pick(true).(5)"),
    ("the result of a value call", "  h.(1)(2)", (2, 3), &[""], &["."], "  h.(1).(2)"),
    ("the result of a method call", "  m.make()(3)", (2, 3), &[""], &["."], "  m.make().(3)"),
    ("the result of a call in a sum", "  pick(false)(x) + 1", (2, 3), &[""], &["."], "  pick(false).(x) + 1"),
];

#[test]
fn the_candidate_for_a_callee_that_is_no_path_edits_the_tokens_that_change() {
    // §18.1: an edit replaces the tokens that change and no others. `(s.f)(x)` becomes `s.f.(x)`: the
    // `(` is removed and the `)` becomes the `.` (the `(` of the arguments stays). `g(x)(y)`
    // becomes `g(x).(y)`: an insertion of `.` between the `)` and the `(`. One diagnostic, one
    // candidate; the main position is the first token of the call (S-316).
    let d = Dir::new("callee_edits");
    for (what, body, start, replaced, replacements, after) in CALLEE_FORMS {
        let text = in_a_function(body);
        let path = d.file("a.onsa", &text);
        let diags = check(&path);
        let e0020: Vec<&Value> = diags.iter().filter(|x| code_of(x) == "E0020").collect();
        assert_eq!(e0020.len(), 1, "{what}: one E0020: {diags:?}");
        assert_eq!(diags.len(), 1, "{what}: nothing else is reported: {diags:?}");
        assert_eq!(start_of(e0020[0]), *start, "{what}: the main position is the first token of the call");
        let fixes = fixes_of(e0020[0]);
        assert_eq!(fixes.len(), 1, "{what}: one candidate: {}", e0020[0]);
        let edits = edits_of(fixes[0]);
        assert_eq!(replaced_texts(&text, &edits), *replaced, "{what}: the tokens that change");
        let replacements_got: Vec<&str> = edits.iter().map(|e| e.replace.as_str()).collect();
        assert_eq!(replacements_got, *replacements, "{what}: what replaces them");
        assert_eq!(apply(&text, &edits), in_a_function(after), "{what}: the text after the candidate");
        let notes = notes_of(e0020[0]);
        assert!(!notes.is_empty(), "{what}: a note shows the rule (§18.1): {}", e0020[0]);
        assert!(notes.iter().any(|n| n.contains(".(")), "{what}: a note shows `.(`: {notes:?}");
    }
}

#[test]
fn a_callee_that_is_no_path_does_not_hide_the_other_functions() {
    // §18.1: the units are independent. The three functions have the error, the fourth is fine;
    // each of the three is reported once and the fine one is not.
    let text = "\
pub struct S {
  f: fn(U8) -> U8,
}

pub type H = fn(U8) -> fn(U8) -> U8

pub fn a(s: S) -> U8 {
  (s.f)(1)
}

pub fn b() -> U8 {
  pick(true)(5)
}

pub fn c(h: H) -> U8 {
  h.(1)(2)
}

pub fn fine(s: S, h: H) -> U8 {
  s.f.(1) + h.(1).(2)
}
";
    let d = Dir::new("units");
    let path = d.file("a.onsa", text);
    let diags = check(&path);
    let lines: Vec<u64> = diags.iter().filter(|x| code_of(x) == "E0020").map(|x| start_of(x).0).collect();
    assert_eq!(lines, vec![8, 12, 16], "{diags:?}");
    assert_eq!(diags.len(), 3, "{diags:?}");
}

#[test]
fn a_space_round_the_dot_of_a_value_call_is_removed_by_the_candidate() {
    // §2.5: the member `.` takes no space inside a line, and `.(` is a member `.`. The candidate
    // removes the space (one edit that replaces the space with nothing).
    let cases: [(&str, &str, &str); 3] =
        [("before", "  g .(1)", "  g.(1)"), ("after", "  g. (1)", "  g.(1)"), ("both", "  g . (1)", "  g.(1)")];
    let d = Dir::new("spacing");
    for (what, body, after) in cases {
        let text = in_a_function(body);
        let path = d.file("a.onsa", &text);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{what}: {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0020", "{what}");
        let fixes = fixes_of(&diags[0]);
        assert_eq!(fixes.len(), 1, "{what}: one candidate: {}", diags[0]);
        let edits = edits_of(fixes[0]);
        assert!(
            replaced_texts(&text, &edits).iter().all(|t| t.chars().all(|c| c == ' ')),
            "{what}: only spaces are replaced: {:?}",
            replaced_texts(&text, &edits)
        );
        assert_eq!(apply(&text, &edits), in_a_function(after), "{what}");
    }
}

// ---- R-42: the operand of `move` and `inout` ----------------------------------------------------

/// (what, the body, the line of the error counted in the file). Every body is in a function that
/// has the helpers `take(move x)`, `bump(inout x)` defined, so the only error is the syntax.
const MARK_ERRORS: &[(&str, &str, u64)] = &[
    ("a sum after move in an argument", "  take(move y + 1)", 2),
    ("a product after move in an argument", "  take(move y * 2)", 2),
    ("a comparison after move in an argument", "  take2(move y < 3)", 2),
    ("a sum after inout in an argument", "  bump(inout v + 1)", 2),
    ("a negated name after move", "  take(move -y)", 2),
    ("a negated name after inout", "  bump(inout -v)", 2),
    ("a conversion after move", "  take(move y as I64)", 2),
    ("a sum after move in a let", "  let z = move y + 1", 2),
    ("a sum after move in an assignment", "  z = move y + 1", 2),
    ("a marked operand in parentheses in a sum", "  let z = 1 + (move y)", 2),
    ("a marked operand in parentheses in a comparison", "  if (move y) == 1 {\n    1\n  } else {\n    2\n  }", 2),
    ("a marked argument in parentheses", "  take((move y))", 2),
    ("a marked initializer in parentheses", "  let z = (move y)", 2),
    ("a marked inout argument in parentheses", "  bump((inout v))", 2),
];

#[test]
fn the_operand_of_a_mark_is_a_postfix_expression() {
    // §5.2: `move y + 1` and `take(move y + 1)` are E0002, and so are `1 + (move y)` and
    // `if (move y) == 1 {`. The error is the one of the syntax stage: nothing from a later stage.
    let d = Dir::new("marks");
    for (what, body, line) in MARK_ERRORS {
        let text = in_a_function(body);
        let path = d.file("a.onsa", &text);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{what}: one diagnostic: {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0002", "{what}: {}", diags[0]);
        assert_eq!(start_of(&diags[0]).0, *line, "{what}: the line of the error: {}", diags[0]);
    }
}

#[test]
fn the_marks_on_a_postfix_expression_and_in_a_tuple_of_two_are_read() {
    // §5.2: a mark on a name and what follows it (fields, indexes, calls) stands in an argument and
    // in a consuming position; a tuple of two or more elements may hold marked elements. These are
    // read today and stay read: no diagnostic of the syntax stage.
    let bodies: [(&str, &str); 7] = [
        ("a name", "  take(move y)"),
        ("a field", "  take(move s.0)"),
        ("an inout element", "  bump(inout xs[0])"),
        ("an inout field", "  bump(inout p.x)"),
        ("a tuple of marked elements", "  let t = (move a, move b)"),
        ("an array of marked elements", "  let u = [move a, move b]"),
        ("a marked call", "  let z = move take(y)"),
    ];
    let d = Dir::new("marks_ok");
    for (what, body) in bodies {
        let path = d.file("a.onsa", &in_a_function(body));
        let diags = check(&path);
        let syntax: Vec<&Value> =
            diags.iter().filter(|x| ["E0001", "E0002", "E0003", "E0010", "E0020"].contains(&code_of(x))).collect();
        assert!(syntax.is_empty(), "{what}: {syntax:?}");
    }
}

// ---- R-43: the one-element tuple ----------------------------------------------------------------

/// (what, the file): a `,` after the only element of a tuple, in an expression, a type and a pattern.
const ONE_ELEMENT: &[(&str, &str)] = &[
    ("an expression", "pub fn f() -> U8 {\n  let t = (1,)\n  1\n}\n"),
    ("a type of a parameter", "pub fn f(t: (U8,)) -> U8 {\n  1\n}\n"),
    ("a type of the result", "pub fn f() -> (U8,) {\n  1\n}\n"),
    ("a type argument", "pub fn f(o: Option[(U8,)]) -> U8 {\n  1\n}\n"),
    ("a pattern of a let", "pub fn f(v: U8) -> U8 {\n  let (a,) = v\n  a\n}\n"),
    ("a pattern of an arm", "pub fn f(v: U8) -> U8 {\n  match v {\n    (0,) => 1,\n    _ => 2,\n  }\n}\n"),
    ("a name in a group", "pub fn f(x: U8) -> U8 {\n  let t = ((x),)\n  x\n}\n"),
    ("a tuple in a tuple", "pub fn f() -> U8 {\n  let t = ((1,), 2)\n  2\n}\n"),
];

#[test]
fn a_comma_after_the_only_element_is_e0002_and_fmt_does_not_rewrite_it() {
    // §2.4: `(e,)`, `(I32,)` and `(p,)` are E0002. R-43 was `fmt` writing `(1,)` as `(1)`, a
    // different program: the file is not rewritten.
    let d = Dir::new("one_element");
    for (what, text) in ONE_ELEMENT {
        let path = d.file("a.onsa", text);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{what}: one diagnostic: {diags:?}");
        assert_eq!(code_of(&diags[0]), "E0002", "{what}: {}", diags[0]);
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 2, "{what}: fmt stops: {out:?}");
        assert_eq!(read(&path), *text, "{what}: the file is not rewritten");
    }
}

#[test]
fn a_group_in_a_type_a_pattern_and_an_expression_is_the_thing_in_it() {
    // §2.4: `(e)` is grouping everywhere: `(I32)` is `I32`, `(a)` binds `a`, `(Some(v))` is
    // `Some(v)`. The file checks with no diagnostic, so the types are those of the groups.
    let text = "\
pub fn f(t: (I32), o: Option[(I32)]) -> I32 {
  let (a) = t
  let b: (I32) = (a)
  match (o) {
    (Some(v)) => v + b,
    (None) => b,
  }
}
";
    let d = Dir::new("group");
    let path = d.file("a.onsa", text);
    let diags = check(&path);
    assert!(diags.is_empty(), "{diags:?}");
}

// ---- S-100: `move` on the last expression of a block ---------------------------------------------

/// Bodies of functions (with the parameters `c: Bool`, `k: I32`, and `a`, `b` of `Buf[F32]` that
/// they own): (what, the function text). Each is read by the syntax stage (§5.2, S-100): the
/// position of the block decides which `move`s are written, and the checker of the modes stage
/// (W4-09) decides the rest, so only the syntax is asserted.
const MOVE_ON_THE_LAST_EXPRESSION: &[(&str, &str)] = &[
    (
        "the arms of an if in a let",
        "fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  let y = if c { move a } else { move b }\n  y\n}\n",
    ),
    (
        "the arms of a match in a let",
        "fn f(k: I32, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  let y = match k {\n    0 => move a,\n    _ => move b,\n  }\n  y\n}\n",
    ),
    (
        "the arms of an if in an argument",
        "fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> U32 {\n  take(if c { move a } else { move b })\n}\n",
    ),
    ("a block expression in a let", "fn f(move a: Buf[F32]) -> Buf[F32] {\n  let y = { move a }\n  y\n}\n"),
    (
        "nested arms",
        "fn f(c: Bool, d: Bool, move a: Buf[F32], move b: Buf[F32], move e: Buf[F32]) -> Buf[F32] {\n  let y = if c {\n    if d { move a } else { move b }\n  } else {\n    move e\n  }\n  y\n}\n",
    ),
    ("a returned value", "fn f(move a: Buf[F32]) -> Buf[F32] {\n  return move a\n}\n"),
    ("the end of a function", "fn f(move a: Buf[F32]) -> Buf[F32] {\n  move a\n}\n"),
    (
        "the arms of an if at the end of a function",
        "fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  if c { move a } else { move b }\n}\n",
    ),
    (
        "the arms of a match at the end of a function",
        "fn f(k: I32, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  match k {\n    0 => move a,\n    _ => move b,\n  }\n}\n",
    ),
    (
        "an if inside an arm at the end of a function",
        "fn f(k: I32, c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  match k {\n    0 => if c { move a } else { move b },\n    _ => move a,\n  }\n}\n",
    ),
    (
        "returned arms",
        "fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  if c {\n    return move a\n  } else {\n    return move b\n  }\n}\n",
    ),
    (
        "a returned if",
        "fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  return if c { move a } else { move b }\n}\n",
    ),
    (
        "an early return and the end",
        "fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  if c {\n    return move a\n  }\n  move b\n}\n",
    ),
    (
        "the end of an anonymous function",
        "fn f(move a: Buf[F32]) -> U32 {\n  let g = fn(move t: Buf[F32]) -> Buf[F32] { move t }\n  1\n}\n",
    ),
];

#[test]
fn a_move_on_the_last_expression_of_a_block_is_read_by_the_syntax_stage() {
    // §5.2: the blocks that are where a value is consumed and where the function returns take a
    // `move` on their last expression. `tests/fuzz/67f69e84.onsa` is the case that found it: the
    // candidate of E0711 (`move` before `a`) gave an E0002.
    let d = Dir::new("move_tail");
    for (what, text) in MOVE_ON_THE_LAST_EXPRESSION {
        let path = d.file("a.onsa", text);
        let diags = check(&path);
        let syntax: Vec<&Value> =
            diags.iter().filter(|x| ["E0001", "E0002", "E0003", "E0010", "E0020"].contains(&code_of(x))).collect();
        assert!(syntax.is_empty(), "{what}: {syntax:?}");
    }
}

#[test]
#[ignore = "W3-12 (S-56): `diff --ast` compares the trees before the rewrites of fmt, and fmt removes the `return` at the end today"]
fn fmt_keeps_a_move_in_a_consuming_position_and_does_not_fail_on_a_returned_one() {
    // §5.2: `let y = if c { move a } else { move b }` is the form E0711 asks for, so fmt keeps it.
    // The `move` of a returned value is extra information that fmt removes; that removal is W3-12's
    // (the text after fmt is not asserted here), but fmt must read the file (exit code 0) and the
    // program must be the same under the rewrite list of docs/onsa-tools.md §3.3.
    let consuming = "fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {\n  let y = if c { move a } else { move b }\n  y\n}\n";
    let returned = "fn f(move a: Buf[F32]) -> Buf[F32] {\n  return move a\n}\n";
    let d = Dir::new("move_tail_fmt");
    let path = d.file("a.onsa", consuming);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&path), consuming, "a move in a consuming position is kept");
    let original = d.file("original.onsa", returned);
    let path = d.file("b.onsa", returned);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let diff = onsa(&["diff", "--ast", &original, &path]);
    assert_eq!(code(&diff), 0, "{diff:?}");
}

// ---- R-196: the commas in the brackets of a type ---------------------------------------------------

#[test]
fn a_bracket_with_a_comma_in_a_type_is_a_type_argument_list() {
    // §4.5: in a type position `[...]` is the list of type arguments, with commas, and `::` is
    // never written there. These well-formed types give no diagnostic at all.
    let text = "\
pub type Pair2 = Pair[I32, F32]

pub type Nested = Pair[Pair[I32, F32], Pair[U8, I32]]

pub type Wide = Result[Pair[I32, F32], Str]

pub struct Holder {
  a: Pair[I32, F32],
  b: [Pair[U8, I32]; 2],
  c: Option[Pair[Option[I32], F32]],
}

pub fn f(x: Pair[Option[I32], F32], r: Ring[F32, 4]) -> Pair[I32, F32] {
  let y: Pair[I32, F32] = Pair { a: 1, b: 2.0 }
  y
}
";
    let d = Dir::new("type_commas");
    let path = d.file("a.onsa", text);
    let diags = check(&path);
    // `Pair` and `Ring` are not declared: the names stage reports them, but nothing of the
    // syntax stage and no suggestion to write `::`.
    for x in &diags {
        assert!(!["E0001", "E0002", "E0003", "E0010", "E0020"].contains(&code_of(x)), "{x}");
        for fix in fixes_of(x) {
            assert!(edits_of(fix).iter().all(|e| e.replace != "::"), "a `::` is suggested: {x}");
        }
    }
}

/// Type positions with a bracket that holds a comma and is not well formed. The error is not an
/// E0020 and no candidate inserts `::`: a type position has no `::[` (§4.5).
const BAD_TYPE_BRACKETS: &[(&str, &str)] = &[
    ("the input of the fuzzer", "type R=e[t[[],l]"),
    ("the same, closed", "type R = e[t[[], l]]"),
    ("an empty bracket in a type", "type R = Pair[[], I32]"),
    ("an empty bracket in a nested type", "type R = Pair[Pair[[], I32], F32]"),
    ("a parameter", "pub fn f(x: Pair[[], I32]) {\n}\n"),
    ("a field", "pub struct S {\n  a: Pair[[], I32],\n}\n"),
    ("a let", "pub fn f() {\n  let a: Pair[[], I32] = 1\n}\n"),
    ("a lower-case name with a bracket in it", "type R = e[t[I32, F32]"),
    ("a bracket that is not closed", "type R = Pair[I32, F32"),
];

#[test]
fn no_candidate_inserts_the_colons_in_a_type_position() {
    // R-196 (found by the fuzzer: `tests/fuzz/82d90c5e.onsa`): the E0020 of `f[a, b](x)` is for an
    // expression; in a type position its candidate `::` leaves the same error after it is applied.
    let d = Dir::new("type_brackets");
    for (what, text) in BAD_TYPE_BRACKETS {
        let text = if text.ends_with('\n') { text.to_string() } else { format!("{text}\n") };
        let path = d.file("a.onsa", &text);
        let diags = check(&path);
        assert!(!diags.is_empty(), "{what}: an error is reported");
        for x in &diags {
            for fix in fixes_of(x) {
                assert!(
                    edits_of(fix).iter().all(|e| e.replace != "::"),
                    "{what}: a candidate inserts `::` in a type position: {x}"
                );
            }
        }
    }
}
