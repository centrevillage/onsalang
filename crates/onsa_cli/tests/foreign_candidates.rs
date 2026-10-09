//! The E0020 forms whose candidates the case files in `tests/spec/fixes/` cannot pin (W3-15/t,
//! W3-15/t2).
//!
//! A `.fixK` file compares the text after the candidates, and `[[test.fix]]` pins a property
//! (`clean`, `same_code`, `leaves`). These tests say what those cannot: how many edits and where
//! (one edit for each foreign token), that a form with no candidate has none and has a note, the
//! words of a doc block comment (`///` or `//`, not stripped), and that a program still has its
//! value after a candidate. The data file `docs/foreign-forms.toml` lists every form.
//!
//! Every test uses only the binary (`onsa check --json`, `onsa test`, `onsa fmt`).
//!
//! The tests marked `#[ignore]` do not pass with the code of 2026-10-09. Each names the work that
//! removes the mark (an ignored test is not silenced by `tests/pending.toml`: it is skipped).
//! Run them with `cargo test -p onsa_cli --test foreign_candidates -- --ignored`.

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_foreign_{}_{tag}", std::process::id()));
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

/// The exit code and the diagnostics of `onsa check --json <path>`.
fn check(path: &str) -> (i32, Vec<Value>) {
    let out = Command::new(ONSA).args(["check", "--json", path]).output().expect("run onsa");
    let code = out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"));
    assert!(
        code == 0 || code == 1,
        "onsa check {path}: exit code {code} (stderr: {})",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8(out.stdout).expect("utf-8 output");
    let diags = match serde_json::from_str::<Value>(&text) {
        Ok(v) => match v.get("diagnostics") {
            Some(Value::Array(a)) => a.clone(),
            _ => panic!("the document has no `diagnostics` array: {v}"),
        },
        Err(e) => panic!("onsa check --json printed no JSON ({e}): {text}"),
    };
    assert_eq!(code == 0, diags.is_empty(), "the exit code {code} and the diagnostics disagree: {diags:?}");
    (code, diags)
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
    match d.get("fixes") {
        None => vec![],
        Some(f) => f.as_array().expect("`fixes` is an array").iter().collect(),
    }
}

fn notes_of(d: &Value) -> Vec<&Value> {
    match d.get("notes") {
        None => vec![],
        Some(n) => n.as_array().expect("`notes` is an array").iter().collect(),
    }
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

/// The byte offset of a (line, column in characters) position of the ASCII-or-not `text`.
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

/// The program with candidate `k` (0-based) of the first diagnostic applied.
fn with_first_fix(text: &str, diags: &[Value], k: usize) -> String {
    let fixes = fixes_of(&diags[0]);
    let fix = fixes.get(k).unwrap_or_else(|| panic!("no candidate {k} for {}", diags[0]));
    apply(text, &edits_of(fix))
}

fn expect_one(diags: &[Value], code: &str, what: &str) {
    assert_eq!(diags.len(), 1, "{what}: one diagnostic expected, got {diags:?}");
    assert_eq!(code_of(&diags[0]), code, "{what}: {}", diags[0]);
}

// ---- fmt does not rewrite a file with a foreign form of the syntax stage (§18.2) -----------------

#[test]
fn fmt_leaves_a_file_with_a_foreign_form_as_it_is_and_exits_with_2() {
    // §18.2: `onsa fmt` and `fmt --check` do not rewrite a file with a diagnostic of the syntax
    // stage, and exit with 2; an E0020 found there (a `;`, `<T>`, `&mut`, `::`, `i32`, a block
    // comment, `let mut`, `loop`) is one. `g` is badly spaced, so a formatter that went on would
    // change the file.
    let forms = [
        ("semicolon", "pub fn f(x: I32) -> I32 {\n  let y = x;\n  y\n}\n"),
        ("angle", "pub fn f<T>(x: T) -> T {\n  x\n}\n"),
        ("reference", "pub fn f(v: &mut I32) {\n}\n"),
        ("path", "pub fn f() -> I32 {\n  I32::MAX\n}\n"),
        ("lowercase", "pub fn f(x: i32) -> I32 {\n  x\n}\n"),
        ("block_comment", "pub fn f() -> I32 {\n  let a = 1 /* c */ + 2\n  a\n}\n"),
        ("let_mut", "pub fn f() -> I32 {\n  let mut n = 0\n  n\n}\n"),
        ("loop", "pub fn f() -> I32 {\n  loop {\n    break\n  }\n  1\n}\n"),
    ];
    let d = Dir::new("fmt");
    for (name, f) in forms {
        let src = format!("{f}\npub fn g()->I32{{\n  2\n}}\n");
        let path = d.file(&format!("{name}.onsa"), &src);
        let (_, diags) = check(&path);
        assert_eq!(code_of(&diags[0]), "E0020", "{name}: {diags:?}");
        for args in [vec!["fmt", path.as_str()], vec!["fmt", "--check", path.as_str()]] {
            let out = Command::new(ONSA).args(&args).output().expect("run onsa");
            assert_eq!(out.status.code(), Some(2), "{name}: onsa {args:?}: {out:?}");
            assert_eq!(std::fs::read_to_string(&path).unwrap(), src, "{name}: onsa {args:?} wrote the file");
        }
    }
}

// ---- Redundant forms that are harmless (S-114, P2): accepted, same value ----------------------

const HARMLESS: &str = "\
pub fn parentheses(x: I32) -> I32 {
  let y = ((x + 1))
  (y)
}

pub fn parentheses_around_a_call(x: I32) -> I32 {
  ((parentheses(x)))
}

pub fn return_in_the_last_position(x: I32) -> I32 {
  return x + 1
}

pub fn return_in_every_last_branch(x: I32) -> I32 {
  if x > 0 {
    return 1
  } else {
    return 2
  }
}

pub fn return_in_the_last_arms(o: Option[I32]) -> I32 {
  match o {
    Some(v) => { return v },
    None => { return 20 },
  }
}

pub fn bare_return_in_the_last_position(inout total: I32) {
  total = total + 1
  return
}

pub fn explicit_unit_result(inout total: I32) -> () {
  total = total + 2
}

pub fn empty_effect_row(x: I32) -> I32 uses {} {
  x + 3
}

pub fn parentheses_around_the_condition(x: I32) -> I32 {
  if (x > 0) {
    1
  } else {
    2
  }
}

pub fn unit_function_type(f: fn(I32) -> ()) {
}

test \"redundant parentheses do not change the value\" {
  assert parentheses(1) == 2
  assert parentheses_around_a_call(1) == 2
}

test \"a return in the last position returns the value\" {
  assert return_in_the_last_position(4) == 5
  assert return_in_every_last_branch(3) == 1
  assert return_in_every_last_branch(-3) == 2
  assert return_in_the_last_arms(Some(10)) == 10
  assert return_in_the_last_arms(None) == 20
}

test \"a unit function with extra forms runs its body\" {
  var total = 0
  bare_return_in_the_last_position(inout total)
  explicit_unit_result(inout total)
  assert total == 3
}

test \"an empty effect row is a pure function\" {
  assert empty_effect_row(4) == 7
  assert parentheses_around_the_condition(1) == 1
  assert parentheses_around_the_condition(-1) == 2
}
";

#[test]
fn the_harmless_redundant_forms_are_accepted_and_keep_their_value() {
    // P2 (§0.2) and §6.1: redundant parentheses, a `return` in the last position, `-> ()`, an empty
    // `uses {}` are accepted with no diagnostic (`onsa fmt` takes them away); the values are the
    // ones of the forms without the extras. These are not E0020, which is for the harmful extras.
    let d = Dir::new("harmless");
    let path = d.file("harmless.onsa", HARMLESS);
    let (code, diags) = check(&path);
    assert!(diags.is_empty(), "a harmless form is rejected: {diags:?}");
    assert_eq!(code, 0);
    let (code, out) = run_tests(&path);
    assert_eq!(code, 0, "the tests fail:\n{out}");
    assert!(out.contains("4 passed, 0 failed"), "four tests expected to run and pass:\n{out}");
}

const PARENTHESIZED: &str = "\
pub fn parenthesized_type(x: (I32)) -> (I32) {
  x
}

pub fn parenthesized_type_argument(x: Option[(I32)]) -> I32 {
  match x {
    Some(v) => v,
    None => 0,
  }
}

pub fn parenthesized_patterns(o: Option[I32]) -> I32 {
  match o {
    (Some(v)) => v,
    (None) => 0,
  }
}

pub fn parenthesized_binding(o: Option[I32]) -> I32 {
  match o {
    Some((v)) => v,
    None => 0,
  }
}

test \"a parenthesized type is the type\" {
  assert parenthesized_type(5) == 5
  assert parenthesized_type_argument(Some(6)) == 6
}

test \"a parenthesized pattern is the pattern\" {
  assert parenthesized_patterns(Some(7)) == 7
  assert parenthesized_patterns(None) == 0
  assert parenthesized_binding(Some(8)) == 8
}
";

#[test]
fn a_parenthesized_type_or_pattern_is_grouping() {
    // §2.4: `(e)` is grouping in an expression, a pattern and a type; only `(e,)` is E0002.
    let d = Dir::new("paren");
    let path = d.file("paren.onsa", PARENTHESIZED);
    let (_, diags) = check(&path);
    assert!(diags.is_empty(), "a parenthesized type or pattern is rejected: {diags:?}");
    let (code, out) = run_tests(&path);
    assert_eq!(code, 0, "the tests fail:\n{out}");
}

// ---- `<` `>` (S-236, R-87 (1)): the candidate edits the brackets and nothing else ----------------

#[test]
fn the_candidate_for_angle_brackets_edits_the_brackets_only() {
    // §18.1: one edit for each bracket token (`<`, `>`, and the token `>>`), each replacing the
    // bracket with the same number of square brackets; the type parameters, the bounds, the type
    // arguments and the spacing between them are not part of any edit.
    let cases: [(&str, &str, &str); 5] = [
        ("one", "pub fn id<T>(x: T) -> T {\n  x\n}\n", "pub fn id[T](x: T) -> T {\n  x\n}\n"),
        (
            "bounds",
            "pub fn pick<T: Ord + Eq,   U>(x: T, y: U) -> T {\n  x\n}\n",
            "pub fn pick[T: Ord + Eq,   U](x: T, y: U) -> T {\n  x\n}\n",
        ),
        ("argument", "pub fn f(x: Option<I32>) -> I32 {\n  1\n}\n", "pub fn f(x: Option[I32]) -> I32 {\n  1\n}\n"),
        (
            "nested",
            "pub fn f(x: Option<Option<I32>>) -> I32 {\n  1\n}\n",
            "pub fn f(x: Option[Option[I32]]) -> I32 {\n  1\n}\n",
        ),
        (
            "impl",
            "pub struct W[T] {\n  v: T,\n}\n\nimpl<T: Ord> W[T] {\n}\n",
            "pub struct W[T] {\n  v: T,\n}\n\nimpl[T: Ord] W[T] {\n}\n",
        ),
    ];
    let d = Dir::new("angle");
    for (name, src, expected) in cases {
        let path = d.file(&format!("{name}.onsa"), src);
        let (_, diags) = check(&path);
        expect_one(&diags, "E0020", name);
        let fixes = fixes_of(&diags[0]);
        assert_eq!(fixes.len(), 1, "{name}: one candidate expected: {}", diags[0]);
        let edits = edits_of(fixes[0]);
        let replaced = replaced_texts(src, &edits);
        for (e, old) in edits.iter().zip(&replaced) {
            assert!(
                !old.is_empty() && old.chars().all(|c| c == '<' || c == '>'),
                "{name}: an edit replaces `{old}`, which is more than a bracket"
            );
            assert_eq!(e.replace.chars().count(), old.chars().count(), "{name}: `{old}` -> `{}`", e.replace);
            assert!(e.replace.chars().all(|c| c == '[' || c == ']'), "{name}: `{old}` -> `{}`", e.replace);
        }
        let brackets = src.matches('<').count() + src.matches('>').count() - src.matches("->").count();
        let replaced_brackets: usize = replaced.iter().map(|r| r.chars().count()).sum();
        assert_eq!(replaced_brackets, brackets, "{name}: every bracket is replaced: {replaced:?}");
        assert_eq!(apply(src, &edits), expected, "{name}");
    }
}

// ---- Forms with no candidate: E0002 and a note (§18.1) -------------------------------------------

#[test]
fn a_foreign_form_with_no_candidate_is_e0002_with_a_note_and_no_candidate() {
    // §18.1: E0020 only when a candidate can be made; otherwise E0002, and the Onsa form may be
    // shown in a note. The rows are docs/foreign-forms.toml rows with code = "E0002" (S-250,
    // S-247, S-249, S-297); the same sources are in tests/spec/negative/foreign_no_candidate.onsa
    // (which checks only the code and the line).
    let sources: [(&str, &str); 19] = [
        ("compound_on_an_index", "pub fn f(inout xs: [I32; 4], i: U32) {\n  xs[i] += 1\n}\n"),
        ("compound_in_an_expression", "pub fn f(inout x: I32) -> I32 {\n  let y = x += 1\n  y\n}\n"),
        ("post_increment_in_an_expression", "pub fn f(inout x: I32) -> I32 {\n  let y = x++\n  y\n}\n"),
        ("pre_increment_in_an_expression", "pub fn f(inout x: I32) -> I32 {\n  let y = ++x\n  y\n}\n"),
        ("increment_of_an_index", "pub fn f(inout xs: [I32; 4]) {\n  xs[0]++\n}\n"),
        ("triple_minus", "pub fn f(x: I32) -> I32 {\n  let y = ---x\n  y\n}\n"),
        ("ref_mut_annotation", "pub fn f() -> I32 {\n  var a = 1\n  var r: &mut I32 = a\n  r\n}\n"),
        ("ref_mut_expression", "pub fn f() -> I32 {\n  var a = 1\n  var r = &mut a\n  r\n}\n"),
        ("ref_mut_result", "pub fn f(v: I32) -> &mut I32 {\n  v\n}\n"),
        ("ref_mut_field", "pub struct S {\n  r: &mut I32,\n}\n"),
        (
            "at_binding_on_a_pattern",
            "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    s @ Some(_) => 1,\n    None => 0,\n  }\n}\n",
        ),
        (
            "range_pattern_in_a_choice",
            "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    Some(1..<3) | None => 1,\n    _ => 0,\n  }\n}\n",
        ),
        ("unclosed_block_comment", "pub fn f() -> I32 {\n  1\n}\n\n/* never closed\npub fn g() -> I32 {\n  2\n}\n"),
        (
            "float_branches_of_other_shapes",
            "pub fn f(t: (F32, I32)) -> I32 {\n  match t {\n    (0.5, 1) | (1.5, 2) => 1,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "float_branch_with_a_binding",
            "pub fn f(o: Option[F32]) -> I32 {\n  match o {\n    Some(0.5) | Some(x) => 1,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "float_comment_in_a_deleted_branch",
            "pub fn f(sample: F32) -> I32 {\n  match sample {\n    0.5 | // the second value\n    1.5 => 1,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "range_branches_of_other_shapes",
            "pub fn f(t: (I32, I32)) -> I32 {\n  match t {\n    (1..<3, 1) | (5..<7, 2) => 1,\n    _ => 0,\n  }\n}\n",
        ),
        ("nested_block_comment", "/* a /* b */ c */\npub fn f() -> I32 {\n  1\n}\n"),
        ("multiline_block_comment_then_code", "pub fn f() -> I32 {\n  let a = 1 /* x\n  */ + 2\n  a\n}\n"),
    ];
    let d = Dir::new("nocandidate");
    for (name, src) in sources {
        let path = d.file(&format!("{name}.onsa"), src);
        let (code, diags) = check(&path);
        assert_eq!(code, 1, "{name}");
        expect_one(&diags, "E0002", name);
        assert!(fixes_of(&diags[0]).is_empty(), "{name}: a candidate for a form with none: {}", diags[0]);
        let notes = notes_of(&diags[0]);
        assert!(!notes.is_empty(), "{name}: no note that shows the Onsa form: {}", diags[0]);
        assert!(
            notes.iter().all(|n| n["message"].as_str().is_some_and(|m| !m.is_empty())),
            "{name}: an empty note: {}",
            diags[0]
        );
    }
}

// ---- One syntactic form is one error, and the edits are per token (S-248, S-251) ----------------

#[test]
fn one_syntactic_form_has_one_candidate_that_edits_every_token_of_the_form() {
    // §18.1: all the `::` of one path, the brackets of one list of type arguments and consecutive
    // `;` are one error with one candidate; the edits replace the foreign tokens one by one.
    let cases: [(&str, &str, &str, &str, usize); 3] = [
        ("repeated_semicolons", "pub fn f() -> I32 {\n  let a = 1;;\n  a\n}\n", ";", "", 2),
        ("three_semicolons", "pub fn f() -> I32 {\n  let a = 1;;;\n  a\n}\n", ";", "", 3),
        ("path", "pub fn f() -> F32 {\n  std::math::sqrt(2.0)\n}\n", "::", ".", 2),
    ];
    let d = Dir::new("tokens");
    for (name, src, old, new, edits_expected) in cases {
        let path = d.file(&format!("{name}.onsa"), src);
        let (_, diags) = check(&path);
        expect_one(&diags, "E0020", name);
        let fixes = fixes_of(&diags[0]);
        assert_eq!(fixes.len(), 1, "{name}: one candidate: {}", diags[0]);
        let edits = edits_of(fixes[0]);
        assert_eq!(edits.len(), edits_expected, "{name}: one edit for each foreign token: {}", diags[0]);
        if !old.is_empty() {
            for (e, text) in edits.iter().zip(replaced_texts(src, &edits)) {
                assert_eq!(text, old, "{name}: an edit replaces `{text}`");
                assert_eq!(e.replace, new, "{name}");
            }
        }
        let fixed = apply(src, &edits);
        let path = d.file(&format!("{name}_fixed.onsa"), &fixed);
        let (_, after) = check(&path);
        assert!(after.is_empty(), "{name}: the fixed program has diagnostics: {after:?}\n{fixed}");
    }
}

#[test]
fn a_stack_of_three_prefix_operators_is_one_error_with_one_candidate() {
    // S-297: `- - -x` (spaces) is one syntactic form, E0012, and the candidate parenthesizes every
    // inner operator: `-(-(-x))`. (`---x` with no space is an increment whose operand is not a
    // name, E0002 with no candidate; it is in the first test above.)
    let src = "pub fn f(x: I32) -> I32 {\n  - - -x\n}\n";
    let d = Dir::new("stack");
    let path = d.file("stack.onsa", src);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0012", "stack");
    let fixes = fixes_of(&diags[0]);
    assert_eq!(fixes.len(), 1, "{}", diags[0]);
    let fixed = apply(src, &edits_of(fixes[0]));
    let squeezed: String = fixed.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(squeezed.contains("-(-(-x))"), "the candidate is not `-(-(-x))`:\n{fixed}");
    let path = d.file("stack_fixed.onsa", &fixed);
    let (_, after) = check(&path);
    assert!(after.is_empty(), "the fixed program has diagnostics: {after:?}\n{fixed}");
}

// ---- Block comments: the words stay as a `//`, `///` or `//!` comment (§2.1, S-247) ------------

/// The lines of `text` whose first non-blank characters are `prefix` (and not a longer run of `/`).
fn comment_lines<'a>(text: &'a str, prefix: &str) -> Vec<&'a str> {
    text.lines()
        .map(str::trim_start)
        .filter(|l| l.starts_with(prefix) && !l[prefix.len()..].starts_with(['/', '!']))
        .collect()
}

#[test]
fn a_doc_block_comment_becomes_a_doc_line_comment_only_before_a_declaration() {
    // S-247: `/** */` is `///` when a declaration that takes a doc comment follows, `//` when none
    // does; the ` * ` that begins the continuation lines is not stripped. The words stay.
    let d = Dir::new("doc");
    let before = "/** the gain */\npub fn f() -> I32 {\n  1\n}\n";
    let path = d.file("before.onsa", before);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0020", "before a declaration");
    let fixed = with_first_fix(before, &diags, 0);
    assert!(!fixed.contains("/*"), "{fixed}");
    let doc = comment_lines(&fixed, "///");
    assert!(doc.len() == 1 && doc[0].contains("the gain"), "a `///` line with the words expected:\n{fixed}");
    let (_, after) = check(&d.file("before_fixed.onsa", &fixed));
    assert!(after.is_empty(), "{after:?}\n{fixed}");

    let inside = "pub fn f() -> I32 {\n  /** inside a body */\n  1\n}\n";
    let path = d.file("inside.onsa", inside);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0020", "inside a body");
    let fixed = with_first_fix(inside, &diags, 0);
    assert!(comment_lines(&fixed, "///").is_empty(), "no declaration follows, so not `///`:\n{fixed}");
    let plain = comment_lines(&fixed, "//");
    assert!(plain.len() == 1 && plain[0].contains("inside a body"), "a `//` line with the words:\n{fixed}");
    let (_, after) = check(&d.file("inside_fixed.onsa", &fixed));
    assert!(after.is_empty(), "{after:?}\n{fixed}");

    // S-302: in the middle of a line it is `//`; `///` only at the start of a line, before a
    // declaration that takes it (so the `///` moved above the line does not attach to another one).
    let middle = "pub fn f(/** in */ x: I32) -> I32 {\n  x\n}\n";
    let path = d.file("middle.onsa", middle);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0020", "in the middle of a line");
    let fixed = with_first_fix(middle, &diags, 0);
    assert!(comment_lines(&fixed, "///").is_empty(), "in the middle of a line, not `///`:\n{fixed}");
    let plain = comment_lines(&fixed, "//");
    assert!(plain.len() == 1 && plain[0].contains("in"), "a `//` line with the words:\n{fixed}");
    let (_, after) = check(&d.file("middle_fixed.onsa", &fixed));
    assert!(after.is_empty(), "{after:?}\n{fixed}");

    let start = "/** gain */ pub fn f() -> I32 {\n  1\n}\n";
    let path = d.file("start.onsa", start);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0020", "at the start of a line, before a declaration");
    let fixed = with_first_fix(start, &diags, 0);
    let doc = comment_lines(&fixed, "///");
    assert!(doc.len() == 1 && doc[0].contains("gain"), "a `///` line with the words:\n{fixed}");
    let (_, after) = check(&d.file("start_fixed.onsa", &fixed));
    assert!(after.is_empty(), "{after:?}\n{fixed}");

    let several = "/** the gain\n * of the voice */\npub fn f() -> I32 {\n  1\n}\n";
    let path = d.file("several.onsa", several);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0020", "over several lines");
    let fixed = with_first_fix(several, &diags, 0);
    assert!(fixed.contains("the gain") && fixed.contains("* of the voice"), "the ` * ` is kept:\n{fixed}");
    assert!(!fixed.contains("/*"), "{fixed}");
    let (_, after) = check(&d.file("several_fixed.onsa", &fixed));
    assert!(after.is_empty(), "{after:?}\n{fixed}");
}

#[test]
fn an_inner_doc_block_comment_at_the_start_of_the_file_has_two_candidates() {
    // S-247: `/*! */` as the first thing of the file has the candidates `//!` and `///`, in this
    // order (Rust and Doxygen read it differently). Each keeps the words and the code.
    let src = "/*! the module */\npub fn f() -> I32 {\n  1\n}\n";
    let d = Dir::new("inner");
    let path = d.file("inner.onsa", src);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0020", "inner doc");
    let fixes = fixes_of(&diags[0]);
    assert_eq!(fixes.len(), 2, "two candidates: {}", diags[0]);
    let first = apply(src, &edits_of(fixes[0]));
    let second = apply(src, &edits_of(fixes[1]));
    assert_eq!(comment_lines(&first, "//!").len(), 1, "the first candidate is `//!`:\n{first}");
    assert_eq!(comment_lines(&second, "///").len(), 1, "the second candidate is `///`:\n{second}");
    for (i, fixed) in [first, second].iter().enumerate() {
        assert!(fixed.contains("the module") && !fixed.contains("/*"), "candidate {i}:\n{fixed}");
        let (_, after) = check(&d.file(&format!("inner_fixed{i}.onsa"), fixed));
        assert!(after.is_empty(), "candidate {i}: {after:?}\n{fixed}");
    }
}

#[test]
fn a_block_comment_candidate_leaves_the_code_and_the_lines_as_they_were() {
    // S-247: whatever the place of the words, the tokens outside the comment and the line breaks
    // between them do not change, so the program checks after the candidate. (The case files check
    // this with `same_code`; this test also runs the program, so a candidate that comments out
    // code and still checks would change the value.)
    let src = "pub fn f() -> I32 {\n  let a = 1 /* one */ + 2\n  a\n}\n\ntest \"the sum\" {\n  assert f() == 3\n}\n";
    let d = Dir::new("blockvalue");
    let path = d.file("blockvalue.onsa", src);
    let (_, diags) = check(&path);
    expect_one(&diags, "E0020", "block comment between operands");
    let fixed = with_first_fix(src, &diags, 0);
    let path = d.file("blockvalue_fixed.onsa", &fixed);
    let (_, after) = check(&path);
    assert!(after.is_empty(), "the fixed program has diagnostics: {after:?}\n{fixed}");
    let (code, out) = run_tests(&path);
    assert_eq!(code, 0, "the value changed after the candidate:\n{fixed}\n{out}");
}

// ---- A float literal in a pattern (S-109, S-252, S-253): the candidate is a guard that checks ---

#[test]
fn a_float_pattern_is_e0020_and_its_candidate_is_a_guard_that_checks() {
    // §7: the candidate is the guard form `x if x == 1.0`. The spec does not fix the name of the
    // guard's variable (S-253); whatever it is, it is a name that is not visible (a binding that
    // shadows is E0304, §5.1), so the first case names the scrutinee `x` like the example of §7.
    // The program after the candidate has no diagnostic. (A `[[test.fix]]` with `clean` would say
    // the same in the case files, but it is an error in the case while the diagnostic is not
    // reported, and the pending list cannot silence that.)
    let cases = [
        ("whole_arm_x", "pub fn f(x: F32) -> I32 {\n  match x {\n    1.0 => 1,\n    _ => 0,\n  }\n}\n"),
        ("whole_arm_v", "pub fn f(v: F32) -> I32 {\n  match v {\n    1.0 => 1,\n    _ => 0,\n  }\n}\n"),
        ("negative", "pub fn f(sample: F32) -> I32 {\n  match sample {\n    -1.0 => 1,\n    _ => 0,\n  }\n}\n"),
        ("some", "pub fn f(o: Option[F32]) -> I32 {\n  match o {\n    Some(2.5) => 1,\n    _ => 0,\n  }\n}\n"),
        ("tuple", "pub fn f(t: (F32, I32)) -> I32 {\n  match t {\n    (0.0, x) => x,\n    _ => 0,\n  }\n}\n"),
        ("exponent", "pub fn f(x: F64) -> I32 {\n  match x {\n    1e3 => 1,\n    _ => 0,\n  }\n}\n"),
        ("choice", "pub fn f(x: F32) -> I32 {\n  match x {\n    0.5 | 1.5 => 1,\n    _ => 0,\n  }\n}\n"),
        (
            "choice_of_options",
            "pub fn f(o: Option[F32]) -> I32 {\n  match o {\n    Some(0.5) | Some(1.5) => 1,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "choice_with_a_shared_binding",
            "pub fn f(t: (F32, I32)) -> I32 {\n  match t {\n    (0.5, n) | (1.5, n) => n,\n    _ => 0,\n  }\n}\n",
        ),
        (
            "choice_inside_some",
            "pub fn f(o: Option[F32]) -> I32 {\n  match o {\n    Some(0.5 | 1.5) => 1,\n    _ => 0,\n  }\n}\n",
        ),
        ("two_floats", "pub fn f(t: (F32, F32)) -> I32 {\n  match t {\n    (0.0, 1.0) => 1,\n    _ => 0,\n  }\n}\n"),
        (
            "guarded_choice",
            "pub fn f(x: F32, flag: Bool) -> I32 {\n  match x {\n    0.5 | 1.5 if flag => 1,\n    _ => 0,\n  }\n}\n",
        ),
    ];
    let d = Dir::new("floatpat");
    for (name, src) in cases {
        let path = d.file(&format!("{name}.onsa"), src);
        let (_, diags) = check(&path);
        expect_one(&diags, "E0020", name);
        assert_eq!(fixes_of(&diags[0]).len(), 1, "{name}: one candidate: {}", diags[0]);
        assert!(!notes_of(&diags[0]).is_empty(), "{name}: no note with the rule: {}", diags[0]);
        let fixed = with_first_fix(src, &diags, 0);
        assert!(fixed.contains(" if "), "{name}: the candidate is not a guard:\n{fixed}");
        // S-317: one candidate for all the floats of the pattern; the conditions are joined with `||`
        // between the branches of a choice and `&&` between the places of a pattern, and a guard that
        // the arm had stays (`&& flag`).
        if name.starts_with("choice") {
            assert!(fixed.contains("||"), "{name}: the branches are joined with `||`:\n{fixed}");
            assert!(!fixed.contains(" | "), "{name}: one branch is left:\n{fixed}");
        }
        if name == "two_floats" {
            assert!(fixed.contains("&&"), "{name}: the conditions are joined with `&&`:\n{fixed}");
        }
        if name == "guarded_choice" {
            assert!(fixed.contains("flag"), "{name}: the guard of the arm is kept:\n{fixed}");
        }
        let path = d.file(&format!("{name}_fixed.onsa"), &fixed);
        let (_, after) = check(&path);
        assert!(after.is_empty(), "{name}: the fixed program has diagnostics: {after:?}\n{fixed}");
    }
}

/// The program without comments (`//` and `/* */`), as lines of tokens: what a candidate for a block
/// comment must keep (`same_code`): the tokens outside the comments and the line breaks between them.
fn code_lines(text: &str) -> Vec<String> {
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
            i += 2;
            while i < chars.len() && !(chars[i] == '*' && chars.get(i + 1) == Some(&'/')) {
                if chars[i] == '\n' {
                    out.push('\n');
                }
                i += 1;
            }
            i += 2;
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out.lines().map(|l| l.split_whitespace().collect::<Vec<_>>().join(" ")).filter(|l| !l.is_empty()).collect()
}

#[test]
fn several_block_comments_on_one_line_are_fixed_one_at_a_time_and_keep_their_words_in_order() {
    // S-302: one-line block comments are fixed one at a time, however many are on a line. After each
    // candidate the tokens outside the comments and the line breaks are the same (`same_code`); in
    // the end nothing is reported, and the words are still there, in the order they were written.
    let src = "pub fn f() -> I32 {\n  let a = 1 /* first */ + 2 /* second */\n  a\n}\n";
    let d = Dir::new("several");
    let mut text = src.to_string();
    let mut steps = 0;
    loop {
        let path = d.file(&format!("step{steps}.onsa"), &text);
        let (_, diags) = check(&path);
        if diags.is_empty() {
            break;
        }
        assert!(steps < 2, "more candidates than comments:\n{text}\n{diags:?}");
        assert_eq!(code_of(&diags[0]), "E0020", "step {steps}: {}", diags[0]);
        let fixed = with_first_fix(&text, &diags, 0);
        assert_eq!(code_lines(&fixed), code_lines(&text), "step {steps}: the code or the lines changed:\n{fixed}");
        text = fixed;
        steps += 1;
    }
    assert_eq!(steps, 2, "one candidate for each of the two comments:\n{text}");
    assert!(!text.contains("/*"), "{text}");
    let (a, b) = (text.find("first"), text.find("second"));
    assert!(a.is_some() && b.is_some() && a < b, "the words stay, `first` before `second`:\n{text}");
}
