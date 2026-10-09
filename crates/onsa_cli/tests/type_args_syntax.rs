//! Type arguments in an expression, `name::[types]` (spec §4.5, S-239, S-256, S-277, S-248):
//! the syntax stage, `onsa fmt` and `onsa diff --ast` (W3-19/t).
//!
//! The case files in `tests/spec/` pin the diagnostics (`negative/syntax_type_args.onsa` for E0002,
//! `fixes/e0020_type_args_*.onsa` for E0020 and the text after each candidate) and the forms that are
//! read (`types/type_args_syntax.onsa`, `mode = "parse"`); `docs/foreign-forms.toml` lists the forms of
//! other languages. These tests say what those cannot: the normal form of the list that `onsa fmt`
//! writes (`docs/onsa-tools.md` §3.2), that the list is kept in the tree and not dropped (R-81:
//! `diff --ast` sees it), that fmt and `diff --ast` stop at the errors of the syntax stage, how the
//! edits of a candidate are cut (the tokens that change and no others, S-251) and that every E0020
//! of these forms has a note that shows `name::[…]` (§18.1).
//!
//! Every test uses only the binary (`onsa fmt`, `onsa diff --ast`, `onsa check --json`). Expected
//! texts are written from the spec; none is taken from the output of the compiler.
//!
//! The tests were written before the syntax of W3-19 and ran ignored until W3-19/i (a test cannot be
//! silenced by `tests/pending.toml`). Those that passed before it say so in their names (an error of
//! the syntax stage is an error before the list is read too).

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_type_args_{}_{tag}", std::process::id()));
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

// ---- fmt: the normal form of the list (docs/onsa-tools.md §3.2) -------------------------------

/// (what the case says, the body as written, the body `onsa fmt` writes). §3.2: no space around
/// `::[`, the elements of the list as in a type position (`, ` between them, no space inside the
/// brackets), a space on both sides of a binary operator, `{ }` of a struct literal with a space
/// inside; a type annotation and a list are not rewritten into each other.
const NORMAL_FORMS: &[(&str, &str, &str)] = &[
    ("spaces inside the list", "  id::[ U8 ](250)", "  id::[U8](250)"),
    ("no space after the comma", "  Rg::[F32,4].CAP", "  Rg::[F32, 4].CAP"),
    ("space before the comma", "  pair::[ U8 ,F32 ](1, 2.0)", "  pair::[U8, F32](1, 2.0)"),
    ("a list inside the list", "  id::[Option[ I32 ]](None)", "  id::[Option[I32]](None)"),
    ("a tuple type in the list", "  id::[ (I32 ,F32) ]((1, 2.0))", "  id::[(I32, F32)]((1, 2.0))"),
    ("a method", "  v.m::[ I32 ](x)", "  v.m::[I32](x)"),
    ("a method that changes its receiver", "  buf.push::[ F32 ]!( x )", "  buf.push::[F32]!(x)"),
    ("a variant of the prelude", "  None::[ I32 ]", "  None::[I32]"),
    ("a struct literal", "  Pr::[U8] {a: 250}", "  Pr::[U8] { a: 250 }"),
    ("an operator in a const argument", "  Rg::[F32, 2*4].CAP", "  Rg::[F32, 2 * 4].CAP"),
    ("a path of modules", "  std.conv.parse::[ I32 ](s)", "  std.conv.parse::[I32](s)"),
    (
        "a line that continues with a dot after the list",
        "  let n = Buf::[F32]\n.zeroed(4)\n.len()\n  n",
        "  let n = Buf::[F32]\n    .zeroed(4)\n    .len()\n  n",
    ),
    ("the annotation is not rewritten", "  let b: Buf[F32] = Buf.zeroed(4)", "  let b: Buf[F32] = Buf.zeroed(4)"),
    ("the list is not rewritten", "  let y = id::[U8](250)", "  let y = id::[U8](250)"),
    ("the annotation of a call is not rewritten", "  let y: U8 = id(250)", "  let y: U8 = id(250)"),
];

#[test]
fn fmt_writes_the_list_in_the_normal_form() {
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
fn fmt_check_names_the_file_that_has_a_list_out_of_form() {
    // §18.2: `fmt --check` exits with 1 and writes nothing for a file that is not in the normal form.
    let d = Dir::new("check");
    let text = in_a_function("  id::[ U8 ](250)");
    let path = d.file("a.onsa", &text);
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 1, "{out:?}");
    assert_eq!(read(&path), text, "--check writes nothing");
    assert!(String::from_utf8_lossy(&out.stdout).contains("a.onsa"), "the file is named: {out:?}");
}

#[test]
fn a_file_in_the_normal_form_is_kept_whatever_the_forms_in_it() {
    // One file with the forms of §4.5 written in the normal form: fmt changes nothing.
    let text = "\
pub fn f(s: Str, v: V, inout buf: Buf[F32]) -> U8 {
  let a = parse::[U32](s)
  let b = Buf::[F32].zeroed(4)
  let c = Rg::[F32, 4].CAP
  let d = Pr::[U8] { a: 250 }
  let e = v.m::[I32](a)
  let g = id::[U8]
  let h = None::[I32]
  let i = Some::[U8](250)
  buf.push::[F32]!(1.0)

  let y: U8 = id(250)

  let z = id::[U8](250)
  z
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

// ---- fmt and diff --ast stop at the errors of the syntax stage (§18.2) -------------------------

/// Files with an error of the syntax stage around the mark: (what, the file, the code of the error).
/// `fmt` and `diff --ast` stop at each of them. The ones with E0002 are the forms that cannot be read.
const SYNTAX_ERRORS: &[(&str, &str, &str)] = &[
    ("angle brackets", "pub fn f() -> U8 {\n  id<U8>(250)\n}\n", "E0020"),
    ("angle brackets with a comma", "pub fn f() -> U8 {\n  pair<U8, F32>(1, 2.0)\n}\n", "E0020"),
    ("turbofish", "pub fn f() -> U8 {\n  id::<U8>(250)\n}\n", "E0020"),
    ("a bracket with a comma", "pub fn f() -> U8 {\n  pair[U8, F32](1, 2.0)\n}\n", "E0020"),
    ("a space before the colons", "pub fn f() -> U8 {\n  id ::[U8](250)\n}\n", "E0020"),
    ("a space after the colons", "pub fn f() -> U8 {\n  id:: [U8](250)\n}\n", "E0020"),
    ("a path separator after the list", "pub fn f() -> U8 {\n  Buf::[F32]::zeroed(4)\n}\n", "E0020"),
    ("the colons in a type position", "pub fn f(b: Buf::[F32]) -> U8 {\n  1\n}\n", "E0020"),
    ("after a parenthesis", "pub fn f() -> U8 {\n  (id)::[U8](250)\n}\n", "E0002"),
    ("after a call", "pub fn f() -> U8 {\n  g(1)::[U8](250)\n}\n", "E0002"),
    ("an empty list", "pub fn f() -> U8 {\n  id::[](250)\n}\n", "E0002"),
    ("a declaration", "pub fn f::[T](x: T) -> T {\n  x\n}\n", "E0002"),
    (
        "a pattern",
        "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    None::[I32] => 0,\n    _ => 1,\n  }\n}\n",
        "E0002",
    ),
    ("a line that starts with the colons", "pub fn f() -> U8 {\n  let a = id\n  ::[U8](250)\n}\n", "E0002"),
    ("a list that is not closed", "pub fn f() -> U8 {\n  id::[U8(250)\n}\n", "E0002"),
];

#[test]
fn fmt_and_diff_stop_at_an_error_of_the_syntax_stage_around_the_mark() {
    // §18.2: a file with a diagnostic of the syntax stage is not rewritten (exit code 2) and
    // `diff --ast` does not compare it (exit code 2); the diagnostic goes to the standard output
    // (docs/onsa-tools.md §3.1, §4). A file that is the same in the normal form is the other side.
    let d = Dir::new("syntax_errors");
    let other = d.file("other.onsa", "pub fn f() -> U8 {\n  250\n}\n");
    for (what, text, _) in SYNTAX_ERRORS {
        let path = d.file("a.onsa", text);
        for args in [vec!["fmt"], vec!["fmt", "--check"]] {
            let mut full = args.clone();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what}: onsa {args:?}: {out:?}");
            assert_eq!(read(&path), *text, "{what}: the file is not rewritten");
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(stdout.contains("error[E00"), "{what}: the diagnostic is on the standard output: {out:?}");
        }
        let diff = onsa(&["diff", "--ast", &path, &other]);
        assert_eq!(code(&diff), 2, "{what}: diff --ast: {diff:?}");
    }
}

// ---- diff --ast: the list is in the tree (R-81) -------------------------------------------------

/// (what the case says, one body, another body): the two files are different programs.
const DIFFERENT: &[(&str, &str, &str)] = &[
    ("a list and none", "  id::[U8](250)", "  id(250)"),
    ("another type", "  id::[U8](250)", "  id::[U16](250)"),
    ("another order", "  pair::[U8, F32](1, 2.0)", "  pair::[F32, U8](1, 2.0)"),
    ("another number of elements", "  pair::[U8, F32](1, 2.0)", "  pair::[U8](1, 2.0)"),
    ("another const argument", "  Rg::[F32, 4].CAP", "  Rg::[F32, 5].CAP"),
    ("a list on a type and none", "  Buf::[F32].zeroed(4)", "  Buf.zeroed(4)"),
    ("a list on a method and none", "  v.m::[I32](x)", "  v.m(x)"),
    ("a list on a variant and none", "  None::[I32]", "  None"),
    ("a list on a struct literal and none", "  Pr::[U8] { a: 250 }", "  Pr { a: 250 }"),
    ("a list on a value and none", "  let g = id::[U8]", "  let g = id"),
    ("a list inside a list", "  id::[Option[U8]](None)", "  id::[Option[U16]](None)"),
    ("a list and an annotation", "  let y: U8 = id(250)", "  let y = id::[U8](250)"),
];

/// (what, one body, another body): the same program written in two ways.
const SAME: &[(&str, &str, &str)] = &[
    ("spaces inside the list", "  id::[U8](250)", "  id::[ U8 ](250)"),
    ("spaces round the comma", "  pair::[U8, F32](1, 2.0)", "  pair::[U8 ,F32](1, 2.0)"),
    ("a method that changes its receiver", "  buf.push::[F32]!(x)", "  buf.push::[ F32 ]!( x )"),
    ("an operator in a const argument", "  Rg::[F32, 2 * 4].CAP", "  Rg::[F32, 2*4].CAP"),
];

#[test]
fn diff_ast_sees_a_list_and_does_not_see_its_spaces() {
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

#[test]
fn fmt_does_not_change_the_program_that_has_a_list() {
    // §18.2: fmt keeps the meaning; `diff --ast` of a file and its formatted self finds nothing.
    let d = Dir::new("fmt_same");
    for (what, written, _) in NORMAL_FORMS {
        let a = d.file("a.onsa", &in_a_function(written));
        let b = d.file("b.onsa", &in_a_function(written));
        let out = onsa(&["fmt", &b]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        let diff = onsa(&["diff", "--ast", &a, &b]);
        assert_eq!(code(&diff), 0, "{what}: fmt changed the program: {diff:?}");
    }
}

// ---- E0002: no candidate ------------------------------------------------------------------------

#[test]
fn a_form_that_cannot_be_read_is_one_e0002_with_no_candidate() {
    // §4.5, §18.1: the syntax cannot say what the writer meant. One diagnostic in the function, E0002,
    // no candidate (a candidate needs a reading of the form). The note may show the form. A list that
    // is not closed is left out: where the recovery stops is not in the spec for a bracket.
    let d = Dir::new("e0002");
    for (what, text, want) in
        SYNTAX_ERRORS.iter().filter(|(w, _, c)| *c == "E0002" && *w != "a list that is not closed")
    {
        let path = d.file("a.onsa", text);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{what}: {diags:?}");
        assert_eq!(code_of(&diags[0]), *want, "{what}: {}", diags[0]);
        assert!(fixes_of(&diags[0]).is_empty(), "{what}: E0002 has no candidate: {}", diags[0]);
    }
}

#[test]
fn a_list_that_is_not_closed_is_an_e0002_and_no_e0020() {
    let d = Dir::new("e0002_open");
    let path = d.file("a.onsa", "pub fn f() -> U8 {\n  id::[U8(250)\n}\n");
    let diags = check(&path);
    assert!(!diags.is_empty(), "an error is expected");
    assert!(diags.iter().all(|x| code_of(x) == "E0002"), "{diags:?}");
    assert!(diags.iter().all(|x| fixes_of(x).is_empty()), "{diags:?}");
}

// ---- E0020: the candidates ---------------------------------------------------------------------

/// The one diagnostic of a file that holds the text and the program with candidate `k` applied.
fn candidate(text: &str, k: usize) -> (usize, String, Value) {
    let d = Dir::new("candidate");
    let path = d.file("a.onsa", text);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "one diagnostic expected for {text}: {diags:?}");
    assert_eq!(code_of(&diags[0]), "E0020", "{}", diags[0]);
    let fixes = fixes_of(&diags[0]);
    let n = fixes.len();
    let fix = fixes.get(k).unwrap_or_else(|| panic!("no candidate {k} for {}", diags[0]));
    (n, apply(text, &edits_of(fix)), diags[0].clone())
}

/// (written, [what the candidates make]) for the body of a function. The order of the candidates is
/// that of the rows of docs/foreign-forms.toml (S-315): the Onsa form first.
const CANDIDATES: &[(&str, &[&str])] = &[
    ("  id<U8>(250)", &["  id::[U8](250)", "  id < U8 && U8 > (250)"]),
    ("  pair<U8, F32>(1, 2.0)", &["  pair::[U8, F32](1, 2.0)"]),
    ("  v.conv<I32>(1)", &["  v.conv::[I32](1)", "  v.conv < I32 && I32 > (1)"]),
    ("  id::<U8>(250)", &["  id::[U8](250)"]),
    ("  id::<Option<U8>>(None)", &["  id::[Option[U8]](None)"]),
    ("  pair[U8, F32](1, 2.0)", &["  pair::[U8, F32](1, 2.0)"]),
    ("  Rg[F32, 4].CAP", &["  Rg::[F32, 4].CAP"]),
    ("  id ::[U8](250)", &["  id::[U8](250)"]),
    ("  id:: [U8](250)", &["  id::[U8](250)"]),
    ("  Buf::[F32]::zeroed(4)", &["  Buf::[F32].zeroed(4)"]),
    ("  std::conv::parse::[I32](s)", &["  std.conv.parse::[I32](s)"]),
    ("  m::Buf::[F32]::zeroed(4)", &["  m.Buf::[F32].zeroed(4)"]),
    ("  (inc)<I32>(5)", &["  inc.(5)"]),
    ("  pick(true)::<I32>(5)", &["  pick(true).(5)"]),
];

#[test]
fn each_form_has_the_candidates_of_the_spec_in_order() {
    for (written, made) in CANDIDATES {
        let text = in_a_function(written);
        for (k, want) in made.iter().enumerate() {
            let (n, after, _) = candidate(&text, k);
            assert_eq!(n, made.len(), "the number of candidates for `{}`", written.trim());
            assert_eq!(after, in_a_function(want), "candidate {} for `{}`", k + 1, written.trim());
        }
    }
}

#[test]
fn a_form_of_the_syntax_stage_is_e0020_and_not_a_chain_of_comparisons() {
    // §4.5: `f<T>(x)` (the `>` is followed by `(`) is not the E0010 of a chain of comparisons; it is
    // one E0020 whose first candidate is the Onsa form. A real chain (`a < b > c`) stays E0010 (§3.1).
    let d = Dir::new("not_a_chain");
    let path = d.file("a.onsa", &in_a_function("  id<U8>(250)"));
    let diags = check(&path);
    assert_eq!(diags.iter().map(code_of).collect::<Vec<_>>(), ["E0020"], "{diags:?}");
    let chain = d.file("b.onsa", &in_a_function("  a < b > c"));
    let diags = check(&chain);
    assert_eq!(diags.iter().map(code_of).collect::<Vec<_>>(), ["E0010"], "{diags:?}");
}

#[test]
fn the_note_of_each_form_shows_the_mark() {
    // §18.1: an E0020 shows the rule in a note without a position; §4.5: the note of these forms
    // says that a type argument in an expression is written `name::[…]` (a `[` alone is an index).
    let forms =
        ["  id<U8>(250)", "  pair<U8, F32>(1, 2.0)", "  id::<U8>(250)", "  pair[U8, F32](1, 2.0)", "  Rg[F32, 4].CAP"];
    let d = Dir::new("notes");
    for written in forms {
        let path = d.file("a.onsa", &in_a_function(written));
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{written}: {diags:?}");
        let notes: Vec<&str> = diags[0]["notes"]
            .as_array()
            .unwrap_or_else(|| panic!("no notes in {}", diags[0]))
            .iter()
            .filter_map(|n| n["message"].as_str())
            .collect();
        assert!(notes.iter().any(|m| m.contains("::[")), "{written}: no note shows `::[`: {notes:?}");
    }
}

#[test]
fn the_edits_of_a_candidate_change_the_brackets_and_not_the_types() {
    // §18.1 (S-251): the edits replace the tokens that change and nothing between them, so the
    // type arguments are untouched. `<T>` becomes `::[T]`: the `<` and the `>` are replaced (an
    // insertion of the `::` may come with them: an edit that replaces nothing is not counted);
    // `::<T>` keeps its `::` (§4.5: the `<` and the `>` become `[` and `]`); `>>` is one token and one
    // edit; a path separator is replaced one `::` at a time and the list next to it is not touched.
    let cases: &[(&str, &[&str])] = &[
        // (written, the texts the edits of candidate 1 replace, in the order of the text)
        ("  id<U8>(250)", &["<", ">"]),
        ("  id::<U8>(250)", &["<", ">"]),
        ("  id::<Option<U8>>(None)", &["<", "<", ">>"]),
        ("  Buf::[F32]::zeroed(4)", &["::"]),
        ("  std::conv::parse::[I32](s)", &["::", "::"]),
    ];
    let d = Dir::new("edits");
    for (written, replaced) in cases {
        let text = in_a_function(written);
        let path = d.file("a.onsa", &text);
        let diags = check(&path);
        assert_eq!(diags.len(), 1, "{written}: {diags:?}");
        let edits = edits_of(fixes_of(&diags[0])[0]);
        let mut at: Vec<(usize, String)> = edits
            .iter()
            .map(|e| (offset(&text, e.start), text[offset(&text, e.start)..offset(&text, e.end)].to_string()))
            .filter(|(_, t)| !t.is_empty())
            .collect();
        at.sort();
        let got: Vec<&str> = at.iter().map(|(_, t)| t.as_str()).collect();
        assert_eq!(&got, replaced, "{written}: the texts the edits replace");
    }
    // A type position loses the `::` only: one edit, and it does not reach the list.
    let text = in_a_function("  let b: Buf::[F32] = Buf.zeroed(4)");
    let path = d.file("b.onsa", &text);
    let diags = check(&path);
    assert_eq!(diags.len(), 1, "{diags:?}");
    let edits = edits_of(fixes_of(&diags[0])[0]);
    assert_eq!(edits.len(), 1, "one edit");
    assert_eq!(replaced_texts(&text, &edits), ["::"]);
    assert_eq!(edits[0].replace, "");
}
