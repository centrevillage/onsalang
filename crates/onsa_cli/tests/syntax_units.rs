//! The syntax-stage stop of `onsa fmt` and `onsa diff --ast`, the report they make, and where the
//! commands write diagnostics (W3-03/t; spec §18.1 and §18.2, S-214, S-232, S-56, R-69, R-71;
//! `docs/onsa-tools.md` §3.1 and §4).
//!
//! What the spec says, in short:
//!
//! - §18.2: `fmt` (and `fmt --check`) writes nothing and exits with 2 for a file with a
//!   diagnostic of the syntax stage, whatever its code: E00xx, the reserved word's E0200
//!   (§2.2), E0408 of an integer literal that has no value and of a tuple index that does not
//!   fit (§2.4), E0006. `diff --ast` compares nothing and exits with 2. A diagnostic of the
//!   names stage or later (E0320, E0302, E0401, the E0020 of a call of a value written `f(x)`)
//!   does not stop them.
//! - `docs/onsa-tools.md` §3.1: the report is `check`'s choice (one diagnostic per unit, the
//!   syntax one first, no E0320 in a unit with a syntax error, §18.1); a diagnostic that is not
//!   of the syntax stage is not reported by `fmt`; with several files all are processed.
//! - `docs/onsa-tools.md` §4 (S-232): every command writes a diagnostic to the standard output,
//!   `fmt` and `diff --ast` included, and a sentence that is not a diagnostic (usage, I/O,
//!   internal error) to the standard error. A diagnostic starts with
//!   `<file>:<line>:<col>: error[<code>]: <message>`, and diagnostics are ordered by file,
//!   line, column, ... .
//!
//! Tests that need a later work are `#[ignore = "<work>"]` (the reason is the work that makes them
//! pass): W3-03 for the unit rules and the streams, W3-04 for the reserved word's E0200, W3-14
//! for E0006. Not written here: the depth limit's own cases (W3-14), the E0020 rule table
//! (W3-15), the top-level shape of `--json` (W3-16; the readers below accept an array and an
//! object with `diagnostics`).

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        // A helper is called from several tests at once, so the tag alone does not make a name.
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_syntax_units_{}_{n}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }

    fn path(&self, name: &str) -> String {
        self.0.join(name).to_string_lossy().into_owned()
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

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// One diagnostic's first line, `<file>:<line>:<col>: error[<code>]: <message>` (onsa-tools §4).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Header {
    file: String,
    line: usize,
    col: usize,
    code: String,
}

/// The first lines of the diagnostics in a text output. The source excerpt, the `note:` lines and
/// the fixes are indented and are not read.
fn headers(text: &str) -> Vec<Header> {
    let mut out = Vec::new();
    for l in text.lines() {
        if l.starts_with(char::is_whitespace) {
            continue;
        }
        let Some(i) = l.find(": error[") else { continue };
        let rest = &l[i + ": error[".len()..];
        let Some(end) = rest.find("]: ") else { continue };
        let mut parts = l[..i].rsplitn(3, ':');
        let (Some(col), Some(line), Some(file)) = (parts.next(), parts.next(), parts.next()) else { continue };
        let (Ok(col), Ok(line)) = (col.parse(), line.parse()) else { continue };
        out.push(Header { file: file.to_string(), line, col, code: rest[..end].to_string() });
    }
    out
}

/// `(line, code)` of the diagnostics of a text output.
fn line_codes(text: &str) -> Vec<(usize, String)> {
    headers(text).into_iter().map(|h| (h.line, h.code)).collect()
}

fn lc(line: usize, code: &str) -> (usize, String) {
    (line, code.to_string())
}

/// The diagnostics in the output of `--json` (an array, an object with `diagnostics`, or one
/// object per line; the top-level shape is W3-16's).
fn json_diagnostics(text: &str) -> Vec<Value> {
    match serde_json::from_str::<Value>(text) {
        Ok(Value::Array(a)) => a,
        Ok(Value::Object(mut o)) => match o.remove("diagnostics") {
            Some(Value::Array(a)) => a,
            _ => vec![Value::Object(o)],
        },
        Ok(other) => panic!("not diagnostics: {other}"),
        Err(_) => text
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| serde_json::from_str(l).unwrap_or_else(|e| panic!("line {l:?} is not JSON: {e}")))
            .collect(),
    }
}

fn no_diagnostic_on_stderr(out: &Output) {
    let err = stderr(out);
    assert!(headers(&err).is_empty(), "a diagnostic went to the standard error: {err}");
    assert!(!err.contains("error[E"), "a diagnostic went to the standard error: {err}");
}

// ---------------------------------------------------------------------------------------------
// Files that `fmt` and `diff --ast` stop at, one per kind of syntax-stage diagnostic. The second
// function of each is badly spaced on purpose, so that a rewrite of the file shows.
// ---------------------------------------------------------------------------------------------

const UGLY_TAIL: &str = "\npub fn  other( )->I32{ 2 }\n";

fn with_tail(head: &str) -> String {
    format!("{head}{UGLY_TAIL}")
}

/// Run the three commands on a file the syntax stage fails: `fmt`, `fmt --check` and
/// `diff --ast` stop with 2 and change nothing.
fn assert_stops(src: &str) {
    let d = Dir::new("stops");
    let path = d.file("bad.onsa", src);
    let other = d.file("other.onsa", src);
    for args in [vec!["fmt", &path], vec!["fmt", "--check", &path]] {
        let out = onsa(&args);
        assert_eq!(code(&out), 2, "onsa {args:?}: {out:?}");
        assert_eq!(read(&path), src, "onsa {args:?} rewrote the file");
    }
    let diff = onsa(&["diff", "--ast", &path, &other]);
    assert_eq!(code(&diff), 2, "diff --ast: {diff:?}");
    assert_eq!(read(&path), src);
    assert_eq!(read(&other), src);
}

/// The report of the stop: exactly the one diagnostic `(line, code)` of the unit, on the standard
/// output, for the three commands.
fn assert_reports(src: &str, line: usize, want: &str) {
    let d = Dir::new("reports");
    let path = d.file("bad.onsa", src);
    let other = d.file("other.onsa", src);
    for args in [vec!["fmt", &path], vec!["fmt", "--check", &path]] {
        let out = onsa(&args);
        assert_eq!(line_codes(&stdout(&out)), vec![lc(line, want)], "onsa {args:?} on stdout: {out:?}");
        no_diagnostic_on_stderr(&out);
    }
    // `diff --ast` reports each of its two files; the two are the same text here.
    let diff = onsa(&["diff", "--ast", &path, &other]);
    assert_eq!(line_codes(&stdout(&diff)), vec![lc(line, want), lc(line, want)], "diff --ast on stdout: {diff:?}");
    no_diagnostic_on_stderr(&diff);
}

/// A case whose stop already works and whose report waits for W3-03 (the streams, one diagnostic
/// per unit); with a sixth argument, a case that waits for that work as a whole.
macro_rules! stop_case {
    ($stops:ident, $reports:ident, $src:expr, $line:expr, $code:expr) => {
        #[test]
        fn $stops() {
            assert_stops(&with_tail($src));
        }

        #[test]
        fn $reports() {
            assert_reports(&with_tail($src), $line, $code);
        }
    };
    ($stops:ident, $reports:ident, $src:expr, $line:expr, $code:expr, reports: $work:expr) => {
        #[test]
        fn $stops() {
            assert_stops(&with_tail($src));
        }

        #[test]
        #[ignore = $work]
        fn $reports() {
            assert_reports(&with_tail($src), $line, $code);
        }
    };
    ($stops:ident, $reports:ident, $src:expr, $line:expr, $code:expr, $work:expr) => {
        #[test]
        #[ignore = $work]
        fn $stops() {
            assert_stops(&with_tail($src));
        }

        #[test]
        #[ignore = $work]
        fn $reports() {
            assert_reports(&with_tail($src), $line, $code);
        }
    };
}

stop_case!(fmt_stops_for_an_unexpected_token, fmt_reports_an_unexpected_token, "pub fn f( {\n  1\n}\n", 1, "E0002");
stop_case!(
    fmt_stops_for_an_invalid_character,
    fmt_reports_an_invalid_character_once,
    "pub fn f(a: I32) -> I32 {\n  a $ 1\n}\n",
    2,
    "E0001"
);
stop_case!(
    fmt_stops_for_else_on_its_own_line,
    fmt_reports_else_on_its_own_line,
    "pub fn f(c: Bool) -> I32 {\n  if c {\n    1\n  }\n  else {\n    2\n  }\n}\n",
    5,
    "E0003",
    // W3-03/i: the stop and its report work; the E0003 is at the line break after `}` (line 4)
    // until W3-06 puts it at the `else` (S-216).
    reports: "W3-06"
);
stop_case!(
    fmt_stops_for_mixed_operator_groups,
    fmt_reports_mixed_operator_groups,
    "pub fn f(a: I32) -> I32 {\n  a + a % 2\n}\n",
    2,
    "E0010"
);
stop_case!(
    fmt_stops_for_a_semicolon,
    fmt_reports_a_semicolon,
    "pub fn f(a: I32) -> I32 {\n  let x = a;\n  x\n}\n",
    2,
    "E0020"
);
stop_case!(
    fmt_stops_for_an_integer_literal_without_a_value,
    fmt_reports_an_integer_literal_without_a_value,
    "pub fn f() -> U64 {\n  99999999999999999999999\n}\n",
    2,
    "E0408"
);
stop_case!(
    fmt_stops_for_a_tuple_index_that_does_not_fit,
    fmt_reports_a_tuple_index_that_does_not_fit,
    "pub fn f(t: (I32, I32)) -> I32 {\n  t.99999999999\n}\n",
    2,
    "E0408"
);
// The reserved words `clock`, `when` and `reset_if` are E0200 at the place they appear (§2.2),
// and it is a diagnostic of the syntax stage (§18.2). The lexer change is W3-04's.
stop_case!(
    fmt_stops_for_a_reserved_word,
    fmt_reports_a_reserved_word,
    "pub fn f(a: I32) -> I32 {\n  let clock = a\n  clock\n}\n",
    2,
    "E0200",
    "W3-04"
);

/// R-69, R-146: the E0320 of `badName` comes before the E0002 of the same function, and `fmt` once
/// took the failed function out of the file (the unit cases of the same rule are in
/// `tests/spec/negative/unit_syntax_hides_later.onsa`).
const FMT_DROP: &str = "\
fn f() {
  let badName = 1
  let = 2
}

fn  g( ){}
";

#[test]
fn fmt_does_not_take_a_failed_function_out_of_the_file() {
    assert_stops(FMT_DROP);
}

#[test]
fn fmt_reports_the_e0002_of_the_failed_function_and_not_its_e0320() {
    assert_reports(FMT_DROP, 3, "E0002");
}

// ---------------------------------------------------------------------------------------------
// Diagnostics of the names stage or later do not stop `fmt` and `diff --ast`, and `fmt` does not
// report them (docs/onsa-tools.md §3.1).
// ---------------------------------------------------------------------------------------------

fn assert_formats(src: &str, canonical: &str) {
    let d = Dir::new("formats");
    let path = d.file("late.onsa", src);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&path), canonical);
    assert!(headers(&stdout(&out)).is_empty(), "fmt reported a diagnostic that is not of the syntax stage: {out:?}");
    assert!(headers(&stderr(&out)).is_empty());
    let again = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&again), 0, "not a fixed point: {again:?}");
    // `diff --ast` compares them: the same program, so no difference.
    let before = d.file("before.onsa", src);
    let diff = onsa(&["diff", "--ast", &before, &path]);
    assert_eq!(code(&diff), 0, "diff --ast between the file and its formatted form: {diff:?}");
}

#[test]
fn fmt_formats_a_naming_error() {
    assert_formats("pub fn BadName(a: I32)->I32{\n  a\n}\n", "pub fn BadName(a: I32) -> I32 {\n  a\n}\n");
}

#[test]
fn fmt_formats_a_name_error() {
    assert_formats("pub fn f(a: I32)->I32{\n  missing\n}\n", "pub fn f(a: I32) -> I32 {\n  missing\n}\n");
}

#[test]
fn fmt_formats_a_type_error() {
    assert_formats(
        "pub fn f(a: I32)->I32{\n  let x: Bool = 1\n  a\n}\n",
        "pub fn f(a: I32) -> I32 {\n  let x: Bool = 1\n  a\n}\n",
    );
}

#[test]
fn fmt_formats_an_e0020_of_the_names_stage() {
    // `f(x)` with a parameter `f` is E0020 (a value is called with `f.(x)`, §6.1), found by the
    // name resolution, so it is not a syntax-stage diagnostic (§18.2: "E0002 and E0020 that come
    // after the names stage are not included"). `check` does not report it before W4-12; the
    // test is for the day it does.
    assert_formats(
        "pub fn apply(f: fn(I32) -> I32, x: I32)->I32{\n  f(x)\n}\n",
        "pub fn apply(f: fn(I32) -> I32, x: I32) -> I32 {\n  f(x)\n}\n",
    );
}

#[test]
fn fmt_formats_a_file_whose_diagnostic_is_an_unsupported_feature() {
    // §18.2 names only the reserved word's E0200 among the stoppers. The E0200 of a feature this
    // version does not handle (`impl Trait for Type` today) is not of the syntax stage, so the
    // flag that stops `fmt` must not be "any E0200".
    assert_formats(
        "pub struct P {\n  x: I32,\n}\n\n\npub trait T {\n  fn a(self) -> I32\n}\n\nimpl T for P {\n  fn a(self) -> I32 {\n    self.x\n  }\n}\n",
        "pub struct P {\n  x: I32,\n}\n\npub trait T {\n  fn a(self) -> I32\n}\n\nimpl T for P {\n  fn a(self) -> I32 {\n    self.x\n  }\n}\n",
    );
}

#[test]
fn diff_ast_compares_files_with_errors_of_later_stages() {
    let d = Dir::new("diff_late");
    let a = d.file("a.onsa", "pub fn f(a: I32) -> I32 {\n  missing\n}\n");
    let b = d.file("b.onsa", "pub fn f(a: I32) -> I32 {\n  other_missing\n}\n");
    let out = onsa(&["diff", "--ast", &a, &b]);
    assert_eq!(code(&out), 1, "different programs: {out:?}");
    assert!(headers(&stdout(&out)).is_empty(), "no diagnostics from diff --ast: {out:?}");
}

// ---------------------------------------------------------------------------------------------
// The report is `check`'s choice: one diagnostic for each unit, the syntax one first, no E0320
// of the heading in a unit that has a syntax error (S-214, §18.1).
// ---------------------------------------------------------------------------------------------

/// Unit 1 (lines 1-3): E0320 on the heading, E0010 later. Unit 2 (lines 5-7): E0002. Unit 3
/// (lines 9-11): an invalid character, which the lexer reports and the parser also complains
/// about at the same place; one diagnostic. Unit 4 (lines 13-15): a name error, a type error and
/// a naming error in unrelated units after them.
const SEVERAL_UNITS: &str = "\
pub fn BadName(a: I32) -> I32 {
  a + a % 2
}

pub fn second(a: I32) -> I32 {
  let = a
}

pub fn third(a: I32) -> I32 {
  a $ 1
}

pub fn fourth(a: I32) -> I32 {
  missing
}

pub fn fifth(a: I32) -> I32 {
  let x: Bool = 1
  a
}

pub fn SixthName(a: I32) -> I32 {
  a
}
";

#[test]
fn check_reports_one_diagnostic_per_unit_syntax_first() {
    let d = Dir::new("check_units");
    let path = d.file("units.onsa", SEVERAL_UNITS);
    let out = onsa(&["check", &path]);
    assert_eq!(code(&out), 1, "{out:?}");
    assert_eq!(
        line_codes(&stdout(&out)),
        vec![lc(2, "E0010"), lc(6, "E0002"), lc(10, "E0001"), lc(14, "E0302"), lc(18, "E0401"), lc(22, "E0320")],
        "{out:?}"
    );
}

#[test]
fn fmt_reports_the_syntax_diagnostics_of_check_and_nothing_else() {
    let d = Dir::new("fmt_report");
    let path = d.file("units.onsa", SEVERAL_UNITS);
    for args in [vec!["fmt", &path], vec!["fmt", "--check", &path]] {
        let out = onsa(&args);
        assert_eq!(code(&out), 2, "{out:?}");
        assert_eq!(
            line_codes(&stdout(&out)),
            vec![lc(2, "E0010"), lc(6, "E0002"), lc(10, "E0001")],
            "onsa {args:?}: the syntax stage of each unit, once, and no E0320 of unit 1: {out:?}"
        );
        no_diagnostic_on_stderr(&out);
    }
    assert_eq!(read(&path), SEVERAL_UNITS);
}

#[test]
fn diff_ast_reports_the_same_diagnostics_as_fmt() {
    let d = Dir::new("diff_report");
    let a = d.file("a.onsa", SEVERAL_UNITS);
    let b = d.file("b.onsa", "pub fn fine() -> I32 {\n  1\n}\n");
    let out = onsa(&["diff", "--ast", &a, &b]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(line_codes(&stdout(&out)), vec![lc(2, "E0010"), lc(6, "E0002"), lc(10, "E0001")], "{out:?}");
    no_diagnostic_on_stderr(&out);
}

#[test]
fn a_unit_with_a_naming_error_and_a_later_syntax_error_reports_the_syntax_error() {
    // The case S-214 is about: the E0320 comes first in the text, the E0010 is of an earlier stage.
    let d = Dir::new("s214");
    let src = "pub fn f(badName: I32) -> I32 {\n  1 + 2 * 3 % 4\n}\n";
    let path = d.file("s214.onsa", src);
    let check = onsa(&["check", &path]);
    assert_eq!(line_codes(&stdout(&check)), vec![lc(2, "E0010")], "{check:?}");
    let fmt = onsa(&["fmt", &path]);
    assert_eq!(code(&fmt), 2);
    assert_eq!(line_codes(&stdout(&fmt)), vec![lc(2, "E0010")], "{fmt:?}");
    assert_eq!(read(&path), src);
}

#[test]
fn a_unit_with_a_naming_error_alone_is_reported_by_check_and_not_by_fmt() {
    let d = Dir::new("naming_alone");
    let src = "pub fn f(badName: I32) -> I32 {\n  badName\n}\n";
    let path = d.file("naming.onsa", src);
    let check = onsa(&["check", &path]);
    assert_eq!(line_codes(&stdout(&check)), vec![lc(1, "E0320")], "{check:?}");
    let fmt = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&fmt), 0, "{fmt:?}");
}

#[test]
fn text_and_json_give_the_same_position_and_code() {
    // onsa-tools §4: file, line and column of the first line are `--json`'s `span` values.
    let d = Dir::new("text_json");
    let path = d.file("units.onsa", SEVERAL_UNITS);
    let text = onsa(&["check", &path]);
    let json = onsa(&["check", "--json", &path]);
    assert_eq!(code(&text), 1);
    assert_eq!(code(&json), 1);
    let from_text: Vec<(String, usize, usize, String)> =
        headers(&stdout(&text)).into_iter().map(|h| (h.file, h.line, h.col, h.code)).collect();
    let from_json: Vec<(String, usize, usize, String)> = json_diagnostics(&stdout(&json))
        .iter()
        .map(|v| {
            let s = &v["span"];
            (
                s["file"].as_str().expect("span.file").to_string(),
                s["line"].as_u64().expect("span.line") as usize,
                s["col"].as_u64().expect("span.col") as usize,
                v["code"].as_str().expect("code").to_string(),
            )
        })
        .collect();
    assert_eq!(from_text, from_json);
    assert_eq!(from_text.len(), 6, "one diagnostic per unit: {from_text:?}");
}

// ---------------------------------------------------------------------------------------------
// Several files (docs/onsa-tools.md §3.1) and the order of the diagnostics (§18.1, onsa-tools §4).
// ---------------------------------------------------------------------------------------------

// The body is broken after the `{` (W3-03/i: `fmt` keeps a one-line body on one line,
// docs/onsa-tools.md §3.2; the expected text below is the block form).
const UGLY_OK: &str = "pub fn  ok( )->I32{\n 1\n}\n";
const SYNTAX_A: &str = "pub fn a() -> I32 {\n  1 + 2 % 3\n}\n";
const SYNTAX_B: &str = "pub fn b( {\n  1\n}\n";

#[test]
fn fmt_with_several_files_reports_every_syntax_error_and_writes_the_clean_ones() {
    let d = Dir::new("many_order");
    let b = d.file("b.onsa", SYNTAX_B);
    let ok = d.file("c.onsa", UGLY_OK);
    let a = d.file("a.onsa", SYNTAX_A);
    let out = onsa(&["fmt", &b, &ok, &a]);
    assert_eq!(code(&out), 2, "{out:?}");
    let mut hs = headers(&stdout(&out));
    hs.sort_by(|x, y| x.file.cmp(&y.file));
    assert_eq!(
        hs.iter().map(|h| (h.file.as_str(), h.line, h.code.as_str())).collect::<Vec<_>>(),
        vec![(a.as_str(), 2, "E0010"), (b.as_str(), 1, "E0002")],
        "{out:?}"
    );
    no_diagnostic_on_stderr(&out);
    assert_eq!(read(&ok), "pub fn ok() -> I32 {\n  1\n}\n", "the clean file is formatted");
    assert_eq!((read(&a), read(&b)), (SYNTAX_A.into(), SYNTAX_B.into()), "the failed files are not written");
}

#[test]
fn fmt_check_with_several_files_reports_the_syntax_errors_and_names_the_unformatted() {
    let d = Dir::new("many_check");
    let a = d.file("a.onsa", SYNTAX_A);
    let ok = d.file("b.onsa", UGLY_OK);
    let out = onsa(&["fmt", "--check", &a, &ok]);
    assert_eq!(code(&out), 2, "a syntax error makes the exit code 2 even though another file is unformatted: {out:?}");
    assert_eq!(line_codes(&stdout(&out)), vec![lc(2, "E0010")], "{out:?}");
    assert_eq!(read(&ok), UGLY_OK, "--check writes nothing");
}

// The order of the diagnostics is S-234's (W3-16): by the file string, then line, column, end line,
// end column, code, message (§18.1; the text output in the same order, onsa-tools §4).

#[test]
fn check_orders_the_diagnostics_of_several_files_by_file() {
    let d = Dir::new("check_order");
    let b = d.file("b.onsa", "pub fn b() -> I32 {\n  missing_b\n}\n");
    let a = d.file("a.onsa", "pub fn a() -> I32 {\n  let x: Bool = 1\n  1\n}\n");
    let out = onsa(&["check", &b, &a]);
    assert_eq!(code(&out), 1, "{out:?}");
    let hs = headers(&stdout(&out));
    assert_eq!(hs.len(), 2, "{out:?}");
    assert!(hs[0].file < hs[1].file, "ordered by the file string, not by the command line: {hs:?}");
}

#[test]
fn fmt_orders_its_report_by_file() {
    let d = Dir::new("fmt_order");
    let b = d.file("b.onsa", SYNTAX_B);
    let a = d.file("a.onsa", SYNTAX_A);
    let out = onsa(&["fmt", &b, &a]);
    assert_eq!(code(&out), 2, "{out:?}");
    let hs = headers(&stdout(&out));
    assert_eq!(
        hs.iter().map(|h| (h.file.as_str(), h.code.as_str())).collect::<Vec<_>>(),
        vec![(a.as_str(), "E0010"), (b.as_str(), "E0002")],
        "{out:?}"
    );
}

#[test]
fn diff_ast_orders_its_report_by_file() {
    let d = Dir::new("diff_order");
    let z = d.file("z.onsa", SYNTAX_B);
    let a = d.file("a.onsa", SYNTAX_A);
    let out = onsa(&["diff", "--ast", &z, &a]);
    assert_eq!(code(&out), 2, "{out:?}");
    let hs = headers(&stdout(&out));
    assert_eq!(
        hs.iter().map(|h| (h.file.as_str(), h.code.as_str())).collect::<Vec<_>>(),
        vec![(a.as_str(), "E0010"), (z.as_str(), "E0002")],
        "{out:?}"
    );
}

// ---------------------------------------------------------------------------------------------
// Where the commands write (S-232): a diagnostic to the standard output, a sentence that is not a
// diagnostic to the standard error.
// ---------------------------------------------------------------------------------------------

const TYPE_ERROR: &str = "pub fn f() -> I32 {\n  let x: Bool = 1\n  1\n}\n\ntest \"t\" {\n  assert f() == 1\n}\n";

const MANIFEST: &str = "\
[package]
name = \"streams_pkg\"
edition = \"2026\"

[export]
prefix = \"sp_\"
fns = [\"util.version\"]

[targets.hosted]
kind = \"source\"
lang = \"c\"
platform = \"host\"
panic = \"poison\"
provides = [\"Alloc\"]
";

fn assert_diagnostic_on_stdout(args: &[&str], line: usize, want: &str) {
    let out = onsa(args);
    assert_eq!(code(&out), 1, "onsa {args:?}: {out:?}");
    assert_eq!(line_codes(&stdout(&out)), vec![lc(line, want)], "onsa {args:?}: {out:?}");
    no_diagnostic_on_stderr(&out);
}

#[test]
fn check_writes_its_diagnostics_to_stdout() {
    let d = Dir::new("stream_check");
    let p = d.file("t.onsa", TYPE_ERROR);
    assert_diagnostic_on_stdout(&["check", &p], 2, "E0401");
}

#[test]
fn check_json_writes_its_diagnostics_to_stdout() {
    let d = Dir::new("stream_check_json");
    let p = d.file("t.onsa", TYPE_ERROR);
    let out = onsa(&["check", "--json", &p]);
    assert_eq!(code(&out), 1, "{out:?}");
    let ds = json_diagnostics(&stdout(&out));
    assert_eq!(ds.len(), 1, "{out:?}");
    assert_eq!(ds[0]["code"], "E0401");
    no_diagnostic_on_stderr(&out);
    assert!(!stderr(&out).contains("E0401"), "{out:?}");
}

#[test]
fn test_writes_the_diagnostics_of_the_check_to_stdout() {
    let d = Dir::new("stream_test");
    let p = d.file("t.onsa", TYPE_ERROR);
    assert_diagnostic_on_stdout(&["test", &p], 2, "E0401");
}

#[test]
fn interface_writes_the_diagnostics_of_the_check_to_stdout() {
    let d = Dir::new("stream_interface");
    let p = d.file("t.onsa", TYPE_ERROR);
    assert_diagnostic_on_stdout(&["interface", &p], 2, "E0401");
}

#[test]
fn build_writes_the_diagnostics_to_stdout() {
    let d = Dir::new("stream_build");
    d.file("onsa.toml", MANIFEST);
    d.file("util.onsa", "pub fn version() -> U32 {\n  let x: Bool = 1\n  1\n}\n");
    let dir = d.path("");
    let out = onsa(&["build", "--target", "hosted", &dir]);
    assert_eq!(code(&out), 1, "{out:?}");
    let hs = headers(&stdout(&out));
    assert_eq!(hs.iter().map(|h| (h.line, h.code.as_str())).collect::<Vec<_>>(), vec![(2, "E0401")], "{out:?}");
    assert_eq!(hs[0].file, "util.onsa", "the file is the path from the package root: {hs:?}");
    no_diagnostic_on_stderr(&out);
}

#[test]
fn fmt_writes_the_syntax_diagnostics_to_stdout_not_to_stderr() {
    // The case S-232 changes: `fmt` wrote them to the standard error.
    let d = Dir::new("stream_fmt");
    let p = d.file("t.onsa", "pub fn f( {\n  1\n}\n");
    let out = onsa(&["fmt", &p]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(line_codes(&stdout(&out)), vec![lc(1, "E0002")], "{out:?}");
    no_diagnostic_on_stderr(&out);
}

#[test]
fn diff_ast_writes_the_syntax_diagnostics_to_stdout() {
    let d = Dir::new("stream_diff");
    let a = d.file("a.onsa", "pub fn f( {\n  1\n}\n");
    let b = d.file("b.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    let out = onsa(&["diff", "--ast", &a, &b]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert!(line_codes(&stdout(&out)).contains(&lc(1, "E0002")), "{out:?}");
    no_diagnostic_on_stderr(&out);
}

/// A sentence that is not a diagnostic goes to the standard error and leaves the standard output
/// empty (usage, I/O, an unknown code), with the exit code 2.
fn assert_stderr_only(args: &[&str]) {
    let out = onsa(args);
    assert_eq!(code(&out), 2, "onsa {args:?}: {out:?}");
    assert!(stdout(&out).is_empty(), "onsa {args:?} wrote to the standard output: {out:?}");
    assert!(!stderr(&out).trim().is_empty(), "onsa {args:?} said nothing on the standard error: {out:?}");
    assert!(headers(&stderr(&out)).is_empty(), "{out:?}");
}

#[test]
fn a_missing_file_is_a_sentence_on_stderr_for_every_command() {
    let d = Dir::new("stream_missing");
    let missing = d.path("missing.onsa");
    let present = d.file("present.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    assert_stderr_only(&["check", &missing]);
    assert_stderr_only(&["check", "--json", &missing]);
    assert_stderr_only(&["fmt", &missing]);
    assert_stderr_only(&["fmt", "--check", &missing]);
    assert_stderr_only(&["diff", "--ast", &present, &missing]);
    assert_stderr_only(&["test", &missing]);
    assert_stderr_only(&["interface", &missing]);
}

#[test]
fn a_usage_error_is_a_sentence_on_stderr() {
    let d = Dir::new("stream_usage");
    let dir = d.path("");
    assert_stderr_only(&["check"]);
    assert_stderr_only(&["fmt"]);
    assert_stderr_only(&["fmt", "--no-such-flag", "x.onsa"]);
    assert_stderr_only(&["build", &dir]); // no --target
    assert_stderr_only(&["explain", "E9999"]);
}

#[test]
fn a_missing_file_among_the_files_of_fmt_splits_the_streams() {
    // The syntax diagnostic of one file goes to the standard output, the I/O sentence about
    // another to the standard error, in the same run.
    let d = Dir::new("stream_mixed");
    let bad = d.file("bad.onsa", "pub fn f( {\n  1\n}\n");
    let missing = d.path("missing.onsa");
    let out = onsa(&["fmt", &bad, &missing]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(line_codes(&stdout(&out)), vec![lc(1, "E0002")], "{out:?}");
    let err = stderr(&out);
    assert!(err.contains("missing.onsa"), "the I/O sentence names the file: {err}");
    no_diagnostic_on_stderr(&out);
}

// ---------------------------------------------------------------------------------------------
// The note on the E0002 of an unclosed `{` (§18.1: "the declaration whose body it is is shown in a
// note"; a note with a span shows a related position, such as the declaration that opened the `{`).
// ---------------------------------------------------------------------------------------------

#[test]
fn the_e0002_of_an_unclosed_brace_points_at_the_brace_and_has_a_note() {
    let d = Dir::new("unclosed_note");
    let src = "\
pub fn unclosed() -> I32 {
  if true {
    1
  } else {
    2
}

pub fn next() -> I32 {
  3
}
";
    let p = d.file("brace.onsa", src);
    let out = onsa(&["check", "--json", &p]);
    assert_eq!(code(&out), 1, "{out:?}");
    let ds = json_diagnostics(&stdout(&out));
    assert_eq!(ds.len(), 1, "only the unclosed brace; `next` is not lost or reported: {ds:?}");
    let d0 = &ds[0];
    assert_eq!(d0["code"], "E0002");
    assert_eq!(d0["span"]["line"], 1, "the `{{` that is never closed: {d0}");
    let notes = d0["notes"].as_array().expect("`notes` is always an array");
    assert!(!notes.is_empty(), "a note shows which declaration's body it is: {d0}");
    let mentions = |n: &Value| n["message"].as_str().unwrap_or("").contains("unclosed") || n["span"]["line"] == 1;
    assert!(notes.iter().any(mentions), "a note names `unclosed` or points at its line: {notes:?}");
}
