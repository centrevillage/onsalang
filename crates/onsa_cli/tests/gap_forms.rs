//! Spaces and line breaks of §2.5 that a case file of `tests/spec/` cannot hold, because the runner also
//! asks that a case without a syntax error is in the normal form of `onsa fmt` (W3-06/t2).
//!
//! - R-203 (S-89, S-399): `onsa fmt` does not write a file with a space before a call or an index
//!   (`let v = g(x) (y)`, `[(1, 2) (3, 4)]`): a diagnostic of the syntax stage stops it, exit code 2, the
//!   file as it was (§18.2). It used to write `g(x)(y)`, which is an E0020 of its own. The right forms
//!   (`g(x).(y)`, `[(1, 2), (3, 4)]`) pass `fmt` and the output passes `check`.
//! - S-374: `:`, `=>`, `as` and `at` have no rule of placement; inside lists a line break before or after
//!   them is a space (`fmt` joins the line, so no case file can hold them).
//! - S-400: the `lib"m"` in the heading of an `extern` block is read by the heading's grammar, not as a name
//!   touching a string (an E0002).
//!

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_gap_forms_{}_{tag}", std::process::id()));
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

/// The codes of the diagnostics `check --json` reports for `path`.
fn codes(path: &str) -> Vec<String> {
    let out = onsa(&["check", "--json", path]);
    let text = stdout(&out);
    let mut found = Vec::new();
    let mut rest = text.as_str();
    while let Some(i) = rest.find("\"code\": \"") {
        rest = &rest[i + 9..];
        let end = rest.find('"').unwrap();
        found.push(rest[..end].to_string());
    }
    found
}

const CALL_OF_A_CALL: &str = "\
pub fn inc(y: I32) -> I32 {
  y + 1
}

pub fn g(x: I32) -> fn(I32) -> I32 {
  inc
}

pub fn f(x: I32, y: I32) -> I32 {
  let v = g(x) (y)
  v
}
";

const TUPLE_AFTER_TUPLE: &str = "\
pub fn f() -> I32 {
  let v = [(1, 2) (3, 4)]
  v[0].0
}
";

const RIGHT_FORMS: &str = "\
pub fn inc(y: I32) -> I32 {
  y + 1
}

pub fn g(x: I32) -> fn(I32) -> I32 {
  inc
}

pub fn f(x: I32, y: I32) -> I32 {
  let v = g(x).(y)
  let w = [(1, 2), (3, 4)]
  v + w[0].0
}
";

#[test]
fn fmt_does_not_write_a_call_of_a_call_with_a_space() {
    // R-203 (S-89, S-399): the space before the `(` of `g(x) (y)` stops `fmt` (exit 2); the file is as it was.
    let d = Dir::new("call_of_call");
    let path = d.file("a.onsa", CALL_OF_A_CALL);
    let out = onsa(&["fmt", &path]);
    assert_eq!(read(&path), CALL_OF_A_CALL, "`fmt` rewrote a file whose `g(x) (y)` is a syntax error");
    assert_eq!(code(&out), 2, "{out:?}");
    assert!(stdout(&out).contains("E0002"), "the diagnostic of `g(x) (y)` is an E0002: {out:?}");
}

#[test]
fn check_reports_a_call_of_a_call_with_a_space_as_a_syntax_error() {
    let d = Dir::new("call_of_call_check");
    let path = d.file("a.onsa", CALL_OF_A_CALL);
    assert_eq!(codes(&path), vec!["E0002".to_string()]);
}

#[test]
fn fmt_does_not_write_a_tuple_after_a_tuple_in_an_array() {
    // `[(1, 2) (3, 4)]` is a missing `,` (S-399); `fmt` used to write `[(1, 2)(3, 4)]`.
    let d = Dir::new("tuple_after_tuple");
    let path = d.file("a.onsa", TUPLE_AFTER_TUPLE);
    let out = onsa(&["fmt", &path]);
    assert_eq!(read(&path), TUPLE_AFTER_TUPLE);
    assert_eq!(code(&out), 2, "{out:?}");
}

#[test]
fn fmt_does_not_write_a_file_with_a_space_before_an_opener() {
    // S-89: a space before the `(` or `[` of a call, an index, a declaration, a type and a pattern is a
    // diagnostic of the syntax stage, so `fmt` stops (exit 2) and writes nothing.
    let forms = [
        "pub fn f(x: I32) -> I32 {\n  x\n}\n\npub fn g(x: I32) -> I32 {\n  f (x)\n}\n",
        "pub fn g(xs: [I32; 4]) -> I32 {\n  xs [0]\n}\n",
        "pub fn f (x: I32) -> I32 {\n  x\n}\n",
        "pub fn f(o: Option [I32]) -> I32 {\n  0\n}\n",
        "pub fn f(o: Option[I32]) -> I32 {\n  match o {\n    Some (x) => x,\n    None => 0,\n  }\n}\n",
    ];
    for (i, text) in forms.iter().enumerate() {
        let d = Dir::new(&format!("opener_{i}"));
        let path = d.file("a.onsa", text);
        let out = onsa(&["fmt", &path]);
        assert_eq!(read(&path), *text, "form {i}: `fmt` rewrote a file with a space before an opener");
        assert_eq!(code(&out), 2, "form {i}: {out:?}");
    }
}

#[test]
fn the_right_forms_pass_fmt_and_the_output_passes_check() {
    // R-203: `g(x).(y)` and `[(1, 2), (3, 4)]` are the right forms; `fmt` keeps them and `check` finds no
    // syntax error in the output.
    let d = Dir::new("right_forms");
    let path = d.file("a.onsa", RIGHT_FORMS);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let after = read(&path);
    assert!(after.contains("g(x).(y)"), "{after}");
    assert!(after.contains("[(1, 2), (3, 4)]"), "{after}");
    let bad: Vec<String> = codes(&path).into_iter().filter(|c| c == "E0002" || c == "E0020").collect();
    assert!(bad.is_empty(), "the output of `fmt` has syntax diagnostics {bad:?}:\n{after}");
}

#[test]
fn a_line_break_around_a_colon_an_arrow_an_as_and_an_at_is_a_space_in_a_list() {
    // S-374 and §2.5: no rule of placement for `:`, `=>`, `as` and `at`; inside parentheses, brackets, a
    // struct literal and the arms of a `match` the line break is a space.
    let text = "\
pub struct Pt {
  x: I32,
  y: I32,
}

pub fn two(a: I32, b: I32) -> I32 {
  a + b
}

pub fn colon_before(a: I32) -> Pt {
  Pt { x
    : a, y: 2 }
}

pub fn colon_after(a: I32) -> Pt {
  Pt { x:
    a, y: 2 }
}

pub fn arrow_before(o: Option[I32]) -> I32 {
  match o {
    Some(v)
      => v,
    None => 0,
  }
}

pub fn arrow_after(o: Option[I32]) -> I32 {
  match o {
    Some(v) =>
      v,
    None =>
      0,
  }
}

pub fn as_before(a: I32) -> I64 {
  two(a
    as I32, 1) as I64
}

pub fn as_after(a: I32) -> I64 {
  (a as
    I64)
}

pub flow at_before(
  x: F32
    at sample,
) -> F32 at sample {
  x
}

pub flow at_after(
  x: F32 at
    sample,
) -> F32 at sample {
  x
}

pub fn parameter_colon(a
  : I32, b: I32) -> I32 {
  a + b
}
";
    let d = Dir::new("lists_around_tokens");
    let path = d.file("a.onsa", text);
    let found = codes(&path);
    assert!(found.is_empty(), "diagnostics for forms that have no rule of placement: {found:?}");
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
}

#[test]
fn the_lib_in_the_heading_of_an_extern_block_may_touch_its_string() {
    // S-400: `lib"m"` is read by the heading's grammar; it is not a name touching a string (an E0002).
    let text = "\
extern \"C\" lib\"m\" {
  rt fn cos(x: F64) -> F64
}
";
    let d = Dir::new("extern_lib");
    let path = d.file("a.onsa", text);
    let found = codes(&path);
    assert!(!found.iter().any(|c| c == "E0002"), "`lib\"m\"` is read as a name touching a string: {found:?}");
}
