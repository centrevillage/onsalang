//! `onsa fmt` and `onsa diff --ast` on a file the parser failed on (spec §18.2, R-146, S-120).
//!
//! §18.2: `fmt` does not rewrite a file with a diagnostic of the lexer or the parser, and
//! `diff --ast` does not compare it. R-146: the parser also fails an item with a diagnostic that is
//! not E00xx (the overflowing tuple index `t.99999999999` is E0408), and then `fmt` must not write
//! the file without that item. S-214 (decided 2026-10-08): `fmt` and `diff --ast` stop at a
//! diagnostic of the syntax stage whatever its code, with the exit code 2, so the tests for the E0408
//! file check the exit code 2 as well as the unchanged file (W3-03/t tightened the `assert_ne!`
//! checks that said "open"). More codes are in `syntax_units.rs`.

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_fmt_syntax_{}_{tag}", std::process::id()));
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

/// `f` fails in the parser with E0408 (the index does not fit); `g` is fine and badly spaced.
const TUPLE_INDEX_OVERFLOW: &str = "\
pub fn f(t: (I32, I32)) -> I32 {
  t.99999999999
}

pub fn g()->I32{
  2
}
";

/// `f` is a syntax error (E0002); `g` is fine and badly spaced.
const SYNTAX_ERROR: &str = "\
pub fn f( {
  1
}

pub fn g()->I32{
  2
}
";

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

#[test]
fn the_fixture_fails_in_the_parser_with_a_code_that_is_not_e00xx() {
    // The premise of the R-146 tests: the parser fails `f` with E0408, which is not E00xx.
    let d = Dir::new("premise");
    let path = d.file("overflow.onsa", TUPLE_INDEX_OVERFLOW);
    let out = onsa(&["check", "--json", &path]);
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("\"E0408\""), "expected an E0408 for `t.99999999999`: {text}");
}

#[test]
fn fmt_leaves_a_file_with_a_failed_item_as_it_is() {
    let d = Dir::new("fmt_failed_item");
    let path = d.file("overflow.onsa", TUPLE_INDEX_OVERFLOW);
    let out = onsa(&["fmt", &path]);
    assert_eq!(read(&path), TUPLE_INDEX_OVERFLOW, "`fmt` rewrote a file the parser failed an item of");
    assert_eq!(code(&out), 2, "{out:?}");
}

#[test]
fn fmt_check_does_not_write_and_does_not_call_the_file_formatted() {
    let d = Dir::new("fmt_check_failed_item");
    let path = d.file("overflow.onsa", TUPLE_INDEX_OVERFLOW);
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(read(&path), TUPLE_INDEX_OVERFLOW);
    assert_eq!(code(&out), 2, "`fmt --check` on a file the syntax stage fails: {out:?}");
}

#[test]
fn fmt_leaves_a_file_with_a_syntax_error_as_it_is_and_exits_with_2() {
    // §18.2: a diagnostic of the lexer or the parser (E00xx) stops `fmt`; exit code 2.
    let d = Dir::new("fmt_syntax_error");
    let path = d.file("syntax.onsa", SYNTAX_ERROR);
    let out = onsa(&["fmt", &path]);
    assert_eq!(read(&path), SYNTAX_ERROR, "`fmt` rewrote a file with a syntax error");
    assert_eq!(code(&out), 2, "{out:?}");
}

#[test]
fn fmt_still_formats_a_file_with_a_naming_error() {
    // §18.2: the diagnostics that are not of the lexer or the parser (E0320 here) do not stop `fmt`.
    let d = Dir::new("fmt_naming");
    let path = d.file("naming.onsa", "pub fn BadName()->I32{\n  1\n}\n");
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let after = read(&path);
    assert_ne!(after, "pub fn BadName()->I32{\n  1\n}\n", "not formatted");
    assert!(after.contains("BadName() -> I32"), "{after:?}");
    let again = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&again), 0, "the result is not a fixed point: {again:?}");
}

#[test]
fn diff_ast_does_not_report_two_files_with_failed_items_as_equal() {
    // Both files lose `f` in the AST; the text of `f` differs. Equal ASTs would say "no difference".
    let d = Dir::new("diff_failed_items");
    let a = d.file("a.onsa", TUPLE_INDEX_OVERFLOW);
    let b = d.file("b.onsa", &TUPLE_INDEX_OVERFLOW.replace("99999999999", "88888888888"));
    let out = onsa(&["diff", "--ast", &a, &b]);
    assert_eq!(code(&out), 2, "`diff --ast` on files the syntax stage fails: {out:?}");
}

#[test]
fn diff_ast_does_not_compare_a_file_with_a_syntax_error_and_exits_with_2() {
    // §18.2: `diff --ast` does not compare a file with a syntax diagnostic; exit code 2.
    let d = Dir::new("diff_syntax_error");
    let a = d.file("a.onsa", SYNTAX_ERROR);
    let b = d.file("b.onsa", &SYNTAX_ERROR.replace("1\n", "3\n"));
    let out = onsa(&["diff", "--ast", &a, &b]);
    assert_eq!(code(&out), 2, "{out:?}");
}
