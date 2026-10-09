//! `onsa fmt` with several files and the diagnostics `fmt` and `diff --ast`
//! report for a file they do not take (`docs/onsa-tools.md` §3.1, W3-02/b 1 and 2).
//!
//! `docs/onsa-tools.md` §3.1: with several files, one file's error does not stop `fmt`: every
//! file is processed, only those without a syntax diagnostic are written, and
//! every diagnostic is reported. A file `fmt` refuses for a syntax diagnostic
//! reports it, even when a diagnostic of a later stage (E0320) comes first in
//! the same item (S-214).
//!
//! W3-03/t: the diagnostics of `fmt` go to the standard output (`docs/onsa-tools.md` §4, S-232),
//! not to the standard error as they did. Two tests that checked the standard error now check
//! the standard output; `the_syntax_diagnostic_that_stops_fmt_is_reported` waits for W3-03 as a
//! whole (`#[ignore]`), and the stream check of the first test is a test of its own. More cases of
//! the report are in `syntax_units.rs`.

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_fmt_many_{}_{tag}", std::process::id()));
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

const UGLY_A: &str = "fn  a( ) -> I32 {\n 1\n}\n";
const UGLY_C: &str = "fn  c( ) -> I32 {\n 3\n}\n";
const BAD: &str = "fn b() -> I32 {\n  let a = 1;\n a\n}\n";

#[test]
fn a_syntax_error_in_the_middle_does_not_stop_the_other_files() {
    let d = Dir::new("middle");
    let a = d.file("a.onsa", UGLY_A);
    let b = d.file("b.onsa", BAD);
    let c = d.file("c.onsa", UGLY_C);
    let out = onsa(&["fmt", &a, &b, &c]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(read(&a), "fn a() -> I32 {\n  1\n}\n", "the file before the error is formatted");
    assert_eq!(read(&c), "fn c() -> I32 {\n  3\n}\n", "the file after the error is formatted");
    assert_eq!(read(&b), BAD, "the file with the error is not written");
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("E0020")
            || String::from_utf8_lossy(&out.stderr).contains("E0020"),
        "its diagnostic is reported: {out:?}"
    );
}

#[test]
fn the_diagnostic_of_the_file_with_the_error_is_on_the_standard_output() {
    // S-232: a diagnostic goes to the standard output, in `fmt` too (it went to the standard error).
    let d = Dir::new("middle_stream");
    let a = d.file("a.onsa", UGLY_A);
    let b = d.file("b.onsa", BAD);
    let out = onsa(&["fmt", &a, &b]);
    assert_eq!(code(&out), 2, "{out:?}");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("b.onsa") && stdout.contains("error[E0020]"), "on the standard output: {out:?}");
    assert!(!String::from_utf8_lossy(&out.stderr).contains("E0020"), "not on the standard error: {out:?}");
}

#[test]
fn fmt_check_reports_every_file_and_writes_none() {
    let d = Dir::new("check");
    let a = d.file("a.onsa", UGLY_A);
    let b = d.file("b.onsa", BAD);
    let c = d.file("c.onsa", UGLY_C);
    let out = onsa(&["fmt", "--check", &a, &b, &c]);
    assert_eq!(code(&out), 2, "{out:?}");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("a.onsa") && stdout.contains("c.onsa"), "both other files are named: {stdout}");
    assert_eq!((read(&a), read(&b), read(&c)), (UGLY_A.into(), BAD.into(), UGLY_C.into()));
}

#[test]
fn an_unreadable_file_does_not_stop_the_others() {
    let d = Dir::new("missing");
    let a = d.file("a.onsa", UGLY_A);
    let missing = d.0.join("missing.onsa").to_string_lossy().into_owned();
    let c = d.file("c.onsa", UGLY_C);
    let out = onsa(&["fmt", &a, &missing, &c]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(read(&a), "fn a() -> I32 {\n  1\n}\n");
    assert_eq!(read(&c), "fn c() -> I32 {\n  3\n}\n");
}

#[test]
fn the_syntax_diagnostic_that_stops_fmt_is_reported() {
    // E0010 stops `fmt`, and is the diagnostic of the unit even though the E0320 comes earlier in
    // the text (S-214: the earlier stage wins). The report is on the standard output (S-232).
    let d = Dir::new("hidden");
    let src = "fn f(badName: I32) -> I32 {\n  1 + 2 % 3\n}\n";
    let p = d.file("hide.onsa", src);
    let out = onsa(&["fmt", &p]);
    assert_eq!(read(&p), src);
    let report = String::from_utf8_lossy(&out.stdout);
    assert!(report.contains("E0010"), "the diagnostic that stops fmt, on the standard output: {out:?}");
    assert!(!report.contains("E0320"), "the heading's naming error is not reported for a unit with a syntax error");
    assert!(!String::from_utf8_lossy(&out.stderr).contains("E0010"), "not on the standard error: {out:?}");
    let other = d.file("other.onsa", src);
    let diff = onsa(&["diff", "--ast", &p, &other]);
    assert_eq!(code(&diff), 2, "{diff:?}");
    let text = String::from_utf8_lossy(&diff.stdout);
    assert_eq!(text.matches("E0010").count(), 2, "both files are reported: {text}");
}
