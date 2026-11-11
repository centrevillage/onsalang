//! `onsa fmt` with several files and the diagnostics `fmt` and `diff --ast`
//! report for a file they do not take (`spec/tools.md` §3.1, W3-02/b 1 and 2).
//!
//! `spec/tools.md` §3.1: with several files, one file's error does not stop `fmt`: every
//! file is processed, only those without a syntax diagnostic are written, and
//! every diagnostic is reported. A file `fmt` refuses for a syntax diagnostic
//! reports it, even when a diagnostic of a later stage (E0320) comes first in
//! the same item (S-214).
//!
//! W3-03/t: the diagnostics of `fmt` go to the standard output (`spec/tools.md` §4, S-232),
//! not to the standard error as they did. Two tests that checked the standard error now check
//! the standard output; `the_syntax_diagnostic_that_stops_fmt_is_reported` waits for W3-03 as a
//! whole (`#[ignore]`), and the stream check of the first test is a test of its own. More cases of
//! the report are in `syntax_units.rs`.
//!
//! W5-24 U8 (S-599, `spec/tools.md` §3.1): a directory among the paths is an io error as a file that cannot be read
//! is (exit code 2, a sentence on the standard error), and the other paths are processed; no path is a usage error.

use crate::test_support::{Dir, code, onsa};

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

const UGLY_A: &str = "fn  a( ) -> I32 {\n 1\n}\n";
const UGLY_C: &str = "fn  c( ) -> I32 {\n 3\n}\n";
const BAD: &str = "fn b() -> I32 {\n  let a = 1;\n a\n}\n";

#[test]
fn a_syntax_error_in_the_middle_does_not_stop_the_other_files() {
    let d = Dir::bare("middle");
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
    let d = Dir::bare("middle_stream");
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
    let d = Dir::bare("check");
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
    let d = Dir::bare("missing");
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
    let d = Dir::bare("hidden");
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

// ---- a directory among the paths (S-599, W5-24 U8) -----------------------------------------------------

/// The standard error of a run, in lower case.
fn stderr_lower(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).to_lowercase()
}

#[test]
fn a_directory_among_the_paths_is_an_io_error_and_the_other_files_are_processed() {
    // S-599, §3.1: `onsa fmt` takes files. A directory is an io error as a file that cannot be read is
    // (exit code 2, a sentence on the standard error, not a diagnostic), and the other files are processed,
    // whether the directory comes before them or after them. The files in the directory are not touched
    // (`fmt` does not take the files of a package).
    let d = Dir::bare("dir_among");
    let a = d.file("a.onsa", UGLY_A);
    let c = d.file("c.onsa", UGLY_C);
    d.write("pkgdir/inner.onsa", UGLY_A);
    let sub = d.path("pkgdir");

    let before = onsa(&["fmt", &sub, &a]);
    assert_eq!(code(&before), 2, "{before:?}");
    assert_eq!(read(&a), "fn a() -> I32 {\n  1\n}\n", "the file after the directory is formatted");
    let err = stderr_lower(&before);
    assert!(err.contains("file"), "the sentence says that `onsa fmt` takes files: {err}");
    assert!(!String::from_utf8_lossy(&before.stdout).contains("pkgdir"), "not on the standard output: {before:?}");

    let after = onsa(&["fmt", &c, &sub]);
    assert_eq!(code(&after), 2, "{after:?}");
    assert_eq!(read(&c), "fn c() -> I32 {\n  3\n}\n", "the file before the directory is formatted");
    assert!(stderr_lower(&after).contains("file"), "{after:?}");

    assert_eq!(read(&d.path("pkgdir/inner.onsa")), UGLY_A, "the files in the directory are not touched");
}

#[test]
fn a_directory_between_files_and_a_syntax_error_do_not_stop_each_other() {
    // S-599, §3.1: every path is processed; the directory is the io error, the file with the error is
    // refused (its diagnostic is on the standard output), the others are written.
    let d = Dir::bare("dir_between");
    let a = d.file("a.onsa", UGLY_A);
    let b = d.file("b.onsa", BAD);
    let c = d.file("c.onsa", UGLY_C);
    std::fs::create_dir_all(d.path("pkgdir")).unwrap();
    let sub = d.path("pkgdir");
    let out = onsa(&["fmt", &a, &sub, &b, &c]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(read(&a), "fn a() -> I32 {\n  1\n}\n");
    assert_eq!(read(&c), "fn c() -> I32 {\n  3\n}\n");
    assert_eq!(read(&b), BAD, "the file with the error is not written");
    assert!(String::from_utf8_lossy(&out.stdout).contains("E0020"), "its diagnostic is reported: {out:?}");
    assert!(stderr_lower(&out).contains("file"), "the sentence about the directory: {out:?}");
}

#[test]
fn a_directory_alone_and_a_directory_with_check_end_with_2() {
    // S-599, §3.1, §18.2: the directory alone is the io error (2); with `--check` the other files are
    // reported and none is written, and the exit code is 2 (the command could not work on a path).
    let d = Dir::bare("dir_alone");
    let a = d.file("a.onsa", UGLY_A);
    std::fs::create_dir_all(d.path("pkgdir")).unwrap();
    let sub = d.path("pkgdir");

    let alone = onsa(&["fmt", &sub]);
    assert_eq!(code(&alone), 2, "{alone:?}");
    assert!(stderr_lower(&alone).contains("file"), "{alone:?}");

    let check = onsa(&["fmt", "--check", &sub, &a]);
    assert_eq!(code(&check), 2, "{check:?}");
    assert!(String::from_utf8_lossy(&check.stdout).contains("a.onsa"), "the other file is reported: {check:?}");
    assert_eq!(read(&a), UGLY_A, "`--check` writes nothing");
    assert!(stderr_lower(&check).contains("file"), "{check:?}");
}

#[test]
fn a_directory_that_may_not_be_read_is_named_as_a_directory() {
    // S-599, §3.1: a directory without the permission to read it fails to open with another error, and is
    // still the io error of a directory (2), and the other file is processed. `Dir` gives the permissions
    // back when it is dropped, also after a failed assertion.
    use std::os::unix::fs::PermissionsExt;
    let d = Dir::bare("dir_no_permission");
    let a = d.file("a.onsa", UGLY_A);
    let sub = d.path("closed");
    std::fs::create_dir_all(&sub).unwrap();
    std::fs::set_permissions(&sub, std::fs::Permissions::from_mode(0o000)).unwrap();
    let out = onsa(&["fmt", &sub, &a]);
    std::fs::set_permissions(&sub, std::fs::Permissions::from_mode(0o755)).unwrap();
    assert_eq!(code(&out), 2, "{out:?}");
    assert!(stderr_lower(&out).contains("is a directory"), "{out:?}");
    assert_ne!(read(&a), UGLY_A, "the other file is written");
}

#[test]
fn no_path_is_a_usage_error_and_writes_nothing() {
    // S-599, §3.1, §18.2: `onsa fmt` and `onsa fmt --check` without a path are a usage error (2).
    let d = Dir::bare("no_path");
    let a = d.file("a.onsa", UGLY_A);
    for args in [vec!["fmt"], vec!["fmt", "--check"]] {
        let out = onsa(&args);
        assert_eq!(code(&out), 2, "onsa {args:?}: {out:?}");
        assert!(out.stdout.is_empty(), "onsa {args:?} prints no diagnostic: {out:?}");
        assert!(!out.stderr.is_empty(), "onsa {args:?} says how to use it: {out:?}");
    }
    assert_eq!(read(&a), UGLY_A);
}
