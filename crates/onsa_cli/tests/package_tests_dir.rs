//! The `tests/` directly under the package root has no role in this version (spec §19.1): a `.onsa`
//! file below it is E0200 at the top of the file, one per file, in every command that gathers the
//! modules, and is not dropped without a word. A file that is not `.onsa` is not read. A `tests/`
//! deeper than the root is an ordinary directory of modules (spec §15.1, §19.1, §18.1; S-96, R-122;
//! W4-14 U2).
//!
//! What the spec fixes, and so what is checked here:
//! - every `.onsa` file below the root `tests/` (at any depth) is one E0200, at line 1 column 1 of the
//!   file, named by the path from the root; the message names the feature (the `tests/` of the
//!   package); `check`, `test` and `build` report the same, `test` runs nothing;
//! - the same holds when such a file is passed by its path (the manifest above it), while the
//!   diagnostics of `check m.onsa` are those of `m.onsa` only (spec §15.1) and `test m.onsa` prints all
//!   the diagnostics that stop it (spec §18.2);
//! - it holds whatever the file holds, and beside the errors of the other modules;
//! - `tests/` deeper than the root (`dsp/tests/n.onsa`) is the module `dsp.tests.n`, with its tests run;
//! - files that are not `.onsa` under the root `tests/` are not read; without a manifest above, `tests/`
//!   is an ordinary directory.
//!
//! Not written here: a `tests/` that has its own `onsa.toml` (a nested package, `package_tree.rs`),
//! the other modules' naming (`package_naming.rs`), the range of `onsa test` (W4-15).
//!
//! Every test here runs (W4-14 U2 took the last ignores out).

mod test_support;

use std::path::Path;

use serde_json::Value;
use test_support::*;

const OK_FN: &str = "pub fn f() -> I32 {\n  1\n}\n";
const OK_TEST: &str = "pub fn f() -> I32 {\n  1\n}\n\ntest \"inline\" {\n  assert f() == 1\n}\n";
/// A file as the Rust habit writes an integration test; the failing test and the `use` are valid.
const API_TEST: &str = "use m.{f}\n\ntest \"from tests dir\" {\n  assert f() == 2\n}\n";
const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// The three files below the root `tests/`, in the order of the file strings (code point order).
const ROOT_TESTS_FILES: [&str; 3] = ["tests/api.onsa", "tests/helpers/deeper/more.onsa", "tests/helpers/util.onsa"];

fn check_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

/// `(code, file, line, col)` of every diagnostic, in the order of the document.
fn places(doc: &Value) -> Vec<(String, String, u64, u64)> {
    diagnostics(doc)
        .iter()
        .map(|d| {
            let sp = span_of(&d["span"]);
            (str_of(d, "code").to_string(), sp.file, sp.line, sp.col)
        })
        .collect()
}

fn e0200_at(file: &str) -> (String, String, u64, u64) {
    ("E0200".to_string(), file.to_string(), 1, 1)
}

fn all_e0200() -> Vec<(String, String, u64, u64)> {
    ROOT_TESTS_FILES.iter().map(|f| e0200_at(f)).collect()
}

/// A package with a module of its own, the three files under the root `tests/`, files that are not
/// `.onsa` there, and a `tests/` deeper than the root.
fn package_with_root_tests(tag: &str, manifest: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    d.write("m.onsa", OK_TEST);
    d.write("tests/api.onsa", API_TEST);
    d.write("tests/helpers/util.onsa", OK_FN);
    d.write("tests/helpers/deeper/more.onsa", OK_FN);
    d.write("tests/notes.md", "this ((( is not onsa\n");
    d.write("tests/data/sample.txt", "fn broken( {\n");
    d.write("dsp/tests/n.onsa", "pub fn nf() -> I32 {\n  2\n}\n\ntest \"nested\" {\n  assert nf() == 2\n}\n");
    d
}

const PLAIN_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n";

// ---- check, test and build -------------------------------------------------------------------------

/// §15.1, §19.1: every `.onsa` file below the root `tests/` is one E0200 at the top, in the order of
/// the file strings, and nothing else is reported (the files that are not `.onsa` are not read, and
/// `dsp/tests/n.onsa` is an ordinary module). The message names the feature.
#[test]
fn every_onsa_file_under_the_root_tests_dir_is_one_e0200_at_the_top_of_the_file() {
    let d = package_with_root_tests("root_tests", PLAIN_MANIFEST);
    let dir = d.arg();
    for (cwd, args) in [
        (d.root().to_path_buf(), vec![]),
        (d.root().to_path_buf(), vec!["."]),
        (d.root().join("dsp"), vec![dir.as_str()]),
    ] {
        let (out, doc) = check_json(&cwd, &args);
        assert_eq!(out.code, 1, "{args:?} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), all_e0200(), "{args:?} from {cwd:?}: {doc}");
        for dg in diagnostics(&doc) {
            assert!(str_of(dg, "message").contains("tests/"), "the message names the feature: {dg}");
        }
    }
}

/// §15.1: with no path, the command searches upwards from the working directory, so run inside
/// `tests/` it still finds the manifest above and reports the files by their path from the root.
#[test]
fn the_e0200_is_found_from_a_working_directory_inside_tests() {
    let d = package_with_root_tests("root_tests_cwd", PLAIN_MANIFEST);
    let (out, doc) = check_json(&d.root().join("tests/helpers"), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), all_e0200(), "{doc}");
}

/// §18.2, §19.1: `test` and `build` gather the modules the same way, so they report the same E0200
/// and stop: `test` runs nothing (an empty `tests` with `--json`).
#[test]
fn test_and_build_report_the_same_e0200_and_run_nothing() {
    let d = package_with_root_tests("root_tests_cmds", BUILD_MANIFEST);
    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), all_e0200(), "{doc}");
    assert!(tests_of(&doc).is_empty(), "nothing is run: {doc}");

    let want: Vec<String> = ROOT_TESTS_FILES.iter().map(|f| format!("{f}:1:1: error[E0200]: ")).collect();
    let out = run(d.root(), &["test"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    for w in &want {
        assert!(out.stdout.lines().any(|l| l.starts_with(w.as_str())), "test: {w:?} in {}", out.stdout);
    }
    assert!(result_lines(&out).is_empty(), "no test result line: {}", out.stdout);

    let out = run(d.root(), &["build", "--target", "host"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    for w in &want {
        assert!(out.stdout.lines().any(|l| l.starts_with(w.as_str())), "build: {w:?} in {}", out.stdout);
    }
}

// ---- a file passed by its path ---------------------------------------------------------------------

/// §15.1, S-96: a file below the root `tests/` that is passed by its path (the manifest above it) is
/// E0200 as well, at any depth; the diagnostics of `check` are those of the passed file only, so a file
/// outside `tests/` is clean and so is a file of a deeper `tests/`.
#[test]
fn a_file_passed_under_the_root_tests_dir_is_e0200_and_the_other_files_print_nothing() {
    let d = package_with_root_tests("root_tests_file", PLAIN_MANIFEST);
    for file in ROOT_TESTS_FILES {
        let (out, doc) = check_json(d.root(), &[file]);
        assert_eq!(out.code, 1, "{file}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), [e0200_at(file)], "{file}: {doc}");
    }
    for file in ["m.onsa", "dsp/tests/n.onsa"] {
        let (out, doc) = check_json(d.root(), &[file]);
        assert_eq!(out.code, 0, "{file}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{file}: {doc}");
    }
}

/// §18.2: the diagnostic that stops `test` is printed whatever file was passed, so `test m.onsa` prints
/// the three E0200 and runs nothing.
#[test]
fn test_with_a_file_prints_all_the_e0200_that_stop_it() {
    let d = package_with_root_tests("root_tests_test_file", PLAIN_MANIFEST);
    let (out, doc) = test_json(d.root(), &["m.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), all_e0200(), "{doc}");
    assert!(tests_of(&doc).is_empty(), "nothing is run: {doc}");
}

// ---- what the file holds, and the other modules ----------------------------------------------------

/// §15.1: the file is E0200 whatever it holds (an error in the syntax is not what is reported for a
/// module that is not read); the other diagnostics of the file are not fixed, so only the E0200 is
/// looked for.
#[test]
fn the_e0200_is_reported_whatever_the_file_holds() {
    let d = Dir::pkg("root_tests_broken");
    d.write("m.onsa", OK_FN);
    d.write("tests/api.onsa", "use m.{f}\n\ntest \"fails\" {\n  assert f() == 5\n}\n\nfn broken( {\n");
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(places(&doc).contains(&e0200_at("tests/api.onsa")), "{doc}");
}

/// §15.1, §18.1: the E0200 is one diagnostic beside the others, in the order of the file strings: the
/// error of `m.onsa` (an E0302 at line 2) comes first and `tests/api.onsa` follows.
#[test]
fn the_e0200_is_reported_beside_the_errors_of_the_other_modules() {
    let d = Dir::pkg("root_tests_beside");
    d.write("m.onsa", "pub fn g() -> I32 {\n  zzz\n}\n");
    d.write("tests/api.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let got = places(&doc);
    assert_eq!(got.len(), 2, "{doc}");
    assert_eq!((got[0].0.as_str(), got[0].1.as_str(), got[0].2), ("E0302", "m.onsa", 2), "{doc}");
    assert_eq!(got[1], e0200_at("tests/api.onsa"), "{doc}");
}

// ---- the tests/ that is not the root one -----------------------------------------------------------

/// §15.1: a `tests/` deeper than the root is an ordinary directory of modules: `dsp/tests/n.onsa` is the
/// module `dsp.tests.n`, whose test is run, beside the test of `m`. The records are in the order of the
/// module strings.
#[test]
fn a_tests_dir_deeper_than_the_root_is_an_ordinary_directory_of_modules() {
    let d = Dir::pkg("deep_tests");
    d.write("m.onsa", OK_TEST);
    d.write("dsp/tests/n.onsa", "pub fn nf() -> I32 {\n  2\n}\n\ntest \"nested\" {\n  assert nf() == 2\n}\n");
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let (out, doc) = check_json(d.root(), &["dsp/tests/n.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        identities(&doc),
        [("dsp.tests.n".to_string(), "nested".to_string()), ("m".to_string(), "inline".to_string())]
    );
}

/// §15.1: only `.onsa` files are read, so a root `tests/` that holds no `.onsa` file (notes, data) gives
/// no diagnostic.
#[test]
fn a_root_tests_dir_with_no_onsa_file_is_not_read() {
    let d = Dir::pkg("root_tests_data");
    d.write("m.onsa", OK_FN);
    d.write("tests/notes.md", "this ((( is not onsa\n");
    d.write("tests/data/sample.txt", "fn broken( {\n");
    d.write("tests/data/table.csv", "a,b\n1,2\n");
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// §15.1: the rule is about the `tests/` of the root of a package. A file with no manifest above it is a
/// package of its own, so a directory named `tests` there is an ordinary directory.
#[test]
fn without_a_manifest_the_tests_dir_is_an_ordinary_directory() {
    let d = Dir::bare("root_tests_bare");
    d.write("tests/api.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &["tests/api.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- the naming rule is not applied below the root `tests/` (S-643) --------------------------------

/// §15.1, §2.3, S-643: the files below the root `tests/` are not modules, so the naming rule is not applied
/// to their names or to the names of the directories above them: `tests/My-File.onsa` and
/// `tests/Bad-Dir/x.onsa` are E0200 and nothing else, and so is `tests/tests/x.onsa` (a `tests/` below the
/// root `tests/`). A name that starts with `.` is not gathered, so `tests/.x.onsa` is not reported for the
/// package, and passed by its path it is E0200 only (no E0320 for the leading `.`).
#[test]
fn the_names_below_the_root_tests_dir_are_not_checked_by_the_naming_rule() {
    let d = Dir::pkg("root_tests_names");
    d.write("m.onsa", OK_FN);
    for file in
        ["tests/My-File.onsa", "tests/Bad-Dir/x.onsa", "tests/tests/x.onsa", "tests/.x.onsa", "tests/.hid/y.onsa"]
    {
        d.write(file, OK_FN);
    }
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        places(&doc),
        [e0200_at("tests/Bad-Dir/x.onsa"), e0200_at("tests/My-File.onsa"), e0200_at("tests/tests/x.onsa")],
        "{doc}"
    );
    for file in
        ["tests/My-File.onsa", "tests/Bad-Dir/x.onsa", "tests/tests/x.onsa", "tests/.x.onsa", "tests/.hid/y.onsa"]
    {
        let (out, doc) = check_json(d.root(), &[file]);
        assert_eq!(out.code, 1, "{file}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), [e0200_at(file)], "{file}: {doc}");
    }
}
