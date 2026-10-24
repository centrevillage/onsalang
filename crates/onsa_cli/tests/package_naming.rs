//! The names of the files and directories of a package are module names, so they follow the rule of
//! §2.3: `snake_case`, an identifier (ASCII letters, digits and `_`, no leading digit, no `__`).
//! A file name that breaks it is E0320 at the top of the file (line 1, column 1), with no
//! candidate (renaming a file is not a text edit) and a note that says `snake_case`. A directory in
//! the path of a module is checked the same way: one E0320 per directory, at the top of the first
//! `.onsa` file below it in the order of the diagnostics, with no candidate. Neither enters the unit
//! of a declaration, so they are reported beside the diagnostics inside the file. A name that is a
//! keyword (`match.onsa`, `test/`) follows the rule (spec §2.3, §15.1, §18.1; S-300, S-313, S-325,
//! R-46; W4-14 U2).
//!
//! What the spec fixes, and so what is checked here:
//! - the name of a file with no manifest above it (the file is a package of its own) and the name
//!   of a file inside a package, for names that break the rule in each of its parts: a `-` or a
//!   `.` or a space in the name, `_` alone, a leading digit, a character that is not ASCII, `__`,
//!   capitals;
//! - the names of the directories: the same set, one diagnostic per directory, the position,
//!   the order, and a directory that only holds deeper files;
//! - the names that start with `.` are not gathered (U1), but a file that is passed by its path
//!   gets the rule applied to its own name and to the `.` directories above it in the package;
//! - the commands that read the package (`test`, `build`) report the same diagnostics.
//!
//! Not written here: the tree that is gathered (`package_tree.rs`, `package_input.rs`), the
//! `tests/` of the root (`package_tests_dir.rs`), two files for one module path and an item with a
//! child module of its name (W4-03), the type parameters (cases under `tests/spec`), the form of
//! the arguments of `graph` and the like (U4, `command_paths.rs`).
//!
//! Every test here runs (W4-14 U2 took the last ignores out).

mod test_support;

use std::path::Path;

use serde_json::Value;
use test_support::*;

const OK_FN: &str = "pub fn f() -> I32 {\n  1\n}\n";
const OK_TEST: &str = "pub fn f() -> I32 {\n  1\n}\n\ntest \"t\" {\n  assert f() == 1\n}\n";
/// One E0302 at line 2.
const BAD_FN: &str = "pub fn g() -> I32 {\n  zzz\n}\n";
const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// File names that break §2.3 in each of its parts. A `-`, a `.`, a space, `_` alone, a leading
/// digit, a character that is not ASCII, `__`, a capital, a camel-case name.
const BAD_FILE_NAMES: [&str; 10] = [
    "My-File.onsa",
    "a.b.onsa",
    "a b.onsa",
    "_.onsa",
    "9x.onsa",
    "音.onsa",
    "a__b.onsa",
    "MyMod.onsa",
    "my-mod.onsa",
    "camelCase.onsa",
];

/// Directory names that break the same rule.
const BAD_DIR_NAMES: [&str; 8] = ["camelDir", "9dir", "_", "音", "a__b", "dir.name", "Mixed_Case", "my-dir"];

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

fn e0320_at(file: &str) -> (String, String, u64, u64) {
    ("E0320".to_string(), file.to_string(), 1, 1)
}

/// A diagnostic of a file or a directory name: no candidate, and a note (`snake_case` for a file name).
fn assert_no_candidate_with_note(d: &Value, snake_case_note: bool) {
    assert_eq!(array_of(d, "fixes").len(), 0, "a file or a directory name has no candidate: {d}");
    let notes = array_of(d, "notes");
    assert!(!notes.is_empty(), "the rule is shown in a note: {d}");
    if snake_case_note {
        assert!(
            notes.iter().any(|n| str_of(n, "message").contains("snake_case")),
            "a note says the file name is to be `snake_case`: {d}"
        );
    }
}

fn sorted(mut v: Vec<(String, String, u64, u64)>) -> Vec<(String, String, u64, u64)> {
    v.sort();
    v
}

// ---- the name of a single file (S-300) -------------------------------------------------------------

/// §2.3, §15.1: a file with no manifest above it is a package of one module whose name is the file
/// name, so the rule applies. The diagnostic is the only one, at the top of the file, named by the path
/// as it was passed, with no candidate and a note that says `snake_case`.
#[test]
fn a_single_file_whose_name_is_not_a_module_name_is_e0320_with_no_candidate() {
    for name in BAD_FILE_NAMES {
        let d = Dir::bare("single_bad");
        d.write(name, OK_FN);
        let (out, doc) = check_json(d.root(), &[name]);
        assert_eq!(out.code, 1, "{name}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), [e0320_at(name)], "{name}: {doc}");
        assert_no_candidate_with_note(&diagnostics(&doc)[0], true);
    }
}

/// §2.3: the names that follow the rule pass, among them the names of keywords (`match`, `test`),
/// which are written in a path as they are (§2.2), and a name with digits (`wrap01`).
#[test]
fn a_single_file_whose_name_is_a_module_name_is_fine() {
    for name in ["ok_name.onsa", "wrap01.onsa", "memory_fs.onsa", "a.onsa", "x1.onsa", "match.onsa", "test.onsa"] {
        let d = Dir::bare("single_ok");
        d.write(name, OK_FN);
        let (out, doc) = check_json(d.root(), &[name]);
        assert_eq!(out.code, 0, "{name}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{name}: {doc}");
    }
}

/// §18.1: the manifest-less input is named by the path as it was passed, with `/` for the
/// separator; the module name is the file name only, so the directory it is in is not checked.
#[test]
fn the_e0320_of_a_single_file_is_named_by_the_path_as_it_was_passed() {
    let d = Dir::bare("single_path");
    d.write("sub/My-File.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &["sub/My-File.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), [e0320_at("sub/My-File.onsa")], "{doc}");
}

/// spec/tools.md §4: the text output starts a diagnostic with `<file>:<line>:<col>: error[<code>]: `
/// on the standard output; a diagnostic is not a usage error, so nothing goes to the standard error.
#[test]
fn the_text_output_of_a_file_name_error_names_the_file_and_the_top_of_it() {
    let d = Dir::bare("single_text");
    d.write("My-File.onsa", OK_FN);
    let out = run(d.root(), &["check", "My-File.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let first = out.stdout.lines().next().unwrap_or("");
    assert!(first.starts_with("My-File.onsa:1:1: error[E0320]: "), "first line: {:?}", out.stdout);
    assert_eq!(out.stderr, "", "a diagnostic is on the standard output only");
}

// ---- the name of a file in a package (S-300) -------------------------------------------------------

/// §2.3, §15.1, §18.1: a file inside a package follows the same rule, one E0320 per file, at the top,
/// named by the path from the root. The diagnostics are in the order of the file strings (code point
/// order). The files with names that follow the rule have none.
#[test]
fn files_of_a_package_with_a_bad_name_are_e0320_one_each_in_the_order_of_the_files() {
    let d = Dir::pkg("pkg_bad_files");
    let mut expected = Vec::new();
    for name in BAD_FILE_NAMES {
        d.write(name, OK_FN);
        expected.push(e0320_at(name));
    }
    d.write("sub/Bad-Name.onsa", OK_FN);
    expected.push(e0320_at("sub/Bad-Name.onsa"));
    for name in ["ok.onsa", "match.onsa", "wrap01.onsa", "sub/ok_name.onsa"] {
        d.write(name, OK_FN);
    }
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), sorted(expected), "{doc}");
    for dg in diagnostics(&doc) {
        assert_no_candidate_with_note(dg, true);
    }
}

/// §18.1: the diagnostics of a file are only those of the file, so passing a good file does not print
/// the E0320 of another, and passing the bad one prints its own.
#[test]
fn passing_a_file_prints_the_file_name_error_of_that_file_only() {
    let d = Dir::pkg("pkg_focus");
    d.write("Bad-Name.onsa", OK_FN);
    d.write("ok.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &["ok.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let (out, doc) = check_json(d.root(), &["Bad-Name.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), [e0320_at("Bad-Name.onsa")], "{doc}");
}

/// §2.3: the E0320 of a file name does not enter the unit of a declaration, so it is reported beside
/// the error inside the file (here an E0302 at line 2), in the order of the line.
#[test]
fn the_error_of_the_file_name_is_reported_beside_the_errors_inside_the_file() {
    let d = Dir::pkg("pkg_beside");
    d.write("Bad-Name.onsa", BAD_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let got = places(&doc);
    assert_eq!(got.len(), 2, "{doc}");
    assert_eq!(&got[0], &e0320_at("Bad-Name.onsa"), "{doc}");
    assert_eq!((got[1].0.as_str(), got[1].1.as_str(), got[1].2), ("E0302", "Bad-Name.onsa", 2), "{doc}");
}

/// §2.3, §18.1: an error in the syntax of the file hides the E0320 of a name inside a declaration, but
/// the name of the file is not a declaration (it is outside the unit), so it is still reported.
#[test]
fn a_syntax_error_in_the_file_does_not_hide_the_error_of_its_name() {
    let d = Dir::pkg("pkg_syntax");
    d.write("Bad-Syntax.onsa", "pub fn broken( {\n");
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let got = places(&doc);
    assert_eq!(got.len(), 2, "{doc}");
    assert_eq!(&got[0], &e0320_at("Bad-Syntax.onsa"), "{doc}");
    assert_eq!((got[1].0.as_str(), got[1].1.as_str()), ("E0002", "Bad-Syntax.onsa"), "{doc}");
}

/// §18.2: `test` and `build` read the package the same way and stop at the same diagnostic; `test`
/// prints no result and `--json` has an empty `tests`.
#[test]
fn test_and_build_report_the_file_name_error_too() {
    let d = Dir::bare("pkg_test_build");
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("Bad-Name.onsa", OK_TEST);
    d.write("ok.onsa", OK_TEST);

    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), [e0320_at("Bad-Name.onsa")], "{doc}");
    assert!(tests_of(&doc).is_empty(), "nothing is run: {doc}");

    let out = run(d.root(), &["test"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.lines().any(|l| l.starts_with("Bad-Name.onsa:1:1: error[E0320]: ")), "{}", out.stdout);
    assert!(result_lines(&out).is_empty(), "no test result line: {}", out.stdout);

    let out = run(d.root(), &["build", "--target", "host"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.lines().any(|l| l.starts_with("Bad-Name.onsa:1:1: error[E0320]: ")), "{}", out.stdout);
}

// ---- the name of a directory (S-313) ---------------------------------------------------------------

/// §2.3: one E0320 for the directory, at the top of the first `.onsa` file below it in the order of the
/// diagnostics (the file strings in code point order): `Bad-Dir/a.onsa`, before `Bad-Dir/b.onsa` and
/// `Bad-Dir/sub/c.onsa`. The files below it have no diagnostic of their own.
#[test]
fn a_directory_with_a_bad_name_gets_one_e0320_at_the_first_file_below_it() {
    let d = Dir::pkg("dir_first");
    d.write("Bad-Dir/b.onsa", OK_FN);
    d.write("Bad-Dir/sub/c.onsa", OK_FN);
    d.write("Bad-Dir/a.onsa", OK_FN);
    d.write("ok.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), [e0320_at("Bad-Dir/a.onsa")], "{doc}");
    assert_no_candidate_with_note(&diagnostics(&doc)[0], false);
}

/// §2.3: the first file is the first in the order of the diagnostics, whatever the file is: when its
/// own name breaks the rule, there are two E0320 at the same place, one for the directory and one for
/// the file (`Bad-Dir/B.onsa` comes before `Bad-Dir/a.onsa`, `B` is before `a` in code point order).
#[test]
fn the_first_file_of_a_directory_may_have_a_bad_name_too_and_both_are_reported() {
    let d = Dir::pkg("dir_both");
    d.write("Bad-Dir/B.onsa", OK_FN);
    d.write("Bad-Dir/a.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), [e0320_at("Bad-Dir/B.onsa"), e0320_at("Bad-Dir/B.onsa")], "{doc}");
    for dg in diagnostics(&doc) {
        assert_no_candidate_with_note(dg, false);
    }
}

/// §2.3: a directory that holds only deeper files is in their path, so it is checked (one E0320 at
/// the first file below it at any depth); two bad directories in one path are two diagnostics, one
/// each, at the same place.
#[test]
fn a_directory_that_only_holds_deeper_files_and_nested_bad_directories_are_checked() {
    let d = Dir::pkg("dir_deep");
    d.write("Deep-Dir/inner/x.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), [e0320_at("Deep-Dir/inner/x.onsa")], "{doc}");

    let d = Dir::pkg("dir_nested");
    d.write("Outer-Dir/Inner-Dir/x.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let at = e0320_at("Outer-Dir/Inner-Dir/x.onsa");
    assert_eq!(places(&doc), [at.clone(), at], "one for each directory: {doc}");
}

/// §2.3 (S-325): the directories that are not identifiers (`_`, a leading digit, a character that is
/// not ASCII, `__`, a `.`, capitals, a `-`) are E0320 in the same way, one each, with no candidate.
#[test]
fn directory_names_that_are_not_identifiers_are_e0320() {
    for name in BAD_DIR_NAMES {
        let d = Dir::pkg("dir_bad");
        let file = format!("{name}/ok.onsa");
        d.write(&file, OK_FN);
        d.write("a.onsa", OK_FN);
        let (out, doc) = check_json(d.root(), &[]);
        assert_eq!(out.code, 1, "{name}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), [e0320_at(&file)], "{name}: {doc}");
        assert_no_candidate_with_note(&diagnostics(&doc)[0], false);
    }
}

/// §2.3: a directory with nothing to gather below it is in no module path: no `.onsa` file at all, or
/// only names that are not gathered (the target of the root, a nested package) give no E0320.
#[test]
fn a_directory_with_no_module_below_it_is_in_no_path() {
    let d = Dir::pkg("dir_empty");
    d.write("Empty-Dir/readme.txt", "hello\n");
    d.write("Hid-Dir/.hid/ok.onsa", OK_FN);
    d.write("Other-Dir/inner/onsa.toml", "[package]\nname = \"inner\"\nedition = \"2026\"\n");
    d.write("Other-Dir/inner/z.onsa", OK_FN);
    d.write("a.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// §2.3, §2.2: the names of keywords (`match/`, `test/`) and names with digits, a deeper path of valid
/// directories, follow the rule, so there is no diagnostic.
#[test]
fn keyword_and_valid_directory_names_have_no_diagnostic() {
    let d = Dir::pkg("dir_ok");
    for f in ["match/x.onsa", "test/y.onsa", "ok_dir/sub_dir/z.onsa", "wrap01/w.onsa", "match.onsa"] {
        d.write(f, OK_FN);
    }
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- names that start with `.` and are passed by their path (S-313) -------------------------------

/// §15.1: a name that starts with `.` is not gathered, so the package is clean; a file that is passed
/// by its path gets the rule applied to its name (`.q.onsa`) and to the `.` directories above it, in a
/// package. The directory is one E0320 at the first file of it: the file that was passed.
#[test]
fn a_name_with_a_dot_that_was_passed_gets_e0320() {
    let d = Dir::pkg("dot_passed");
    d.write("a.onsa", OK_FN);
    d.write(".q.onsa", OK_FN);
    d.write(".hid/ok.onsa", OK_FN);
    d.write("sub/.hid/ok.onsa", OK_FN);
    let (out, doc) = check_json(d.root(), &[]);
    assert_eq!(out.code, 0, "the package leaves the dot names out: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    for file in [".q.onsa", ".hid/ok.onsa", "sub/.hid/ok.onsa"] {
        let (out, doc) = check_json(d.root(), &[file]);
        assert_eq!(out.code, 1, "{file}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), [e0320_at(file)], "{file}: {doc}");
        assert_no_candidate_with_note(&diagnostics(&doc)[0], file == ".q.onsa");
    }
}
