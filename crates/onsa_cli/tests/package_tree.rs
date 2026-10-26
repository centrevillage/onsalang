//! Which files make the modules of a package: the tree that is gathered from the root, what is left
//! out by its name, and the packages nested in a package (spec §15.1; S-592, S-324, S-313; R-47;
//! W4-14 U1).
//!
//! What the spec fixes, and so what is checked here:
//! - the package is the `.onsa` files below the root; the module of a file is its path from the
//!   root with `.` between the parts (§11.8, §15.1). An item whose name starts with `.` (a
//!   directory or a file) and the directory `target/` directly under the root are left out; a file
//!   that does not end in `.onsa` is not read. `target/` deeper in the tree is an ordinary
//!   directory, and so is `tests/` deeper than the root;
//! - a directory that has an `onsa.toml` is another package (a nested package): the package around
//!   it does not gather below it, and a file of it belongs to it alone, so the search upward
//!   finds the nested package first. The name of such a directory is not a module path of the
//!   outer package, so it makes no E0320 or E0304 there (S-324). `tests/` of the root that has its
//!   own `onsa.toml` is a nested package like any other and is not E0200.
//!
//! What a command shows of the tree: the modules in `onsa test --json` (every file here has a test
//! named `t`), the files in `onsa check --json`.
//!
//! Not written here: the links and the special files (`package_links.rs`), the choice of the
//! package from a path (`package_input.rs`), the E0320 for a name that breaks §2.3 and the E0200 of
//! `tests/` of the root (U2: `tests/spec/negative`), the range of `onsa test` (W4-15).
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use std::path::{Path, PathBuf};

use serde_json::Value;
use test_support::*;

const OK_TEST: &str = "pub fn f() -> I32 {\n  1\n}\n\ntest \"t\" {\n  assert f() == 1\n}\n";

/// A module with an error and a failing test: it must not be read when it is left out.
const BAD: &str = "pub fn f() -> I32 {\n  zzz\n}\n\ntest \"t\" {\n  assert 1 == 2\n}\n";

fn s(x: &str) -> String {
    x.to_string()
}

fn manifest(name: &str) -> String {
    format!("[package]\nname = \"{name}\"\nedition = \"2026\"\n")
}

fn modules(doc: &Value) -> Vec<String> {
    let mut m: Vec<String> = identities(doc).into_iter().map(|(module, _)| module).collect();
    m.dedup();
    m
}

fn code_files(doc: &Value) -> Vec<(String, String)> {
    diagnostics(doc).iter().map(|d| (str_of(d, "code").to_string(), span_of(&d["span"]).file)).collect()
}

/// `onsa test --json <arg>` in `cwd`: the code and the modules that ran.
fn ran(cwd: &Path, arg: &str) -> (Out, Value, Vec<String>) {
    let (out, doc) = test_json(cwd, &[arg]);
    let m = modules(&doc);
    (out, doc, m)
}

fn check_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

fn path(d: &Dir, rel: &str) -> PathBuf {
    d.root().join(rel)
}

// ---- what is left out by its name ------------------------------------------------------------------

/// §15.1: a name that starts with `.` (directory or file, at any depth) and the root's `target/`
/// are not gathered, and a file that does not end in `.onsa` is not read. Every item left out would
/// fail the check and the tests if it were read.
#[test]
fn dot_names_the_target_of_the_root_and_other_files_are_not_gathered() {
    let d = Dir::pkg("tree_left_out");
    d.write("a.onsa", OK_TEST);
    d.write("sub/b.onsa", OK_TEST);
    d.write(".hid/q.onsa", BAD);
    d.write(".q.onsa", BAD);
    d.write("sub/.hid/x.onsa", BAD);
    d.write("sub/.y.onsa", BAD);
    d.write(".hid/deep/z.onsa", BAD);
    d.write("target/g.onsa", BAD);
    d.write("target/deep/h.onsa", BAD);
    d.write("README.md", "this is ((( not onsa\n");
    d.write("notes.txt", BAD);
    d.write("a.onsa.bak", BAD);
    d.write("sub/Makefile", BAD);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let (out, doc, m) = ran(d.root(), ".");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("a"), s("sub.b")], "{doc}");
}

/// §15.1: only the `target/` directly under the root is left out; `tests/` deeper than the root is
/// an ordinary module directory (the root's own `tests/` is for the U2 cases). The names are
/// keywords of the language, which a module path may use (§2.3).
#[test]
fn target_and_tests_deeper_than_the_root_are_directories_of_modules() {
    let d = Dir::pkg("tree_deeper");
    d.write("a.onsa", OK_TEST);
    d.write("target/x.onsa", BAD);
    d.write("sub/target/y.onsa", OK_TEST);
    d.write("sub/tests/n.onsa", OK_TEST);
    d.write("sub/deep/target/w.onsa", OK_TEST);
    let (out, doc, m) = ran(d.root(), ".");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("a"), s("sub.deep.target.w"), s("sub.target.y"), s("sub.tests.n")], "{doc}");
}

/// §15.1: what is left out stays left out when a file of the package is given: the whole package
/// is gathered the same way.
#[test]
fn a_file_given_gathers_the_package_without_the_names_left_out() {
    let d = Dir::pkg("tree_given_file");
    d.write("a.onsa", "pub fn ga() -> I32 {\n  1\n}\n");
    d.write("sub/b.onsa", "use a.{ga}\n\npub fn fb() -> I32 {\n  ga()\n}\n");
    d.write(".hid/a.onsa", BAD);
    d.write("target/a.onsa", BAD);
    let (out, doc) = check_json(&path(&d, "sub"), &["b.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- nested packages (S-324) -----------------------------------------------------------------------

/// A package with a nested package `inner` (a directory with an `onsa.toml`): `inner/z.onsa` and
/// `inner/deep/y.onsa` have a test each and are the nested package's.
fn outer_with_inner(tag: &str, inner_dir: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("a.onsa", OK_TEST);
    d.write(&format!("{inner_dir}/onsa.toml"), &manifest("inner"));
    d.write(&format!("{inner_dir}/z.onsa"), OK_TEST);
    d.write(&format!("{inner_dir}/deep/y.onsa"), OK_TEST);
    d
}

/// §15.1: the package around a nested package does not gather below it; the nested package is
/// read through its own root.
#[test]
fn the_package_around_a_nested_package_does_not_gather_below_it() {
    let d = outer_with_inner("nested_basic", "inner");
    let (out, _, m) = ran(d.root(), ".");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("a")]);
    let (out, _, m) = ran(d.root(), "inner");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("deep.y"), s("z")]);
    let (out, _, m) = ran(d.root(), "inner/onsa.toml");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("deep.y"), s("z")]);
}

#[test]
fn a_nested_package_deeper_in_the_tree_is_left_out_with_its_whole_directory() {
    let d = outer_with_inner("nested_deep", "sub/inner");
    d.write("sub/b.onsa", OK_TEST);
    let (out, _, m) = ran(d.root(), ".");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("a"), s("sub.b")]);
}

/// §15.1: nothing of a nested package reaches the check of the package around it.
#[test]
fn the_errors_of_a_nested_package_are_not_the_errors_of_the_package_around_it() {
    let d = Dir::pkg("nested_errors");
    d.write("a.onsa", OK_TEST);
    d.write("inner/onsa.toml", &manifest("inner"));
    d.write("inner/z.onsa", BAD);
    d.write("inner/deep/y.onsa", BAD);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    // and read through its own root, they are its own, named from that root
    let (out, doc) = check_json(d.root(), &["inner"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("deep/y.onsa")), (s("E0302"), s("z.onsa"))], "{doc}");
}

/// §15.1: a file belongs to the package of the first `onsa.toml` above it. Whatever way the file
/// of the nested package is given, the package around it is not looked at, so its modules are not
/// found: `use a.{f}` is E0302.
#[test]
fn a_file_of_a_nested_package_belongs_to_the_nested_package_only() {
    let d = Dir::pkg("nested_file");
    d.write("a.onsa", OK_TEST);
    d.write("inner/onsa.toml", &manifest("inner"));
    d.write("inner/z.onsa", "use a.{f}\n");
    d.write("inner/deep/y.onsa", "pub fn g() -> I32 {\n  1\n}\n");
    let cases: Vec<(PathBuf, Vec<&str>)> = vec![
        (d.root().to_path_buf(), vec!["inner/z.onsa"]),
        (path(&d, "inner"), vec!["z.onsa"]),
        (path(&d, "inner/deep"), vec!["../z.onsa"]),
        (d.root().to_path_buf(), vec!["inner"]),
        (path(&d, "inner"), vec![]),
        (path(&d, "inner/deep"), vec![]),
        (d.root().to_path_buf(), vec!["inner/onsa.toml"]),
    ];
    for (cwd, args) in cases {
        let (out, doc) = check_json(&cwd, &args);
        assert_eq!(out.code, 1, "{args:?} from {cwd:?}: {}{}", out.stdout, out.stderr);
        let found = code_files(&doc);
        assert!(!found.is_empty(), "{args:?} from {cwd:?}: {doc}");
        assert!(
            found.iter().all(|(c, f)| c == "E0302" && f == "z.onsa"),
            "{args:?} from {cwd:?}: every diagnostic is E0302 in the nested package's z.onsa: {doc}"
        );
    }
    // a file deeper in the nested package is named from its root
    let (out, doc) = check_json(d.root(), &["inner/deep/y.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// S-324: the name of the directory of a nested package is not a module path of the package
/// around it, so a name that breaks §2.3 (`Inner-Pkg`) is no E0320 there; and the root of a
/// package is not named by a rule, whatever the directory is called.
#[test]
fn the_name_of_a_nested_package_makes_no_diagnostic_in_the_package_around_it() {
    let d = Dir::pkg("nested_name");
    d.write("a.onsa", OK_TEST);
    d.write("Inner-Pkg/onsa.toml", &manifest("inner"));
    d.write("Inner-Pkg/z.onsa", OK_TEST);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let (out, _, m) = ran(d.root(), ".");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("a")]);
    let (out, _, m) = ran(d.root(), "Inner-Pkg");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("z")]);
}

/// S-324, §15.1: a nested package is not a child module, so an item and a directory of the same
/// name (`a.onsa` has `b`, and `a/` has a manifest and `b.onsa`) is no E0304 of the outer package.
#[test]
fn a_nested_package_is_not_a_child_module_that_clashes_with_an_item() {
    let d = Dir::pkg("nested_clash_pkg");
    d.write("a.onsa", "pub fn b() -> I32 {\n  1\n}\n");
    d.write("a/onsa.toml", &manifest("a_pkg"));
    d.write("a/b.onsa", "pub fn g() -> I32 {\n  2\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// The contrast of the test above (§15.1): the same tree without the manifest in `a/` makes `b.onsa`
/// the child module `a.b`, which clashes with the item `b` of `a.onsa` (E0304).
#[test]
fn without_the_manifest_the_same_tree_is_the_clash_of_an_item_and_a_child_module() {
    let d = Dir::pkg("nested_clash_module");
    d.write("a.onsa", "pub fn b() -> I32 {\n  1\n}\n");
    d.write("a/b.onsa", "pub fn g() -> I32 {\n  2\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(code_files(&doc).iter().any(|(c, _)| c == "E0304"), "{doc}");
}

/// S-592 (2), §15.1: `tests/` of the root that has its own `onsa.toml` is a nested package like any
/// other: it is not gathered and it is not E0200.
#[test]
fn a_tests_directory_of_the_root_that_has_a_manifest_is_a_nested_package() {
    let d = Dir::pkg("nested_tests");
    d.write("a.onsa", OK_TEST);
    d.write("tests/onsa.toml", &manifest("integration"));
    d.write("tests/api.onsa", OK_TEST);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let (out, _, m) = ran(d.root(), ".");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("a")]);
    let (out, _, m) = ran(d.root(), "tests");
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(m, [s("api")]);
}

/// §15.1: a package nested in a hidden directory is not looked at at all, and a nested package in
/// a package nested in a package is read by its own root only.
#[test]
fn packages_nested_in_a_hidden_directory_or_in_each_other_are_read_by_their_own_roots() {
    let d = Dir::pkg("nested_chain");
    d.write("a.onsa", OK_TEST);
    d.write(".hid/onsa.toml", &manifest("hidden"));
    d.write(".hid/h.onsa", BAD);
    d.write("mid/onsa.toml", &manifest("mid"));
    d.write("mid/m.onsa", OK_TEST);
    d.write("mid/low/onsa.toml", &manifest("low"));
    d.write("mid/low/l.onsa", OK_TEST);
    for (arg, want) in [(".", vec!["a"]), ("mid", vec!["m"]), ("mid/low", vec!["l"])] {
        let (out, _, m) = ran(d.root(), arg);
        assert_eq!(out.code, 0, "{arg}: {}{}", out.stdout, out.stderr);
        assert_eq!(m, want, "{arg}");
    }
}
