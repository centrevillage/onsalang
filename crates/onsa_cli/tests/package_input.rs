//! Which package a command reads, from the path it is given: the search for `onsa.toml` in the
//! directories above, the manifest passed by its path, and the rule that one run reads one package
//! through one path (spec §15.1, §18.2; S-159, S-312, S-286, S-234, S-622; R-47, R-178, R-189;
//! W4-14 U1).
//!
//! What the spec fixes, and so what is checked here:
//! - the command looks for `onsa.toml` from the file it is given (from the working directory when
//!   it is given none) and goes up to the first directory that has one; that directory is the
//!   root. A file of a package makes the command gather and resolve the whole package and print
//!   only the diagnostics of that file, with `span.file` the path from the root (§15.1, §18.1).
//!   A file with no manifest above it is a package of its own, and its `span.file` is the path as
//!   it was passed. Without a path, a manifest that is not found is a usage error (exit code 2);
//! - a directory argument is the root of a package, so a directory with no `onsa.toml` is a usage
//!   error, and `onsa.toml` as a path is the directory it is in (R-178);
//! - the path is one, the last optional argument. Two or more are a usage error (exit code 2) for
//!   every command that reads a package, so `x/a.onsa y/a.onsa` no longer loses a test (R-189);
//!   `fmt` works file by file and is outside this rule. A file that is neither `.onsa` nor
//!   `onsa.toml` is a usage error, and so is a file below `target/` of the root;
//! - with `--json`, a 2 that has no diagnostic prints nothing on the standard output (§18.2).
//!
//! Not written here: the tree that is gathered (`package_tree.rs`), links and special files
//! (`package_links.rs`), the names of the files (E0320) and the `tests/` of the root (U2), the form
//! of the arguments of `graph`, `build` and the others (U4, `command_paths.rs`), `audit`, `play` and `probe` (not in
//! this version of the CLI), the range of `onsa test` (`test_file_selection.rs`), the
//! content of the manifest (W4-02), and `use` (W4-03).
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use std::path::{Path, PathBuf};

use serde_json::Value;
use test_support::*;

const OK_FN: &str = "pub fn f() -> I32 {\n  1\n}\n";
const OK_TEST: &str = "pub fn f() -> I32 {\n  1\n}\n\ntest \"t\" {\n  assert f() == 1\n}\n";

/// One E0302 at line 2.
fn unresolved(name: &str, ident: &str) -> String {
    format!("pub fn {name}() -> I32 {{\n  {ident}\n}}\n")
}

fn code_of(d: &Value) -> &str {
    str_of(d, "code")
}

fn file_of(d: &Value) -> String {
    span_of(&d["span"]).file
}

/// `(code, file)` of every diagnostic of a document.
fn code_files(doc: &Value) -> Vec<(String, String)> {
    diagnostics(doc).iter().map(|d| (code_of(d).to_string(), file_of(d))).collect()
}

fn s(x: &str) -> String {
    x.to_string()
}

/// A command that ended in 2 without a diagnostic: the reason is on the standard error, and with
/// `--json` the standard output is empty (§18.2).
fn assert_usage_error(out: &Out, json: bool, what: &str) {
    assert_eq!(out.code, 2, "{what}: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.is_empty(), "{what}: the reason is on the standard error");
    if json {
        assert_eq!(out.stdout, "", "{what}: nothing on the standard output with --json");
    }
}

/// `onsa.toml`, `a.onsa` (one error, `ga` is public), `sub/b.onsa` (one error, and `use a.{ga}`),
/// and `sub/deep/c.onsa`, which has no error of its own and uses both.
fn package_with_errors(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("a.onsa", "pub fn ga() -> I32 {\n  1\n}\n\npub fn bad_a() -> I32 {\n  zzz\n}\n");
    d.write("sub/b.onsa", "use a.{ga}\n\npub fn fb() -> I32 {\n  ga() + yyy\n}\n");
    d.write("sub/deep/c.onsa", "use a.{ga}\nuse sub.b.{fb}\n\npub fn g() -> I32 {\n  ga() + fb()\n}\n");
    d
}

fn abs(d: &Dir, rel: &str) -> String {
    d.root().join(rel).to_string_lossy().into_owned()
}

fn cwd_of(d: &Dir, rel: &str) -> PathBuf {
    d.root().join(rel)
}

fn check_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

// ---- the upward search from a file (S-159, R-47) --------------------------------------------------

/// §15.1: a file of a package gathers the package; `use a.{ga}` and `use sub.b.{fb}` resolve; the
/// file has no diagnostic of its own, so the others (`a.onsa`, `sub/b.onsa`) are not printed and
/// the result is a success.
#[test]
fn a_file_of_a_package_is_checked_with_the_package_and_a_clean_file_is_a_success() {
    let d = package_with_errors("up_clean");
    let elsewhere = Dir::bare("up_clean_elsewhere");
    let cases: Vec<(PathBuf, String)> = vec![
        (cwd_of(&d, "sub/deep"), s("c.onsa")),
        (cwd_of(&d, "sub/deep"), s("./c.onsa")),
        (cwd_of(&d, "sub"), s("deep/c.onsa")),
        (cwd_of(&d, "sub"), s("../sub/deep/c.onsa")),
        (d.root().to_path_buf(), s("sub/deep/c.onsa")),
        (d.root().to_path_buf(), abs(&d, "sub/deep/c.onsa")),
        (elsewhere.root().to_path_buf(), abs(&d, "sub/deep/c.onsa")),
    ];
    for (cwd, arg) in cases {
        let (out, doc) = check_json(&cwd, &[&arg]);
        assert_eq!(out.code, 0, "{arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{arg} from {cwd:?}: {doc}");
    }
}

/// §15.1, §18.1: the diagnostics of the given file only, named by the path from the root, whatever
/// the working directory and the way the path is written.
#[test]
fn only_the_diagnostics_of_the_given_file_are_printed_and_named_by_the_root_path() {
    let d = package_with_errors("up_only");
    let elsewhere = Dir::bare("up_only_elsewhere");
    let cases: Vec<(PathBuf, String)> = vec![
        (cwd_of(&d, "sub"), s("b.onsa")),
        (cwd_of(&d, "sub/deep"), s("../b.onsa")),
        (d.root().to_path_buf(), s("sub/b.onsa")),
        (d.root().to_path_buf(), s("./sub/../sub/b.onsa")),
        (d.root().to_path_buf(), abs(&d, "sub/b.onsa")),
        (elsewhere.root().to_path_buf(), abs(&d, "sub/b.onsa")),
    ];
    for (cwd, arg) in cases {
        let (out, doc) = check_json(&cwd, &[&arg]);
        assert_eq!(out.code, 1, "{arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(code_files(&doc), [(s("E0302"), s("sub/b.onsa"))], "{arg} from {cwd:?}: {doc}");
    }
    // the file at the top of the package: its error is the only one, though b.onsa has one too
    let (out, doc) = check_json(&cwd_of(&d, "sub"), &["../a.onsa"]);
    assert_eq!(out.code, 1, "{}", out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("a.onsa"))], "{doc}");
}

/// §15.1: the whole package is gathered and resolved, so a name that another module defines is
/// found. The same file checked as a package of its own (`use a.{ga}` has no `a`) is E0302.
#[test]
fn the_use_of_a_file_of_a_package_resolves_in_the_package_and_not_beside_it() {
    let d = package_with_errors("up_use");
    let copy = Dir::bare("up_use_copy");
    copy.write("b.onsa", "use a.{ga}\n\npub fn fb() -> I32 {\n  ga()\n}\n");
    let (_, in_package) = check_json(d.root(), &["sub/deep/c.onsa"]);
    assert!(diagnostics(&in_package).is_empty(), "{in_package}");
    let (out, alone) = check_json(copy.root(), &["b.onsa"]);
    assert_eq!(out.code, 1, "{}", out.stderr);
    assert!(
        code_files(&alone).iter().any(|(c, f)| c == "E0302" && f == "b.onsa"),
        "no package above the file, so `a` is not found: {alone}"
    );
}

/// §15.1: the first `onsa.toml` found going up is the root, also with a file in the root itself.
#[test]
fn the_nearest_manifest_above_the_file_is_the_root() {
    let d = package_with_errors("up_nearest");
    // a manifest above the root of the package is not looked at
    let above = Dir::bare("up_nearest_above");
    above.write("onsa.toml", "[package]\nname = \"outer\"\nedition = \"2026\"\n");
    above.write("p/onsa.toml", "[package]\nname = \"inner\"\nedition = \"2026\"\n");
    above.write("p/q/x.onsa", &unresolved("f", "zzz"));
    let (out, doc) = check_json(above.root(), &["p/q/x.onsa"]);
    assert_eq!(out.code, 1, "{}", out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("q/x.onsa"))], "{doc}");
    // a file in the root
    let (_, doc) = check_json(d.root(), &["a.onsa"]);
    assert_eq!(code_files(&doc), [(s("E0302"), s("a.onsa"))], "{doc}");
}

/// §15.1: the search starts from the given file. The package in the working directory is not used
/// for a file that is not in it: the file is a package of its own, named as it was passed.
#[test]
fn a_file_with_no_manifest_above_it_is_a_package_of_its_own_whatever_the_working_directory_has() {
    let d = Dir::bare("up_loose");
    d.write("pkg/onsa.toml", "[package]\nname = \"demo\"\nedition = \"2026\"\n");
    d.write("pkg/a.onsa", "pub fn ga() -> I32 {\n  1\n}\n");
    d.write("loose/x.onsa", "use a.{ga}\n");
    let (out, doc) = check_json(&cwd_of(&d, "pkg"), &["../loose/x.onsa"]);
    assert_eq!(out.code, 1, "{}", out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("../loose/x.onsa"))], "{doc}");
}

// ---- a directory is a root (S-312) ---------------------------------------------------------------

/// §15.1: a directory argument is the root of a package, so a directory with no `onsa.toml` is a
/// usage error, also when a manifest is above it.
#[test]
fn a_directory_with_no_manifest_is_a_usage_error_wherever_it_is() {
    let d = package_with_errors("dir_no_manifest");
    let plain = Dir::bare("dir_plain");
    plain.write("a.onsa", OK_FN);
    let empty = Dir::bare("dir_empty");
    let cases: Vec<(PathBuf, String)> = vec![
        (d.root().to_path_buf(), s("sub")),
        (d.root().to_path_buf(), s("sub/")),
        (d.root().to_path_buf(), s("sub/deep")),
        (d.root().to_path_buf(), abs(&d, "sub")),
        (cwd_of(&d, "sub"), s(".")),
        (cwd_of(&d, "sub/deep"), s("..")),
        (plain.root().to_path_buf(), s(".")),
        (empty.root().to_path_buf(), s(".")),
    ];
    for (cwd, arg) in cases {
        for cmd in ["check", "test", "interface"] {
            let out = run(&cwd, &[cmd, "--json", &arg]);
            assert_usage_error(&out, true, &format!("{cmd} {arg} from {cwd:?}"));
        }
    }
}

// ---- no path: the working directory (S-159, R-47) -------------------------------------------------

/// §15.1: without a path the search starts in the working directory and goes up, and the whole
/// package is the input (no file is given to narrow it).
#[test]
fn without_a_path_the_manifest_is_searched_for_upwards_from_the_working_directory() {
    let d = package_with_errors("nopath_up");
    let (_, base) = check_json(d.root(), &["."]);
    assert_eq!(code_files(&base), [(s("E0302"), s("a.onsa")), (s("E0302"), s("sub/b.onsa"))], "the package: {base}");
    for dir in ["", "sub", "sub/deep"] {
        let (out, doc) = check_json(&cwd_of(&d, dir), &[]);
        assert_eq!(out.code, 1, "from {dir:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(doc["diagnostics"], base["diagnostics"], "from {dir:?}");
    }
}

#[test]
fn without_a_path_the_tests_of_the_package_above_the_working_directory_run() {
    let d = Dir::pkg("nopath_test");
    d.write("a.onsa", OK_TEST);
    d.write("sub/b.onsa", OK_TEST);
    d.write("sub/deep/c.onsa", OK_TEST);
    let want = vec![(s("a"), s("t")), (s("sub.b"), s("t")), (s("sub.deep.c"), s("t"))];
    for dir in ["", "sub", "sub/deep"] {
        let (out, doc) = test_json(&cwd_of(&d, dir), &[]);
        assert_eq!(out.code, 0, "from {dir:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(identities(&doc), want, "from {dir:?}");
    }
}

/// §15.1: no `onsa.toml` in the working directory or above it, and no path: a usage error. A
/// `.onsa` file in the working directory is not a package.
#[test]
fn without_a_path_and_without_a_manifest_above_it_is_a_usage_error() {
    let d = Dir::bare("nopath_none");
    d.write("ok.onsa", OK_FN);
    d.write("sub/deeper.onsa", OK_FN);
    for dir in ["", "sub"] {
        let cwd = cwd_of(&d, dir);
        for cmd in ["check", "test", "interface"] {
            let out = run(&cwd, &[cmd, "--json"]);
            assert_usage_error(&out, true, &format!("{cmd} from {dir:?}"));
        }
        for cmd in ["check", "test", "interface"] {
            let out = run(&cwd, &[cmd]);
            assert_usage_error(&out, false, &format!("{cmd} (text) from {dir:?}"));
        }
    }
}

// ---- the manifest as a path (R-178) --------------------------------------------------------------

/// §15.1, R-178: `onsa.toml` as a path is the directory it is in, for every command that reads a
/// package, and also when its directory part is empty.
#[test]
fn a_bare_manifest_in_the_working_directory_is_the_package_for_every_command() {
    let d = Dir::pkg("manifest_bare");
    d.write("a.onsa", OK_TEST);
    d.write("sub/b.onsa", OK_TEST);
    let want = vec![(s("a"), s("t")), (s("sub.b"), s("t"))];
    for arg in ["onsa.toml", "./onsa.toml"] {
        let (out, doc) = test_json(d.root(), &[arg]);
        assert_eq!(out.code, 0, "test {arg}: {}{}", out.stdout, out.stderr);
        assert_eq!(identities(&doc), want, "test {arg}");
        let out = run(d.root(), &["interface", "--json", arg]);
        assert_eq!(out.code, 0, "interface {arg}: {}{}", out.stdout, out.stderr);
        assert_eq!(doc_of(&out)["package"], "demo", "interface {arg}");
    }
}

#[test]
fn a_manifest_given_by_a_path_is_the_package_in_its_directory_from_anywhere() {
    let d = Dir::pkg("manifest_far");
    d.write("a.onsa", OK_TEST);
    d.write("sub/b.onsa", OK_TEST);
    let want = vec![(s("a"), s("t")), (s("sub.b"), s("t"))];
    let parent = d.root().parent().unwrap().to_path_buf();
    let name = d.root().file_name().unwrap().to_string_lossy().into_owned();
    let elsewhere = Dir::bare("manifest_far_elsewhere");
    for (cwd, arg) in [
        (parent, format!("{name}/onsa.toml")),
        (cwd_of(&d, "sub"), s("../onsa.toml")),
        (elsewhere.root().to_path_buf(), abs(&d, "onsa.toml")),
    ] {
        let (out, doc) = test_json(&cwd, &[&arg]);
        assert_eq!(out.code, 0, "{arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(identities(&doc), want, "{arg} from {cwd:?}");
    }
}

/// §15.1: a manifest inside a package belongs to the package that it makes; the file one level up
/// is not asked.
#[test]
fn a_manifest_in_a_sub_directory_makes_a_package_of_that_directory() {
    let d = Dir::pkg("manifest_sub");
    d.write("a.onsa", OK_TEST);
    d.write("sub/onsa.toml", "[package]\nname = \"inner\"\nedition = \"2026\"\n");
    d.write("sub/b.onsa", OK_TEST);
    d.write("sub/c/d.onsa", OK_TEST);
    let (out, doc) = test_json(&cwd_of(&d, "sub"), &["onsa.toml"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(identities(&doc), [(s("b"), s("t")), (s("c.d"), s("t"))]);
    let (out, doc) = test_json(d.root(), &["sub/onsa.toml"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(identities(&doc), [(s("b"), s("t")), (s("c.d"), s("t"))]);
}

// ---- a path that is not a package input ------------------------------------------------------------

/// §15.1: a file that is neither `.onsa` nor `onsa.toml` is a usage error, in a package or not.
#[test]
fn a_file_that_is_neither_onsa_nor_the_manifest_is_a_usage_error() {
    let d = Dir::pkg("not_input");
    d.write("a.onsa", OK_FN);
    for name in ["README.md", "notes.txt", "noext", "onsa.toml.bak", "x.onsa.txt", "sub/y.onsa.bak"] {
        d.write(name, "plain text\n");
    }
    let loose = Dir::bare("not_input_loose");
    for name in ["README.md", "x.onsa.txt", "onsa.toml.bak"] {
        loose.write(name, "plain text\n");
    }
    for name in ["README.md", "notes.txt", "noext", "onsa.toml.bak", "x.onsa.txt", "sub/y.onsa.bak"] {
        for cmd in ["check", "test", "interface"] {
            let out = run(d.root(), &[cmd, "--json", name]);
            assert_usage_error(&out, true, &format!("{cmd} {name} in a package"));
        }
    }
    for name in ["README.md", "x.onsa.txt", "onsa.toml.bak"] {
        for cmd in ["check", "test", "interface"] {
            let out = run(loose.root(), &[cmd, "--json", name]);
            assert_usage_error(&out, true, &format!("{cmd} {name} with no package"));
        }
    }
}

/// §15.1: the output directory of the build is not a place for modules, so a file below `target/`
/// of the root is a usage error. `target/` deeper in the tree is an ordinary directory.
#[test]
fn a_file_below_the_target_directory_of_the_root_is_a_usage_error() {
    let d = Dir::pkg("target_file");
    d.write("a.onsa", OK_TEST);
    d.write("target/g.onsa", OK_TEST);
    d.write("target/deep/h.onsa", OK_TEST);
    d.write("sub/target/k.onsa", OK_TEST);
    let cases: Vec<(PathBuf, String)> = vec![
        (d.root().to_path_buf(), s("target/g.onsa")),
        (d.root().to_path_buf(), s("./target/deep/h.onsa")),
        (d.root().to_path_buf(), abs(&d, "target/g.onsa")),
        (cwd_of(&d, "target"), s("g.onsa")),
        (cwd_of(&d, "target/deep"), s("h.onsa")),
    ];
    for (cwd, arg) in cases {
        for cmd in ["check", "test", "interface"] {
            let out = run(&cwd, &[cmd, "--json", &arg]);
            assert_usage_error(&out, true, &format!("{cmd} {arg} from {cwd:?}"));
        }
    }
    // `target/` that is not directly under the root is a directory of modules
    let (out, doc) = test_json(d.root(), &["sub/target/k.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- one path, one package (S-312, S-286, R-189) --------------------------------------------------

/// §15.1, §18.2: two or more paths are a usage error for every command that reads a package
/// (`audit`, `play` and `probe` are not in this version of the CLI, and `graph` is in `command_paths.rs`, U4).
#[test]
fn two_files_are_a_usage_error_for_every_command_that_reads_a_package() {
    let d = Dir::bare("many_files");
    d.write("a.onsa", OK_TEST);
    d.write("b.onsa", OK_TEST);
    for cmd in ["check", "test", "interface"] {
        for json in [true, false] {
            let mut args = vec![cmd];
            if json {
                args.push("--json");
            }
            args.extend(["a.onsa", "b.onsa"]);
            assert_usage_error(&run(d.root(), &args), json, &format!("{args:?}"));
        }
    }
    // three, the same file twice, and the flag after the paths
    assert_usage_error(&run(d.root(), &["check", "--json", "a.onsa", "b.onsa", "a.onsa"]), true, "three");
    assert_usage_error(&run(d.root(), &["check", "--json", "a.onsa", "a.onsa"]), true, "the same file twice");
    assert_usage_error(&run(d.root(), &["check", "a.onsa", "--json", "b.onsa"]), true, "a flag between");
}

#[test]
fn other_pairs_of_paths_are_a_usage_error_too() {
    let d = Dir::bare("many_kinds");
    for p in ["p", "q"] {
        d.write(&format!("{p}/onsa.toml"), "[package]\nname = \"demo\"\nedition = \"2026\"\n");
        d.write(&format!("{p}/a.onsa"), OK_TEST);
        d.write(&format!("{p}/sub/b.onsa"), OK_TEST);
    }
    d.write("loose.onsa", OK_TEST);
    let pairs: Vec<[&str; 2]> = vec![
        ["p", "q"],
        ["p", "p"],
        ["p", "p/a.onsa"],
        ["p/a.onsa", "p/sub/b.onsa"],
        ["p/a.onsa", "q/a.onsa"],
        ["p/onsa.toml", "q/onsa.toml"],
        ["p/onsa.toml", "p/a.onsa"],
        ["p", "loose.onsa"],
        ["loose.onsa", "p/a.onsa"],
    ];
    for pair in pairs {
        for cmd in ["check", "test", "interface"] {
            let out = run(d.root(), &[cmd, "--json", pair[0], pair[1]]);
            assert_usage_error(&out, true, &format!("{cmd} {pair:?}"));
        }
    }
}

/// R-189: `x/a.onsa` and `y/a.onsa` are both the module `a`, and `onsa test` of the two used to
/// report one `a "t"` and lose the other. Each of them alone runs its test; both together are
/// refused before anything runs.
#[test]
fn two_files_of_the_same_module_name_are_refused_and_each_alone_runs_its_test() {
    let d = Dir::bare("same_module");
    d.write("x/a.onsa", OK_TEST);
    d.write("y/a.onsa", OK_TEST);
    for one in ["x/a.onsa", "y/a.onsa"] {
        let (out, doc) = test_json(d.root(), &[one]);
        assert_eq!(out.code, 0, "{one}: {}{}", out.stdout, out.stderr);
        assert_eq!(identities(&doc), [(s("a"), s("t"))], "{one}");
    }
    let out = run(d.root(), &["test", "x/a.onsa", "y/a.onsa"]);
    assert_usage_error(&out, false, "test x/a.onsa y/a.onsa");
    assert!(result_lines(&out).is_empty(), "no test runs: {}", out.stdout);
    let out = run(d.root(), &["test", "--json", "x/a.onsa", "y/a.onsa"]);
    assert_usage_error(&out, true, "test --json x/a.onsa y/a.onsa");
    // `check` does not report an overlap either: it refuses the two paths first
    let out = run(d.root(), &["check", "--json", "x/a.onsa", "y/a.onsa"]);
    assert_usage_error(&out, true, "check --json x/a.onsa y/a.onsa");
}

const BUILD_TARGET: &str = "\n[export]\nprefix = \"pk_\"\nfns = [\"a.f\"]\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// §18.2: `build` reads one package too. With one package it works, with two it is refused (the
/// test shows that the count of the paths is what is refused).
#[test]
fn build_with_two_paths_is_a_usage_error_and_with_one_it_works() {
    let d = Dir::bare("many_build");
    for p in ["p", "q"] {
        d.write(&format!("{p}/onsa.toml"), &format!("[package]\nname = \"{p}\"\nedition = \"2026\"\n{BUILD_TARGET}"));
        d.write(&format!("{p}/a.onsa"), OK_FN);
    }
    let out = run(d.root(), &["build", "--target", "host", "p"]);
    assert_eq!(out.code, 0, "one package builds: {}{}", out.stdout, out.stderr);
    let out = run(d.root(), &["build", "--target", "host", "p", "q"]);
    assert_usage_error(&out, false, "build --target host p q");
    assert!(!d.root().join("q/target").exists(), "nothing is built for the second path");
}

/// §15.1: `fmt` and `diff --ast` process file by file, so they are outside the rule of one path.
#[test]
fn fmt_still_takes_many_files() {
    let d = Dir::bare("many_fmt");
    d.write("a.onsa", OK_FN);
    d.write("b.onsa", OK_FN);
    let out = run(d.root(), &["fmt", "--check", "a.onsa", "b.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
}

/// §15.1: `build` has the whole package for its result, so a file is a usage error whatever the file
/// is: a file that is not `.onsa`, a `.onsa` file in the root, and a `.onsa` file in a directory that
/// has no manifest of its own. Nothing is written below `--out`. The directory and `onsa.toml` build.
#[test]
fn build_with_a_file_is_a_usage_error_and_writes_nothing() {
    let d = Dir::bare("build_file");
    d.write("p/onsa.toml", &format!("[package]\nname = \"p\"\nedition = \"2026\"\n{BUILD_TARGET}"));
    d.write("p/a.onsa", OK_FN);
    d.write("p/notes.txt", "hello\n");
    d.write("p/sub/x.onsa", OK_FN);
    for (i, file) in ["notes.txt", "a.onsa", "sub/x.onsa"].into_iter().enumerate() {
        let out_dir = format!("out_file_{i}");
        let out = run(&cwd_of(&d, "p"), &["build", "--target", "host", "--out", &out_dir, file]);
        assert_usage_error(&out, false, &format!("build {file}"));
        assert_eq!(out.stdout, "", "build {file}: nothing on the standard output");
        assert!(!d.root().join("p").join(&out_dir).exists(), "build {file}: nothing is written");
        assert!(!d.root().join("p/target").exists(), "build {file}: no default output either");
    }
    for (i, arg) in [".", "onsa.toml"].into_iter().enumerate() {
        let out_dir = format!("out_ok_{i}");
        let out = run(&cwd_of(&d, "p"), &["build", "--target", "host", "--out", &out_dir, arg]);
        assert_eq!(out.code, 0, "build {arg}: {}{}", out.stdout, out.stderr);
        assert!(d.root().join("p").join(&out_dir).is_dir(), "build {arg}: the output is written");
    }
}
