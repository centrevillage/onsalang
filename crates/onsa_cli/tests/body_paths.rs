//! The path in a body, seen from the command line: which names a body can start a path from, and what the
//! check reports for the rest (spec §15.1, §18.1; S-611, R-39, R-84, R-88; W4-03 U2b).
//!
//! What the spec fixes, and so what is checked here:
//! - another module or a package is named in a body only through a name that a `use` of the module took;
//!   what is visible without a `use` is the items of the module, the prelude and the built-in types. A path
//!   that starts from a name not taken (`std.math.sqrt(x)`, `util.f()`, `util.sub.g()`, the own name of
//!   the package, the name of the module itself, a package nobody declared) is E0302, and the candidate
//!   of the E0302 of a path with no `use` adds a `use`. Applying it ends the repair: the check then
//!   reports nothing;
//! - the dependencies are made by `use` lines alone, so two modules that name each other in bodies with
//!   no `use` are two E0302 and not a cycle (no E0310);
//! - the names of a module are in different spaces (S-611): in the body of `main`, `inner` is what its
//!   `use kp.inner` took, and in another module's path `main.inner` is the child module
//!   `main/inner.onsa`. A name that only a `use` of `main` took is not found through `main`.
//!
//! The same cases with the positions of the marks are under `tests/spec/packages` (`body_path_*`) and
//! `tests/spec/fixes/pkg_body_path_use`; here it is the exit code, the document of `check --json`, the
//! candidates (their number and what applying them leaves) and the tests that are not run.
//!
//! Not written here: the form of the `use` that a candidate adds (the spec does not fix it), the candidates
//! of the `use` with a head not taken and of the own package name (U3a), the E0304 / E0305 / E0310 of the
//! overlaps and the cycles that `use` lines make (U3a), the names of the failed `use` that stay silent
//! (U3b), the visibility (U4).
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause.

mod test_support;

use std::collections::BTreeSet;
use std::path::Path;

use serde_json::Value;
use test_support::*;

fn check_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

/// `(code, file, line)` of every diagnostic, as a set.
fn places(doc: &Value) -> BTreeSet<(String, String, u64)> {
    diagnostics(doc)
        .iter()
        .map(|d| {
            let sp = span_of(&d["span"]);
            (str_of(d, "code").to_string(), sp.file, sp.line)
        })
        .collect()
}

fn set(items: &[(&str, &str, u64)]) -> BTreeSet<(String, String, u64)> {
    items.iter().map(|(c, f, l)| (c.to_string(), f.to_string(), *l)).collect()
}

/// `(file, line)` of every diagnostic, whatever its code.
fn lines_of(doc: &Value) -> BTreeSet<(String, u64)> {
    diagnostics(doc)
        .iter()
        .map(|d| {
            let sp = span_of(&d["span"]);
            (sp.file, sp.line)
        })
        .collect()
}

fn codes(doc: &Value) -> BTreeSet<String> {
    diagnostics(doc).iter().map(|d| str_of(d, "code").to_string()).collect()
}

/// The `fixes` of a diagnostic, an array that is always present (§18.1).
fn fixes_of(diagnostic: &Value) -> &Vec<Value> {
    array_of(diagnostic, "fixes")
}

/// The byte offset of the position (`line`, `col`: from 1, columns count characters) in `text`.
fn offset(text: &str, line: u64, col: u64) -> usize {
    let mut start = 0;
    for (i, l) in text.split_inclusive('\n').enumerate() {
        if i as u64 + 1 == line {
            let in_line = l.char_indices().nth(col as usize - 1).map(|(b, _)| b).unwrap_or(l.len());
            return start + in_line;
        }
        start += l.len();
    }
    text.len()
}

/// The edits of one file: the start and end offsets and the replacement.
type FileEdits = (String, Vec<(usize, usize, String)>);

/// Apply every edit of one candidate to the files of `d` (all edits together, from the end of each file).
fn apply(d: &Dir, fix: &Value) {
    let mut by_file: Vec<FileEdits> = Vec::new();
    for e in array_of(fix, "edits") {
        let sp = span_of(&e["span"]);
        let text = std::fs::read_to_string(d.root().join(&sp.file)).unwrap();
        let (a, b) = (offset(&text, sp.line, sp.col), offset(&text, sp.end_line, sp.end_col));
        let rep = str_of(e, "replace").to_string();
        match by_file.iter_mut().find(|(f, _)| *f == sp.file) {
            Some((_, v)) => v.push((a, b, rep)),
            None => by_file.push((sp.file.clone(), vec![(a, b, rep)])),
        }
    }
    for (file, mut edits) in by_file {
        let mut text = std::fs::read_to_string(d.root().join(&file)).unwrap();
        edits.sort_by(|x, y| y.0.cmp(&x.0));
        for (a, b, rep) in edits {
            text.replace_range(a..b, &rep);
        }
        d.write(&file, &text);
    }
}

const UTIL: &str = "pub fn double(x: I32) -> I32 {\n  x * 2\n}\n";
const SUB: &str = "pub fn h() -> I32 {\n  3\n}\n";

// ---- a path with no `use` is E0302, and its candidate ends the repair (R-39) ------------------------

/// §15.1, §18.1: the three shapes of a path with no `use` (the package `std`, a module at the root, a
/// child module through the root) are one E0302 each, in a package of two modules. The diagnostic has a
/// candidate (the candidate of an E0302 of a path with no `use` adds the `use`); applying the first one
/// leaves a text with a `use` line that the text did not have, and the check then reports nothing.
#[test]
fn a_path_with_no_use_is_e0302_and_applying_the_candidate_ends_the_repair() {
    let shapes: [(&str, &str); 3] = [
        ("std", "pub fn root(x: F32) -> F32 {\n  std.math.sqrt(x)\n}\n"),
        ("root", "pub fn twice() -> I32 {\n  util.double(2)\n}\n"),
        ("child", "pub fn three() -> I32 {\n  util.sub.h()\n}\n"),
    ];
    for (tag, main) in shapes {
        let d = Dir::pkg(&format!("nouse_{tag}"));
        d.write("util.onsa", UTIL);
        d.write("util/sub.onsa", SUB);
        d.write("main.onsa", main);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), set(&[("E0302", "main.onsa", 2)]), "{tag}: {doc}");
        let fixes = fixes_of(&diagnostics(&doc)[0]);
        assert!(!fixes.is_empty(), "{tag}: the candidate adds a `use`: {doc}");
        apply(&d, &fixes[0]);
        let text = std::fs::read_to_string(d.root().join("main.onsa")).unwrap();
        assert!(text.lines().any(|l| l.starts_with("use ")), "{tag}: the candidate adds a `use` line:\n{text}");
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 0, "{tag}: after the candidate: {}{}\n{text}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{tag}: after the candidate: {doc}\n{text}");
    }
}

/// §15.1: the same on a file with no manifest (a single file is a package of one module), where the
/// only path that can lack a `use` is the package `std`.
#[test]
fn a_single_file_with_a_path_to_std_and_no_use_is_e0302_with_a_candidate() {
    let d = Dir::bare("nouse_single");
    d.write("one.onsa", "pub fn root(x: F32) -> F32 {\n  std.math.sqrt(x)\n}\n");
    let (out, doc) = check_json(d.root(), &["one.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0302", "one.onsa", 2)]), "{doc}");
    let fixes = fixes_of(&diagnostics(&doc)[0]);
    assert!(!fixes.is_empty(), "{doc}");
    apply(&d, &fixes[0]);
    let (out, doc) = check_json(d.root(), &["one.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// §18.1: a path that starts from a name that is nothing (no module, no package of that name) has no
/// candidate: the candidate of an E0302 is for the path with no `use` of a module or a package that
/// exists, and a close spelling is not a candidate.
#[test]
fn a_path_from_a_name_that_is_nothing_is_e0302_with_no_candidate() {
    let d = Dir::pkg("nouse_nothing");
    d.write("util.onsa", UTIL);
    d.write(
        "main.onsa",
        "pub fn a() -> I32 {\n  nosuch.f()\n}\n\npub fn b() -> I32 {\n  nosuch.deep.f()\n}\n\npub fn c() -> I32 {\n  uti.double(1)\n}\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        places(&doc),
        set(&[("E0302", "main.onsa", 2), ("E0302", "main.onsa", 6), ("E0302", "main.onsa", 10)]),
        "{doc}"
    );
    for dg in diagnostics(&doc) {
        assert!(fixes_of(dg).is_empty(), "{dg}");
    }
}

/// §15.1: a `use` is decided by itself wherever it is written, so the `use` below the function that
/// names the module serves the path (the same as above the function). No diagnostic.
#[test]
fn a_use_written_below_the_function_serves_the_path() {
    let d = Dir::pkg("use_below");
    d.write("util.onsa", UTIL);
    d.write(
        "main.onsa",
        "pub fn twice() -> I32 {\n  util.double(2)\n}\n\nuse util\n\npub fn root(x: F32) -> F32 {\n  std.math.sqrt(x)\n}\n\nuse std\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// §15.1, §18.1: a `use` of a name takes that name alone, so `use std.math` does not make
/// `std.math.sqrt(x)` valid, and `use util.{double}` does not make `util.double(1)` valid.
#[test]
fn a_use_takes_its_last_name_alone() {
    let d = Dir::pkg("takes_last");
    d.write("util.onsa", UTIL);
    d.write("util/sub.onsa", SUB);
    d.write(
        "main.onsa",
        "use std.math\nuse util.{double}\nuse util.sub\n\npub fn a(x: F32) -> F32 {\n  std.math.sqrt(x)\n}\n\npub fn b() -> I32 {\n  util.double(1)\n}\n\npub fn c() -> I32 {\n  util.sub.h()\n}\n\npub fn ok(x: F32) -> F32 {\n  math.sqrt(x)\n}\n\npub fn ok_too() -> I32 {\n  double(1) + sub.h()\n}\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        places(&doc),
        set(&[("E0302", "main.onsa", 6), ("E0302", "main.onsa", 10), ("E0302", "main.onsa", 14)]),
        "{doc}"
    );
}

// ---- the tests are not run when the check reports (R-39) --------------------------------------------

fn test_package(tag: &str, main: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("util.onsa", UTIL);
    d.write("main.onsa", main);
    d
}

const TEST_BODY: &str = "pub fn four() -> I32 {\n  util.double(2)\n}\n\ntest \"four\" {\n  assert four() == 4\n}\n";

/// §18.1: the path with no `use` is a check error, so `test --json` runs no test: exit code 1 and an
/// empty `tests` array; with the `use`, the same test runs and passes.
#[test]
fn a_path_with_no_use_runs_no_test_and_the_use_runs_it() {
    let d = test_package("tests_nouse", TEST_BODY);
    let (out, doc) = test_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0302", "main.onsa", 2)]), "{doc}");
    assert!(tests_of(&doc).is_empty(), "{doc}");

    let d = test_package("tests_use", &format!("use util\n\n{TEST_BODY}"));
    let (out, doc) = test_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(identities(&doc), [("main".to_string(), "four".to_string())], "{doc}");
    assert_eq!(str_of(&tests_of(&doc)[0], "status"), "ok", "{doc}");
}

// ---- the dependencies are made by `use` lines alone (R-39) ------------------------------------------

/// §15.1 (R-39, `tests/review-phase1/types/cyc2`): two modules that name each other in bodies with no
/// `use` are two E0302 and no E0310, because the dependencies are the `use` lines.
#[test]
fn modules_that_name_each_other_with_no_use_are_two_e0302_and_not_a_cycle() {
    let d = Dir::pkg("mutual");
    d.write("a.onsa", "pub fn f() -> I32 {\n  b.g()\n}\n");
    d.write("b.onsa", "pub fn g() -> I32 {\n  a.f()\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0302", "a.onsa", 2), ("E0302", "b.onsa", 2)]), "{doc}");
    assert!(!codes(&doc).contains("E0310"), "{doc}");
}

/// §15.1: `a` takes `b` with a `use` and `b` names `a` with no `use`: the only dependency is `a` on `b`,
/// so there is no cycle, and the one wrong path is the one in `b`.
#[test]
fn a_use_in_one_direction_and_a_path_with_no_use_back_is_not_a_cycle() {
    let d = Dir::pkg("one_way");
    d.write("a.onsa", "use b\n\npub fn f() -> I32 {\n  b.g()\n}\n");
    d.write("b.onsa", "pub fn g() -> I32 {\n  1\n}\n\npub fn back() -> I32 {\n  a.f()\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0302", "b.onsa", 6)]), "{doc}");
}

/// §15.1: the same two modules with a `use` in each direction are the cycle (E0310). The contrast of the
/// two tests above; the code of the cycle itself is under `tests/spec/packages/cycle`.
#[test]
fn modules_that_take_each_other_with_use_lines_are_a_cycle() {
    let d = Dir::pkg("mutual_use");
    d.write("a.onsa", "use b\n\npub fn f() -> I32 {\n  1\n}\n\npub fn g() -> I32 {\n  b.g()\n}\n");
    d.write("b.onsa", "use a\n\npub fn g() -> I32 {\n  a.f()\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(codes(&doc).contains("E0310"), "{doc}");
    assert!(!codes(&doc).contains("E0302"), "{doc}");
}

// ---- a package nobody declared, the own name, the module itself (R-88) -------------------------------

/// §15.1, §15.3 (R-88): the package has no dependency but the implicit `std`, so `serde.decode(1)` and
/// `std.serde.decode(1)` are E0302, and so is a path from the own package name (`fx.util.helper()`),
/// even after `use util`; the package does not name itself.
#[test]
fn a_package_that_is_not_a_dependency_and_the_own_package_name_are_not_found() {
    let d = Dir::bare("undeclared");
    d.write("onsa.toml", "[package]\nname = \"fx\"\nedition = \"2026\"\n");
    d.write("util.onsa", "pub fn helper() -> I32 {\n  1\n}\n");
    d.write(
        "main.onsa",
        "use std\nuse util\n\npub fn a() -> I32 {\n  fx.util.helper()\n}\n\npub fn b() -> I32 {\n  serde.decode(1)\n}\n\npub fn c() -> I32 {\n  std.serde.decode(1)\n}\n\npub fn ok() -> I32 {\n  util.helper()\n}\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        places(&doc),
        set(&[("E0302", "main.onsa", 5), ("E0302", "main.onsa", 9), ("E0302", "main.onsa", 13)]),
        "{doc}"
    );
}

/// §15.1: the name of a module is not visible in its own body (the items of the module, the prelude and
/// the built-in types are), so `main.k()` in `main.onsa` is E0302; the module that takes itself with
/// `use main` names its items through its own name, and that `use` is not a cycle.
#[test]
fn a_module_names_itself_only_after_taking_itself() {
    let d = Dir::pkg("itself");
    d.write("main.onsa", "pub fn k() -> I32 {\n  1\n}\n\npub fn j() -> I32 {\n  main.k()\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0302", "main.onsa", 6)]), "{doc}");

    d.write("main.onsa", "use main\n\npub fn k() -> I32 {\n  1\n}\n\npub fn j() -> I32 {\n  main.k()\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- the spaces of the names of a module (S-611) -----------------------------------------------------

/// `main.onsa` takes `kp.inner` as `inner` and `kp.leaf.{l}`, and has the child module `main/inner.onsa`
/// (with `h`; `kp/inner.onsa` has `g`).
fn s611(tag: &str, main: &str, other: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("main.onsa", main);
    d.write("main/inner.onsa", SUB);
    d.write("kp/inner.onsa", "pub fn g() -> I32 {\n  2\n}\n");
    d.write("kp/leaf.onsa", "pub fn l() -> I32 {\n  4\n}\n");
    d.write("other.onsa", other);
    d
}

const S611_MAIN: &str = "use kp.inner\nuse kp.leaf.{l}\nuse main.inner.{h}\n\npub fn k() -> I32 {\n  1\n}\n\npub fn from_the_binding() -> I32 {\n  inner.g() + l() + h()\n}\n";

/// §15.1: in the body of `main`, `inner` is what the `use` took, and the child module's `h` is taken by
/// `use main.inner.{h}`; in another module that took `main`, `main.k()` is an item and `main.inner.h()`
/// goes through the child module. No diagnostic.
#[test]
fn the_binding_of_main_and_its_child_module_are_in_different_spaces() {
    let d = s611(
        "s611_ok",
        S611_MAIN,
        "use main\n\npub fn item() -> I32 {\n  main.k()\n}\n\npub fn child() -> I32 {\n  main.inner.h()\n}\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

const S611_OTHER_BAD: &str = "use main\n\npub fn a() -> I32 {\n  main.l()\n}\n\npub fn b() -> I32 {\n  main.inner.g()\n}\n\npub fn c() -> I32 {\n  main.leaf.l()\n}\n\npub fn ok() -> I32 {\n  main.k() + main.inner.h()\n}\n";

/// §15.1: through `main`, the names that only the `use` lines of `main` took (`l`, `leaf`) are not
/// found, and `main.inner` is the child module, which has no `g` (it is in `kp/inner.onsa`, which `main`
/// took as `inner`). Each is rejected at its line and the line that goes through the item and the child
/// module is not. The code of the rejection is E0302 (the next test).
#[test]
fn through_main_a_name_that_only_a_use_of_main_took_is_rejected() {
    let d = s611("s611_bad", S611_MAIN, S611_OTHER_BAD);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        lines_of(&doc),
        [("other.onsa".to_string(), 4), ("other.onsa".to_string(), 8), ("other.onsa".to_string(), 12)]
            .into_iter()
            .collect::<BTreeSet<_>>(),
        "{doc}"
    );
}

/// §15.1, §18.1 (R-254): the same rejections are E0302, the name stage, not a type error. R-254 is fixed
/// by W4-04.
#[test]
#[ignore = "W4-04"]
fn through_main_a_name_that_only_a_use_of_main_took_is_e0302() {
    let d = s611("s611_bad_code", S611_MAIN, S611_OTHER_BAD);
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(
        places(&doc),
        set(&[("E0302", "other.onsa", 4), ("E0302", "other.onsa", 8), ("E0302", "other.onsa", 12)]),
        "{doc}"
    );
}

/// §15.1, S-611 (R-254): in the body of `main`, `inner` is the binding of `kp.inner`, so `inner.h()`
/// (the child module's item) is not found there: E0302. The child module's items are taken by
/// `use main.inner.{h}`.
#[test]
#[ignore = "W4-04"]
fn in_the_body_of_main_the_child_module_is_not_a_name() {
    let d = s611("s611_body", "use kp.inner\n\npub fn k() -> I32 {\n  inner.h()\n}\n", "use main\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0302", "main.onsa", 4)]), "{doc}");
}
