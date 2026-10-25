//! The cycles that `use` lines make (E0310) and the candidates of the E0302 of a `use` head, seen from the
//! command line (spec §15.1, §18.1; S-594, R-39, S-37, S-663, R-106; W4-03 U3a2).
//!
//! What the spec fixes, and so what is checked here:
//! - a `use` that takes a module (a package too) is a dependency on that module and on every module below
//!   it, the module that writes the `use` left out; a `use` that takes an item is a dependency on the
//!   module of the item; the path in a body is not looked at (§15.1). A cycle of these dependencies is
//!   E0310, and the note shows how to narrow the path;
//! - the cycles through a lower module, through a directory with no file of its own, between a module and
//!   its child, and through the elements of a list are cycles; the same modules with the path narrowed to
//!   an item or to a module that does not depend back are not; a `use` of another package (`std`) is no
//!   dependency of the package;
//! - a candidate is safe (§18.1): applying it alone leaves no diagnostic of the same stage or before in
//!   what it touched, so the candidate that adds a `use` for a path with no `use` (R-39) is not given when
//!   the `use` would close a cycle, however the cycle is closed;
//! - the head of a `use` that is a name a `use` took gets the candidate of the full path of that name
//!   (`use std.math` and `use math.{sin}` give `use std.math.{sin}`), and the own name of the package
//!   gets the candidate that takes the name off, one `use` per element for a list (S-37, S-663).
//!
//! The spec leaves out the number and the place of the E0310 of one cycle, so the tests ask for the code
//! (at least one) and the note, never for the line. The same cases with the marks of the E0302 are under
//! `tests/spec/fixes` (`pkg_own_name*`, `pkg_use_head_*`, `pkg_body_path_cycle*`).
//!
//! The candidate of a path in a body that starts from the own package name or names the module itself
//! (S-673, R-268), written by W4-03 U3a2/i, is at the end: the part that names the package or the module
//! is taken off, the `use` of the new head added when it is not there, and the candidate is given only
//! when the path is then read whole and the `use` closes no cycle.
//!
//! A `use` that failed in the names stage is no dependency (S-678), the note of a candidate that is left
//! out for a cycle shows the form and the module of the cycle (S-682), and the note that narrows a `use`
//! counts only the narrowings that can be written (S-683): the last three groups of tests (W4-03 U3b1).
//!
//! Not written here: the clash of the names (E0304 / E0305, U3a1), the names of the failed `use` that
//! stay silent (`failed_names.rs`), the visibility (U4).
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

fn codes(doc: &Value) -> BTreeSet<String> {
    diagnostics(doc).iter().map(|d| str_of(d, "code").to_string()).collect()
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|c| c.to_string()).collect()
}

/// The diagnostics of `code`, in the order of the document.
fn of_code<'a>(doc: &'a Value, code: &str) -> Vec<&'a Value> {
    diagnostics(doc).iter().filter(|d| str_of(d, "code") == code).collect()
}

fn fixes_of(diagnostic: &Value) -> &Vec<Value> {
    array_of(diagnostic, "fixes")
}

fn notes_of(diagnostic: &Value) -> &Vec<Value> {
    array_of(diagnostic, "notes")
}

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

/// The lines of `file` that start with `use `, trimmed.
fn use_lines(d: &Dir, file: &str) -> Vec<String> {
    let text = std::fs::read_to_string(d.root().join(file)).unwrap();
    text.lines().map(|l| l.trim()).filter(|l| l.starts_with("use ")).map(String::from).collect()
}

/// A package `demo` with the given files.
fn pkg(tag: &str, files: &[(&str, &str)]) -> Dir {
    let d = Dir::pkg(tag);
    for (f, t) in files {
        d.write(f, t);
    }
    d
}

/// A package `fx` with the given files.
fn fx(tag: &str, files: &[(&str, &str)]) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", "[package]\nname = \"fx\"\nedition = \"2026\"\n");
    for (f, t) in files {
        d.write(f, t);
    }
    d
}

/// A function with the name `name`, so that a `use` of it is a real item.
fn f(name: &str) -> String {
    format!("pub fn {name}() -> I32 {{\n  1\n}}\n")
}

/// The package is a cycle: exit code 1 and only E0310 (one or more, the spec fixes neither number nor
/// place).
fn assert_cycle(d: &Dir, what: &str) -> Value {
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{what}: {}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0310"]), "{what}: {doc}");
    doc
}

/// The package has no diagnostic.
fn assert_clean(d: &Dir, what: &str) {
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{what}: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{what}: {doc}");
}

// ---- the modules that take each other with items ----------------------------------------------------

/// §15.1: two modules, each taking an item of the other, are a cycle (the dependency is on the module of
/// the item), wherever the `use` is written in the file. The text of `tests/review-phase1/types/cyc3` with
/// the package name left out of the paths (S-37, R-39).
#[test]
fn two_modules_that_take_items_of_each_other_are_a_cycle() {
    let d = pkg(
        "two_items",
        &[
            ("a.onsa", "use b.{g}\n\npub fn f() -> I32 {\n  g()\n}\n"),
            ("b.onsa", "use a.{f}\n\npub fn g() -> I32 {\n  f()\n}\n"),
        ],
    );
    assert_cycle(&d, "uses at the top");
    let d = pkg(
        "two_items_below",
        &[
            ("a.onsa", "pub fn f() -> I32 {\n  g()\n}\n\nuse b.{g}\n"),
            ("b.onsa", "pub fn g() -> I32 {\n  f()\n}\n\nuse a.{f}\n"),
        ],
    );
    assert_cycle(&d, "uses below the functions");
}

/// §15.1: three modules in a ring are a cycle, and the same ring with one link cut is not.
#[test]
fn three_modules_in_a_ring_are_a_cycle_and_a_cut_ring_is_not() {
    let a = "use b.{g}\n\npub fn f() -> I32 {\n  g()\n}\n";
    let b = "use c.{h}\n\npub fn g() -> I32 {\n  h()\n}\n";
    let d = pkg("ring", &[("a.onsa", a), ("b.onsa", b), ("c.onsa", "use a.{f}\n\npub fn h() -> I32 {\n  f()\n}\n")]);
    assert_cycle(&d, "ring");
    let d = pkg("ring_cut", &[("a.onsa", a), ("b.onsa", b), ("c.onsa", "pub fn h() -> I32 {\n  1\n}\n")]);
    assert_clean(&d, "ring with one link cut");
}

/// §15.1: no tests run when the check reports the cycle; with the cycle cut the same test runs.
#[test]
fn a_cycle_runs_no_test() {
    let d = pkg(
        "cycle_no_test",
        &[
            ("a.onsa", "use b.{g}\n\npub fn f() -> I32 {\n  g()\n}\n\ntest \"f\" {\n  assert f() == 1\n}\n"),
            ("b.onsa", "use a.{f}\n\npub fn g() -> I32 {\n  1\n}\n"),
        ],
    );
    let (out, doc) = test_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0310"]), "{doc}");
    assert!(tests_of(&doc).is_empty(), "{doc}");
    d.write("b.onsa", "pub fn g() -> I32 {\n  1\n}\n");
    let (out, doc) = test_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(str_of(&tests_of(&doc)[0], "status"), "ok", "{doc}");
}

// ---- the `use` of a module is a dependency on every module below it ----------------------------------

/// §15.1: two modules that take each other as modules (`use b`, `use a`) are a cycle.
#[test]
fn two_modules_that_take_each_other_as_modules_are_a_cycle() {
    let d = pkg(
        "two_modules",
        &[
            ("a.onsa", "use b\n\npub fn f() -> I32 {\n  b.g()\n}\n"),
            ("b.onsa", "use a\n\npub fn g() -> I32 {\n  a.f()\n}\n"),
        ],
    );
    assert_cycle(&d, "use b, use a");
}

/// §15.1: `use b` is a dependency on `b` and on `b.inner`, so when `b.inner` takes `a` the cycle is closed
/// although the body of `a` names only `b`'s own function. The note shows how to narrow the path, and the
/// path narrowed to the item of `b` is not a cycle (`b` itself has no `use` of `a`).
#[test]
fn use_of_a_module_depends_on_the_modules_below_it() {
    let d = pkg(
        "below",
        &[
            ("a.onsa", "use b\n\npub fn f() -> I32 {\n  b.g()\n}\n"),
            ("b.onsa", "pub fn g() -> I32 {\n  1\n}\n"),
            ("b/inner.onsa", "use a.{f}\n\npub fn h() -> I32 {\n  f()\n}\n"),
        ],
    );
    let doc = assert_cycle(&d, "use b, b.inner takes a");
    for e in of_code(&doc, "E0310") {
        assert!(!notes_of(e).is_empty(), "the note shows how to narrow the path: {e}");
    }
    d.write("a.onsa", "use b.{g}\n\npub fn f() -> I32 {\n  g()\n}\n");
    assert_clean(&d, "use b.{g}");
}

/// §15.1, S-666: a directory with no file of its own (`dsp/`) is a module with no items, and `use dsp` is a
/// dependency on `dsp.synth` and `dsp.util`. `dsp.synth` takes `main`, so the cycle is closed; the path
/// narrowed to `dsp.util` is not a cycle, and the path narrowed to an item of `dsp.synth` still is.
#[test]
fn use_of_a_directory_with_no_file_depends_on_the_modules_below_it() {
    let main = "use dsp\n\npub fn k() -> I32 {\n  1\n}\n";
    let d = pkg(
        "dir_only",
        &[
            ("main.onsa", main),
            ("dsp/synth.onsa", "use main.{k}\n\npub fn voice() -> I32 {\n  k()\n}\n"),
            ("dsp/util.onsa", "pub fn h() -> I32 {\n  1\n}\n"),
        ],
    );
    let doc = assert_cycle(&d, "use dsp");
    for e in of_code(&doc, "E0310") {
        assert!(!notes_of(e).is_empty(), "the note shows how to narrow the path: {e}");
    }
    d.write("main.onsa", "use dsp.synth.{voice}\n\npub fn k() -> I32 {\n  1\n}\n");
    assert_cycle(&d, "use dsp.synth.{voice}: still a dependency on dsp.synth");
    d.write("main.onsa", "use dsp.util.{h}\n\npub fn k() -> I32 {\n  1\n}\n");
    assert_clean(&d, "use dsp.util.{h}");
}

/// §15.1: a child module that takes its parent and a parent that takes the child's module are a cycle:
/// `b` takes `a` (so `a` and `a.sub`), and `a.sub` takes an item of `b`; the body of `a.sub` is not
/// looked at. The child alone taking the parent's item is not.
#[test]
fn a_child_and_its_parent_are_a_cycle_when_each_takes_the_other() {
    let d = pkg(
        "child_parent",
        &[
            ("a.onsa", &f("x")),
            ("a/sub.onsa", "use b.{g}\n\npub fn s() -> I32 {\n  g()\n}\n"),
            ("b.onsa", "use a\n\npub fn g() -> I32 {\n  a.x()\n}\n"),
        ],
    );
    let doc = assert_cycle(&d, "b takes a, a.sub takes b");
    for e in of_code(&doc, "E0310") {
        assert!(!notes_of(e).is_empty(), "the note shows how to narrow the path: {e}");
    }
    d.write("b.onsa", "use a.{x}\n\npub fn g() -> I32 {\n  x()\n}\n");
    assert_clean(&d, "b takes the item of a");

    let d = pkg(
        "parent_child",
        &[
            ("a.onsa", "use a.sub\n\npub fn x() -> I32 {\n  sub.s()\n}\n"),
            ("a/sub.onsa", "use a.{x}\n\npub fn s() -> I32 {\n  1\n}\n"),
        ],
    );
    assert_cycle(&d, "a takes a.sub, a.sub takes the item of a");
    d.write("a/sub.onsa", "pub fn s() -> I32 {\n  1\n}\n");
    assert_clean(&d, "the child takes nothing");
    d.write("a.onsa", "pub fn x() -> I32 {\n  1\n}\n");
    d.write("a/sub.onsa", "use a.{x}\n\npub fn s() -> I32 {\n  x()\n}\n");
    assert_clean(&d, "only the child takes the parent's item");
}

/// §15.1: the note shows how to narrow the `use` of a module only when narrowing every such `use` of the
/// cycle to items cuts it. When the cycle stays (`main` takes `main.inner`, which takes an item of `main`;
/// `dsp.x` and `dsp.y` take each other), the rule says that no path narrows to cut it, at no `use`. The
/// control: narrowing `use b` cuts the cycle through `b.inner`, and the note is at the `use`.
#[test]
fn the_note_narrows_only_a_cycle_that_narrowing_cuts() {
    let child = pkg(
        "narrow_child",
        &[
            ("main.onsa", "use main.inner\n\npub fn k() -> I32 {\n  inner.g()\n}\n"),
            ("main/inner.onsa", "use main.{k}\n\npub fn g() -> I32 {\n  1\n}\n"),
        ],
    );
    let pair = pkg(
        "narrow_pair",
        &[
            ("dsp/x.onsa", "use dsp.y\n\npub fn f() -> I32 {\n  y.g()\n}\n"),
            ("dsp/y.onsa", "use dsp.x\n\npub fn g() -> I32 {\n  x.f()\n}\n"),
        ],
    );
    for (d, what) in [(&child, "main and main.inner"), (&pair, "dsp.x and dsp.y")] {
        let doc = assert_cycle(d, what);
        for e in of_code(&doc, "E0310") {
            assert!(!notes_of(e).is_empty(), "{what}: the rule: {e}");
            assert!(notes_of(e).iter().all(|n| n.get("span").is_none()), "{what}: no `use` to narrow: {e}");
        }
    }
    let below = pkg(
        "narrow_below",
        &[
            ("a.onsa", "use b\n\npub fn f() -> I32 {\n  b.g()\n}\n"),
            ("b.onsa", &f("g")),
            ("b/inner.onsa", "use a.{f}\n\npub fn h() -> I32 {\n  f()\n}\n"),
        ],
    );
    let doc = assert_cycle(&below, "use b");
    for e in of_code(&doc, "E0310") {
        assert!(notes_of(e).iter().any(|n| n.get("span").is_some()), "the note at `use b`: {e}");
    }
}

/// §15.1 (S-679): a module does not take itself: `use main` in `main.onsa` and `use dsp.synth` (or
/// `use dsp.{synth}`) in `dsp/synth.onsa` are E0302 with no candidate and a note that the items of the
/// module are named by their names alone. Its parent (`use dsp`) and its child (`use main.inner`) are
/// taken. (Whether the failed `use main` is a dependency on the modules below is S-678, not fixed here.)
#[test]
fn a_module_does_not_take_itself() {
    let cases: [(&str, &str, &str); 3] = [
        ("self_root", "main.onsa", "use main\n\npub fn k() -> I32 {\n  1\n}\n"),
        ("self_below", "dsp/synth.onsa", "use dsp.synth\n\npub fn k() -> I32 {\n  1\n}\n"),
        ("self_list", "dsp/synth.onsa", "use dsp.{synth}\n\npub fn k() -> I32 {\n  1\n}\n"),
    ];
    for (tag, file, text) in cases {
        let d = pkg(tag, &[(file, text), ("main/inner.onsa", &f("g"))]);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0302"]), "{tag}: {doc}");
        let e = &diagnostics(&doc)[0];
        assert!(fixes_of(e).is_empty(), "{tag}: {e}");
        assert!(!notes_of(e).is_empty(), "{tag}: the note shows the items named alone: {e}");
    }
    let d = pkg(
        "self_parent_child",
        &[
            ("main.onsa", "use main.inner\n\npub fn k() -> I32 {\n  inner.g()\n}\n"),
            ("main/inner.onsa", &f("g")),
            ("dsp.onsa", &f("h")),
            ("dsp/synth.onsa", "use dsp\n\npub fn v() -> I32 {\n  dsp.h()\n}\n"),
        ],
    );
    assert_clean(&d, "the parent and the child are taken");
}

// ---- the elements of a list ---------------------------------------------------------------------------

/// §15.1: each element of a list is a name that is taken, and the dependency is made element by element:
/// `use b.{c}` where `c` is a child module of `b` is a dependency on `b.c` alone, not on `b`.
#[test]
fn a_list_makes_a_dependency_for_each_element() {
    let a = |list: &str| format!("use b.{{{list}}}\n\npub fn f() -> I32 {{\n  1\n}}\n");
    let b = "use a.{f}\n\npub fn g() -> I32 {\n  f()\n}\n";
    // `b` takes `a`, and `a` takes only `b.c`, which does not take `a`: no cycle.
    let d = pkg("list_child", &[("a.onsa", &a("c")), ("b.onsa", b), ("b/c.onsa", &f("c"))]);
    assert_clean(&d, "use b.{c}: the child module alone");
    // with an item of `b` in the list, `a` depends on `b`: cycle.
    d.write("a.onsa", &a("c, g"));
    assert_cycle(&d, "use b.{c, g}: g is an item of b");
    // with the child module taking `a`, the child alone is the cycle.
    d.write("a.onsa", &a("c"));
    d.write("b.onsa", &f("g"));
    d.write("b/c.onsa", "use a.{f}\n\npub fn c() -> I32 {\n  f()\n}\n");
    assert_cycle(&d, "use b.{c}: the child module takes a");
}

// ---- another package makes no dependency --------------------------------------------------------------

/// §15.1: `use std.math.{sqrt}` is a dependency on the package `std`, not on the module `math` of this
/// package, so a module `math` of this package that takes `a` while `a` takes `std.math` is no cycle.
#[test]
fn the_use_of_another_package_is_not_a_dependency_of_this_one() {
    let d = pkg(
        "other_package",
        &[
            ("a.onsa", "use std.math.{sqrt}\n\npub fn f(x: F32) -> F32 {\n  sqrt(x)\n}\n"),
            ("math.onsa", "use a.{f}\n\npub fn g(x: F32) -> F32 {\n  f(x)\n}\n"),
        ],
    );
    assert_clean(&d, "std.math and the module math");
    d.write("a.onsa", "use std\n\npub fn f(x: F32) -> F32 {\n  std.math.sqrt(x)\n}\n");
    assert_clean(&d, "use std and the module math");
}

// ---- the candidate that would close a cycle is not given (R-39, §18.1) --------------------------------

/// The E0302 of the path at `file` has no candidate.
fn assert_no_candidate(doc: &Value, file: &str, what: &str) {
    let found: Vec<&Value> = of_code(doc, "E0302").into_iter().filter(|d| span_of(&d["span"]).file == file).collect();
    assert_eq!(found.len(), 1, "{what}: one E0302 in {file}: {doc}");
    assert!(fixes_of(found[0]).is_empty(), "{what}: a candidate that closes a cycle is not given: {}", found[0]);
}

/// §15.1, §18.1: the E0302 of a path with no `use` has the candidate that adds the `use` of the module;
/// when `b` takes `a`, that `use` would close the cycle, so there is no candidate, and no E0310 is
/// reported for the text as it is.
#[test]
fn no_candidate_when_the_use_would_close_a_cycle_directly() {
    let d = pkg(
        "close_direct",
        &[("a.onsa", "pub fn f() -> I32 {\n  b.g()\n}\n"), ("b.onsa", "use a.{f}\n\npub fn g() -> I32 {\n  f()\n}\n")],
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_no_candidate(&doc, "a.onsa", "b takes a");
}

/// §15.1: the same through a module below: `use d` is a dependency on `d.inner` too, and `d.inner` takes
/// `c`. The module `d` itself has no `use` of `c`. And the same in a child module: `f` takes `e`, so
/// `use f` in `e.sub` closes the cycle through the parent.
#[test]
fn no_candidate_when_the_use_would_close_a_cycle_through_a_module_below_or_the_parent() {
    let d = pkg(
        "close_below",
        &[
            ("c.onsa", "pub fn f() -> I32 {\n  d.h()\n}\n"),
            ("d.onsa", &f("h")),
            ("d/inner.onsa", "use c.{f}\n\npub fn leaf() -> I32 {\n  f()\n}\n"),
        ],
    );
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_no_candidate(&doc, "c.onsa", "d.inner takes c");

    let d = pkg(
        "close_parent",
        &[
            ("e.onsa", &f("fb")),
            ("e/sub.onsa", "pub fn lower() -> I32 {\n  f.k()\n}\n"),
            ("f.onsa", "use e\n\npub fn k() -> I32 {\n  1\n}\n"),
        ],
    );
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_no_candidate(&doc, "e/sub.onsa", "f takes e");
}

/// §15.1, §18.1: the same shape without the cycle has the candidate, and applying it leaves nothing
/// (the control of the two tests above: the candidate is withheld because of the cycle alone).
#[test]
fn the_candidate_is_given_when_the_use_closes_no_cycle() {
    let d = pkg(
        "close_none",
        &[("c.onsa", "pub fn f() -> I32 {\n  d.h()\n}\n"), ("d.onsa", &f("h")), ("d/inner.onsa", &f("leaf"))],
    );
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    let fixes = fixes_of(&diagnostics(&doc)[0]);
    assert!(!fixes.is_empty(), "{doc}");
    apply(&d, &fixes[0]);
    assert_clean(&d, "after the candidate");
}

/// §15.1, §18.1 (a case the parent asked for; the candidate of a path from the name of the module itself
/// is S-673, so whether there is one is not fixed): `main.inner.g()` in the body of `main` with no `use`,
/// where the child module `main.inner` takes an item of `main`. The candidate `use main` would be a
/// dependency of `main` on `main.inner`, and the child depends on `main`, so applying it gives E0310
/// (the test above). What is fixed here: applying the candidate, if there is one, does not leave E0310.
#[test]
fn a_candidate_for_the_path_through_the_child_does_not_close_the_cycle() {
    let d = pkg(
        "self_child_path",
        &[
            ("main.onsa", "pub fn k() -> I32 {\n  1\n}\n\npub fn j() -> I32 {\n  main.inner.g()\n}\n"),
            ("main/inner.onsa", "use main.{k}\n\npub fn g() -> I32 {\n  k() + 1\n}\n"),
        ],
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    let fixes = fixes_of(&diagnostics(&doc)[0]).clone();
    if let Some(first) = fixes.first() {
        apply(&d, first);
        let (_, doc) = check_json(d.root(), &["."]);
        assert!(!codes(&doc).contains("E0310"), "the candidate closes the cycle: {doc}");
    }
}

// ---- the head of a `use` that is a name a `use` took (S-37) -------------------------------------------

/// §15.1: `use std.math` and then `use math.{sin}` is E0302 with one candidate, `use std.math.{sin}`; the
/// whole list stays in the candidate; applying it leaves nothing; and a name that a `use` of a child
/// module took (`use util.counter`, `use counter.{next}`) gets the path of the child.
#[test]
fn the_head_that_a_use_took_gets_the_candidate_of_its_full_path() {
    let counter = "pub fn next(x: I32) -> I32 {\n  x + 1\n}\n";
    let cases: [(&str, &str, &str); 3] = [
        ("std_one", "use std.math\n\nuse math.{sin}\n", "use std.math.{sin}"),
        ("std_list", "use std.math\n\nuse math.{sin, cos}\n", "use std.math.{sin, cos}"),
        ("child", "use util.counter\n\nuse counter.{next}\n", "use util.counter.{next}"),
    ];
    for (tag, main, want) in cases {
        let d = pkg(tag, &[("main.onsa", main), ("util.onsa", &f("double")), ("util/counter.onsa", counter)]);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0302"]), "{tag}: {doc}");
        let fixes = fixes_of(&diagnostics(&doc)[0]);
        assert_eq!(fixes.len(), 1, "{tag}: one candidate: {doc}");
        apply(&d, &fixes[0]);
        assert!(use_lines(&d, "main.onsa").iter().any(|l| l == want), "{tag}: {:?}", use_lines(&d, "main.onsa"));
        assert_clean(&d, &format!("{tag}: after the candidate"));
    }
}

/// §15.1, §18.1: a candidate of a `use` head binds what the `use` names, so it is not given when that
/// name cannot be bound there: an item of the module of the name (`use math.{sin}` with `fn sin`, an
/// E0304 after it), or a builtin name of a flow (`use fx.{prev}` would be `use prev`, an E0304, S-542).
#[test]
fn a_use_head_candidate_binds_only_free_names() {
    let sin = "use std.math\n\nuse math.{sin}\n\nfn sin() -> I32 {\n  1\n}\n";
    let d = pkg("head_clash", &[("main.onsa", sin)]);
    let (_, doc) = check_json(d.root(), &["."]);
    let e = of_code(&doc, "E0302");
    assert_eq!(e.len(), 1, "{doc}");
    assert!(fixes_of(e[0]).is_empty(), "{doc}");
    let d = fx("own_prev", &[("prev.onsa", &f("g")), ("main.onsa", "use fx.{prev}\n")]);
    let (_, doc) = check_json(d.root(), &["."]);
    let e: Vec<&Value> =
        of_code(&doc, "E0302").into_iter().filter(|d| span_of(&d["span"]).file == "main.onsa").collect();
    assert_eq!(e.len(), 1, "{doc}");
    assert!(fixes_of(e[0]).is_empty(), "{doc}");
}

/// §15.1, §18.1: the head is a function (the one a `use` took, one of the module): the full path of the
/// binding is not a module, so the candidate would leave the E0302 and is not given.
#[test]
fn the_head_that_is_a_function_has_no_candidate() {
    let d = pkg(
        "head_function",
        &[
            ("main.onsa", "use util.{double}\n\nfn local() -> I32 {\n  1\n}\n\nuse double.{x}\nuse local.{y}\n"),
            ("util.onsa", &f("double")),
        ],
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(of_code(&doc, "E0302").len(), 2, "{doc}");
    for e in of_code(&doc, "E0302") {
        assert!(fixes_of(e).is_empty(), "{e}");
    }
}

/// §15.1: a head that is the module at the root or a dependency is not E0302, and a binding of the same
/// name does not take it (the control of the candidates above: `use util` takes `util`, the head `util` is
/// the module).
#[test]
fn a_head_that_is_a_root_module_is_not_a_binding() {
    let d = pkg(
        "head_root",
        &[
            ("main.onsa", "use util\nuse std.math\nuse util.counter\nuse std.math.{sin}\n"),
            ("util.onsa", &f("double")),
            ("util/counter.onsa", &f("next")),
        ],
    );
    assert_clean(&d, "heads that are modules of the root and std");
}

// ---- the own package name at the head (S-663, R-106) --------------------------------------------------

fn fx_util() -> [(&'static str, &'static str); 3] {
    [
        ("util.onsa", "pub fn helper() -> I32 {\n  1\n}\n"),
        ("a.onsa", "pub fn fa() -> I32 {\n  1\n}\n"),
        ("b.onsa", "pub fn fb() -> I32 {\n  2\n}\n"),
    ]
}

/// §15.1: a `use` that starts with the own package name is E0302 with the candidate that takes the name
/// off, and for a list one `use` per element: `use fx.util.{helper}` is `use util.{helper}`, `use fx.util`
/// is `use util`, `use fx.{util}` is `use util`, `use fx.{a, b}` is `use a` and `use b` (two lines).
#[test]
fn the_own_package_name_at_the_head_gets_the_candidate_that_takes_it_off() {
    let cases: [(&str, &str, &[&str]); 4] = [
        ("items", "use fx.util.{helper}\n", &["use util.{helper}"]),
        ("module", "use fx.util\n", &["use util"]),
        ("list_one", "use fx.{util}\n", &["use util"]),
        ("list_two", "use fx.{a, b}\n", &["use a", "use b"]),
    ];
    for (tag, main, want) in cases {
        let mut files = fx_util().to_vec();
        files.push(("main.onsa", main));
        let d = fx(&format!("own_{tag}"), &files);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0302"]), "{tag}: {doc}");
        assert_eq!(diagnostics(&doc).len(), 1, "{tag}: {doc}");
        let fixes = fixes_of(&diagnostics(&doc)[0]);
        assert_eq!(fixes.len(), 1, "{tag}: one candidate: {doc}");
        apply(&d, &fixes[0]);
        let got = use_lines(&d, "main.onsa");
        assert_eq!(got, want.iter().map(|s| s.to_string()).collect::<Vec<_>>(), "{tag}");
        assert_clean(&d, &format!("{tag}: after the candidate"));
    }
}

/// §15.1: `use fx` takes the package itself by its own name: E0302 with no candidate (the way to repair it
/// also reaches the paths in the bodies), and a note that shows how to take a module directly.
#[test]
fn use_of_the_own_package_has_no_candidate_and_a_note() {
    let mut files = fx_util().to_vec();
    files.push(("main.onsa", "use fx\n"));
    let d = fx("own_whole", &files);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    let e = &diagnostics(&doc)[0];
    assert!(fixes_of(e).is_empty(), "{e}");
    assert!(!notes_of(e).is_empty(), "the note shows the module taken directly: {e}");
}

/// §18.1: the candidate that takes the package name off must be safe. `use fx.nosuch.{x}` has no module
/// `nosuch` at the root, so `use nosuch.{x}` is E0302 again and the candidate is not given. (The text of
/// §15.1 says "the candidate is to take the name off"; this reads the safety of §18.1 over it.)
#[test]
fn the_own_package_name_before_a_name_that_is_nothing_has_no_candidate() {
    let mut files = fx_util().to_vec();
    files.push(("main.onsa", "use fx.nosuch.{x}\n"));
    let d = fx("own_nothing", &files);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert!(fixes_of(&diagnostics(&doc)[0]).is_empty(), "{doc}");
}

/// §15.1, §18.1: a list with no name after the own package name (`use fx.{}`, on two lines, with a comment
/// in it, `pub use`, after a module) has no candidate, and the check ends with its E0302, not an internal
/// error. (Its E0002 is S-515, W5-11.)
#[test]
fn an_empty_list_after_the_own_package_name_has_no_candidate() {
    let cases = [
        ("one_line", "main.onsa", "use fx.{}\n"),
        ("lines", "main.onsa", "use fx.{\n}\n"),
        ("comment", "dsp/synth.onsa", "use fx.{ // c\n}\n"),
        ("pub", "main.onsa", "pub use fx.{}\n"),
        ("module", "main.onsa", "use fx.util.{}\n"),
    ];
    for (tag, file, text) in cases {
        let mut files = fx_util().to_vec();
        files.push((file, text));
        let d = fx(&format!("own_empty_{tag}"), &files);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0302"]), "{tag}: {doc}");
        assert!(diagnostics(&doc).iter().all(|e| fixes_of(e).is_empty()), "{tag}: {doc}");
    }
}

/// §15.1, §18.1: a list that names one name twice (`use fx.{a, a}`, `use fx.util.{helper, helper}`, and
/// `use math.{sin, sin}` after `use std.math`) has no candidate: what it would write binds the name twice,
/// an E0304 that the failed `use` did not have.
#[test]
fn a_list_with_a_name_twice_has_no_candidate() {
    let cases = [
        ("own_list", "use fx.{a, a}\n"),
        ("own_module", "use fx.util.{helper, helper}\n"),
        ("binding", "use std.math\n\nuse math.{sin, sin}\n"),
    ];
    for (tag, text) in cases {
        let mut files = fx_util().to_vec();
        files.push(("main.onsa", text));
        let d = fx(&format!("twice_{tag}"), &files);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0302"]), "{tag}: {doc}");
        assert!(diagnostics(&doc).iter().all(|e| fixes_of(e).is_empty()), "{tag}: {doc}");
    }
}

/// §15.1, R-39 (`tests/review-phase1/types/cyc3`): two modules take each other by the own package name.
/// Both `use` lines are E0302, each with the candidate that takes the name off; applying one leaves the
/// other E0302 alone (no cycle: the failed `use` is no dependency); applying both gives the cycle, E0310
/// alone, the diagnostic that the first repair had hidden.
#[test]
fn modules_that_take_each_other_by_the_own_package_name_end_in_the_cycle() {
    // The bodies do not use the names, so that nothing but the `use` lines is reported (the names of a
    // failed `use` that stay silent are U3b).
    let a = "use fx.b.{g}\n\npub fn f() -> I32 {\n  1\n}\n";
    let b = "use fx.a.{f}\n\npub fn g() -> I32 {\n  2\n}\n";
    let d = fx("cyc3", &[("a.onsa", a), ("b.onsa", b)]);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 2, "{doc}");
    for e in diagnostics(&doc) {
        assert_eq!(fixes_of(e).len(), 1, "{e}");
    }
    let first = fixes_of(&diagnostics(&doc)[0])[0].clone();
    let second = fixes_of(&diagnostics(&doc)[1])[0].clone();
    apply(&d, &first);
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(codes(&doc), set(&["E0302"]), "after one candidate: {doc}");
    assert_eq!(diagnostics(&doc).len(), 1, "after one candidate: {doc}");
    d.write("a.onsa", a);
    d.write("b.onsa", b);
    apply(&d, &first);
    // The second candidate was made for the text before the first was applied; the spans of the two
    // files are separate, so it applies to the other file as it is.
    apply(&d, &second);
    assert_cycle(&d, "both package names taken off");
}

/// §15.1 (S-663: "a module at the root with the same name is what the name points to"): the package `fx`
/// with a module `fx.onsa`: `use fx.{g}` takes `g` of that module, not the own package name. No
/// diagnostic. (The same case with tests is `tests/spec/packages/use_own_name_module`.)
#[test]
fn a_root_module_with_the_name_of_the_package_is_what_the_name_points_to() {
    let d = fx("own_module", &[("fx.onsa", &f("g")), ("main.onsa", "use fx.{g}\nuse fx\n")]);
    assert_clean(&d, "use fx.{g} and use fx with the module fx");
}

// ---- a path in a body that names the own package or module (S-673, R-268) ----------------------------

/// The package has one E0302 in `file`, with one candidate; applying it leaves no diagnostic, and the
/// lines of `file` that start with `use ` are `uses`.
fn assert_body_candidate(d: &Dir, file: &str, uses: &[&str], what: &str) {
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{what}: {}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{what}: {doc}");
    let e = &diagnostics(&doc)[0];
    assert_eq!(span_of(&e["span"]).file, file, "{what}: {doc}");
    assert_eq!(fixes_of(e).len(), 1, "{what}: one candidate: {e}");
    apply(d, &fixes_of(e)[0]);
    assert_eq!(use_lines(d, file), uses.iter().map(|s| s.to_string()).collect::<Vec<_>>(), "{what}");
    assert_clean(d, &format!("{what}: after the candidate"));
}

/// The package has one E0302, with no candidate and a note.
fn assert_body_no_candidate(d: &Dir, what: &str) {
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{what}: {}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{what}: {doc}");
    assert_eq!(diagnostics(&doc).len(), 1, "{what}: {doc}");
    let e = &diagnostics(&doc)[0];
    assert!(fixes_of(e).is_empty(), "{what}: {e}");
    assert!(!notes_of(e).is_empty(), "{what}: the note shows the form: {e}");
}

/// §15.1, S-673: `fx.util.helper()` in the package `fx` takes `fx.` off and adds `use util`; with
/// `use util` there, it only takes `fx.` off.
#[test]
fn a_body_path_from_the_own_package_name_takes_it_off() {
    let call = "pub fn run() -> I32 {\n  fx.util.helper()\n}\n";
    let d = fx("body_own_pkg", &[("util.onsa", &f("helper")), ("main.onsa", call)]);
    assert_body_candidate(&d, "main.onsa", &["use util"], "no use of util");
    let d = fx("body_own_pkg_used", &[("util.onsa", &f("helper")), ("main.onsa", &format!("use util\n\n{call}"))]);
    assert_body_candidate(&d, "main.onsa", &["use util"], "use util there");
}

/// §15.1, S-673: a path that names the module itself by its name or by its path from the root takes that
/// part off (`main.other()` is `other()`, `synth.g()` and `dsp.synth.g()` in `dsp/synth.onsa` are
/// `g()`), and a child module after it gets the `use` of the child (`main.inner.g()` is `use main.inner`
/// and `inner.g()`).
#[test]
fn a_body_path_that_names_the_module_itself_takes_it_off() {
    let other = "pub fn other() -> I32 {\n  1\n}\n";
    let d = pkg("body_self_root", &[("main.onsa", &format!("{other}\npub fn j() -> I32 {{\n  main.other()\n}}\n"))]);
    assert_body_candidate(&d, "main.onsa", &[], "main.other()");
    for (tag, call) in [("body_self_name", "synth.g()"), ("body_self_path", "dsp.synth.g()")] {
        let text = format!("pub fn g() -> I32 {{\n  1\n}}\n\npub fn j() -> I32 {{\n  {call}\n}}\n");
        let d = pkg(tag, &[("dsp/synth.onsa", &text)]);
        assert_body_candidate(&d, "dsp/synth.onsa", &[], call);
    }
    let main = "pub fn j() -> I32 {\n  main.inner.g()\n}\n";
    let d = pkg("body_self_child", &[("main.onsa", main), ("main/inner.onsa", &f("g"))]);
    assert_body_candidate(&d, "main.onsa", &["use main.inner"], "main.inner.g()");
}

/// §15.1, S-673: a head that is the name of a module at the root and the own name of a module below it
/// is read as the module at the root first (`util.f()` in `dsp/util.onsa` is `use util`), and as the own
/// name when the module at the root has no `f`.
#[test]
fn a_head_that_is_a_module_at_the_root_and_the_own_name_reads_the_root_first() {
    let call = "pub fn j() -> I32 {\n  util.f()\n}\n";
    let d = pkg("root_first", &[("util.onsa", &f("f")), ("dsp/util.onsa", call)]);
    assert_body_candidate(&d, "dsp/util.onsa", &["use util"], "the root has f");
    let d = pkg("root_then_own", &[("util.onsa", &f("g")), ("dsp/util.onsa", &format!("{}\n{call}", f("f")))]);
    assert_body_candidate(&d, "dsp/util.onsa", &[], "only the module itself has f");
}

/// §15.1, §18.1, R-268: the candidate is given only when the path is then read whole: `std.serde.decode(1)`
/// (no `serde` in `std`) and `util.nosuch()` have none; `fx.nosuch.f()` and `main.nosuch()` have none
/// and a note that shows the form.
#[test]
fn a_candidate_is_given_only_when_the_path_is_then_read_whole() {
    let body = |call: &str| format!("pub fn j() -> I32 {{\n  {call}\n}}\n");
    let d = pkg("rest_std", &[("main.onsa", &body("std.serde.decode(1)"))]);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(of_code(&doc, "E0302").iter().all(|e| fixes_of(e).is_empty()), "{doc}");
    let d = pkg("rest_util", &[("util.onsa", &f("g")), ("main.onsa", &body("util.nosuch()"))]);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(of_code(&doc, "E0302").iter().all(|e| fixes_of(e).is_empty()), "{doc}");
    assert_body_no_candidate(&fx("rest_own", &[("main.onsa", &body("fx.nosuch.f()"))]), "fx.nosuch.f()");
    assert_body_no_candidate(&pkg("rest_self", &[("main.onsa", &body("main.nosuch()"))]), "main.nosuch()");
}

/// §2.2, S-542: a module at the root with a builtin name of a flow (`prev.onsa`) cannot be taken by
/// `use prev`, so `prev.f()` has no candidate, and the note shows the `use` of the item.
#[test]
fn a_head_that_a_use_cannot_bind_has_a_note() {
    let d = pkg("head_prev", &[("prev.onsa", &f("f")), ("main.onsa", "pub fn j() -> I32 {\n  prev.f()\n}\n")]);
    let (_, doc) = check_json(d.root(), &["."]);
    let found: Vec<&Value> =
        of_code(&doc, "E0302").into_iter().filter(|e| span_of(&e["span"]).file == "main.onsa").collect();
    assert_eq!(found.len(), 1, "{doc}");
    assert!(fixes_of(found[0]).is_empty(), "{doc}");
    assert!(!notes_of(found[0]).is_empty(), "{doc}");
}

// ---- a `use` that failed in the names stage is no dependency (S-678, W4-03 U3b1) ---------------------

/// The text of a module that has `use_line` first and a function `f` (so that another module can take
/// `f`), and the text of the module `b` that takes `f` of `a`.
fn takes_f(use_line: &str) -> String {
    format!("{use_line}\n\npub fn f() -> I32 {{\n  1\n}}\n")
}

const B_TAKES_A: &str = "use a.{f}\n\npub fn g() -> I32 {\n  f()\n}\n";
const B_WITH_COLOR: &str = "use a.{f}\n\npub enum Color {\n  Red,\n}\n\npub fn g() -> I32 {\n  f()\n}\n";

/// §15.1, §18.1 (S-678): a `use` that fails in the names stage is no dependency, so `a` and `b` that take
/// each other are not a cycle while one of the two `use` lines fails: the diagnostic is the E0302 of the
/// failed `use`, and E0310 comes only when the name is written right. The failed forms: the last name is
/// not there, a step of the path is not there, an enumerator, the own package name at the head, a head
/// that is nothing.
#[test]
fn a_failed_use_is_no_dependency_and_the_cycle_comes_when_the_name_is_right() {
    // (tag, the package manifest name, the failed `use` of `a`)
    let forms = [
        ("last", "demo", "use b.{nosuch}"),
        ("step", "demo", "use b.nosuch.{x}"),
        ("variant", "demo", "use b.Color.{Red}"),
        ("own_name", "fx", "use fx.b.{g}"),
        ("head", "demo", "use missing.{g}"),
    ];
    let mut problems: Vec<String> = Vec::new();
    for (tag, pkg_name, failed) in forms {
        let d = Dir::bare(&format!("failed_edge_{tag}"));
        d.write("onsa.toml", &format!("[package]\nname = \"{pkg_name}\"\nedition = \"2026\"\n"));
        d.write("a.onsa", &takes_f(failed));
        d.write("b.onsa", B_WITH_COLOR);
        let (out, doc) = check_json(d.root(), &["."]);
        if out.code != 1 || codes(&doc) != set(&["E0302"]) || diagnostics(&doc).len() != 1 {
            problems.push(format!("{tag}: want only the E0302 of the failed `use`, no cycle: {doc}"));
        }
        d.write("a.onsa", &takes_f("use b.{g}"));
        let (out, doc) = check_json(d.root(), &["."]);
        if out.code != 1 || codes(&doc) != set(&["E0310"]) {
            problems.push(format!("{tag}: with the name written right, want the cycle (E0310): {doc}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1 (S-678): the names of a list that are there are dependencies as always. `use b.{g, nosuch}` is a
/// cycle with `use a.{f}` of `b`: E0310 is reported. (Whether the E0302 of `nosuch` is reported with it
/// is not fixed, S-678 leaves it to the rule of the unit.)
#[test]
fn the_names_of_a_list_that_are_there_still_make_the_dependency() {
    let d = pkg("failed_edge_list", &[("a.onsa", &takes_f("use b.{g, nosuch}")), ("b.onsa", B_TAKES_A)]);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(codes(&doc).contains("E0310"), "{doc}");
}

/// §15.1 (S-678, S-679): a module does not take itself (`use main` is E0302), and the failed `use` makes no
/// dependency on the modules below: `main.inner` takes an item of `main`, and there is no cycle.
#[test]
fn the_use_of_the_module_itself_makes_no_dependency_on_the_modules_below() {
    let d = pkg(
        "failed_edge_self",
        &[
            ("main.onsa", "use main\n\npub fn k() -> I32 {\n  1\n}\n"),
            ("main/inner.onsa", "use main.{k}\n\npub fn g() -> I32 {\n  k()\n}\n"),
        ],
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 1, "{doc}");
}

// ---- the note of a candidate that is left out for a cycle (S-682) -------------------------------------

/// The messages of the notes of `diagnostic`, joined.
fn note_text(diagnostic: &Value) -> String {
    notes_of(diagnostic).iter().filter_map(|n| n.get("message").and_then(Value::as_str)).collect::<Vec<_>>().join("\n")
}

/// §15.1 (S-682): the candidate that takes the package name off the head of a `use` is left out when the
/// form would close a cycle, and the note shows the form that was left out and the module that closes the
/// cycle. `use fx.a.{f}` of `b` would be `use a.{f}`, and `a` takes `b`: no candidate, and the note has
/// `use a.{f}`. The control: when `a` does not take `b` the candidate is there.
#[test]
fn a_use_head_candidate_left_out_for_a_cycle_has_a_note_with_the_form() {
    let d = fx(
        "note_head",
        &[("a.onsa", &takes_f("use b.{g}")), ("b.onsa", "use fx.a.{f}\n\npub fn g() -> I32 {\n  2\n}\n")],
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 1, "{doc}");
    let e = &diagnostics(&doc)[0];
    assert_eq!(span_of(&e["span"]).file, "b.onsa", "{doc}");
    assert!(fixes_of(e).is_empty(), "the form would close a cycle: {e}");
    let text = note_text(e);
    assert!(text.contains("use a.{f}"), "the note shows the form that was left out: {text:?} in {e}");

    let d = fx(
        "note_head_control",
        &[("a.onsa", &takes_f("")), ("b.onsa", "use fx.a.{f}\n\npub fn g() -> I32 {\n  2\n}\n")],
    );
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(fixes_of(&diagnostics(&doc)[0]).len(), 1, "no cycle, so the candidate: {doc}");

    // The list form: `use fx.{a}` is `use a`.
    let d = fx(
        "note_head_list",
        &[("a.onsa", &takes_f("use b.{g}")), ("b.onsa", "use fx.{a}\n\npub fn g() -> I32 {\n  2\n}\n")],
    );
    let (_, doc) = check_json(d.root(), &["."]);
    let e = &diagnostics(&doc)[0];
    assert!(fixes_of(e).is_empty(), "{e}");
    assert!(note_text(e).contains("use a"), "{e}");
}

/// §15.1 (S-682): the same for the candidates of a path in a body that start with the own package name or
/// the name of the module itself: `fx.b.g()` in `a` would be `use b` and `b.g()`, and `b` takes `a`;
/// `main.inner.g()` in `main` would be `use main.inner` and `inner.g()`, and `main.inner` takes `main`.
/// There is no candidate, and a note shows the form and the module of the cycle. (That the note does not
/// *recommend* the form that closes the cycle is not checked here, the spec fixes no wording.)
#[test]
fn a_body_candidate_left_out_for_a_cycle_has_a_note_with_the_form() {
    let d = fx("note_body_own", &[("a.onsa", "pub fn f() -> I32 {\n  fx.b.g()\n}\n"), ("b.onsa", B_TAKES_A)]);
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    let e = &diagnostics(&doc)[0];
    assert!(fixes_of(e).is_empty(), "{e}");
    assert!(note_text(e).contains("use b"), "the form that was left out: {e}");

    let d = pkg(
        "note_body_self",
        &[
            ("main.onsa", "pub fn j() -> I32 {\n  main.inner.g()\n}\n"),
            ("main/inner.onsa", "use main\n\npub fn g() -> I32 {\n  1\n}\n"),
        ],
    );
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    let e = &diagnostics(&doc)[0];
    assert!(fixes_of(e).is_empty(), "{e}");
    assert!(note_text(e).contains("main.inner"), "the module of the cycle: {e}");
}

// ---- the note that narrows a `use` (S-683) ------------------------------------------------------------

/// Whether the package is a cycle (E0310 alone, exit 1) whose every diagnostic has notes and none of
/// them has a position (the rule note: narrowing does not cut), or, with `positioned`, whose every
/// diagnostic has a note with a position (the note at the `use` to narrow). `None` when it is so, the
/// reason when it is not.
fn narrowing_problem(d: &Dir, positioned: bool) -> Option<String> {
    let (out, doc) = check_json(d.root(), &["."]);
    if out.code != 1 || codes(&doc) != set(&["E0310"]) {
        return Some(format!("want the cycle alone: {doc}"));
    }
    for e in of_code(&doc, "E0310") {
        let notes = notes_of(e);
        let ok = if positioned {
            notes.iter().any(|n| n.get("span").is_some())
        } else {
            !notes.is_empty() && notes.iter().all(|n| n.get("span").is_none())
        };
        if !ok {
            return Some(format!("want {} note: {e}", if positioned { "a positioned" } else { "only the rule" }));
        }
    }
    None
}

/// §15.1 (S-683): the note that narrows a `use` is given only when the `use` can be written narrower and
/// that cuts the cycle. A module that has no file of its own, only a directory (`b/` with `b/c.onsa`),
/// has no items, so `use b` cannot be narrowed to an item of `b`, and no narrowing helps: `use b` with the
/// body `b.c.s()` and `b/c.onsa` taking `a.{f}` is a cycle whose note has no `use` to narrow. The control
/// with a file `b.onsa` is the narrowing `use b.{g}`, which cuts it. When another `use` of the same cycle
/// can be narrowed and this one cannot, the cycle stays, so there is no narrowing note.
#[test]
fn the_narrowing_note_is_given_only_for_a_use_that_can_be_written_narrower() {
    let a_uses_b = "use b\n\npub fn f() -> I32 {\n  b.c.s()\n}\n";
    let c_takes_a = "use a.{f}\n\npub fn s() -> I32 {\n  f()\n}\n";
    let mut problems: Vec<String> = Vec::new();
    let mut check = |tag: &str, d: Dir, positioned: bool| {
        if let Some(p) = narrowing_problem(&d, positioned) {
            problems.push(format!("{tag}: {p}"));
        }
    };
    check("b is only a directory", pkg("narrow_dir_only", &[("a.onsa", a_uses_b), ("b/c.onsa", c_takes_a)]), false);
    check(
        "b is a directory above a directory",
        pkg(
            "narrow_dir_only_deep",
            &[("a.onsa", "use b\n\npub fn f() -> I32 {\n  b.c.d.s()\n}\n"), ("b/c/d.onsa", c_takes_a)],
        ),
        false,
    );
    check(
        "b has a file (the control)",
        pkg("narrow_with_file", &[("a.onsa", a_uses_b), ("b.onsa", &f("g")), ("b/c.onsa", c_takes_a)]),
        true,
    );
    check(
        "one `use` can be narrowed and the other cannot",
        pkg(
            "narrow_one_of_two",
            &[
                ("a.onsa", "use b\nuse e\n\npub fn f() -> I32 {\n  b.c.s() + e.h()\n}\n"),
                ("b/c.onsa", c_takes_a),
                ("e.onsa", &f("h")),
                ("e/inner.onsa", "use a.{f}\n\npub fn t() -> I32 {\n  f()\n}\n"),
            ],
        ),
        false,
    );
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}
