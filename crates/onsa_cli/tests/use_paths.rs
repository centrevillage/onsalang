//! The path of a `use` and the path of a module, seen from the command line: where a path starts, what it
//! passes through, and that the result does not depend on the order or the place of the `use` lines
//! (spec §15.1, §18.1; S-37, S-312, S-313, S-611; R-46, R-50, R-250; W4-03 U2a).
//!
//! What the spec fixes, and so what is checked here:
//! - a `use` is decided by itself, wherever it is written and whatever the other `use` lines are
//!   (§15.1), so writing the same lines in every order, or moving them among the items, gives the same
//!   diagnostics;
//! - the head of the path is a module at the root or a dependency, never a name that the module took
//!   (`use std.math` and then `use math.{sin}` is E0302, in either order); the middle and the end of
//!   the path in another module are looked up in its definitions (items and child modules) alone, so a
//!   `use` binding there is not found (E0302) and hides no child module (R-250, S-611);
//! - the path of a module is the sequence of the elements of its file: `a.b.onsa` and `a/b.onsa` are two
//!   modules and both are checked (R-46); a directory with no file is passed through (`a/b/c.onsa` is
//!   `a.b.c`), and `a.onsa` with `a/b.onsa` is a module and its child.
//!
//! The same cases, with the positions of the marks, are under `tests/spec/packages` (`use_*`,
//! `module_*`); here it is the exit code, the document of `check --json` and the names of the modules in
//! `test --json`.
//!
//! Not written here: the candidates of E0302 and the E0304 / E0305 / E0310 of the overlaps and the
//! cycles (U3a), the names of the failed `use` that are silent (U3b), the visibility (U4).
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

/// `(code, text of the line)` of every diagnostic of `file`, in a sorted list: the diagnostics of a
/// layout whose lines moved are compared by what they point at, not by the line number.
fn by_line_text(d: &Dir, doc: &Value, file: &str) -> Vec<(String, String)> {
    let text = std::fs::read_to_string(d.root().join(file)).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    let mut v: Vec<(String, String)> = diagnostics(doc)
        .iter()
        .map(|x| {
            let sp = span_of(&x["span"]);
            assert_eq!(sp.file, file, "{doc}");
            (str_of(x, "code").to_string(), lines[(sp.line - 1) as usize].trim().to_string())
        })
        .collect();
    v.sort();
    v
}

/// Every order of a list.
fn permutations<T: Clone>(items: &[T]) -> Vec<Vec<T>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let head = rest.remove(i);
        for mut tail in permutations(&rest) {
            tail.insert(0, head.clone());
            out.push(tail);
        }
    }
    out
}

const UTIL: &str = "pub fn double(x: I32) -> I32 {\n  x * 2\n}\n";
const SUB: &str = "pub fn h() -> I32 {\n  3\n}\n";

// ---- a `use` is decided by itself (R-50) ------------------------------------------------------------

/// §15.1: the four lines make two bindings (`math` from std, `sub` from `util`) and two paths that start
/// from them (`use math.{sin}`, `use sub.{h}`), which are E0302 wherever the lines are, in whatever
/// order. The 24 orders give the two E0302 and nothing else.
#[test]
fn every_order_of_the_use_lines_gives_the_same_diagnostics() {
    let lines = ["use std.math", "use util.sub", "use math.{sin}", "use sub.{h}"];
    let want =
        vec![("E0302".to_string(), "use math.{sin}".to_string()), ("E0302".to_string(), "use sub.{h}".to_string())];
    for order in permutations(&lines) {
        let d = Dir::pkg("use_orders");
        d.write("util.onsa", UTIL);
        d.write("util/sub.onsa", SUB);
        d.write("main.onsa", &format!("{}\n\npub fn one() -> I32 {{\n  1\n}}\n", order.join("\n")));
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{order:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(by_line_text(&d, &doc, "main.onsa"), want, "{order:?}: {doc}");
    }
}

/// §15.1: the same lines at the top of the file, among the items, or after the last item and a test,
/// give the same diagnostics (a `use` can be written anywhere among the items). The names the lines take
/// are used above and below them.
#[test]
fn the_place_of_the_use_lines_among_the_items_does_not_change_the_diagnostics() {
    let uses = ["use util.{double}", "use util.sub", "use sub.{h}", "use std.math"];
    let items = [
        "pub fn a() -> I32 {\n  double(1)\n}",
        "pub fn b() -> I32 {\n  sub.h()\n}",
        "test \"t\" {\n  assert a() == 2\n}",
    ];
    let top = format!("{}\n\n{}\n", uses.join("\n"), items.join("\n\n"));
    let bottom = format!("{}\n\n{}\n", items.join("\n\n"), uses.join("\n"));
    let between = format!(
        "{}\n\n{}\n\n{}\n\n{}\n\n{}\n",
        items[0],
        uses[0..2].join("\n"),
        items[1],
        uses[2..].join("\n"),
        items[2]
    );
    let mut results = Vec::new();
    for (tag, text) in [("top", top), ("bottom", bottom), ("between", between)] {
        let d = Dir::pkg(&format!("use_places_{tag}"));
        d.write("util.onsa", UTIL);
        d.write("util/sub.onsa", SUB);
        d.write("main.onsa", &text);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        results.push((tag, by_line_text(&d, &doc, "main.onsa")));
    }
    let want = vec![("E0302".to_string(), "use sub.{h}".to_string())];
    for (tag, got) in &results {
        assert_eq!(got, &want, "{tag}");
    }
}

// ---- the middle and the end of a path in another module (R-250, S-611) ------------------------------

fn r250(tag: &str, main: &str, with_child: bool) -> Dir {
    let d = Dir::pkg(tag);
    d.write("main.onsa", main);
    d.write("kp/inner.onsa", "pub fn g() -> I32 {\n  2\n}\n");
    if with_child {
        d.write("main/inner.onsa", "pub fn h() -> I32 {\n  3\n}\n");
        d.write("other.onsa", "use main.inner.{h}\n\npub fn m() -> I32 {\n  h()\n}\n");
    }
    d
}

/// §15.1: `main` has no child `inner`, so `use main.inner.{g}` is E0302 after the `use kp.inner` that
/// makes the binding `inner`, and before it. Neither order lets the binding be a step of the path.
#[test]
fn a_use_binding_is_not_a_step_of_a_path_in_either_order() {
    for (tag, main, line) in [
        ("r250_after", "use kp.inner\nuse main.inner.{g}\n\npub fn k() -> I32 {\n  1\n}\n", 2),
        ("r250_before", "use main.inner.{g}\nuse kp.inner\n\npub fn k() -> I32 {\n  1\n}\n", 1),
    ] {
        let d = r250(tag, main, false);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), set(&[("E0302", "main.onsa", line)]), "{tag}: {doc}");
    }
}

/// §15.1, S-611: `main` takes `kp.inner` as the name `inner`, and `main/inner.onsa` is its child module,
/// so the other module's `use main.inner.{h}` is the child and the program has no diagnostic.
#[test]
fn a_use_binding_does_not_hide_a_child_module_from_another_module() {
    let d = r250("r250_hides", "use kp.inner\n\npub fn k() -> I32 {\n  inner.g()\n}\n", true);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// §15.1: what `main` took with a `use` is not found by the other modules: `main.{inner}` and `main.{l}`
/// are E0302 when `main` has no child module or item of the name (and not E0303, which says the name
/// exists but is not visible).
#[test]
fn a_name_that_only_a_use_has_is_not_found_in_another_module() {
    let d = Dir::pkg("only_a_use");
    d.write("main.onsa", "use kp.inner\nuse kp.leaf.{l}\n\npub fn k() -> I32 {\n  1\n}\n");
    d.write("kp/inner.onsa", "pub fn g() -> I32 {\n  2\n}\n");
    d.write("kp/leaf.onsa", "pub fn l() -> I32 {\n  3\n}\n");
    d.write("other.onsa", "use main.{inner}\nuse main.{l}\nuse main.{k}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0302", "other.onsa", 1), ("E0302", "other.onsa", 2)]), "{doc}");
}

// ---- the path of a module is the sequence of the elements of its file (S-312, S-313, R-46) ----------

fn dupmod(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("main.onsa", "use a.b.{two}\nuse a.b.{one}\n\npub fn x() -> I32 {\n  two()\n}\n");
    d.write("a.b.onsa", "pub fn one() -> I32 {\n  1\n}\n\npub fn also_broken() -> I32 {\n  yyy\n}\n");
    d.write("a/b.onsa", "pub fn two() -> I32 {\n  2\n}\n\npub fn broken() -> I32 {\n  zzz\n}\n");
    d
}

/// §15.1, §2.3 (R-46): `a.b.onsa` and `a/b.onsa` are two modules. Both are read and checked: the E0320
/// of the file name `a.b` at the top of `a.b.onsa`, the unknown name in each, and the `one` that only
/// `a.b.onsa` has, which `use a.b.{one}` does not find (it means `a/b.onsa`).
#[test]
fn a_dotted_file_name_and_a_directory_are_two_modules_and_both_are_checked() {
    let d = dupmod("dupmod");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        places(&doc),
        set(
            &[("E0320", "a.b.onsa", 1), ("E0302", "a.b.onsa", 6), ("E0302", "a/b.onsa", 6), ("E0302", "main.onsa", 2),]
        ),
        "{doc}"
    );
}

/// §15.1: a file passed by its path gives the diagnostics of its own module only, and the two files
/// of the same dotted path give different ones.
#[test]
fn a_file_of_the_dotted_pair_is_checked_as_its_own_module() {
    let d = dupmod("dupmod_files");
    let (_, doc) = check_json(d.root(), &["a/b.onsa"]);
    assert_eq!(places(&doc), set(&[("E0302", "a/b.onsa", 6)]), "{doc}");
    let (_, doc) = check_json(d.root(), &["a.b.onsa"]);
    assert_eq!(places(&doc), set(&[("E0320", "a.b.onsa", 1), ("E0302", "a.b.onsa", 6)]), "{doc}");
}

/// §11.8, §15.1: the module of `a/b/c.onsa` is `a.b.c` though `a` and `a/b` have no file, and `a.onsa`
/// with `a/b.onsa` are `a` and `a.b`; the tests of each carry that module.
#[test]
fn the_modules_of_a_directory_only_path_and_of_a_file_with_a_directory_are_named_by_their_paths() {
    let d = Dir::pkg("module_names");
    let t = |v: i32| format!("pub fn f() -> I32 {{\n  {v}\n}}\n\ntest \"t\" {{\n  assert f() == {v}\n}}\n");
    d.write("a/b/c.onsa", &t(1));
    d.write("p.onsa", &t(2));
    d.write("p/q.onsa", &t(3));
    let (out, doc) = test_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let mut ids: Vec<String> = identities(&doc).into_iter().map(|(m, _)| m).collect();
    ids.sort();
    assert_eq!(ids, ["a.b.c", "p", "p.q"], "{doc}");
}
