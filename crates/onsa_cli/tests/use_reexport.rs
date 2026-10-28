//! The re-export `pub use`, seen from the command line (spec §15.1, §18.1, §18.2, §19.1; S-596, S-443;
//! W4-03 U3b2/t).
//!
//! What the spec fixes, and so what is checked here:
//! - a `pub use` is E0200 at the `pub`, in the names stage, with no candidate; a note shows how to take the
//!   name from its definition (`use kp.inner.{g}`), so the note holds the path of the definition (§15.1);
//! - the names it takes are failed names, in the module and in the other modules (§18.1): nothing is reported
//!   where they are used. A path that goes through the name (`use main.inner.{g}`) is E0302, and a child module
//!   of the same name is what `use main.{inner}` points to;
//! - the `pub use` of a name that is a reserved word has the E0200 of the word first and no other (S-443);
//! - `onsa fmt` formats a file that has a `pub use` (the E0200 is a diagnostic of check, not of the syntax
//!   stage that stops `fmt`, §18.2).
//!
//! The same cases, with the places of the marks, are under `tests/spec/packages/pub_use_*`. The other
//! consequences of a `pub use` that is a failed name (it makes no dependency, E0310) are in `use_name_rules.rs`.
//!
//! Not written here: the second phase (what a re-export takes, whether it is a binding that a path goes
//! through, what `onsa interface` shows), which §19.1 leaves open.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause.

mod test_support;

use std::collections::BTreeSet;
use std::path::Path;

use serde_json::Value;
use test_support::*;

fn check_json(cwd: &Path) -> (Out, Value) {
    let out = run(cwd, &["check", "--json", "."]);
    let doc = doc_of(&out);
    (out, doc)
}

fn codes(doc: &Value) -> BTreeSet<String> {
    diagnostics(doc).iter().map(|d| str_of(d, "code").to_string()).collect()
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|c| c.to_string()).collect()
}

fn note_text(diagnostic: &Value) -> String {
    array_of(diagnostic, "notes")
        .iter()
        .filter_map(|n| n.get("message").and_then(Value::as_str))
        .collect::<Vec<_>>()
        .join("\n")
}

fn f(name: &str) -> String {
    format!("pub fn {name}() -> I32 {{\n  1\n}}\n")
}

/// A package `demo` with a module `util` (the items `shown` and `other`, the child module `util.inner`).
fn util_package(tag: &str, main: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("util.onsa", &format!("{}\n{}", f("shown"), f("other")));
    d.write("util/inner.onsa", &f("g"));
    d.write("main.onsa", main);
    d
}

/// §15.1, S-596: a `pub use` is E0200 at the `pub` (line 1, column 1), whatever it takes: an item, a path to
/// an item, a list, a child module, an item of `std`, a module of `std`. The only diagnostic, with no
/// candidate, and a note that holds the path of the definition (the way to take the name from it).
#[test]
fn a_pub_use_is_an_e0200_at_the_pub_with_no_candidate_and_a_note_of_the_definition_path() {
    let forms: [(&str, &str, &str); 6] = [
        ("item_list", "pub use util.{shown}\n", "use util"),
        ("item_path", "pub use util.other\n", "use util"),
        ("list", "pub use util.{shown, other}\n", "use util"),
        ("module", "pub use util.inner\n", "use util.inner"),
        ("std_item", "pub use std.math.{sqrt}\n", "use std.math"),
        ("std_module", "pub use std.math\n", "use std"),
    ];
    let mut problems = Vec::new();
    for (tag, line, want) in forms {
        let d = util_package(&format!("reexport_{tag}"), line);
        let (out, doc) = check_json(d.root());
        if out.code != 1 || codes(&doc) != set(&["E0200"]) || diagnostics(&doc).len() != 1 {
            problems.push(format!("{tag}: want one E0200, exit code 1: {}", doc));
            continue;
        }
        let e = &diagnostics(&doc)[0];
        let sp = span_of(&e["span"]);
        if (sp.file.as_str(), sp.line, sp.col) != ("main.onsa", 1, 1) {
            problems.push(format!("{tag}: the place is the `pub` ({sp:?})"));
        }
        if !array_of(e, "fixes").is_empty() {
            problems.push(format!("{tag}: no candidate: {e}"));
        }
        let note = note_text(e);
        if !note.contains(want) {
            problems.push(format!("{tag}: the note shows the definition path {want:?}: {note:?}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1, S-596: two `pub use` in one module, in a module below and after other lines, are two E0200, one
/// for each; the other diagnostics of the file are reported with them (a `pub use` stops nothing else: the
/// `use` of a name that is not there next to it is its E0302).
#[test]
fn a_pub_use_stops_nothing_else_in_the_file() {
    let main = "use util.{missing}\npub use util.{shown}\n\npub fn run() -> I32 {\n  1\n}\n\npub use util.other\n";
    let d = util_package("reexport_others", main);
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let by_code = |c: &str| diagnostics(&doc).iter().filter(|e| str_of(e, "code") == c).count();
    assert_eq!((by_code("E0200"), by_code("E0302"), diagnostics(&doc).len()), (2, 1, 3), "{doc}");
}

/// §15.1, §18.1, S-596: the names of a `pub use` are failed names. In the module that writes it and in
/// another module, taking and using them reports nothing; the E0200 is the only diagnostic.
#[test]
fn the_names_of_a_pub_use_are_silent_in_the_module_and_in_the_others() {
    let main = "pub use util.{shown}\n\npub fn here() -> I32 {\n  shown() + other()\n}\n\npub use util.other\n";
    let d = util_package("reexport_silent", main);
    d.write("consumer.onsa", "use main.{shown, other}\n\npub fn there() -> I32 {\n  shown() + other()\n}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0200"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 2, "{doc}");
}

/// §18.1, S-596: a path through the name is E0302 (the middle of a path is read from the child modules and the
/// definitions alone): `use main.inner.{g}` after `pub use util.inner`, when `main` has no child module `inner`.
#[test]
fn a_path_through_the_name_is_e0302() {
    let d = util_package("reexport_path", "pub use util.inner\n");
    d.write("consumer.onsa", "use main.inner.{g}\n\npub fn run() -> I32 {\n  1\n}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let e302: Vec<&Value> = diagnostics(&doc).iter().filter(|e| str_of(e, "code") == "E0302").collect();
    assert_eq!(e302.len(), 1, "{doc}");
    assert_eq!(span_of(&e302[0]["span"]).file, "consumer.onsa", "{doc}");
}

/// §18.1, S-596, S-611: with a child module of the same name (`main/inner.onsa`, which has `h`), `use main.{inner}`
/// of another module is the child module and the path through it, `use main.inner.{h}`, is fine: the `pub use`
/// is the only diagnostic.
#[test]
fn a_child_module_of_the_same_name_is_what_the_use_points_to() {
    let d = util_package("reexport_child", "pub use util.inner\n");
    d.write("main/inner.onsa", &f("h"));
    d.write("consumer.onsa", "use main.{inner}\nuse main.inner.{h}\n\npub fn run() -> I32 {\n  inner.h() + h()\n}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0200"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 1, "{doc}");
}

/// §15.1, §18.1, S-596, S-611, R-254: the child module is what `use main.{inner}` takes, so the name it does not
/// have (`inner.g()`, `g` is in `util.inner` only) is an E0302 of the names stage, one, besides the E0200.
#[test]
fn a_name_the_child_module_of_the_same_name_does_not_have_is_e0302() {
    let d = util_package("reexport_child_missing", "pub use util.inner\n");
    d.write("main/inner.onsa", &f("h"));
    d.write("consumer.onsa", "use main.{inner}\n\npub fn run() -> I32 {\n  inner.g()\n}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0200", "E0302"]), "{doc}");
    let e302: Vec<&Value> = diagnostics(&doc).iter().filter(|e| str_of(e, "code") == "E0302").collect();
    assert_eq!(e302.len(), 1, "the child module has no `g`: {doc}");
    assert_eq!(span_of(&e302[0]["span"]).line, 4, "{doc}");
}

/// §15.1, S-443: the `pub use` of a reserved word has the E0200 of the word and no other: the column is the
/// word's (`pub use kp.clock` is column 12, `pub use kp.{clock}` is column 13).
#[test]
fn the_pub_use_of_a_reserved_word_has_the_e0200_of_the_word_alone() {
    for (tag, line, col) in [("path", "pub use kp.clock\n", 12), ("list", "pub use kp.{clock}\n", 13)] {
        let d = Dir::pkg(&format!("reexport_word_{tag}"));
        d.write("kp/clock.onsa", &f("tick"));
        d.write("main.onsa", line);
        let (out, doc) = check_json(d.root());
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0200"]), "{tag}: {doc}");
        assert_eq!(diagnostics(&doc).len(), 1, "{tag}: {doc}");
        assert_eq!(span_of(&diagnostics(&doc)[0]["span"]).col, col, "{tag}: {doc}");
    }
}

/// §15.1, §18.2, S-596: `onsa fmt` formats a file with a `pub use`: the rest of the file is written in its
/// canonical form (a hexadecimal literal, a `return` at the end), the `pub use` line is kept, and the
/// formatted file is the same under `--check`.
#[test]
fn fmt_formats_a_file_with_a_pub_use() {
    let d = Dir::bare("reexport_fmt");
    let rough = "pub use util.shown\n\nfn f(a: I32) -> I32 {\n  let x = 0XaB + a\n  return x\n}\n";
    let fine = "pub use util.shown\n\nfn f(a: I32) -> I32 {\n  let x = 0xAB + a\n  x\n}\n";
    d.write("main.onsa", rough);
    let file = d.root().join("main.onsa");
    let path = file.to_string_lossy().into_owned();
    let out = run(d.root(), &["fmt", "--check", &path]);
    assert_eq!(out.code, 1, "the rest of the file is not canonical: {}{}", out.stdout, out.stderr);
    let out = run(d.root(), &["fmt", &path]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(std::fs::read_to_string(&file).unwrap(), fine);
    let out = run(d.root(), &["fmt", "--check", &path]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
}
