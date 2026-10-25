//! The name a `use` takes, read by the rule of the name of a declaration, and the `use` lines that fail by a
//! rule and make no dependency (spec §15.1, §2.2, §18.1; R-266, S-596, S-678; W4-03 U3b2/t).
//!
//! What the spec fixes, and so what is checked here:
//! - the name a `use` takes (an element of the list, or the last name of a path with no list) is read as the
//!   name of a declaration: a keyword is E0002 (`use std.test`, `use match`, with a note that shows the
//!   way: a name of the list, or the path from the parent), a reserved word is E0200 at the word (`use kp.clock`,
//!   `use clock`, `use kp.{clock}`, and `when`, `reset_if`, `ser`); the words before that name are module
//!   names, keywords and reserved words included (`use kp.clock.{tick}`, `use match.{x}`);
//! - such a name is a failed name, so it is no binding (two lines that take `clock` clash with nothing) and no
//!   dependency (E0310): `a` takes `b.clock` by a path, `b/clock.onsa` takes `a`, and there is no cycle. The
//!   same for the `pub use` (E0200, S-596). Written with a name that is no word the same two modules are a
//!   cycle, which is the control of each form below.
//!
//! The same cases, with the places of the marks, are under `tests/spec/packages` (`use_names_*`,
//! `use_*_no_cycle`, `pub_use_no_cycle`).
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

fn f(name: &str) -> String {
    format!("pub fn {name}() -> I32 {{\n  1\n}}\n")
}

/// The modules the forms below take: words and a keyword, at the root and under `kp/`.
fn words_package(tag: &str, main: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("match.onsa", &f("x"));
    d.write("clock.onsa", &f("beat"));
    d.write("ser.onsa", &f("rank"));
    d.write("kp/clock.onsa", &f("tick"));
    d.write("kp/when.onsa", &f("after"));
    d.write("kp/reset_if.onsa", &f("latch"));
    d.write("main.onsa", main);
    d
}

/// §15.1, R-266: a keyword that a `use` takes is E0002, one diagnostic with a note and no candidate: as the
/// last name of a path, as the element of a list, as the name of a module of the package (`match.onsa`).
#[test]
fn a_keyword_taken_by_a_use_is_e0002_with_a_note_and_no_candidate() {
    let mut problems = Vec::new();
    for (tag, line) in [("path", "use std.test\n"), ("list", "use std.{test}\n"), ("module", "use match\n")] {
        let d = words_package(&format!("rules_keyword_{tag}"), line);
        let (out, doc) = check_json(d.root());
        if out.code != 1 || codes(&doc) != set(&["E0002"]) || diagnostics(&doc).len() != 1 {
            problems.push(format!("{tag}: want one E0002, exit code 1: {doc}"));
            continue;
        }
        let e = &diagnostics(&doc)[0];
        if !array_of(e, "fixes").is_empty() {
            problems.push(format!("{tag}: no candidate: {e}"));
        }
        if array_of(e, "notes").is_empty() {
            problems.push(format!("{tag}: a note shows the list or the path from the parent: {e}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1, §2.2, R-266: a reserved word that a `use` takes is E0200 at the word, one diagnostic with no
/// candidate: the last name of a path (`use kp.clock`), the head of a path of one name (`use clock`), an element
/// of a list (`use kp.{clock}`), and the words `when`, `reset_if`, `ser`.
#[test]
fn a_reserved_word_taken_by_a_use_is_e0200_at_the_word() {
    let forms: [(&str, u64); 6] = [
        ("use kp.clock", 8),
        ("use clock", 5),
        ("use kp.{clock}", 9),
        ("use kp.when", 8),
        ("use kp.{reset_if}", 9),
        ("use ser", 5),
    ];
    let mut problems = Vec::new();
    for (i, (line, col)) in forms.iter().enumerate() {
        let d = words_package(&format!("rules_word_{i}"), &format!("{line}\n"));
        let (out, doc) = check_json(d.root());
        if out.code != 1 || codes(&doc) != set(&["E0200"]) || diagnostics(&doc).len() != 1 {
            problems.push(format!("{line}: want one E0200, exit code 1: {doc}"));
            continue;
        }
        let e = &diagnostics(&doc)[0];
        if span_of(&e["span"]).col != *col {
            problems.push(format!("{line}: the E0200 is at the word, column {col}: {e}"));
        }
        if !array_of(e, "fixes").is_empty() {
            problems.push(format!("{line}: no candidate: {e}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1, §2.2, §18.1, R-266: the words before the name that is taken are names of modules, and the name
/// taken may be one of the module that has a word as its name: `use kp.clock.{tick}`, `use match.{x}` and
/// `use clock.{beat}` are fine; two lines that take a failed name of the same spelling clash with nothing (only
/// the E0200 of each).
#[test]
fn the_words_before_the_name_are_module_names_and_a_failed_name_clashes_with_nothing() {
    let d = words_package("rules_before", "use kp.clock.{tick}\nuse match.{x}\nuse clock.{beat}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

#[test]
fn a_failed_name_of_the_same_spelling_clashes_with_nothing() {
    let d = words_package("rules_twice", "use kp.clock\nuse clock\nuse kp.{clock}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0200"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 3, "{doc}");
}

/// The package of two modules: `a` has the line `a_use` that takes a name of `b`, and `b` (the file `b_file`)
/// takes `f` of `a`. The two are a cycle when the line is a real `use`.
fn pair(tag: &str, a_use: &str, b_file: &str, extra: &[(&str, String)]) -> Dir {
    let d = Dir::pkg(tag);
    d.write("a.onsa", &format!("{a_use}\n\n{}", f("f")));
    d.write(b_file, &format!("use a.{{f}}\n\n{}", f("g")));
    for (file, text) in extra {
        d.write(file, text);
    }
    d
}

/// §15.1, §18.1, R-266, S-596, S-678: a `use` that fails by a rule of the name (a `pub use`, a reserved word,
/// a keyword) takes a failed name, which is no dependency: the two modules that take each other that way are
/// not a cycle, and the only diagnostic is the one of the rule. The control of each form is the same
/// two modules with a `use` of a name that is none of them, which are a cycle (E0310).
#[test]
fn a_use_that_fails_by_a_rule_of_the_name_is_no_dependency() {
    // (tag, the `use` of a, the file of b, the code of the rule, the `use` of the control, the file of b in it)
    let forms: [(&str, &str, &str, &str, &str, &str); 5] = [
        ("pub_use", "pub use b.{g}", "b.onsa", "E0200", "use b.{g}", "b.onsa"),
        ("reserved_path", "use b.clock", "b/clock.onsa", "E0200", "use b.tock", "b/tock.onsa"),
        ("reserved_list", "use b.{clock}", "b/clock.onsa", "E0200", "use b.{tock}", "b/tock.onsa"),
        ("keyword", "use match", "match.onsa", "E0002", "use mach", "mach.onsa"),
        ("keyword_list", "use kw.{match}", "kw/match.onsa", "E0002", "use kw.{mach}", "kw/mach.onsa"),
    ];
    let mut problems = Vec::new();
    for (tag, a_use, b_file, code, control, control_file) in forms {
        let d = pair(&format!("rules_edge_{tag}"), a_use, b_file, &[]);
        let (out, doc) = check_json(d.root());
        if out.code != 1 || codes(&doc) != set(&[code]) {
            problems.push(format!("{tag}: want only {code}: {doc}"));
        }
        let d = pair(&format!("rules_edge_{tag}_control"), control, control_file, &[]);
        let (_, doc) = check_json(d.root());
        if !codes(&doc).contains("E0310") {
            problems.push(format!("{tag}: the control is a cycle: {doc}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1, S-596, S-678: the `pub use` that takes a name in a mutual way (`a` and `b` each `pub use` a name of
/// the other) is two E0200 and no cycle; with a plain `use` on one side the other side is the only edge, and
/// there is no cycle either.
#[test]
fn pub_use_of_each_other_is_no_cycle() {
    let d = Dir::pkg("rules_edge_pub_pair");
    d.write("a.onsa", &format!("pub use b.{{g}}\n\n{}", f("f")));
    d.write("b.onsa", &format!("pub use a.{{f}}\n\n{}", f("g")));
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0200"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 2, "{doc}");

    let d = Dir::pkg("rules_edge_pub_one_side");
    d.write("a.onsa", &format!("pub use b.{{g}}\n\n{}", f("f")));
    d.write("b.onsa", &format!("use a.{{f}}\n\n{}", f("g")));
    let (_, doc) = check_json(d.root());
    assert_eq!(codes(&doc), set(&["E0200"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 1, "{doc}");
}

/// §15.1, §11.6: two `use` of one name are an E0304 on the later `use` in the source, with the note on the
/// earlier one, whichever of the two takes the item of the namespace of a flow (`gain.process_inplace`, an item
/// the namespace has) and whichever is written first. (The same cases with the marks are
/// `tests/spec/packages/use_flow_item_clash_order`.)
#[test]
fn the_e0304_of_two_uses_of_one_name_is_on_the_later_use_in_the_source() {
    let flow = "pub flow gain(\n  x: F32 at sample,\n) -> F32 at sample {\n  x\n}\n";
    let item_from_a_flow = "use dsp.synth.gain.{process_inplace}\n";
    let item_from_a_module = "use dsp.other.{process_inplace}\n";
    for (tag, first, second) in
        [("flow_first", item_from_a_flow, item_from_a_module), ("module_first", item_from_a_module, item_from_a_flow)]
    {
        let d = Dir::pkg(&format!("clash_order_{tag}"));
        d.write("dsp/synth.onsa", flow);
        d.write("dsp/other.onsa", &f("process_inplace"));
        d.write("main.onsa", &format!("{first}{second}"));
        let (out, doc) = check_json(d.root());
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0304"]), "{tag}: {doc}");
        assert_eq!(diagnostics(&doc).len(), 1, "{tag}: {doc}");
        let e = &diagnostics(&doc)[0];
        assert_eq!(span_of(&e["span"]).line, 2, "{tag}: the later use: {doc}");
        let notes = array_of(e, "notes");
        assert_eq!(notes.len(), 1, "{tag}: {doc}");
        assert_eq!(span_of(&notes[0]["span"]).line, 1, "{tag}: the earlier use is the note: {doc}");
    }
}
