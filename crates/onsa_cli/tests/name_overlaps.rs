//! Names that overlap (E0304, E0305), seen from the command line: what the case files in
//! `tests/spec/packages/overlap_*` cannot say, the places that the spec leaves out of the marks, and
//! the properties of the diagnostics (spec §2.2, §5.1, §11.2, §11.4, §15.1, §18.1; R-177, S-246,
//! S-37, S-611, R-103, S-542, S-666; W4-03 U3a1).
//!
//! What the spec fixes, and so what is checked here:
//! - an item and a child module of the same name (`a.onsa` with `pub fn b` and `a/b.onsa`, a
//!   directory with no file of the name too) are E0304 on the item; the file of the child has none,
//!   and `check` of the file of the child alone is clean (the diagnostics of a file are the ones of
//!   its own module). The note of a child that is only a directory points at the start of the first
//!   `.onsa` file below it in the order of the diagnostics (the file strings in code point order);
//! - a module at the root, or a root directory that holds a module, with the name of a dependency
//!   (`std`) is E0304, and `use std.math.{sqrt}` is still std's (no E0302, no other diagnostic). The
//!   spec does not say where in the directory the diagnostic is, so only the file is checked;
//! - E0305 (a flow and another declaration of the name) is on the later declaration, with a note at
//!   the earlier one (§11.2);
//! - the built-in flow names (`prev`, `delay`, `vdelay`, `sample_rate`, `sample_tick`) as an item or
//!   a `use` binding are E0304 with no candidate (S-542); the prelude and the built-in type names
//!   are E0304 too (S-611, R-103) and do not make other diagnostics (the user's `struct F32` does
//!   not take over the `F32` of a function);
//! - a body path whose head is a name that a `use` could not bind (a built-in flow name, a reserved
//!   word) is E0302 or another error without a candidate that adds a `use` (the `use` would be an
//!   error, and a candidate leaves none of the same stage, §18.1).
//!
//! Places that the spec leaves open, so only "one diagnostic, on one of the two lines" is checked:
//! the pair of an item and a `use` (or a flow and a `use`) when the item is the later declaration.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "W4-03"]`.

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

/// `(code, file)` of every diagnostic, as a set.
fn files(doc: &Value) -> BTreeSet<(String, String)> {
    diagnostics(doc).iter().map(|d| (str_of(d, "code").to_string(), span_of(&d["span"]).file)).collect()
}

fn set(items: &[(&str, &str, u64)]) -> BTreeSet<(String, String, u64)> {
    items.iter().map(|(c, f, l)| (c.to_string(), f.to_string(), *l)).collect()
}

fn pairs(items: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    items.iter().map(|(c, f)| (c.to_string(), f.to_string())).collect()
}

fn fixes_of(d: &Value) -> usize {
    d.get("fixes").and_then(|f| f.as_array()).map_or(0, |f| f.len())
}

fn of_code<'a>(doc: &'a Value, code: &str) -> Vec<&'a Value> {
    diagnostics(doc).iter().filter(|d| str_of(d, "code") == code).collect()
}

fn notes_with_span(d: &Value) -> Vec<Span> {
    d.get("notes")
        .and_then(|n| n.as_array())
        .map(|n| n.iter().filter_map(|x| x.get("span")).map(span_of).collect())
        .unwrap_or_default()
}

const ONE: &str = "pub fn one() -> I32 {\n  1\n}\n";

fn fn_item(name: &str) -> String {
    format!("pub fn {name}() -> I32 {{\n  1\n}}\n")
}

// ---- an item and a child module (R-177, S-666) ------------------------------------------------------

/// §15.1 (R-177): the item `b` of `a.onsa` and `a/b.onsa`, a flow and `e/f.onsa`, a `priv fn` and
/// `h/m.onsa` are each one E0304 on the item, at line 1 of the file of the parent. The files of the
/// children have no diagnostic.
#[test]
fn an_item_and_a_child_module_of_one_name_are_e0304_on_the_item() {
    let d = Dir::pkg("item_child");
    d.write("a.onsa", &fn_item("b"));
    d.write("a/b.onsa", &fn_item("c"));
    d.write("e.onsa", "pub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n");
    d.write("e/f.onsa", &fn_item("g"));
    d.write("h.onsa", "priv fn m() -> I32 {\n  1\n}\n");
    d.write("h/m.onsa", &fn_item("n"));
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "a.onsa", 1), ("E0304", "e.onsa", 1), ("E0304", "h.onsa", 1)]), "{doc}");
}

/// §15.1: the diagnostics of a file are the ones of its own module, so `check` of the parent has the
/// E0304 and `check` of the child, which only has the name `b`, is clean.
#[test]
fn the_clash_is_in_the_file_of_the_item_and_not_in_the_file_of_the_child() {
    let d = Dir::pkg("item_child_files");
    d.write("a.onsa", &fn_item("b"));
    d.write("a/b.onsa", &fn_item("c"));
    let (out, doc) = check_json(d.root(), &["a.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "a.onsa", 1)]), "{doc}");
    let (out, doc) = check_json(d.root(), &["a/b.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// §15.1: the item of a module that is itself a child (`a/b.onsa`) clashes with its own child
/// (`a/b/c.onsa`), and the same names one level up do not (the item `c` of `a.onsa` is an item of `a`,
/// and `a/b/c.onsa` is a grandchild).
#[test]
fn the_clash_is_between_a_module_and_its_own_children_only() {
    let d = Dir::pkg("item_child_nested");
    d.write("a.onsa", &fn_item("c"));
    d.write("a/b.onsa", &fn_item("c"));
    d.write("a/b/c.onsa", &fn_item("w"));
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "a/b.onsa", 1)]), "{doc}");
}

/// §15.1 (S-666): a child that is only a directory (`p/q/` with the files `p/q/b.onsa` and
/// `p/q/a/x.onsa`) clashes with the item `q` of `p.onsa`. The diagnostic is on the item, and the
/// note is at the start of the first `.onsa` file below the directory in the order of the diagnostics:
/// the file strings in code point order, so `p/q/a/x.onsa` comes before `p/q/b.onsa`.
#[test]
fn the_note_of_a_directory_only_child_is_the_start_of_its_first_file() {
    let d = Dir::pkg("item_dir_only");
    d.write("p.onsa", &fn_item("q"));
    d.write("p/q/b.onsa", &fn_item("b"));
    d.write("p/q/a/x.onsa", &fn_item("x"));
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "p.onsa", 1)]), "{doc}");
    let found = of_code(&doc, "E0304");
    let notes = notes_with_span(found[0]);
    let at_start = notes.iter().any(|s| s.file == "p/q/a/x.onsa" && s.line == 1 && s.col == 1);
    assert!(at_start, "a note at the start of p/q/a/x.onsa: {notes:?} in {}", found[0]);
}

/// §15.1: a directory that holds no `.onsa` file is not a module, so it clashes with nothing; the
/// `.onsa` files must be below it.
#[test]
fn a_directory_without_an_onsa_file_is_not_a_child_module() {
    let d = Dir::pkg("item_empty_dir");
    d.write("p.onsa", &fn_item("q"));
    d.write("p/q/readme.txt", "no .onsa file\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- the root module or directory and a dependency name (S-37, S-246) -------------------------------

const USES_STD: &str = "use std.math.{sqrt}\n\npub fn r(x: F32) -> F32 {\n  sqrt(x)\n}\n";

/// §15.1 (S-37): a module `std.onsa` at the root has the name of a dependency, E0304 in that file.
/// `use std.math.{sqrt}` in another module is std's: no E0302 and nothing else.
#[test]
fn a_root_module_named_like_a_dependency_is_e0304_and_the_dependency_is_still_std() {
    let d = Dir::pkg("root_std_file");
    d.write("std.onsa", ONE);
    d.write("main.onsa", USES_STD);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(files(&doc), pairs(&[("E0304", "std.onsa")]), "{doc}");
    assert_eq!(of_code(&doc, "E0304").len(), 1, "{doc}");
}

/// §15.1 (S-246): a root directory that holds a module (`std/math.onsa`, there is no `std.onsa`) has
/// the name of a dependency, E0304 (the file is the only one below the directory; the spec does not
/// say where in the file), and `use std.math.{sqrt}` is std's.
#[test]
fn a_root_directory_named_like_a_dependency_is_e0304_and_the_dependency_is_still_std() {
    let d = Dir::pkg("root_std_dir");
    d.write("std/math.onsa", ONE);
    d.write("main.onsa", USES_STD);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(files(&doc), pairs(&[("E0304", "std/math.onsa")]), "{doc}");
    assert_eq!(of_code(&doc, "E0304").len(), 1, "{doc}");
}

/// §15.1: names that are not the name of a dependency are free: `stdx`, `std_math`, and a child
/// module `std` (`a/std.onsa` is `a.std`, not a module at the root). `a.onsa` and `a/` are a module
/// and its child, not an overlap.
#[test]
fn names_that_only_look_like_a_dependency_are_free() {
    let d = Dir::pkg("root_std_like");
    d.write("stdx.onsa", ONE);
    d.write("std_math.onsa", &fn_item("two"));
    d.write("a.onsa", &fn_item("top"));
    d.write("a/std.onsa", &fn_item("three"));
    d.write("main.onsa", &format!("{USES_STD}\nuse a.std.{{three}}\nuse stdx.{{one}}\n"));
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- the body: items and `use` lines ----------------------------------------------------------------

fn main_with(tag: &str, text: &str) -> (Out, Value, Dir) {
    let d = Dir::pkg(tag);
    d.write("util.onsa", "pub fn quad() -> I32 {\n  4\n}\n");
    d.write("main.onsa", text);
    let (out, doc) = check_json(d.root(), &["."]);
    (out, doc, d)
}

/// §15.1, §11.2: the pair of an item (a function or a flow) and a `use` that takes the same name is
/// one E0304 and nothing else. With the `use` first and the item after it, the spec does not say which
/// of the two gets it (the later declaration for two items), so the line is one of the two.
#[test]
fn an_item_after_a_use_of_its_name_gives_one_e0304_on_one_of_the_two() {
    let item_fn = "pub fn quad() -> I32 {\n  4\n}\n";
    let item_flow = "pub flow quad(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
    for (tag, item) in [("fn", item_fn), ("flow", item_flow)] {
        let (out, doc, _d) = main_with(&format!("use_item_{tag}"), &format!("use util.{{quad}}\n\n{item}"));
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(diagnostics(&doc).len(), 1, "{tag}: {doc}");
        let found = of_code(&doc, "E0304");
        assert_eq!(found.len(), 1, "{tag}: {doc}");
        let sp = span_of(&found[0]["span"]);
        assert!(sp.file == "main.onsa" && (sp.line == 1 || sp.line == 3), "{tag}: {doc}");
    }
}

/// §15.1, §11.2: with the item written first, the later declaration is the `use` and gets the E0304
/// (both readings of the spec agree on this order).
#[test]
fn a_use_written_after_an_item_of_its_name_gets_the_e0304() {
    let item_fn = "pub fn quad() -> I32 {\n  4\n}\n";
    let item_flow = "pub flow quad(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
    for (tag, item) in [("fn", item_fn), ("flow", item_flow)] {
        let (out, doc, _d) = main_with(&format!("item_use_{tag}"), &format!("{item}\nuse util.{{quad}}\n"));
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), set(&[("E0304", "main.onsa", 5)]), "{tag}: {doc}");
    }
}

/// §11.2: E0305 is on the later declaration and a note shows the earlier one, whichever of the two is
/// the flow. (A flow and a function, a flow and a flow.)
#[test]
fn e0305_is_on_the_later_declaration_with_a_note_at_the_earlier_one() {
    let flow = "pub flow gain(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
    let func = "pub fn gain() -> F32 {\n  1.0\n}\n";
    for (tag, first, second, line2) in [("ff", flow, flow, 5), ("fn_flow", flow, func, 5), ("flow_fn", func, flow, 5)] {
        let d = Dir::pkg(&format!("e0305_{tag}"));
        d.write("main.onsa", &format!("{first}\n{second}"));
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), set(&[("E0305", "main.onsa", line2)]), "{tag}: {doc}");
        let found = of_code(&doc, "E0305");
        let notes = notes_with_span(found[0]);
        assert!(notes.iter().any(|s| s.file == "main.onsa" && s.line == 1), "{tag}: a note at line 1: {}", found[0]);
    }
}

// ---- the built-in flow names and the prelude (S-542, S-611, R-103) ----------------------------------

const FLOW_NAMES: [&str; 5] = ["prev", "delay", "vdelay", "sample_rate", "sample_tick"];

/// A form of a test: its tag, the text of `main.onsa`, and another file (its path and text).
type Form = (&'static str, String, Option<(String, String)>);

/// §2.2, §5.1 (S-542): each built-in flow name, as a function, as a flow, as a module taken by a
/// `use` and as an item taken by a `use`, is one E0304 in the module that names it, with no
/// candidate (a rename is the writer's to choose).
#[test]
fn a_built_in_flow_name_is_e0304_as_an_item_or_a_use_binding_and_has_no_candidate() {
    for name in FLOW_NAMES {
        let module = (format!("dsp/{name}.onsa"), ONE.to_string());
        let forms: Vec<Form> = vec![
            ("fn", format!("pub fn {name}() -> I32 {{\n  1\n}}\n"), None),
            ("flow", format!("pub flow {name}(x: F32 at sample) -> F32 at sample {{\n  x\n}}\n"), None),
            ("mod", format!("use dsp.{name}\n"), Some(module.clone())),
            ("list", format!("use dsp.{{{name}}}\n"), Some(module)),
        ];
        for (tag, text, extra) in forms {
            let d = Dir::pkg(&format!("flow_name_{name}_{tag}"));
            d.write("main.onsa", &text);
            if let Some((path, body)) = &extra {
                d.write(path, body);
            }
            let (out, doc) = check_json(d.root(), &["."]);
            assert_eq!(out.code, 1, "{name} {tag}: {}{}", out.stdout, out.stderr);
            assert_eq!(places(&doc), set(&[("E0304", "main.onsa", 1)]), "{name} {tag}: {doc}");
            assert_eq!(fixes_of(of_code(&doc, "E0304")[0]), 0, "{name} {tag}: {doc}");
        }
    }
}

/// §2.2, §11.4: the names are free where the spec says so (the file of a module, a field, a method,
/// the bindings of a `fn`): the case `overlap_names_apart` has them; here the file names alone.
#[test]
fn a_module_file_may_be_named_like_a_built_in_flow() {
    for name in FLOW_NAMES {
        let d = Dir::pkg(&format!("flow_name_file_{name}"));
        d.write(&format!("{name}.onsa"), ONE);
        d.write("main.onsa", &format!("use {name}.{{one}}\n\npub fn k() -> I32 {{\n  one()\n}}\n"));
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 0, "{name}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{name}: {doc}");
    }
}

/// §5.1 (S-542): the example `use util.{prev}` (the item `prev` of `util` is an error of its own
/// module, and the `use` that takes it is one in the module that has the `use`; neither has a
/// candidate).
#[test]
fn use_of_an_item_with_a_built_in_flow_name_is_e0304_in_both_modules() {
    let d = Dir::pkg("use_item_prev");
    d.write("util.onsa", &fn_item("prev"));
    d.write("main.onsa", "use util.{prev}\n\npub fn k() -> I32 {\n  1\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "main.onsa", 1), ("E0304", "util.onsa", 1)]), "{doc}");
    for x in of_code(&doc, "E0304") {
        assert_eq!(fixes_of(x), 0, "{x}");
    }
}

/// §15.1, §5.1 (S-611, R-103): an item with the name of a prelude function or of a built-in type, or a
/// `use` that binds such a name (the module `panic`, or the item `panic` of a user module), is E0304.
/// The names of the built-in types and of the prelude's enumerators here; `panic` in
/// [`an_item_or_a_use_named_panic_is_e0304`].
#[test]
fn an_item_or_a_use_with_a_prelude_or_built_in_name_is_e0304() {
    prelude_items_are_e0304(&[
        ("struct_f32", "pub struct F32 {\n  v: I32,\n}\n"),
        ("enum_option", "pub enum Option {\n  Nothing,\n}\n"),
        ("struct_err", "pub struct Err {\n  code: I32,\n}\n"),
        ("alias_str", "pub type Str = I32\n"),
        ("enum_map", "pub enum Map {\n  Entry,\n}\n"),
    ]);
}

/// [`an_item_or_a_use_with_a_prelude_or_built_in_name_is_e0304`] for the prelude function `panic`.
#[test]
#[ignore = "W4-03: panic is in the table of the prelude from U5"]
fn an_item_or_a_use_named_panic_is_e0304() {
    prelude_items_are_e0304(&[
        ("fn_panic", "pub fn panic() -> I32 {\n  1\n}\n"),
        ("flow_panic", "pub flow panic(x: F32 at sample) -> F32 at sample {\n  x\n}\n"),
    ]);
    let d = Dir::pkg("prelude_use_module");
    d.write("panic.onsa", ONE);
    d.write("main.onsa", "use panic\n\npub fn k() -> I32 {\n  1\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "main.onsa", 1)]), "{doc}");
    let d = Dir::pkg("prelude_use_item");
    d.write("kp.onsa", &fn_item("panic"));
    d.write("main.onsa", "use kp.{panic}\n\npub fn k() -> I32 {\n  1\n}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "kp.onsa", 1), ("E0304", "main.onsa", 1)]), "{doc}");
}

/// Each of `cases` (a tag and the text of `main.onsa`) is one E0304 on its first line.
fn prelude_items_are_e0304(cases: &[(&str, &str)]) {
    for &(tag, text) in cases {
        let d = Dir::pkg(&format!("prelude_{tag}"));
        d.write("main.onsa", text);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(places(&doc), set(&[("E0304", "main.onsa", 1)]), "{tag}: {doc}");
    }
}

/// §5.1, R-103 (`parent/r84_type.onsa`): the user's `struct F32` does not take over the `F32` of the
/// function written after it: the one diagnostic is the E0304 of the struct, and `x * 0.5` has no
/// error about a float literal.
#[test]
fn a_struct_named_like_a_built_in_type_does_not_make_other_diagnostics() {
    let d = Dir::pkg("f32_struct");
    d.write(
        "main.onsa",
        "struct F32 {\n  v: I32,\n}\n\nenum Option {\n  Nothing,\n}\n\nfn half(x: F32) -> F32 {\n  x * 0.5\n}\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(places(&doc), set(&[("E0304", "main.onsa", 1), ("E0304", "main.onsa", 5)]), "{doc}");
}

// ---- a body path whose head a `use` cannot bind ------------------------------------------------------

/// §15.1, §18.1: `prev.x()` with a root module `prev.onsa` and no `use` is an error, and the candidate
/// that adds `use prev` would be E0304 (a built-in flow name cannot be bound), so there is no
/// candidate. The same for the other names, for a reserved word (`static.tick()`, where the code is
/// not fixed: E0302 or the E0200 of the reserved word) and for the prelude name `panic`. A module
/// named `util` is the control: its error has the candidate that adds `use util`.
#[test]
fn a_body_path_whose_head_cannot_be_bound_by_a_use_has_no_use_candidate() {
    let heads = ["prev", "delay", "vdelay", "sample_rate", "sample_tick", "static"];
    heads_have_no_use_candidate("unbindable_heads", &heads);
}

/// [`a_body_path_whose_head_cannot_be_bound_by_a_use_has_no_use_candidate`] for the prelude name `panic`.
#[test]
#[ignore = "W4-03: panic is in the table of the prelude from U5"]
fn a_body_path_whose_head_is_panic_has_no_use_candidate() {
    heads_have_no_use_candidate("unbindable_head_panic", &["panic"]);
}

/// A package with a module for each of `heads` and a body path `h.x()` for each: no candidate on them,
/// and the control `util.f()` has the one that adds `use util`.
fn heads_have_no_use_candidate(tag: &str, heads: &[&str]) {
    let d = Dir::pkg(tag);
    d.write("util.onsa", &fn_item("f"));
    let mut text = String::from("pub fn control() -> I32 {\n  util.f()\n}\n");
    for h in heads {
        d.write(&format!("{h}.onsa"), &fn_item("x"));
        text.push_str(&format!("\npub fn use_{h}() -> I32 {{\n  {h}.x()\n}}\n"));
    }
    d.write("main.onsa", &text);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let lines: Vec<&str> = text.lines().collect();
    let line_of = |needle: &str| lines.iter().position(|l| l.trim() == needle).unwrap() as u64 + 1;
    let control = line_of("util.f()");
    let at_control: Vec<&Value> = diagnostics(&doc)
        .iter()
        .filter(|x| span_of(&x["span"]).file == "main.onsa" && span_of(&x["span"]).line == control)
        .collect();
    assert_eq!(at_control.len(), 1, "{doc}");
    assert_eq!(str_of(at_control[0], "code"), "E0302", "{doc}");
    assert_eq!(fixes_of(at_control[0]), 1, "{doc}");
    for h in heads {
        let line = line_of(&format!("{h}.x()"));
        let here: Vec<&Value> = diagnostics(&doc)
            .iter()
            .filter(|x| span_of(&x["span"]).file == "main.onsa" && span_of(&x["span"]).line == line)
            .collect();
        assert!(!here.is_empty(), "{h}: no diagnostic on line {line}: {doc}");
        for x in here {
            assert_eq!(fixes_of(x), 0, "{h}: a candidate on a head that a use cannot bind: {x}");
        }
    }
}
