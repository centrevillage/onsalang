//! What `onsa interface` lists of a module by the visibility of an item, a member and a field (spec §18.2,
//! §15.1; S-660, R-265, S-36, S-35; W4-03 U4b/t).
//!
//! What the spec fixes, and so what is checked:
//! - §18.2 (S-660): the `pub` items and the items with no word are listed, with the visibility shown as the
//!   source writes it (`pub fn f()` and `fn f()`); the `priv` items and members are not listed, and the `impl`
//!   of a type that is not listed (a `priv` one) is not listed either (R-265). It holds for each kind of
//!   item (a function, an `rt` function, a constant, a struct, an enum, a type alias, a flow and the items a
//!   flow gives, which take the visibility of the flow, §11.6) and for the members of an `impl` (a function
//!   and a constant). A struct that is listed has the `priv` fields marked with the word (`priv tag: U32`);
//!   the fields with no word have none, whatever the struct is. `--json` has the same items, and a column of
//!   the visibility of a field;
//! - §15.1: the file argument is the module of the file, and the package without it is every module; the
//!   rule of what is listed is the same.
//!
//! Not asked: the rest of the text of a line (the layout, the sizes, the values of a constant), the keys of
//! the JSON beyond what the spec names (the signature, the name of an item, the visibility of a field; the
//! visibility of an item is looked at as "a string `pub` is in its object or is not"), and `primer --std`
//! (the command is not in this version).

mod test_support;

use std::collections::BTreeSet;

use serde_json::Value;
use test_support::*;

const SOURCE: &str = "\
pub struct Point {
  x: F32,
  priv tag: U32,
}

struct Shared {
  a: I32,
  priv b: I32,
}

priv struct Hidden {
  a: I32,
}

pub enum Mode {
  A,
  B(I32),
}

enum Inner {
  X,
}

priv enum Secret {
  Y,
}

pub const PUB_C: I32 = 1

const PKG_C: I32 = 2

priv const PRIV_C: I32 = 3

pub type PubT = F32

type PkgT = F32

priv type PrivT = F32

pub fn pub_f() -> I32 {
  1
}

fn pkg_f() -> I32 {
  2
}

priv fn priv_f() -> I32 {
  3
}

pub rt fn pub_rt() -> I32 {
  4
}

rt fn pkg_rt() -> I32 {
  5
}

priv rt fn priv_rt() -> I32 {
  6
}

pub flow pub_flow(x: F32 at sample) -> F32 at sample {
  x
}

flow pkg_flow(x: F32 at sample) -> F32 at sample {
  x
}

priv flow priv_flow(x: F32 at sample) -> F32 at sample {
  x
}

impl Point {
  pub fn new() -> Point {
    Point { x: 0.0, tag: 0 }
  }

  fn pkg_m(self) -> F32 {
    self.x
  }

  priv fn priv_m(self) -> F32 {
    self.x
  }

  pub const PC: I32 = 1

  const KC: I32 = 2

  priv const QC: I32 = 3
}

impl Shared {
  fn make() -> Shared {
    Shared { a: 1, b: 2 }
  }

  priv fn hidden_m(self) -> I32 {
    self.b
  }
}

impl Hidden {
  fn make() -> Hidden {
    Hidden { a: 1 }
  }

  priv fn hid_m(self) -> I32 {
    self.a
  }
}
";

/// What is listed, as the trimmed starts of the lines: each is a line of the text of `interface`.
const LISTED: &[&str] = &[
    "pub struct Point",
    "struct Shared",
    "pub enum Mode",
    "enum Inner",
    "pub const PUB_C: I32",
    "const PKG_C: I32",
    "pub type PubT",
    "type PkgT",
    "pub fn pub_f() -> I32",
    "fn pkg_f() -> I32",
    "pub rt fn pub_rt() -> I32",
    "rt fn pkg_rt() -> I32",
    "pub flow pub_flow(",
    "flow pkg_flow(",
    "impl Point",
    "pub fn new() -> Point",
    "fn pkg_m(self) -> F32",
    "pub const PC: I32",
    "const KC: I32",
    "impl Shared",
    "fn make() -> Shared",
];

/// The names that are not listed in any form: `priv` items and members, and the type that is not listed with
/// its `impl`.
const NOT_LISTED: &[&str] =
    &["Hidden", "Secret", "PRIV_C", "PrivT", "priv_f", "priv_rt", "priv_flow", "priv_m", "QC", "hidden_m", "hid_m"];

fn interface_text(d: &Dir, args: &[&str]) -> String {
    let mut a = vec!["interface"];
    a.extend_from_slice(args);
    let out = run(d.root(), &a);
    assert_eq!(out.code, 0, "{a:?}: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    out.stdout
}

fn interface_json(d: &Dir, args: &[&str]) -> Value {
    let mut a = vec!["interface", "--json"];
    a.extend_from_slice(args);
    let out = run(d.root(), &a);
    assert_eq!(out.code, 0, "{a:?}: {}{}", out.stdout, out.stderr);
    doc_of(&out)
}

fn source_dir(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("m.onsa", SOURCE);
    d
}

fn trimmed_lines(text: &str) -> Vec<&str> {
    text.lines().map(str::trim).collect()
}

// ---- the text ---------------------------------------------------------------------------------

/// §18.2 (S-660): every item and member that is `pub` or has no word is listed with the word it has, and
/// the `priv` ones are not.
#[test]
fn the_text_lists_pub_and_unmarked_items_with_their_words_and_leaves_out_priv() {
    let d = source_dir("text");
    let text = interface_text(&d, &["m.onsa"]);
    let lines = trimmed_lines(&text);
    for want in LISTED {
        assert!(lines.iter().any(|l| l.starts_with(want)), "`{want}` is listed:\n{text}");
    }
    for name in NOT_LISTED {
        assert!(!text.contains(name), "`{name}` is not listed:\n{text}");
    }
    // A function with no word is not shown as `pub`, and a `pub` one is not shown without its word.
    assert!(lines.contains(&"fn pkg_f() -> I32"), "{text}");
    assert!(lines.contains(&"pub fn pub_f() -> I32"), "{text}");
    assert!(!lines.contains(&"pub fn pkg_f() -> I32"), "{text}");
    assert!(!lines.contains(&"fn pub_f() -> I32"), "{text}");
}

/// §18.2 (S-660): the word `priv` is on a listed line only as the word of a field, and the fields with no
/// word have none.
#[test]
fn the_word_priv_is_in_the_text_only_before_a_field_that_has_it() {
    let d = source_dir("text_priv");
    let text = interface_text(&d, &["m.onsa"]);
    let lines = trimmed_lines(&text);
    let mut with_priv: Vec<&str> = lines.iter().copied().filter(|l| l.starts_with("priv ")).collect();
    with_priv.sort();
    assert_eq!(with_priv.len(), 2, "the two `priv` fields only:\n{text}");
    assert!(with_priv[0].starts_with("priv b: I32"), "{with_priv:?}");
    assert!(with_priv[1].starts_with("priv tag: U32"), "{with_priv:?}");
    // The fields with no word of a `pub` struct and of a struct with no word have none, and they are listed.
    assert!(lines.iter().any(|l| l.starts_with("x: F32")), "{text}");
    assert!(lines.iter().any(|l| l.starts_with("a: I32")), "{text}");
    assert!(!lines.iter().any(|l| l.starts_with("pub x:") || l.starts_with("pub a:")), "{text}");
}

/// §18.2, §11.6 (S-660): the items that a flow gives take its visibility: a `pub` flow has `pub` items, a
/// flow with no word has the items with no word, and a `priv` flow and its items are not listed.
#[test]
fn the_items_of_a_flow_have_the_word_of_the_flow() {
    let d = source_dir("text_flow");
    let text = interface_text(&d, &["m.onsa"]);
    let lines = trimmed_lines(&text);
    let of = |name: &str| -> Vec<&str> {
        let key = format!("{name}.");
        lines.iter().copied().filter(|l| l.contains(&key)).collect()
    };
    let shared = of("pkg_flow");
    assert!(shared.len() >= 5, "the items of `pkg_flow`:\n{text}");
    for l in &shared {
        assert!(!l.starts_with("pub ") && !l.starts_with("priv "), "no word on an item of a flow with no word: {l}");
    }
    for want in ["struct pkg_flow.State", "struct pkg_flow.Params", "fn pkg_flow.init(", "rt fn pkg_flow.process("] {
        assert!(shared.iter().any(|l| l.starts_with(want)), "`{want}`:\n{text}");
    }
    let open = of("pub_flow");
    assert!(open.len() >= 5, "the items of `pub_flow`:\n{text}");
    for l in &open {
        assert!(l.starts_with("pub "), "`pub` on an item of a `pub` flow: {l}");
    }
    assert!(!text.contains("priv_flow"), "{text}");
}

/// §18.2 (R-265): the `impl` of a type that is listed is listed with the members that are listed, and the
/// `impl` of a `priv` type is not listed, with whatever word its members have.
#[test]
fn the_impl_of_a_type_that_is_not_listed_is_not_listed() {
    let d = source_dir("text_impl");
    let text = interface_text(&d, &["m.onsa"]);
    let lines = trimmed_lines(&text);
    let impls: Vec<&str> = lines.iter().copied().filter(|l| l.starts_with("impl ")).collect();
    assert_eq!(impls.len(), 2, "the `impl` of `Point` and of `Shared`:\n{text}");
    assert!(
        impls.iter().any(|l| l.starts_with("impl Point")) && impls.iter().any(|l| l.starts_with("impl Shared")),
        "{impls:?}"
    );
    assert_eq!(lines.iter().filter(|l| l.starts_with("fn make() -> ")).count(), 1, "only `Shared.make`:\n{text}");
}

// ---- a package and a file -----------------------------------------------------------------------

/// §15.1, §18.2: the same rule for a module of a package, whether the file is named or not: the other
/// module's `pub` and unmarked items are listed with the package, and the `priv` ones are not.
#[test]
fn a_package_and_the_file_of_a_module_list_by_the_same_rule() {
    let d = Dir::pkg("package");
    d.write(
        "a.onsa",
        "pub fn a_pub() -> I32 {\n  1\n}\n\nfn a_pkg() -> I32 {\n  2\n}\n\npriv fn a_priv() -> I32 {\n  3\n}\n",
    );
    d.write(
        "sub/b.onsa",
        "pub struct BPub {\n  x: I32,\n}\n\nstruct BPkg {\n  priv y: I32,\n}\n\npriv struct BPriv {\n  z: I32,\n}\n",
    );
    let all = interface_text(&d, &[]);
    for want in ["a_pub", "a_pkg", "BPub", "BPkg", "priv y: I32"] {
        assert!(all.contains(want), "`{want}`:\n{all}");
    }
    for no in ["a_priv", "BPriv"] {
        assert!(!all.contains(no), "`{no}` is not listed:\n{all}");
    }
    assert!(trimmed_lines(&all).contains(&"fn a_pkg() -> I32"), "{all}");
    let a = interface_text(&d, &["a.onsa"]);
    assert!(a.contains("a_pub") && a.contains("a_pkg") && !a.contains("a_priv") && !a.contains("BPub"), "{a}");
    let b = interface_text(&d, &["sub/b.onsa"]);
    assert!(b.contains("BPub") && b.contains("BPkg") && !b.contains("BPriv") && !b.contains("a_pub"), "{b}");
}

// ---- the JSON ---------------------------------------------------------------------------------

/// Every object of the document, at any depth.
fn objects<'a>(v: &'a Value, out: &mut Vec<&'a Value>) {
    match v {
        Value::Object(m) => {
            out.push(v);
            m.values().for_each(|x| objects(x, out));
        }
        Value::Array(xs) => xs.iter().for_each(|x| objects(x, out)),
        _ => {}
    }
}

/// The names (`name` keys with a string) of the objects of the document.
fn names(doc: &Value) -> BTreeSet<String> {
    let mut os = Vec::new();
    objects(doc, &mut os);
    os.iter().filter_map(|o| o.get("name").and_then(Value::as_str).map(str::to_string)).collect()
}

/// The strings that are values of the object itself (not of the objects in it).
fn own_strings(o: &Value) -> Vec<&str> {
    o.as_object().map(|m| m.values().filter_map(Value::as_str).collect()).unwrap_or_default()
}

/// The objects whose `name` is `name` and which have `key`.
fn named<'a>(doc: &'a Value, name: &str, key: &str) -> Vec<&'a Value> {
    let mut os = Vec::new();
    objects(doc, &mut os);
    os.into_iter().filter(|o| o.get("name").and_then(Value::as_str) == Some(name) && o.get(key).is_some()).collect()
}

/// §18.2 (S-660): `--json` lists the same items and members as the text.
#[test]
fn the_json_lists_the_same_items_and_members() {
    let d = source_dir("json");
    let doc = interface_json(&d, &["m.onsa"]);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let names = names(&doc);
    for want in [
        "Point", "Shared", "Mode", "Inner", "PUB_C", "PKG_C", "PubT", "PkgT", "pub_f", "pkg_f", "pub_rt", "pkg_rt",
        "pub_flow", "pkg_flow", "new", "pkg_m", "PC", "KC", "make",
    ] {
        assert!(names.contains(want), "`{want}` is listed: {names:?}");
    }
    for no in NOT_LISTED {
        assert!(!names.contains(*no), "`{no}` is not listed: {names:?}");
    }
    // `make` of `Hidden` is not listed, so there is the one of `Shared`.
    let mut os = Vec::new();
    objects(&doc, &mut os);
    let makes = os.iter().filter(|o| o.get("name").and_then(Value::as_str) == Some("make")).count();
    assert_eq!(makes, 1, "{doc}");
}

/// §18.2 (S-660): the signature of a function has the word it has in the source.
#[test]
fn the_json_signature_has_the_word_of_the_source() {
    let d = source_dir("json_signature");
    let doc = interface_json(&d, &["m.onsa"]);
    let sig = |name: &str| -> Vec<String> {
        named(&doc, name, "signature").iter().map(|o| o["signature"].as_str().unwrap_or("").to_string()).collect()
    };
    assert_eq!(sig("pub_f"), ["pub fn pub_f() -> I32"]);
    assert_eq!(sig("pkg_f"), ["fn pkg_f() -> I32"]);
    assert_eq!(sig("pub_rt"), ["pub rt fn pub_rt() -> I32"]);
    assert_eq!(sig("pkg_rt"), ["rt fn pkg_rt() -> I32"]);
}

/// §18.2 (S-660): the visibility of an item is the word of the source: `pub` for a `pub` item, and no
/// `pub` or `priv` for an item with no word.
#[test]
fn the_json_visibility_of_an_item_is_the_word_of_the_source() {
    let d = source_dir("json_vis");
    let doc = interface_json(&d, &["m.onsa"]);
    for (name, key, pub_word) in [
        ("pub_f", "signature", true),
        ("pkg_f", "signature", false),
        ("Point", "fields", true),
        ("Shared", "fields", false),
        ("PUB_C", "ty", true),
        ("PKG_C", "ty", false),
        ("PubT", "ty", true),
        ("PkgT", "ty", false),
    ] {
        let found = named(&doc, name, key);
        assert_eq!(found.len(), 1, "`{name}`: {doc}");
        let words = own_strings(found[0]);
        assert_eq!(words.contains(&"pub"), pub_word, "`{name}` has the word `pub` or not: {}", found[0]);
        assert!(!words.contains(&"priv"), "`{name}` is not `priv`: {}", found[0]);
    }
}

/// §18.2 (S-660): the fields of a struct that is listed have a column of the visibility in `--json`: a `priv`
/// field has the word, and a field with no word does not.
#[test]
fn the_json_fields_have_a_visibility_column_with_priv_for_the_priv_ones() {
    let d = source_dir("json_fields");
    let doc = interface_json(&d, &["m.onsa"]);
    for (field, ty, priv_word) in [("tag", "U32", true), ("x", "F32", false), ("b", "I32", true), ("a", "I32", false)] {
        let found: Vec<&Value> =
            named(&doc, field, "ty").into_iter().filter(|o| o["ty"].as_str() == Some(ty)).collect();
        let found: Vec<&Value> = found.into_iter().filter(|o| o.get("offset").is_some()).collect();
        // `a: I32` is a field of `Shared` and of `Hidden`; `Hidden` is not listed, so there is the one.
        assert_eq!(found.len(), 1, "the field `{field}`: {doc}");
        assert_eq!(own_strings(found[0]).contains(&"priv"), priv_word, "the field `{field}`: {}", found[0]);
    }
}
