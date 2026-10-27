//! The reach of the visibilities seen from the side that uses a name: what another module of the package
//! gets of an item, a field and a member of an `impl` that has `pub`, no word or `priv` (spec §15.1, §11.6,
//! §7; S-36, S-35, R-38, S-491, S-672, S-482, S-593; W4-03 U4a/t).
//!
//! What the spec fixes, and so what is checked:
//! - §15.1 (S-36): an item with no word is seen by every module of the package, a `pub` item too, and a
//!   `priv` item by its module alone; a `use` of a `priv` name in another module is one E0303 on the `use`
//!   and its uses are silent (S-462). Checked for each kind of item (a function, a constant, a struct, an
//!   enum, a type alias, a flow) and for the two ways to write a `use`;
//! - §15.1 (S-35): a field follows its struct, and a `priv` field is the module's alone: another module
//!   reading it, writing it, naming it in a struct literal or in a pattern gets E0303, and the module that
//!   declares it gets none of it. The fields with no word are fine for every module. A `..` that leaves a
//!   field that the module cannot see is E0303 with a note and no candidate (§7, §15.1, S-366), and E0020
//!   (with a candidate) when every field that is left is seen. The fields of a `priv struct` take `priv` and no
//!   word alike (S-672);
//! - §15.1 (R-38, S-491): a `priv` member of an `impl` called with `s.m()`, `S.m()` or `S.C` in another module
//!   is E0303 (the associated function used to be E0401 "is not a value"); a member with no word and a `pub`
//!   member are fine.
//!
//! Not asked: the position of a diagnostic beyond the file, and the text of a message.
//! The same forms, with the places of the marks, are under `tests/spec/packages/visibility_*`.

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

/// `(code, file)` of every diagnostic, in the order of the document.
fn found(doc: &Value) -> Vec<(String, String)> {
    diagnostics(doc).iter().map(|d| (str_of(d, "code").to_string(), span_of(&d["span"]).file)).collect()
}

fn pair(code: &str, file: &str) -> (String, String) {
    (code.to_string(), file.to_string())
}

/// A package of the texts `(path, text)`, checked once: the exit code and the diagnostics as `(code, file)`.
fn check_package(tag: &str, texts: &[(&str, String)]) -> (i32, Vec<(String, String)>, Value) {
    let d = Dir::pkg(tag);
    for (path, text) in texts {
        d.write(path, text);
    }
    let (out, doc) = check_json(d.root());
    assert!(!out.stderr.contains("internal error"), "{tag}: {}", out.stderr);
    assert!(out.code == 0 || out.code == 1, "{tag}: exit {}: {}{}", out.code, out.stdout, out.stderr);
    (out.code, found(&doc), doc)
}

// ---- the items: a function, a constant, a struct, an enum, a type alias and a flow ------------------

/// `(kind, declaration with {w} in front, the body of the module that takes it, the name taken)`.
type Kind = (&'static str, &'static str, &'static str, &'static str);

const KINDS: [Kind; 6] = [
    ("fn", "{w}fn item() -> I32 {\n  1\n}\n", "fn call() -> I32 {\n  item()\n}\n", "item"),
    ("const", "{w}const ITEM: I32 = 1\n", "fn call() -> I32 {\n  ITEM\n}\n", "ITEM"),
    ("struct", "{w}struct Item {\n  a: I32,\n}\n", "fn call() -> Item {\n  Item { a: 1 }\n}\n", "Item"),
    ("enum", "{w}enum Item {\n  A,\n}\n", "fn call() -> Item {\n  Item.A\n}\n", "Item"),
    ("type", "{w}type Item = F32\n", "fn call() -> Item {\n  1.0\n}\n", "Item"),
    (
        "flow",
        "{w}flow item(x: F32 at sample) -> F32 at sample {\n  x\n}\n",
        "flow call(x: F32 at sample) -> F32 at sample {\n  item~(x)\n}\n",
        "item",
    ),
];

/// §15.1 (S-36): `pub` and no word are seen by another module of the package, `priv` is not. The `use` is the
/// first line of `other.onsa`; for a `priv` item it is the only diagnostic, and the uses of the name are silent.
#[test]
fn an_item_is_seen_by_the_package_unless_it_is_priv() {
    let mut problems: Vec<String> = Vec::new();
    for (kind, decl, body, name) in KINDS {
        for (word, label, seen) in [("pub ", "pub", true), ("", "none", true), ("priv ", "priv", false)] {
            for use_line in [format!("use util.{{{name}}}\n"), format!("use util.{name}\n")] {
                let tag = format!("vis_item_{kind}_{label}");
                let util = decl.replace("{w}", word);
                let other = format!("{use_line}\n{body}");
                let (code, diags, doc) = check_package(&tag, &[("util.onsa", util), ("other.onsa", other)]);
                let ok = if seen {
                    code == 0 && diags.is_empty()
                } else {
                    code == 1
                        && diags == vec![pair("E0303", "other.onsa")]
                        && span_of(&diagnostics(&doc)[0]["span"]).line == 1
                };
                if !ok {
                    problems.push(format!("{kind} {label} `{}`: exit {code}, {diags:?}: {doc}", use_line.trim()));
                }
            }
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1: the module that declares a `priv` item uses it, and the other modules of the package see nothing
/// else of it: a child module (`a/b.onsa`) is another module than its parent (`a.onsa`), and two modules of
/// a directory are two modules.
#[test]
fn a_priv_item_reaches_the_module_alone_and_not_a_child_module_or_a_sibling() {
    let texts = [
        ("a.onsa", "priv fn secret() -> I32 {\n  1\n}\n\nfn inside() -> I32 {\n  secret()\n}\n".to_string()),
        ("a/b.onsa", "use a.{secret}\n\nfn child() -> I32 {\n  1\n}\n".to_string()),
        ("dsp/x.onsa", "priv fn only_x() -> I32 {\n  1\n}\n".to_string()),
        ("dsp/y.onsa", "use dsp.x.{only_x}\n".to_string()),
    ];
    let (code, diags, doc) = check_package("vis_priv_modules", &texts);
    assert_eq!(code, 1, "{doc}");
    let want: BTreeSet<(String, String)> =
        [pair("E0303", "a/b.onsa"), pair("E0303", "dsp/y.onsa")].into_iter().collect();
    assert_eq!(diags.iter().cloned().collect::<BTreeSet<_>>(), want, "{doc}");
    assert_eq!(diags.len(), 2, "one for each `use`: {doc}");
}

/// §15.1 (S-36): the name that a `use` binds is the module's alone, so another module that looks for it in the
/// module is told it is not there (E0302, not E0303: the item is not in `main` at all).
#[test]
fn what_a_module_took_with_a_use_is_not_seen_by_another_module() {
    let texts = [
        ("util.onsa", "fn double(x: I32) -> I32 {\n  x * 2\n}\n".to_string()),
        ("main.onsa", "use util.{double}\n\npub fn k() -> I32 {\n  double(1)\n}\n".to_string()),
        ("other.onsa", "use main.{k}\nuse main.{double}\n".to_string()),
    ];
    let (code, diags, doc) = check_package("vis_use_not_seen", &texts);
    assert_eq!(code, 1, "{doc}");
    assert_eq!(diags, vec![pair("E0302", "other.onsa")], "{doc}");
}

// ---- the fields --------------------------------------------------------------------------------------

/// The operations on a field `f` of a struct `S` that has the fields `a` and `f`, as the text of a function
/// `op`: a read, a write, a struct literal that names both fields, a pattern that names both, and a pattern
/// that ends in `..` with the field `f` left out.
const FIELD_OPS: [(&str, &str); 5] = [
    ("read", "fn op(s: S) -> I32 {\n  s.f\n}\n"),
    ("write", "fn op(inout s: S) {\n  s.f = 1\n}\n"),
    ("literal", "fn op() -> S {\n  S { a: 1, f: 2 }\n}\n"),
    ("pattern", "fn op(s: S) -> I32 {\n  match s {\n    S { a: _, f: y } => y,\n  }\n}\n"),
    ("rest", "fn op(s: S) -> I32 {\n  match s {\n    S { a: x, .. } => x,\n  }\n}\n"),
];

/// §15.1 (S-35), §7 (S-366): for a struct that is `pub` or has no word, and a field that is `priv` or has no word,
/// each operation is checked in the module that declares the struct and in another module. The `priv` field
/// is E0303 in another module for the four operations that name it; `..` is E0303 there too when the field
/// that is left cannot be seen (no candidate and a note), and E0020 otherwise (the candidate names the fields
/// left).
#[test]
fn a_priv_field_is_the_modules_and_a_field_with_no_word_follows_the_struct() {
    let mut problems: Vec<String> = Vec::new();
    for (struct_word, struct_label) in [("pub ", "pub"), ("", "none")] {
        for (field_word, field_label) in [("priv ", "priv"), ("", "none")] {
            let decl = format!("{struct_word}struct S {{\n  a: I32,\n  {field_word}f: I32,\n}}\n");
            for (op_label, op) in FIELD_OPS {
                for other_module in [false, true] {
                    let tag = format!("vis_field_{struct_label}_{field_label}_{op_label}_{}", other_module as u8);
                    let (file, texts) = if other_module {
                        (
                            "other.onsa",
                            vec![("shapes.onsa", decl.clone()), ("other.onsa", format!("use shapes.{{S}}\n\n{op}"))],
                        )
                    } else {
                        ("shapes.onsa", vec![("shapes.onsa", format!("{decl}\n{op}"))])
                    };
                    let hidden = other_module && field_label == "priv";
                    let want: Vec<(String, String)> = match (op_label, hidden) {
                        ("rest", true) => vec![pair("E0303", file)],
                        ("rest", false) => vec![pair("E0020", file)],
                        (_, true) => vec![pair("E0303", file)],
                        (_, false) => vec![],
                    };
                    let (code, diags, doc) = check_package(&tag, &texts);
                    if diags != want || code != if want.is_empty() { 0 } else { 1 } {
                        problems.push(format!("{tag}: exit {code}, want {want:?}: {doc}"));
                    }
                }
            }
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1 (S-672): the fields of a `priv struct` are `priv` or have no word, and neither is E0020; the module
/// uses all of them. The struct itself is the module's, so another module gets E0303 on the `use` of it.
#[test]
fn the_fields_of_a_priv_struct_take_priv_and_no_word_alike() {
    let mut problems: Vec<String> = Vec::new();
    for (field_word, field_label) in [("priv ", "priv"), ("", "none")] {
        let decl = format!("priv struct S {{\n  a: I32,\n  {field_word}f: I32,\n}}\n");
        for (op_label, op) in FIELD_OPS {
            let tag = format!("vis_privstruct_{field_label}_{op_label}");
            // `priv fn`: a `fn` with no word that names a `priv` type would be E0303 (the heading names a narrower type).
            let op = op.replacen("fn op", "priv fn op", 1);
            let want: Vec<(String, String)> =
                if op_label == "rest" { vec![pair("E0020", "shapes.onsa")] } else { vec![] };
            let (code, diags, doc) = check_package(&tag, &[("shapes.onsa", format!("{decl}\n{op}"))]);
            if diags != want || code != if want.is_empty() { 0 } else { 1 } {
                problems.push(format!("{tag}: exit {code}, want {want:?}: {doc}"));
            }
        }
        let tag = format!("vis_privstruct_{field_label}_other");
        let texts = [("shapes.onsa", decl), ("other.onsa", "use shapes.{S}\n".to_string())];
        let (code, diags, doc) = check_package(&tag, &texts);
        if code != 1 || diags != vec![pair("E0303", "other.onsa")] {
            problems.push(format!("{tag}: exit {code}, want one E0303 on the `use`: {doc}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §7, §15.1 (S-366): a `..` that leaves a field that the module cannot see is one E0303 with at least one note
/// and no candidate, and the same `..` with every field seen is one E0020 with exactly one candidate.
#[test]
fn a_rest_pattern_that_leaves_a_hidden_field_has_a_note_and_no_candidate() {
    let shapes =
        "pub struct Ring {\n  data: [F32; 4],\n  priv head: U32,\n}\n\npub struct Open {\n  x: F32,\n  y: F32,\n}\n";
    let other = "use shapes.{Ring, Open}\n\n\
        fn hidden(r: Ring) -> F32 {\n  match r {\n    Ring { data: d, .. } => d[0],\n  }\n}\n\n\
        fn seen(o: Open) -> F32 {\n  match o {\n    Open { x: a, .. } => a,\n  }\n}\n";
    let d = Dir::pkg("vis_rest_note");
    d.write("shapes.onsa", shapes);
    d.write("other.onsa", other);
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let diags = diagnostics(&doc);
    assert_eq!(diags.len(), 2, "{doc}");
    let by_line = |line: u64| -> &Value {
        diags
            .iter()
            .find(|x| span_of(&x["span"]).line == line)
            .unwrap_or_else(|| panic!("no diagnostic on line {line}: {doc}"))
    };
    let hidden = by_line(5);
    assert_eq!(str_of(hidden, "code"), "E0303", "{doc}");
    assert!(array_of(hidden, "fixes").is_empty(), "no candidate: {doc}");
    assert!(!array_of(hidden, "notes").is_empty(), "a note: {doc}");
    let seen = by_line(11);
    assert_eq!(str_of(seen, "code"), "E0020", "{doc}");
    assert_eq!(array_of(seen, "fixes").len(), 1, "{doc}");
}

/// §15.1: a field of a generic struct is as hidden as any other (`Ring[T, const N: U32]` with a `priv head`),
/// whatever the arguments the other module writes.
#[test]
fn a_priv_field_of_a_generic_struct_is_hidden_for_every_argument() {
    let shapes = "pub struct Ring[T, const N: U32] {\n  data: [T; N],\n  priv head: U32,\n}\n";
    let mut problems: Vec<String> = Vec::new();
    for (elem, len, label) in [("F32", "4", "f32"), ("I32", "8", "i32"), ("Bool", "2", "bool")] {
        let other = format!(
            "use shapes.{{Ring}}\n\nfn hidden(r: Ring[{elem}, {len}]) -> U32 {{\n  r.head\n}}\n\nfn seen(r: Ring[{elem}, {len}]) -> {elem} {{\n  r.data[0]\n}}\n"
        );
        let tag = format!("vis_generic_{label}");
        let (code, diags, doc) = check_package(&tag, &[("shapes.onsa", shapes.to_string()), ("other.onsa", other)]);
        if code != 1 || diags != vec![pair("E0303", "other.onsa")] {
            problems.push(format!("{tag}: exit {code}, want one E0303: {doc}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

// ---- the members of an impl ---------------------------------------------------------------------------

/// The calls of a member `m` (a method), `make` (an associated function) and `C` (an associated constant) of `S`.
const MEMBER_CALLS: [(&str, &str); 3] = [
    ("method", "fn call(s: S) -> I32 {\n  s.m()\n}\n"),
    ("assoc_fn", "fn call() -> S {\n  S.make()\n}\n"),
    ("assoc_const", "fn call() -> I32 {\n  S.C\n}\n"),
];

/// §15.1 (R-38, S-491): a member with `priv` is the module's alone, whichever way it is called, and a member
/// with no word is the package's; a `pub` member is fine on a `pub` struct (on a struct with no word it is a
/// repeat, E0020, and is left out here). The associated function is E0303 and not E0401 "is not a value".
#[test]
fn a_priv_member_is_the_modules_whichever_way_it_is_called() {
    let mut problems: Vec<String> = Vec::new();
    // (struct word, member word): a `pub` member of a type with no word is a different diagnostic.
    let combos = [("pub ", "pub "), ("pub ", ""), ("pub ", "priv "), ("", ""), ("", "priv ")];
    for (struct_word, member_word) in combos {
        let impl_text = format!(
            "{struct_word}struct S {{\n  a: I32,\n}}\n\nimpl S {{\n  {member_word}fn m(self) -> I32 {{\n    1\n  }}\n\n  {member_word}fn make() -> S {{\n    S {{ a: 1 }}\n  }}\n\n  {member_word}const C: I32 = 1\n}}\n"
        );
        for (call_label, call) in MEMBER_CALLS {
            for other_module in [false, true] {
                let tag = format!(
                    "vis_member_{}_{}_{call_label}_{}",
                    struct_word.trim(),
                    if member_word.is_empty() { "none" } else { member_word.trim() },
                    other_module as u8
                );
                let (file, texts) = if other_module {
                    (
                        "other.onsa",
                        vec![("shapes.onsa", impl_text.clone()), ("other.onsa", format!("use shapes.{{S}}\n\n{call}"))],
                    )
                } else {
                    ("shapes.onsa", vec![("shapes.onsa", format!("{impl_text}\n{call}"))])
                };
                let hidden = other_module && member_word == "priv ";
                let want: Vec<(String, String)> = if hidden { vec![pair("E0303", file)] } else { vec![] };
                let (code, diags, doc) = check_package(&tag, &texts);
                if diags != want || code != if hidden { 1 } else { 0 } {
                    problems.push(format!("{tag}: exit {code}, want {want:?}: {doc}"));
                }
                if hidden {
                    for d in diagnostics(&doc) {
                        if str_of(d, "message").contains("is not a value") {
                            problems.push(format!("{tag}: the message says the type is not a value: {d}"));
                        }
                    }
                }
            }
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1 (S-662 as the spec states it): the members of a type with `priv` are `fn` and `priv fn` alike, and both
/// reach the module that declares it.
#[test]
fn the_members_of_a_priv_type_reach_the_module() {
    let text = "priv struct Hidden {\n  v: I32,\n}\n\nimpl Hidden {\n  fn plain(self) -> I32 {\n    self.v\n  }\n\n  priv fn narrow(self) -> I32 {\n    self.v + 1\n  }\n\n  fn make() -> Hidden {\n    Hidden { v: 1 }\n  }\n}\n\npriv fn use_it() -> I32 {\n  let h = Hidden.make()\n  h.plain() + h.narrow()\n}\n";
    let (code, diags, doc) = check_package("vis_priv_type_members", &[("shapes.onsa", text.to_string())]);
    assert_eq!((code, diags), (0, vec![]), "{doc}");
}

// ---- std ----------------------------------------------------------------------------------------------

/// §11.8 (S-36): `Gen[T]` of `std.test` keeps its contents to itself (`seed` is `priv`), so the user's code
/// that reads, writes, builds or matches it gets E0303, and the generators of `std.test.gen` are fine.
#[test]
fn the_contents_of_gen_are_not_seen_by_the_user() {
    let mut problems: Vec<String> = Vec::new();
    let ops = [
        ("read", "fn op(g: Gen[F32]) -> U64 {\n  g.seed\n}\n", true),
        ("write", "fn op(inout g: Gen[F32]) {\n  g.seed = 1\n}\n", true),
        ("literal", "fn op() -> Gen[F32] {\n  Gen { seed: 7 }\n}\n", true),
        ("pattern", "fn op(g: Gen[F32]) -> U64 {\n  match g {\n    Gen { seed: s } => s,\n  }\n}\n", true),
        ("made", "fn op() -> Gen[F32] {\n  gen.f32(0.0, 1.0)\n}\n", false),
    ];
    for (label, op, bad) in ops {
        let tag = format!("vis_gen_{label}");
        let text = format!("use std.test.{{gen, Gen}}\n\n{op}");
        let (code, diags, doc) = check_package(&tag, &[("main.onsa", text)]);
        let want = if bad { vec![pair("E0303", "main.onsa")] } else { vec![] };
        if diags != want || code != if bad { 1 } else { 0 } {
            problems.push(format!("{tag}: exit {code}, want {want:?}: {doc}"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

// ---- the heads that were read on after a mistake (S-482, S-593) -------------------------------------------

/// §18.1 (S-482, S-593): the visibility of a declaration whose head has a mistake and is read on is the one
/// that was written when one kind of word was written right (`pub` only or `priv` only, a doubled word is
/// one), and none (the package) otherwise. Another module takes the declaration with a `use`: E0303 for
/// the ones recorded `priv`, nothing for the rest. The diagnostics of `util.onsa` are the mistakes.
#[test]
fn a_declaration_read_on_after_a_mistake_has_the_visibility_that_was_written() {
    // (the head, whether the module `other` sees it, whether the head has a mistake). The code of the mistake
    // is not asked (the spec states it for some heads only); each head with a mistake has one in `util.onsa`.
    let heads: [(&str, bool, bool); 12] = [
        ("#[inline] pub fn", true, true),
        ("#[inline] priv fn", false, true),
        ("pub export fn", true, true),
        ("priv export fn", false, true),
        ("pub const fn", true, true),
        ("pub pub fn", true, true),
        ("priv priv fn", false, true),
        ("pub(crate) fn", true, true),
        ("pub(crate) pub fn", true, true),
        ("priv pub fn", true, true),
        ("pub fn", true, false),
        ("fn", true, false),
    ];
    let mut problems: Vec<String> = Vec::new();
    for (i, (head, seen, mistake)) in heads.iter().enumerate() {
        let name = format!("h{i}");
        let tag = format!("vis_heads_{i}");
        let util = format!("{head} {name}() -> I32 {{\n  1\n}}\n");
        let other = format!("use util.{{{name}}}\n\nfn call() -> I32 {{\n  {name}()\n}}\n");
        let (code, diags, doc) = check_package(&tag, &[("util.onsa", util), ("other.onsa", other)]);
        let in_util = diags.iter().filter(|(_, f)| f == "util.onsa").count();
        let in_other: Vec<(String, String)> = diags.iter().filter(|(_, f)| f == "other.onsa").cloned().collect();
        let want_other = if *seen { vec![] } else { vec![pair("E0303", "other.onsa")] };
        let want_code = if *mistake || !seen { 1 } else { 0 };
        if in_util != *mistake as usize || in_other != want_other || code != want_code {
            problems.push(format!(
                "`{head}`: exit {code}, {in_util} in util.onsa, want {mistake} and {want_other:?}: {doc}"
            ));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}
