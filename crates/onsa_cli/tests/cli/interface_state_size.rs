//! `onsa interface` does not show the size of the state of a flow as an item of its namespace (spec §11.6, §12.4,
//! §18.2; R-490; W7-15 U4/t).
//!
//! What the spec fixes, and so what is checked:
//! - §11.6: the size of the state (the bytes of the fast and the bulk region) is not in the namespace of a flow; it is in the C
//!   header and in `onsa interface`, and the names of the items in the namespace are fixed to the list of §11.6 (`State`, `Config`,
//!   `Params`, `Event`, `In`, `Out`, `Rendered`, `init`, `reset`, `process`, `process_inplace`, `render`). So the text and the
//!   `--json` of `onsa interface` have no item (a `const`) of a flow with the name `SIZE` or `BULK_SIZE`, nor `ALIGN` and
//!   `BULK_ALIGN` that §12.4 puts in the same place as the sizes (`g.SIZE`, `g.BULK_SIZE`, `g.ALIGN`, `g.BULK_ALIGN` for the flow
//!   `g`), for a flow with a state of any kind (a block input, a delay, a nested instance, a `prev~`), `pub`, with no word, in the
//!   text and in the package form;
//! - §11.6, §18.2: the other items the flow gives are listed as they are with the word of the flow (`g.State`, `g.Params` for a
//!   flow with a `block` input, `g.In` for two `sample` inputs, `g.Rendered`, `g.init`, `g.reset`, `g.process`,
//!   `g.process_inplace`, `g.render`), and the user's own constants of the module with these names (a `const SIZE` of the module,
//!   which is not in the namespace of a flow) are listed as any constant is, so the constants listed are the user's only;
//! - §18.2: a `priv` flow and its items are not listed, so no size of it is either.
//!
//! Not asked: where and how `onsa interface` shows the size of a state (the text of the note of the `State` line, the JSON
//! keys of the size), the values of the sizes, `--target` (the option is not in this version; what it shows of the sizes is not
//! fixed here), the layout of the fields of a state, and `@mem(bulk)` (E0200 in this version, so a bulk size is not made).

use crate::test_support;

use std::collections::BTreeSet;

use serde_json::Value;
use test_support::*;

const SOURCE: &str = "\
pub const SIZE: U32 = 3

pub const BULK_SIZE: U32 = 4

pub flow g(k: F32 at block, x: F32 at sample) -> F32 at sample {
  x * k
}

pub flow echo(x: F32 at sample) -> F32 at sample {
  let y = delay~(x, 4)
  y
}

flow nested(x: F32 at sample) -> F32 at sample {
  let a = g~(1.0, x)
  let b = echo~(a)
  a + b
}

pub flow two(l: F32 at sample, r: F32 at sample) -> F32 at sample {
  let p = prev~(l)
  p + r
}

pub flow long_line(x: F32 at sample) -> F32 at sample {
  let line = delay~(x, 64)
  line
}

priv flow hidden(x: F32 at sample) -> F32 at sample {
  prev~(x)
}
";

/// The flows of `SOURCE` that are listed, with the word of each.
const FLOWS: &[(&str, &str)] =
    &[("g", "pub "), ("echo", "pub "), ("nested", ""), ("two", "pub "), ("long_line", "pub ")];

/// The names that `§11.6` and `§12.4` keep out of the namespace of a flow.
const SIZE_NAMES: &[&str] = &["SIZE", "BULK_SIZE", "ALIGN", "BULK_ALIGN"];

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

/// Whether `name` (a dotted name such as `g.SIZE`) is a whole word of the text: the words are cut at the characters that are
/// not a letter, a digit, `_` or `.`, so `big.SIZE` is not `g.SIZE`.
fn mentions(text: &str, name: &str) -> bool {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.')).any(|w| w == name)
}

/// The lines of the text that start a constant (with the word or without), trimmed.
fn const_lines(text: &str) -> Vec<&str> {
    trimmed_lines(text).into_iter().filter(|l| l.starts_with("pub const ") || l.starts_with("const ")).collect()
}

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

/// The names of the objects of the document whose `kind` is `const`.
fn const_names(doc: &Value) -> BTreeSet<String> {
    let mut os = Vec::new();
    objects(doc, &mut os);
    os.iter()
        .filter(|o| o.get("kind").and_then(Value::as_str) == Some("const"))
        .filter_map(|o| o.get("name").and_then(Value::as_str).map(str::to_string))
        .collect()
}

// ---- the text ---------------------------------------------------------------------------------

/// §11.6, §12.4: the text has no `const` of a flow for the size of its state or its alignment, for each of the flows (a
/// `block` input, a delay, a nested instance, two `sample` inputs, a `prev~`; `pub` and with no word).
#[test]
fn the_text_has_no_item_of_the_size_of_a_state_in_the_namespace_of_a_flow() {
    let d = source_dir("text_size");
    let text = interface_text(&d, &["m.onsa"]);
    for (flow, _) in FLOWS {
        for size in SIZE_NAMES {
            let name = format!("{flow}.{size}");
            assert!(!mentions(&text, &name), "`{name}` is not an item of the namespace:\n{text}");
        }
    }
}

/// §11.6: the flow of the spec's own example (a `block` input and a `sample` input, `x * k`) alone in a file: no size in the
/// namespace of `g`.
#[test]
fn a_flow_with_a_block_input_has_no_size_item_alone_in_its_file() {
    let d = Dir::pkg("text_size_g");
    d.write("g.onsa", "pub flow g(k: F32 at block, x: F32 at sample) -> F32 at sample {\n  x * k\n}\n");
    let text = interface_text(&d, &["g.onsa"]);
    assert!(text.lines().any(|l| l.trim().starts_with("pub struct g.State")), "`g.State` is listed:\n{text}");
    for size in SIZE_NAMES {
        let name = format!("g.{size}");
        assert!(!mentions(&text, &name), "`{name}` is not an item of the namespace:\n{text}");
    }
    assert!(const_lines(&text).is_empty(), "no constant in a file of a flow only:\n{text}");
}

/// §11.6, §18.2: no item of the namespace is a constant: the constants of the text are the module's own, with the word they
/// have in the source (the names of the namespace are fixed to the list of §11.6, which has no constant).
#[test]
fn the_constants_of_the_text_are_the_constants_of_the_module_only() {
    let d = source_dir("text_consts");
    let text = interface_text(&d, &["m.onsa"]);
    let consts = const_lines(&text);
    assert_eq!(consts.len(), 2, "the two constants of the module only:\n{text}");
    assert!(consts.iter().any(|l| l.starts_with("pub const SIZE: U32")), "{consts:?}");
    assert!(consts.iter().any(|l| l.starts_with("pub const BULK_SIZE: U32")), "{consts:?}");
}

/// §11.6, §18.2: the other items of a flow are listed with the word of the flow, as before: the types and the functions of
/// the list of §11.6 that the flow has.
#[test]
fn the_other_generated_items_are_listed_with_the_word_of_the_flow() {
    let d = source_dir("text_items");
    let text = interface_text(&d, &["m.onsa"]);
    let lines = trimmed_lines(&text);
    let listed = |want: String| lines.iter().any(|l| l.starts_with(&want));
    for (flow, vis) in FLOWS {
        for want in [
            "struct {}.State",
            "struct {}.Rendered",
            "fn {}.init(",
            "rt fn {}.reset(",
            "rt fn {}.process(",
            "fn {}.render(",
        ] {
            let line = format!("{vis}{}", want.replace("{}", flow));
            assert!(listed(line.clone()), "`{line}` is listed:\n{text}");
        }
    }
    // `Params` is of a flow with a `block` input, `In` of a flow with two `sample` inputs, and `process_inplace` of a flow whose
    // `sample` inputs and outputs match.
    assert!(listed("pub struct g.Params".into()), "{text}");
    assert!(listed("pub struct two.In".into()), "{text}");
    assert!(listed("pub rt fn g.process_inplace(".into()), "{text}");
    assert!(listed("rt fn nested.process_inplace(".into()), "{text}");
}

/// §18.2: a `priv` flow and its items are not listed, so nothing of its size either.
#[test]
fn a_priv_flow_is_not_listed_with_anything() {
    let d = source_dir("text_priv");
    let text = interface_text(&d, &["m.onsa"]);
    assert!(!mentions(&text, "hidden") && !text.contains("hidden."), "{text}");
}

// ---- the package ------------------------------------------------------------------------------

/// §15.1, §11.6: the package form (no file named) lists the flows of every module the same way: no size in the namespace of any,
/// and the items of the list are still there.
#[test]
fn the_package_form_has_no_size_item_for_the_flows_of_any_module() {
    let d = Dir::pkg("package");
    d.write(
        "a.onsa",
        "pub flow a_flow(k: F32 at block, x: F32 at sample) -> F32 at sample {\n  let d = delay~(x, 8)\n  d * k\n}\n",
    );
    d.write("sub/b.onsa", "flow b_flow(x: F32 at sample) -> F32 at sample {\n  prev~(x)\n}\n");
    let text = interface_text(&d, &[]);
    for want in ["pub struct a_flow.State", "pub struct a_flow.Params", "struct b_flow.State", "fn b_flow.init("] {
        assert!(trimmed_lines(&text).iter().any(|l| l.starts_with(want)), "`{want}` is listed:\n{text}");
    }
    for flow in ["a_flow", "b_flow"] {
        for size in SIZE_NAMES {
            let name = format!("{flow}.{size}");
            assert!(!mentions(&text, &name), "`{name}` is not an item of the namespace:\n{text}");
        }
    }
    assert!(const_lines(&text).is_empty(), "no constant in a package of flows only:\n{text}");
    let json = interface_json(&d, &[]);
    assert!(const_names(&json).is_empty(), "no constant in the JSON of a package of flows only: {json}");
}

// ---- the JSON ---------------------------------------------------------------------------------

/// §11.6, §12.4: the items of `--json` have no object named for the size of a state or the alignment in the namespace of a
/// flow, and no constant of a flow at all.
#[test]
fn the_json_has_no_item_of_the_size_of_a_state_in_the_namespace_of_a_flow() {
    let d = source_dir("json_size");
    let doc = interface_json(&d, &["m.onsa"]);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let names = names(&doc);
    for (flow, _) in FLOWS {
        for size in SIZE_NAMES {
            let name = format!("{flow}.{size}");
            assert!(!names.contains(&name), "`{name}` is not an item of the namespace: {names:?}");
        }
    }
    let consts: BTreeSet<String> = ["SIZE", "BULK_SIZE"].iter().map(|s| s.to_string()).collect();
    assert_eq!(const_names(&doc), consts, "the constants of the module only: {doc}");
}

/// §11.6, §18.2: the JSON has the other items of each flow, as before, with the names of the list of §11.6.
#[test]
fn the_json_has_the_other_generated_items() {
    let d = source_dir("json_items");
    let doc = interface_json(&d, &["m.onsa"]);
    let names = names(&doc);
    for (flow, _) in FLOWS {
        for item in ["State", "Rendered", "init", "reset", "process", "render"] {
            let name = format!("{flow}.{item}");
            assert!(names.contains(&name), "`{name}` is listed: {names:?}");
        }
    }
    for want in ["g.Params", "two.In", "g.process_inplace"] {
        assert!(names.contains(want), "`{want}` is listed: {names:?}");
    }
    assert!(names.contains("SIZE") && names.contains("BULK_SIZE"), "the constants of the module: {names:?}");
    assert!(!names.iter().any(|n| n.starts_with("hidden")), "{names:?}");
}
