//! The generated API of the flows with an event in their head in `onsa interface` and in the notes (W7-11 U2h/t; spec §11.6, §11.9, §11.11, §15.1, §18.1, §18.2; S-564, S-1087, S-560).
//!
//! - `process`, `process_inplace` and `render` of a flow with an event input or an event output are the functions that the border of the events stops (E0200 in `check`, until W10-07), so `onsa interface` does not list
//!   them; it lists `State`, `init` and `reset` (the border stops only the three), and the types that are generated: `Rendered` of every flow, `Out` of a struct at `sample`, `In` of two inputs at `sample`
//!   (the `Rendered` of an event output has the positions and the values, §11.6: `out: Buf[(U32, E)]`). A flow with no event and a flow at `sample * N` are listed as they are.
//! - The E0302 of the `process_inplace` of a flow with an event output says that the flow gives events (a note with the word `event`; the words are not fixed, §18.1).
//!
//! The texts are written from the spec; no expectation is taken from the output of the compiler.

use crate::test_support::sweep::{Texts, check_input_out, input_of};
use crate::test_support::{Dir, code_of, diagnostics, doc_of, notes_of, run, str_of};
use serde_json::Value;

const SOURCE: &str = "\
pub struct Pair: Default {
  l: F32,
  r: F32,
}

pub enum Mode {
  A,
  B,
}

pub flow plain(x: F32 at sample) -> F32 at sample {
  x
}

pub flow wide(x: F32 at sample) -> F32 at (sample * 2) {
  [x, x]
}

pub flow in_only(m: U32 at event) -> U32 at sample {
  m
}

pub flow in_two(a: F32 at sample, b: F32 at sample, m: U32 at event) -> F32 at sample {
  a + b
}

pub flow in_struct(x: F32 at sample, m: U32 at event) -> Pair at sample {
  Pair { l: x, r: x }
}

pub flow out_only(x: F32 at sample) -> U32 at event {
  if x > 0.5 { Some(1) } else { None }
}

pub flow out_same(x: F32 at sample) -> F32 at event {
  Some(x)
}

pub flow out_pair(x: F32 at sample) -> Pair at event {
  Some(Pair { l: x, r: x })
}

pub flow out_mode(x: F32 at sample) -> Mode at event {
  if x > 0.5 { Some(Mode.A) } else { None }
}

pub flow both(m: U32 at event) -> U32 at event {
  Some(m)
}

pub flow slow_first(x: F32 at (sample / 4), m: U32 at event) -> F32 at sample {
  0.0
}
";

/// The names of the members that `onsa interface --json` lists under the flow `flow`.
fn members(doc: &Value, flow: &str) -> Vec<String> {
    let items = doc["modules"][0]["items"].as_array().expect("items");
    let item =
        items.iter().find(|i| i["kind"] == "flow" && i["name"] == flow).unwrap_or_else(|| panic!("no flow {flow}"));
    item["members"].as_array().expect("members").iter().map(|m| str_of(m, "name").to_string()).collect()
}

fn listed(doc: &Value, flow: &str, name: &str) -> bool {
    members(doc, flow).contains(&format!("{flow}.{name}"))
}

/// The names and the types of the fields of the `Rendered` listed under the flow `flow`.
fn rendered_fields(doc: &Value, flow: &str) -> Vec<(String, String)> {
    let items = doc["modules"][0]["items"].as_array().expect("items");
    let item = items.iter().find(|i| i["kind"] == "flow" && i["name"] == flow).expect("the flow");
    let name = format!("{flow}.Rendered");
    let members = item["members"].as_array().expect("members");
    let rendered = members.iter().find(|m| m["name"] == name.as_str()).unwrap_or_else(|| panic!("no {name}"));
    let fields = rendered["fields"].as_array().expect("fields");
    fields.iter().map(|f| (str_of(f, "name").to_string(), str_of(f, "ty").to_string())).collect()
}

fn interface_doc(tag: &str) -> Value {
    let d = Dir::pkg(tag);
    d.write("main.onsa", SOURCE);
    let out = run(d.root(), &["interface", "--json"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    doc_of(&out)
}

const EVENT_FLOWS: [&str; 9] =
    ["in_only", "in_two", "in_struct", "out_only", "out_same", "out_pair", "out_mode", "both", "slow_first"];

#[test]
fn the_functions_of_the_border_are_not_listed_for_a_flow_with_an_event() {
    let doc = interface_doc("event_interface_border");
    for flow in EVENT_FLOWS {
        for name in ["process", "process_inplace", "render"] {
            assert!(!listed(&doc, flow, name), "{flow}.{name} is listed: {:?}", members(&doc, flow));
        }
    }
}

#[test]
fn state_init_and_reset_are_listed_for_a_flow_with_an_event() {
    let doc = interface_doc("event_interface_state");
    for flow in EVENT_FLOWS {
        for name in ["State", "init", "reset"] {
            assert!(listed(&doc, flow, name), "{flow}.{name} is not listed: {:?}", members(&doc, flow));
        }
    }
}

/// `Rendered` of a flow with a `sample` output is listed, and of an event output with the positions and the values (§11.6); `Out` of a struct at `sample` and `In` of two inputs at `sample` are listed, and an event output has no `Out`.
#[test]
fn the_generated_types_are_listed_where_they_are_generated() {
    let doc = interface_doc("event_interface_types");
    for flow in ["in_only", "in_two", "in_struct", "slow_first"] {
        assert!(listed(&doc, flow, "Rendered"), "{flow}.Rendered: {:?}", members(&doc, flow));
    }
    for (flow, event) in
        [("out_only", "U32"), ("out_same", "F32"), ("out_pair", "Pair"), ("out_mode", "Mode"), ("both", "U32")]
    {
        let fields = rendered_fields(&doc, flow);
        assert_eq!(fields, [("out".to_string(), format!("Buf[(U32, {event})]"))], "{flow}.Rendered");
        assert!(!listed(&doc, flow, "Out"), "{flow}.Out: {:?}", members(&doc, flow));
    }
    assert!(listed(&doc, "in_struct", "Out"), "{:?}", members(&doc, "in_struct"));
    assert!(listed(&doc, "in_two", "In"), "{:?}", members(&doc, "in_two"));
    assert!(!listed(&doc, "in_only", "Out") && !listed(&doc, "in_only", "In"), "{:?}", members(&doc, "in_only"));
}

/// A flow with no event is listed with the three functions (and `process_inplace` where the types agree), and so is a flow at `sample * N` (the border of that is a later work, §11.9).
#[test]
fn a_flow_with_no_event_and_a_flow_at_sample_times_n_are_listed_as_they_are() {
    let doc = interface_doc("event_interface_plain");
    for name in ["State", "init", "reset", "process", "process_inplace", "render", "Rendered"] {
        assert!(listed(&doc, "plain", name), "plain.{name}: {:?}", members(&doc, "plain"));
    }
    for name in ["State", "init", "reset", "process", "render"] {
        assert!(listed(&doc, "wide", name), "wide.{name}: {:?}", members(&doc, "wide"));
    }
}

/// The text output has the same: no line of a function of the border under a flow with an event, and the lines of the flow beside it.
#[test]
fn the_text_of_interface_has_the_same_lists() {
    let d = Dir::pkg("event_interface_text");
    d.write("main.onsa", SOURCE);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("E0200") && !out.stderr.contains("internal error"), "{}{}", out.stdout, out.stderr);
    for flow in EVENT_FLOWS {
        for name in ["process", "process_inplace", "render"] {
            let at = format!("fn {flow}.{name}(");
            assert!(!out.stdout.contains(&at), "`{at}` is listed:\n{}", out.stdout);
        }
        assert!(out.stdout.contains(&format!("fn {flow}.init(")), "no `{flow}.init`:\n{}", out.stdout);
    }
    assert!(out.stdout.contains("fn plain.process_inplace("), "{}", out.stdout);
    assert!(out.stdout.contains("fn plain.render("), "{}", out.stdout);
}

/// A flow with an event in its head and a flow with a heading that is in error: the error is the only diagnostic of `interface` (the flow with the error lists nothing it cannot know), and the flows beside it are listed as above.
#[test]
fn interface_of_a_package_with_a_heading_in_error_is_stopped_by_that_error_alone() {
    let d = Dir::pkg("event_interface_heading_error");
    d.write("main.onsa", &format!("{SOURCE}\npub flow bad(x: F32 at sample) -> Nope at event {{\n  None\n}}\n"));
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("error[E0302]") || out.stderr.contains("error[E0302]"), "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("E0200") && !out.stderr.contains("E0200"), "{}{}", out.stdout, out.stderr);
}

// ---------------------------------------------------------------- the port that the E0200 of the border is of

/// The E0200 of the border is of the port of the heading written first (§11.9, §11.11), of the event or of the derived clock: the text has its clock, and only that of a derived clock has the note of `.down~(N)`.
#[test]
fn the_e0200_of_the_border_is_of_the_first_port_of_the_heading() {
    let flows = [
        ("flow k(m: U32 at event, x: F32 at (sample / 4)) -> F32 at sample {\n  0.0\n}\n", true),
        ("flow k(x: F32 at (sample / 4), m: U32 at event) -> F32 at sample {\n  0.0\n}\n", false),
        ("flow k(x: F32 at (sample / 4)) -> U32 at event {\n  None\n}\n", false),
    ];
    for (flow, event) in flows {
        for name in ["process", "render"] {
            let src = format!("{flow}\nfn u() {{\n  let _ = k.{name}\n}}\n");
            let diags = check_main(&src);
            let codes: Vec<&str> = diags.iter().map(code_of).collect();
            assert_eq!(codes, ["E0200"], "{src}\n{diags:?}");
            let text = str_of(&diags[0], "message");
            assert_eq!((text.contains("at `event`"), text.contains("sample / N")), (event, !event), "{text}\n{src}");
            let notes = notes_of(&diags[0]);
            assert_eq!(notes.iter().any(|n| str_of(n, "message").contains(".down~(N)")), !event, "{notes:?}\n{src}");
        }
    }
}

/// The E0200 of a flow that does not run in this version is at the first `event` of its heading, the inputs before the output.
#[test]
fn the_e0200_of_a_run_is_at_the_first_event_of_the_heading() {
    let heads = [
        "flow k(x: F32 at sample, m: F32 at event, n: F32 at event) -> F32 at sample {\n  x\n}\n",
        "flow k(x: F32 at sample, m: F32 at event) -> F32 at event {\n  Some(m)\n}\n",
        "flow k(x: F32 at sample) -> F32 at event {\n  Some(x)\n}\n",
    ];
    for head in heads {
        let d = Dir::pkg("event_gate_first_port");
        d.write("main.onsa", &format!("pub {head}"));
        let out = run(d.root(), &["dump", "--core"]);
        assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
        let at = format!("main.onsa:1:{}: error[E0200]", "pub ".len() + head.find("event").expect("event") + 1);
        assert!(out.stdout.contains(&at) || out.stderr.contains(&at), "no `{at}`:\n{}{}", out.stdout, out.stderr);
    }
}

// ---------------------------------------------------------------- the note of the E0302 of `process_inplace`

fn check_main(src: &str) -> Vec<Value> {
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), src.to_string());
    let out = check_input_out(&input_of("demo", &texts));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}\n{src}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

/// The `process_inplace` of a flow that gives events is E0302 with a note that says so (the flow is not one whose types differ: the types of the `sample` inputs and the output of `out_same` agree as written), for each
/// shape of the output (the one value of the type of the input, a struct, an enum) and each number of inputs.
#[test]
fn the_e0302_of_a_flow_with_an_event_output_says_that_it_gives_events() {
    let flows = [
        "flow k(x: F32 at sample) -> F32 at event {\n  Some(x)\n}\n",
        "flow k(x: F32 at sample) -> Pair at event {\n  Some(Pair { l: x, r: x })\n}\n",
        "flow k(a: F32 at sample, b: F32 at sample) -> Pair at event {\n  Some(Pair { l: a, r: b })\n}\n",
        "flow k(x: F32 at sample) -> Mode at event {\n  if x > 0.5 { Some(Mode.A) } else { None }\n}\n",
        "flow k(m: F32 at event) -> F32 at event {\n  Some(m)\n}\n",
    ];
    for flow in flows {
        let src = format!(
            "struct Pair: Default {{\n  l: F32,\n  r: F32,\n}}\n\nenum Mode {{\n  A,\n  B,\n}}\n\n{flow}\nfn u() {{\n  let _ = k.process_inplace\n}}\n"
        );
        let diags = check_main(&src);
        let codes: Vec<&str> = diags.iter().map(code_of).collect();
        assert_eq!(codes, ["E0302"], "{src}\n{diags:?}");
        let notes: Vec<String> = notes_of(&diags[0]).iter().map(|n| str_of(n, "message").to_string()).collect();
        assert!(notes.iter().any(|n| n.contains("event")), "no note with `event`: {notes:?}\n{src}");
    }
}
