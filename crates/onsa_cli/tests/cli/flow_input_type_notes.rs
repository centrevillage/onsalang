//! W7-13 U3/t: what the E0810 of a type that cannot cross the boundary says (R-245; spec §11.6, §18.1), and the note of the E0806 of
//! a call `.(` on a value (S-372; spec §11.2, §18.1).
//!
//! R-245: the E0810 of the type of an input or an output at `sample` that is not a scalar, an array of scalars or (an output) a
//! struct of them said "nested arrays cannot cross the boundary" whatever the type was. The words are not fixed (§18.1), so these
//! tests pin only what the writer must be able to read: the type that was refused is in the words of the diagnostic (the main
//! sentence or a note) as it is written in the program, and the words do not speak of nested arrays when there is none.
//!
//! S-372: a call `f.(x)` whose callee is a value (an input of the flow, a field of an input) is the E0806 of the body of a flow (§11.2),
//! with no candidate (nothing to remove: what is written is not an item), and a fixed note that says why and what to write instead
//! (the words are not fixed; these tests pin that a note is, and that no candidate is). The callee that is an item has the candidate
//! that removes the `.` as it had (S-811).
//!
//! The inputs are programs in memory (`check_input_out`, nothing is written, `rules/common.md` 3.7).

use crate::test_support::sweep::{Texts, check_input_out, input_of};
use crate::test_support::{code_of, diagnostics, doc_of, fixes_of, notes_of, str_of};
use serde_json::Value;

/// The diagnostics of the package of the one file `main.onsa` of `src`.
fn check_main(src: &str) -> Vec<Value> {
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), src.to_string());
    let out = check_input_out(&input_of("demo", &texts));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}\n{src}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

/// The words of a diagnostic: the main sentence and the notes.
fn words_of(d: &Value) -> String {
    let notes: Vec<String> = notes_of(d).iter().map(|n| str_of(n, "message").to_string()).collect();
    format!("{}\n{}", str_of(d, "message"), notes.join("\n"))
}

fn codes_of(diags: &[Value]) -> Vec<String> {
    diags.iter().map(|d| code_of(d).to_string()).collect()
}

/// A program with a flow `g` that has a type that cannot cross the boundary at `sample`, and the type as it is written.
struct Boundary {
    /// What the case is about.
    name: &'static str,
    /// The declarations that the flow uses.
    decls: &'static str,
    /// The flow `g`.
    flow: &'static str,
    /// The spelling of the type that is refused, a word of the diagnostic.
    spelling: &'static str,
}

const BOUNDARY: &[Boundary] = &[
    Boundary {
        name: "an Option in an input",
        decls: "",
        flow: "pub flow g(x: Option[F32] at sample) -> F32 at sample { 1.0 }",
        spelling: "Option[F32]",
    },
    Boundary {
        name: "an Option in an output",
        decls: "",
        flow: "pub flow g(x: F32 at sample) -> Option[F32] at sample { None }",
        spelling: "Option[F32]",
    },
    Boundary {
        name: "an enum in an input",
        decls: "pub enum Curve { Tanh, Hard }",
        flow: "pub flow g(c: Curve at sample) -> F32 at sample { 1.0 }",
        spelling: "Curve",
    },
    Boundary {
        name: "an enum in an output",
        decls: "pub enum Curve { Tanh, Hard }",
        flow: "pub flow g(x: F32 at sample) -> Curve at sample { Curve.Tanh }",
        spelling: "Curve",
    },
    Boundary {
        name: "a struct in an input (R-41, R-279)",
        decls: "pub struct Pair { l: F32, r: F32 }",
        flow: "pub flow g(p: Pair at sample) -> F32 at sample { 1.0 }",
        spelling: "Pair",
    },
    Boundary {
        name: "the Params of another flow in an input",
        decls: "pub flow h(k: F32 at block, x: F32 at sample) -> F32 at sample { x * k }",
        flow: "pub flow g(p: h.Params at sample) -> F32 at sample { 1.0 }",
        spelling: "Params",
    },
    Boundary {
        name: "a function type in an input (S-372, read before the shape of the boundary)",
        decls: "",
        flow: "pub flow g(f: (rt fn(F32) -> F32) at sample, x: F32 at sample) -> F32 at sample { x }",
        spelling: "fn(F32) -> F32",
    },
    Boundary {
        name: "a text in an input",
        decls: "",
        flow: "pub flow g(s: Str at sample) -> F32 at sample { 1.0 }",
        spelling: "Str",
    },
];

#[test]
fn the_e0810_of_a_type_that_cannot_cross_the_boundary_names_the_type_and_not_nested_arrays() {
    let mut problems = Vec::new();
    for b in BOUNDARY {
        let src = format!("{}\n{}\n", b.decls, b.flow);
        let diags = check_main(&src);
        if codes_of(&diags) != ["E0810"] {
            problems.push(format!("{}: the diagnostics are not one E0810: {diags:?}", b.name));
            continue;
        }
        let words = words_of(&diags[0]);
        if !words.contains(b.spelling) {
            problems.push(format!("{}: `{}` is not in the words: {words}", b.name, b.spelling));
        }
        if words.contains("nested arrays") {
            problems.push(format!("{}: the words speak of nested arrays: {words}", b.name));
        }
        if !fixes_of(&diags[0]).is_empty() {
            problems.push(format!("{}: the E0810 has a candidate: {:?}", b.name, fixes_of(&diags[0])));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// A flow `g` whose body has a call `.(` on a value.
const VALUE_CALLS: &[(&str, &str, &str)] = &[
    (
        "an input of a function type",
        "",
        "pub flow g(f: (rt fn(F32) -> F32) at block, x: F32 at sample) -> F32 at sample { f.(x) }",
    ),
    (
        "an input of a function type at init",
        "",
        "pub flow g(f: (rt fn(F32) -> F32) at init, x: F32 at sample) -> F32 at sample { f.(x) }",
    ),
    (
        "a field of a struct input that is a function",
        "pub struct Pt { cb: rt fn(F32) -> F32, k: F32 }",
        "pub flow g(p: Pt at init, x: F32 at sample) -> F32 at sample { p.cb.(x) }",
    ),
    (
        "the input of a function type, in an argument",
        "rt fn twice(y: F32) -> F32 { y * 2.0 }",
        "pub flow g(f: (rt fn(F32) -> F32) at block, x: F32 at sample) -> F32 at sample { twice(f.(x)) }",
    ),
];

#[test]
fn the_e0806_of_a_call_on_a_value_has_a_note_and_no_candidate() {
    let mut problems = Vec::new();
    for (name, decls, flow) in VALUE_CALLS {
        let src = format!("{decls}\n{flow}\n");
        let diags = check_main(&src);
        if codes_of(&diags) != ["E0806"] {
            problems.push(format!("{name}: the diagnostics are not one E0806: {diags:?}"));
            continue;
        }
        if notes_of(&diags[0]).is_empty() {
            problems.push(format!("{name}: the E0806 has no note: {:?}", diags[0]));
        }
        if !fixes_of(&diags[0]).is_empty() {
            problems.push(format!("{name}: the E0806 has a candidate: {:?}", diags[0]));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn the_e0806_of_a_call_on_an_item_has_the_candidate_that_removes_the_dot() {
    let src = "rt fn dbl(y: F32) -> F32 { y * 2.0 }\npub flow g(x: F32 at sample) -> F32 at sample { dbl.(x) }\n";
    let diags = check_main(src);
    assert_eq!(codes_of(&diags), ["E0806"], "{diags:?}");
    assert_eq!(fixes_of(&diags[0]).len(), 1, "{:?}", diags[0]);
}
