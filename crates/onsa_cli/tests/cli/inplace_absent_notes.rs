//! W7-12 U3b/t: the notes of the E0302 of a `process_inplace` that a flow does not have (R-480; spec §11.6, §15.1, §18.1),
//! and the words of the E0200 of the C names that name the input of the user (S-30, R-15; §11.6, §14.2, §18.1).
//!
//! `process_inplace` is generated for a flow whose `sample` inputs and outputs agree in number and in types, in order, the
//! struct of an output expanded into its fields and an array `[T; N]` one type with its length (S-197, S-220; §11.6). For any
//! other flow the name is not there, so the body path `k.process_inplace(…)` and the `use main.k.process_inplace` are an E0302.
//! The E0302 shows how the flow differs: a note that tells the types of the `sample` inputs and the types of the outputs (the
//! fields of a struct) of the flow, in the order they are written, so that the writer sees why it was not made. The words of the
//! note are not fixed (§18.1); these tests pin that a note is, and that the spellings of the types are in it.
//!
//! No note of this kind is given when the name is no `process_inplace` (`k.nope`), when the flow has `process_inplace`, and when
//! the heading of the flow does not read (an output that is an E0810, a clock that is not read): the E0302 of `process_inplace`
//! is not reported at all (§18.1, S-1087, R-471). A path in the position of a type is the E0308 of a name that is no type (S-708,
//! §11.6): that is no E0302 either.
//!
//! The inputs are programs in memory (`check_input_out`, nothing is written, `rules/common.md` 3.7), except the build of the
//! last test, which writes a package (the files that `onsa build` reads).

use crate::test_support::sweep::{Texts, check_input_out, input_of};
use crate::test_support::{Dir, code_of, diagnostics, doc_of, notes_of, run, span_of, str_of};
use serde_json::Value;

/// The diagnostics of the package of the one file `main.onsa` of `src`.
fn check_main(src: &str) -> Vec<Value> {
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), src.to_string());
    let out = check_input_out(&input_of("demo", &texts));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}\n{src}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

fn notes_text(d: &Value) -> String {
    notes_of(d).iter().map(|n| str_of(n, "message")).collect::<Vec<_>>().join("\n")
}

fn codes_of(diags: &[Value]) -> Vec<String> {
    diags.iter().map(|d| code_of(d).to_string()).collect()
}

/// The one E0302 of a program of which that is the only diagnostic.
fn only_e0302(src: &str) -> Value {
    let diags = check_main(src);
    assert_eq!(codes_of(&diags), ["E0302"], "{src}\n{diags:?}");
    diags[0].clone()
}

/// What is wrong with the E0302 of the program `src` of the shape `s` (the one diagnostic of it, with the note, at `line`);
/// empty when right. The shapes are all tried, and the problems are told together.
fn judge_program(s: &Shape, form: &str, src: &str, line: usize) -> Vec<String> {
    let diags = check_main(src);
    if codes_of(&diags) != ["E0302"] {
        return vec![format!("{} ({form}): the diagnostics are not one E0302: {diags:?}", s.name)];
    }
    check_note(s, form, &diags[0], line)
}

/// A flow `k` of the heading `head` (an output of a struct is declared before it), and the user of its `process_inplace`.
struct Shape {
    /// What the case is about.
    name: &'static str,
    /// The declarations the heading uses (structs).
    decls: &'static str,
    /// The flow `k`.
    flow: &'static str,
    /// The spellings of the types that the note shows (inputs and outputs, the fields of a struct), each a word of the note.
    spellings: &'static [&'static str],
    /// The spellings of types of the flow that the note does not show (a `block` and an `init` input are not counted).
    absent: &'static [&'static str],
    /// The spellings that stand in this order in the note (the order they are written in).
    order: &'static [&'static str],
}

const ABSENT: &[Shape] = &[
    // The numbers differ: two scalars and one array (S-220: an array is not expanded).
    Shape {
        name: "count: F32, F32 -> [F32; 2]",
        decls: "",
        flow: "pub flow k(l: F32 at sample, r: F32 at sample) -> [F32; 2] at sample { [l, r] }",
        spellings: &["F32", "[F32; 2]"],
        absent: &[],
        order: &[],
    },
    // The same with types that tell one place from another, in the order they are written.
    Shape {
        name: "count, types of each place: U8, F64 -> [I32; 2]",
        decls: "",
        flow: "pub flow k(a: U8 at sample, b: F64 at sample) -> [I32; 2] at sample { [0, 0] }",
        spellings: &["U8", "F64", "[I32; 2]"],
        absent: &[],
        order: &["U8", "F64"],
    },
    // The numbers differ the other way: one input and three fields.
    Shape {
        name: "count: F32 -> P { l: F64, r: U32, w: I16 }",
        decls: "pub struct P { l: F64, r: U32, w: I16 }",
        flow: "pub flow k(x: F32 at sample) -> P at sample { P { l: 0.0, r: 0, w: 0 } }",
        spellings: &["F32", "F64", "U32", "I16"],
        absent: &[],
        order: &["F64", "U32", "I16"],
    },
    // The element type differs.
    Shape {
        name: "type: F32 -> F64",
        decls: "",
        flow: "pub flow k(x: F32 at sample) -> F64 at sample { x as F64 }",
        spellings: &["F32", "F64"],
        absent: &[],
        order: &[],
    },
    // The element type of the arrays differs.
    Shape {
        name: "type of the elements: [F32; 2] -> [F64; 2]",
        decls: "",
        flow: "pub flow k(x: [F32; 2] at sample) -> [F64; 2] at sample { [x[0] as F64, x[1] as F64] }",
        spellings: &["[F32; 2]", "[F64; 2]"],
        absent: &[],
        order: &[],
    },
    // The length of the arrays differs (the length is a part of the type).
    Shape {
        name: "length: [F32; 2] -> [F32; 3]",
        decls: "",
        flow: "pub flow k(x: [F32; 2] at sample) -> [F32; 3] at sample { [x[0], x[1], 0.0] }",
        spellings: &["[F32; 2]", "[F32; 3]"],
        absent: &[],
        order: &[],
    },
    // An array of one element is not its element.
    Shape {
        name: "array and a value: F32 -> [F32; 1]",
        decls: "",
        flow: "pub flow k(x: F32 at sample) -> [F32; 1] at sample { [x] }",
        spellings: &["F32", "[F32; 1]"],
        absent: &[],
        order: &[],
    },
    Shape {
        name: "array and a value: [F64; 1] -> F64",
        decls: "",
        flow: "pub flow k(x: [F64; 1] at sample) -> F64 at sample { x[0] }",
        spellings: &["[F64; 1]", "F64"],
        absent: &[],
        order: &[],
    },
    // The struct of the output is expanded into its fields; an array input is one type, not two fields.
    Shape {
        name: "struct fields: [F32; 2] -> P { l: F32, r: F32 }",
        decls: "pub struct P { l: F32, r: F32 }",
        flow: "pub flow k(x: [F32; 2] at sample) -> P at sample { P { l: x[0], r: x[1] } }",
        spellings: &["[F32; 2]", "F32"],
        absent: &[],
        order: &[],
    },
    Shape {
        name: "struct fields of two types: [F32; 2] -> P { l: F64, r: U32 }",
        decls: "pub struct P { l: F64, r: U32 }",
        flow: "pub flow k(x: [F32; 2] at sample) -> P at sample { P { l: x[0] as F64, r: 0 } }",
        spellings: &["[F32; 2]", "F64", "U32"],
        absent: &[],
        order: &["F64", "U32"],
    },
    // The field of the output is an array: the two scalars are not the array.
    Shape {
        name: "array field: F32, F32 -> S { x: [F32; 2] }",
        decls: "pub struct S { x: [F32; 2] }",
        flow: "pub flow k(l: F32 at sample, r: F32 at sample) -> S at sample { S { x: [l, r] } }",
        spellings: &["F32", "[F32; 2]"],
        absent: &[],
        order: &[],
    },
    // The array field is in its place in the order of the fields.
    Shape {
        name: "array field, order: F64, [F32; 2] -> R { v: [F32; 2], w: F64 }",
        decls: "pub struct R { v: [F32; 2], w: F64 }",
        flow: "pub flow k(a: F64 at sample, b: [F32; 2] at sample) -> R at sample { R { v: b, w: a } }",
        spellings: &["F64", "[F32; 2]"],
        absent: &[],
        order: &[],
    },
    // The numbers are the same, the second type differs.
    Shape {
        name: "second type: F32, F32 -> P { l: F32, r: F64 }",
        decls: "pub struct P { l: F32, r: F64 }",
        flow: "pub flow k(l: F32 at sample, r: F32 at sample) -> P at sample { P { l: l, r: r as F64 } }",
        spellings: &["F32", "F64"],
        absent: &[],
        order: &[],
    },
    // No `sample` input: no input to pair with the output (the note shows the types of the output).
    Shape {
        name: "no input: -> F64",
        decls: "",
        flow: "pub flow k() -> F64 at sample { 0.0 }",
        spellings: &["F64"],
        absent: &[],
        order: &[],
    },
    Shape {
        name: "no input: -> P { l: F64, r: U32 }",
        decls: "pub struct P { l: F64, r: U32 }",
        flow: "pub flow k() -> P at sample { P { l: 0.0, r: 0 } }",
        spellings: &["F64", "U32"],
        absent: &[],
        order: &["F64", "U32"],
    },
    // A `block` and an `init` input between the `sample` inputs are not counted: the `sample` inputs are `F32, F64`, and the
    // note shows them, not the types of the `block` input (`U16`) and of the `init` input (`I8`).
    Shape {
        name: "block and init inputs between: F32, [U16 block], F64, [I8 init] -> P { l: F32, r: U32 }",
        decls: "pub struct P { l: F32, r: U32 }",
        flow: "pub flow k(a: F32 at sample, g: U16 at block, b: F64 at sample, t: I8 at init) -> P at sample { P { l: a, r: 0 } }",
        spellings: &["F32", "F64", "U32"],
        absent: &["U16", "I8"],
        order: &["F32", "F64"],
    },
    // The same where the `sample` inputs agree with the fields only when the other inputs are counted (a `block` input of
    // the type of the second field): the pair does not exist, because the `block` input is not an input of the pair.
    Shape {
        name: "block input of the type of the field: F32 + [F64 block] -> P { l: F32, r: F64 }",
        decls: "pub struct P { l: F32, r: F64 }",
        flow: "pub flow k(a: F32 at sample, g: F64 at block) -> P at sample { P { l: a, r: g } }",
        spellings: &["F32", "F64"],
        absent: &[],
        order: &[],
    },
];

/// The program of a shape: the call of `k.process_inplace` in a body, the line of the call, and the program.
fn body_call(s: &Shape) -> (String, usize) {
    let src = format!(
        "{decls}\n{flow}\npub fn f(inout st: k.State, inout xs: [Span[F32]; 2]) {{\n  k.process_inplace(inout st, inout xs)\n}}\n",
        decls = s.decls,
        flow = s.flow
    );
    (src, 4)
}

/// The program of a shape with the `use` of `process_inplace` in the first line.
fn use_line(s: &Shape) -> (String, usize) {
    let src = format!("use main.k.process_inplace\n{decls}\n{flow}\n", decls = s.decls, flow = s.flow);
    (src, 1)
}

fn check_note(shape: &Shape, form: &str, diag: &Value, line: usize) -> Vec<String> {
    let at = format!("{} ({form})", shape.name);
    let mut bad = Vec::new();
    if code_of(diag) != "E0302"
        || span_of(&diag["span"]).line as usize != line
        || !str_of(diag, "message").contains("process_inplace")
    {
        bad.push(format!("{at}: not the E0302 of `process_inplace` at line {line}: {diag}"));
        return bad;
    }
    let text = notes_text(diag);
    if text.is_empty() {
        bad.push(format!("{at}: no note tells how the flow differs"));
        return bad;
    }
    for w in shape.spellings {
        if !text.contains(w) {
            bad.push(format!("{at}: the note does not show `{w}`: {text}"));
        }
    }
    for w in shape.absent {
        if text.contains(w) {
            bad.push(format!("{at}: the note shows `{w}`, a type that is no `sample` input or output: {text}"));
        }
    }
    let mut from = 0;
    for w in shape.order {
        match text[from..].find(w) {
            Some(i) => from += i + w.len(),
            None => bad.push(format!("{at}: `{w}` is not after the types before it in the note: {text}")),
        }
    }
    bad
}

fn assert_none(bad: Vec<String>, shapes: usize) {
    assert!(bad.is_empty(), "{} problems in {shapes} shapes:\n{}", bad.len(), bad.join("\n"));
}

/// R-480: the body path call of a `process_inplace` that the flow does not have gets a note of the types.
#[test]
fn a_body_call_of_an_absent_process_inplace_notes_the_types_of_the_inputs_and_the_outputs() {
    let mut bad = Vec::new();
    for s in ABSENT {
        let (src, line) = body_call(s);
        bad.extend(judge_program(s, "the call in a body", &src, line));
    }
    assert_none(bad, ABSENT.len());
}

/// R-480: the `use` of a `process_inplace` that the flow does not have (the E0302 of the type stage) gets the same note.
#[test]
fn the_use_of_an_absent_process_inplace_notes_the_types_of_the_inputs_and_the_outputs() {
    let mut bad = Vec::new();
    for s in ABSENT {
        let (src, line) = use_line(s);
        bad.extend(judge_program(s, "the `use`", &src, line));
    }
    assert_none(bad, ABSENT.len());
}

/// R-480, §18.1: after the failed `use` the name is a failed name, and its uses report nothing more: the note is on the `use`
/// alone and the calls and the types that follow have no E0302 of their own.
#[test]
fn the_uses_after_a_failed_use_of_process_inplace_say_nothing() {
    let s = &ABSENT[0];
    let src = format!(
        "use main.k.process_inplace\n{decls}\n{flow}\npub fn f(inout st: k.State, inout xs: [Span[F32]; 2]) {{\n  process_inplace(inout st, inout xs)\n}}\npub fn g(inout st: k.State, inout xs: [Span[F32]; 2]) {{\n  process_inplace(inout st, inout xs)\n}}\n",
        decls = s.decls,
        flow = s.flow
    );
    assert_none(judge_program(s, "the `use` followed by calls", &src, 1), 1);
}

/// S-1087, S-708: the body call and the `use` of the same flow in one program are two names, each its own E0302 with the note.
#[test]
fn the_body_call_and_the_use_of_one_flow_each_have_the_note() {
    let s = &ABSENT[1];
    let src = format!(
        "use main.k.process_inplace\n{decls}\n{flow}\npub fn f(inout st: k.State, inout xs: [Span[F32]; 2]) {{\n  k.process_inplace(inout st, inout xs)\n}}\n",
        decls = s.decls,
        flow = s.flow
    );
    let diags = check_main(&src);
    assert!(codes_of(&diags).iter().all(|c| c == "E0302") && !diags.is_empty(), "{diags:?}");
    // The `use` has the note; the call in the body is a path of its own and, if it is reported, has it too.
    let use_diag = diags.iter().find(|d| span_of(&d["span"]).line == 1).expect("the E0302 of the `use`");
    let mut bad = check_note(s, "the `use` with a call", use_diag, 1);
    for d in diags.iter().filter(|d| span_of(&d["span"]).line != 1) {
        bad.extend(check_note(s, "the call beside a `use`", d, span_of(&d["span"]).line as usize));
    }
    assert_none(bad, 1);
}

/// S-708, §11.6: a path in the position of a type is the E0308 of a function that is no type, with the process_inplace
/// there or not; it is no E0302, so it has no note of the types.
#[test]
fn a_process_inplace_path_in_the_position_of_a_type_is_an_e0308_and_no_e0302() {
    for s in [&ABSENT[0], &ABSENT[5]] {
        let src = format!("{decls}\n{flow}\npub fn f(x: k.process_inplace) {{\n}}\n", decls = s.decls, flow = s.flow);
        let diags = check_main(&src);
        assert_eq!(codes_of(&diags), ["E0308"], "{}: {diags:?}", s.name);
    }
}

/// A flow that has `process_inplace` is used with no diagnostic (the controls of the cases above).
#[test]
fn a_flow_that_has_process_inplace_gives_no_diagnostic_and_no_note() {
    let src = r#"pub struct Stereo { l: F32, r: F32 }
pub struct Q { v: [F32; 2] }
pub flow same(l: F32 at sample, r: F32 at sample) -> Stereo at sample { Stereo { l: l, r: r } }
pub flow planar(x: [F32; 2] at sample) -> Q at sample { Q { v: [x[1], x[0]] } }
pub flow planar_array(x: [F32; 2] at sample) -> [F32; 2] at sample { [x[1], x[0]] }
pub flow one(x: F32 at sample) -> F32 at sample { x }
pub flow with_block(a: F32 at sample, g: U16 at block, b: F32 at sample) -> Stereo at sample { Stereo { l: a, r: b } }
pub fn f_same(inout st: same.State, inout a: Span[F32], inout b: Span[F32]) {
  same.process_inplace(inout st, inout same.Out { l: a, r: b })
}
pub fn f_planar(inout st: planar.State, inout a: Span[F32], inout b: Span[F32]) {
  planar.process_inplace(inout st, inout planar.Out { v: [a, b] })
}
pub fn f_planar_array(inout st: planar_array.State, inout a: Span[F32], inout b: Span[F32]) {
  planar_array.process_inplace(inout st, inout [a, b])
}
pub fn f_one(inout st: one.State, inout a: Span[F32]) {
  one.process_inplace(inout st, inout a)
}
"#;
    let diags = check_main(src);
    assert!(diags.is_empty(), "{diags:?}");
    // The `use` of a name that is there is no error either.
    let uses = "use main.one.process_inplace\npub flow one(x: F32 at sample) -> F32 at sample { x }\n";
    let diags = check_main(uses);
    assert!(diags.is_empty(), "{diags:?}");
}

/// An item that the namespace of the flow has no name for is an E0302 of its own, with no note of the types of the flow: the
/// note is of `process_inplace`, the one name that the flow may have or not.
#[test]
fn a_name_that_is_no_item_of_the_flow_is_an_e0302_without_the_types() {
    let flow = "pub flow k(a: U8 at sample, b: F64 at sample) -> [I32; 2] at sample { [0, 0] }";
    let body =
        format!("{flow}\npub fn f(inout st: k.State, inout xs: [Span[F32]; 2]) {{\n  k.nope(inout st, inout xs)\n}}\n");
    let uses = format!("use main.k.nope\n{flow}\n");
    for (what, src) in [("the call", body), ("the use", uses)] {
        let diag = only_e0302(&src);
        assert!(str_of(&diag, "message").contains("nope"), "{what}: {diag}");
        let text = notes_text(&diag);
        for w in ["U8", "F64", "I32"] {
            assert!(!text.contains(w), "{what}: a note shows `{w}` of the flow: {text}");
        }
    }
}

/// §18.1, S-1087, R-471: a flow whose output is not a type of the boundary (an E0810) or has a clock that does not read has an
/// error of its own, and the E0302 of `process_inplace` is not reported (the file has that or those errors only).
#[test]
fn a_flow_whose_heading_does_not_read_has_no_e0302_of_process_inplace_and_no_note() {
    let call = |flow: &str| {
        format!(
            "{flow}\npub fn f(inout st: k.State, inout xs: [Span[F32]; 2]) {{\n  k.process_inplace(inout st, inout xs)\n}}\n"
        )
    };
    let used = |flow: &str| format!("use main.k.process_inplace\n{flow}\n");
    for (what, flow) in [
        (
            "a nested array for the output",
            "pub flow k(x: F32 at sample) -> [[F32; 2]; 2] at sample { [[x, x], [x, x]] }",
        ),
        ("a clock that is not read", "pub flow k(x: F32 at nonsense) -> F32 at sample { x }"),
    ] {
        for (form, src) in [("call", call(flow)), ("use", used(flow))] {
            let diags = check_main(&src);
            assert!(!diags.is_empty(), "{what} ({form}): the flow has an error of its own");
            for d in &diags {
                let process_inplace = str_of(d, "message").contains("process_inplace");
                assert!(
                    !(code_of(d) == "E0302" && process_inplace),
                    "{what} ({form}): an E0302 of process_inplace: {d}"
                );
            }
        }
    }
}

// ---- the words of the E0200 of the C names (S-30, R-15, §14.2, §18.1) -------------------------------------

/// The build of a target stops with an E0200 at a flow whose names in the C are another's (until W10-03). The words name the
/// signal that the user wrote (`int`), not alone the name that it has in the C (`int_`, the name of the signal turned into a
/// C name when the C word `int` is one that the C reserves: the user does not write that name).
#[test]
fn the_e0200_of_a_name_in_the_c_names_the_signal_the_user_wrote() {
    let d = Dir::bare("inplace_absent_e0200");
    d.write(
        "onsa.toml",
        "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[export]\nprefix = \"dm_\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\npanic = \"trap\"\nprovides = []\n",
    );
    d.write("main.onsa", "@export\npub flow c_int(int: F32 at sample, int_: F32 at sample) -> F32 at sample { 0.0 }\n");
    let out = run(d.root(), &["build", "--target", "host"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(text.contains("E0200"), "{text}");
    assert!(text.contains("`int`"), "the E0200 does not name the signal `int` that the user wrote: {text}");
}
