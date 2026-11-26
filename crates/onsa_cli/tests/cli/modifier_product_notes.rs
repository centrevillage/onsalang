//! The note of the E0808 of the product of the N of the modifiers (W7-16 U5b1/t; spec §11.9, §18.1; S-1089), which the case files in `tests/spec/flow_clock/` cannot pin (the runner of the
//! cases does not compare notes): "超えると E0808 で、… 位置は超えた修飾子の名前（flow をまたいで超えるときは、包む側の flow の連鎖の修飾子）で、note に経路（後の上限では宣言の N も）を示す（中の flow が単独で超えるときは、
//! 中の flow にだけ出す）".
//!
//! The note shows the path from the body that is the outermost to the instance, so it names the modifiers on it (their N) and, when the path goes through other flows, the flows. The test checks
//! that these are in the notes and not the text, which the spec does not fix. The error is one, at the name of the modifier that passes 2^24 (the line and the column are checked on the first
//! form), and a flow that is past the limit by itself has the error in itself only.
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::test_support::{Dir, code_of, diagnostics, doc_of, notes_of, run, span_of, str_of};
use serde_json::Value;

const LEAF: &str = "flow leaf(x: F32 at sample) -> F32 at sample {\n  x * 0.5 + prev~(x) * 0.5\n}\n\n";

/// The diagnostics of `check --json` of a package whose `main.onsa` is `text` (exit code 1: an error).
fn errors_of(tag: &str, text: &str) -> Vec<Value> {
    let d = Dir::pkg(tag);
    d.write("main.onsa", text);
    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

/// The text of all the notes of a diagnostic, in one string.
fn note_text(d: &Value) -> String {
    notes_of(d).iter().map(|n| str_of(n, "message").to_string()).collect::<Vec<_>>().join("\n")
}

/// One chain of two modifiers of 2^13: one E0808 at the second modifier (line 6, the column of the name after the `.`), with a note that shows the N of the modifiers.
#[test]
fn a_chain_past_2_to_the_24_has_one_e0808_at_the_modifier_that_passes_and_a_note_with_the_path() {
    let text = format!(
        "{LEAF}pub flow f(p: F32 at block) -> F32 at sample {{\n  leaf~(p).down~(8192).down~(8192) at sample\n}}\n"
    );
    let ds = errors_of("product_note_one_chain", &text);
    assert_eq!(ds.len(), 1, "one error: {ds:?}");
    assert_eq!(code_of(&ds[0]), "E0808", "{}", ds[0]);
    let s = span_of(&ds[0]["span"]);
    assert_eq!((s.file.as_str(), s.line, s.col), ("main.onsa", 6, 24), "at the name of the second modifier: {}", ds[0]);
    let notes = note_text(&ds[0]);
    assert!(notes.contains("8192"), "the note shows the N of the modifiers on the path: {notes:?}");
}

/// The product across two flows: `mid` has 2^12 on its own path and is run with 2^13, so the error is in the flow that runs `mid` (its modifier), once, and the note names `mid` and the N of
/// both modifiers.
#[test]
fn a_product_across_two_flows_is_at_the_outer_modifier_and_the_note_names_the_inner_flow_and_both_n() {
    let text = format!(
        "{LEAF}flow mid(p: F32 at block) -> F32 at sample {{\n  leaf~(p).down~(4096) at sample\n}}\n\npub flow outer(p: F32 at block) -> F32 at sample {{\n  mid~(p).down~(8192) at sample\n}}\n"
    );
    let ds = errors_of("product_note_two_flows", &text);
    assert_eq!(ds.len(), 1, "one error, in the outer flow only: {ds:?}");
    assert_eq!(code_of(&ds[0]), "E0808", "{}", ds[0]);
    let s = span_of(&ds[0]["span"]);
    assert_eq!((s.line, s.col), (10, 11), "at the name of the modifier of the outer flow: {}", ds[0]);
    let notes = note_text(&ds[0]);
    for needle in ["mid", "4096", "8192"] {
        assert!(notes.contains(needle), "the note of the path has `{needle}`: {notes:?}");
    }
}

/// Three flows: each level has 2^8 and the outer modifier of 2 passes 2^24, so the note names the flows of the path.
#[test]
fn the_note_of_a_product_across_three_flows_names_every_flow_of_the_path() {
    let text = format!(
        "{LEAF}flow deep_a(p: F32 at block) -> F32 at sample {{\n  leaf~(p).down~(256) at sample\n}}\n\nflow deep_b(p: F32 at block) -> F32 at sample {{\n  deep_a~(p).down~(256) at sample\n}}\n\nflow deep_c(p: F32 at block) -> F32 at sample {{\n  deep_b~(p).down~(256) at sample\n}}\n\npub flow top(p: F32 at block) -> F32 at sample {{\n  deep_c~(p).down~(2) at sample\n}}\n"
    );
    let ds = errors_of("product_note_three_flows", &text);
    assert_eq!(ds.len(), 1, "one error, in the outer flow only: {ds:?}");
    assert_eq!(code_of(&ds[0]), "E0808", "{}", ds[0]);
    let s = span_of(&ds[0]["span"]);
    assert_eq!((s.line, s.col), (18, 14), "at the name of the modifier of `top`: {}", ds[0]);
    let notes = note_text(&ds[0]);
    for needle in ["deep_c", "deep_b", "deep_a"] {
        assert!(notes.contains(needle), "the note of the path has `{needle}`: {notes:?}");
    }
}

/// A flow that is past the limit by itself has the error in itself only: the flow that runs it, with a modifier or none, reports nothing.
#[test]
fn a_flow_past_the_limit_by_itself_has_the_error_and_its_callers_have_none() {
    let text = format!(
        "{LEAF}flow past(p: F32 at block) -> F32 at sample {{\n  leaf~(p).down~(8192).down~(8192) at sample\n}}\n\npub flow user(p: F32 at block) -> F32 at sample {{\n  past~(p).down~(2) at sample\n}}\n\npub flow plain(p: F32 at block) -> F32 at sample {{\n  past~(p)\n}}\n"
    );
    let ds = errors_of("product_note_alone_past", &text);
    assert_eq!(ds.len(), 1, "one error, in `past`: {ds:?}");
    assert_eq!(code_of(&ds[0]), "E0808", "{}", ds[0]);
    let s = span_of(&ds[0]["span"]);
    assert_eq!(s.line, 6, "in the flow that is past the limit by itself: {}", ds[0]);
}
