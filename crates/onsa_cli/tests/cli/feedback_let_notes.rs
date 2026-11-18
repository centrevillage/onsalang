//! W7-14 U3/i, S-395 (a): a `^name` above a `let` with no annotation reads a value whose type is not
//! known there (§11.2, §4.7), so an operation that needs the head of its type (`^s.l`, `^p.0`) is
//! E0420, and a note shows the `let` on which the type is written (no candidate: what to write is
//! the writer's). The runner of the cases does not compare notes, so these tests pin them: the
//! note is at the line of the `let` the `^` names, and an E0420 that no `^` above a `let` makes has
//! no such note. The words are not fixed (§18.1): the tests read the position and the code only.
//!
//! The inputs are programs in memory (`check_input_out`, nothing is written, `rules/common.md` 3.7).

use crate::test_support::sweep::{Texts, check_input_out, input_of};
use crate::test_support::{code_of, diagnostics, doc_of, fixes_of, notes_of, span_of};
use serde_json::Value;

/// The diagnostics of the package of the one file `main.onsa` of `src`.
fn check_main(src: &str) -> Vec<Value> {
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), src.to_string());
    let out = check_input_out(&input_of("demo", &texts));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}\n{src}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

/// The one E0420 of `src`, at `line`.
fn e0420_at(src: &str, line: u64) -> Value {
    let diags = check_main(src);
    let [d] = &diags[..] else { panic!("one diagnostic expected: {diags:?}\n{src}") };
    assert_eq!((code_of(d), span_of(&d["span"]).line), ("E0420", line), "{d}\n{src}");
    assert!(fixes_of(d).is_empty(), "no candidate: {d}");
    d.clone()
}

/// The lines of the notes of `d` that have a position.
fn note_lines(d: &Value) -> Vec<u64> {
    notes_of(d).iter().filter(|n| !n["span"].is_null()).map(|n| span_of(&n["span"]).line).collect()
}

const ST: &str = "pub struct St { l: F32, r: F32 }\n";

#[test]
fn a_field_of_a_feedback_above_a_let_with_no_annotation_notes_the_let() {
    let src = format!(
        "{ST}pub flow f(x: F32 at sample) -> F32 at sample {{\n  let a = prev~(^s.l)\n  let s = St {{ l: x + a, r: x }}\n  s.r\n}}\n"
    );
    assert_eq!(note_lines(&e0420_at(&src, 3)), vec![4]);
}

#[test]
fn the_note_names_the_let_the_feedback_reads_among_others() {
    // `^t` reads the third `let`, not the one between, which has no annotation either.
    let src = format!(
        "{ST}pub flow f(x: F32 at sample) -> F32 at sample {{\n  let a = prev~(^t.0)\n  let s = St {{ l: x, r: x }}\n  let t = (x + a, s.l)\n  t.1\n}}\n"
    );
    assert_eq!(note_lines(&e0420_at(&src, 3)), vec![5]);
}

#[test]
fn a_local_of_a_pattern_notes_its_let() {
    let src = format!(
        "{ST}pub flow f(x: F32 at sample) -> F32 at sample {{\n  let a = prev~(^s.l)\n  let (s, k) = (St {{ l: x + a, r: x }}, 1.0)\n  s.r * k\n}}\n"
    );
    assert_eq!(note_lines(&e0420_at(&src, 3)), vec![4]);
}

#[test]
fn a_let_with_its_type_written_is_read_above_it() {
    let src = format!(
        "{ST}pub flow f(x: F32 at sample) -> F32 at sample {{\n  let a = prev~(^s.l)\n  let s: St = St {{ l: x + a, r: x }}\n  s.r\n}}\n"
    );
    assert!(check_main(&src).is_empty(), "{src}");
}

#[test]
fn an_e0420_of_no_feedback_has_no_note_of_a_let() {
    // The type of `v` is not known where `.l` reads it, in a function and in a flow whose later `let`
    // has no annotation either: no `^` reads that `let`, and no note shows it.
    let decls = format!("{ST}pub fn mk[T: Default]() -> T {{ T.default() }}\n");
    let in_a_fn = format!("{decls}pub fn g() -> F32 {{\n  let v = mk()\n  v.l\n}}\n");
    assert!(note_lines(&e0420_at(&in_a_fn, 5)).is_empty());
    let in_a_flow = format!(
        "{decls}pub flow f(x: F32 at sample) -> F32 at sample {{\n  let v = mk()\n  let w = v.l\n  let s = St {{ l: x + w, r: x }}\n  s.r\n}}\n"
    );
    assert!(note_lines(&e0420_at(&in_a_flow, 5)).is_empty());
}
