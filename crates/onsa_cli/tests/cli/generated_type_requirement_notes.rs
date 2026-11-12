//! S-908 (§11.6, decided 2026-11-12, W5-13 U5b/t, D4): a type a flow generates (`g.Params`, `g.Config`)
//! implements no trait, and the E0416 of a trait asked of it carries a note that says so ("use its
//! fields, or write a method of it in an `impl`"). The decision does not limit the place: the type is
//! passed to a type parameter that has a trait as a bound
//! - as a value use (`mk(x)` for a `fn mk[T: Eq](x: T)`),
//! - written in a type: a signature, a field, the right side of an alias, an annotation,
//! - and in a constant expression, `N::[g.Params].K` in a body and in the length of an array type.
//!
//! `decided_notes.rs` pins the first, from the case file `negative/generated_type_traits.onsa`; this file
//! asks the others, with the input in memory (`check_input_out`, nothing is written, `rules/common.md`
//! 3.7). Each test checks the words that tell what the note shows, as `decided_notes.rs` does, not its
//! text, which the spec does not fix. The note is a note of the E0416, besides the notes that point at a
//! place (`the parameter `T` of `N` is declared here`).
//!
//! The negative side: a type of the user that has no derive (the same bound, the same places) has no such
//! note, and `g.Params` meets a bound it does have (the kind `Copy` of its fields: `Params` is Copy, §11.6).

use crate::test_support::sweep::check_input_out;
use crate::test_support::{code_of, diagnostics, doc_of, notes_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

/// A flow with a `block` input and an `init` input, so that it has both `g.Params` and `g.Config` (§11.6).
const FLOW: &str = "pub flow g(
  x: F32 at sample,
  @param(min: 0.0, max: 2.0, default: 1.0)
  level: F32 at block,
  n: I32 at init,
) -> F32 at sample {
  x * level + F32.round_from(100 / n)
}

pub struct Plain {
  v: F32,
}

";

const PLACES: [&str; 7] = ["signature", "field", "alias", "annotation", "body const", "type const", "value use"];

/// The program that passes `ty` to a parameter with the bound `bound`, in the `place` of `PLACES`.
fn program(bound: &str, ty: &str, place: &str) -> String {
    let decls = format!(
        "pub struct N[T: {bound}] {{\n  a: T,\n}}\n\nimpl[T: {bound}] N[T] {{\n  pub const K: U32 = 1\n}}\n\n\
         fn mk[T: {bound}](x: T) -> U32 {{\n  0\n}}\n\n"
    );
    let tail = match place {
        "signature" => format!("pub fn f(x: N[{ty}]) -> U32 {{\n  0\n}}\n"),
        "field" => format!("pub struct M {{\n  n: N[{ty}],\n}}\n"),
        "alias" => format!("pub type Al = N[{ty}]\n"),
        "annotation" => format!("pub fn f() -> U32 {{\n  let _: Option[N[{ty}]] = None\n  0\n}}\n"),
        "body const" => format!("pub fn f() -> U32 {{\n  N::[{ty}].K\n}}\n"),
        "type const" => format!("pub fn f(x: [F32; N::[{ty}].K]) -> U32 {{\n  0\n}}\n"),
        "value use" => format!("pub fn f(x: {ty}) -> U32 {{\n  mk(x)\n}}\n"),
        other => panic!("no place {other}"),
    };
    format!("{FLOW}{decls}{tail}")
}

/// The diagnostics of the program (the document `onsa check --json` prints).
fn diagnostics_of(text: &str) -> Vec<Value> {
    let out = check_input_out(&PackageInput::single_file("main.onsa", text));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

fn notes(d: &Value) -> Vec<String> {
    notes_of(d).iter().map(|n| str_of(n, "message").to_string()).collect()
}

/// The note of S-908: what it shows, in words (a type a flow generates, no trait, its fields, a method).
fn says_no_trait(d: &Value) -> bool {
    notes(d).iter().any(|n| ["a flow generates", "no trait", "its fields", "method"].iter().all(|w| n.contains(w)))
}

/// The programs of `bound` x `ty` at the `places`, each with one E0416 and the note of S-908 given once.
fn check_notes(places: &[&str], expected: usize) {
    let mut failed = Vec::new();
    let mut checked = 0;
    for bound in ["Eq", "PartialEq", "Ord", "Hash", "Show"] {
        for ty in ["g.Params", "g.Config"] {
            for &place in places {
                let diags = diagnostics_of(&program(bound, ty, place));
                checked += 1;
                let e0416: Vec<&Value> = diags.iter().filter(|d| code_of(d) == "E0416").collect();
                if diags.len() != 1 || e0416.len() != 1 {
                    let codes: Vec<&str> = diags.iter().map(code_of).collect();
                    failed.push(format!("T: {bound} x {ty} at {place}: want one E0416, got {codes:?}"));
                } else if !says_no_trait(e0416[0]) {
                    failed.push(format!(
                        "T: {bound} x {ty} at {place}: no note that the type has no trait: {:?}",
                        notes(e0416[0])
                    ));
                } else if notes(e0416[0]).iter().filter(|n| n.contains("a flow generates")).count() != 1 {
                    failed.push(format!("T: {bound} x {ty} at {place}: the note is given more than once"));
                }
            }
        }
    }
    assert_eq!(checked, expected, "the number of programs");
    assert!(failed.is_empty(), "{} of {checked} programs:\n  {}", failed.len(), failed.join("\n  "));
}

#[test]
fn a_trait_asked_of_a_generated_type_in_a_value_use_notes_that_it_has_none() {
    // The place that has the note today (the case file `negative/generated_type_traits.onsa` is another form
    // of it: `need(p)`): five traits that a bound can ask, two generated types that are Copy (so that the
    // implicit `Dup` is met and the requirement reported is the trait).
    check_notes(&["value use"], 10);
}

#[test]
fn a_trait_asked_of_a_generated_type_in_a_type_notes_that_it_has_none() {
    // S-908 does not limit the place (W5-13, D4): written in a signature, a field, the right side of an alias, an
    // annotation, and in a constant expression (`N::[g.Params].K` in a body and in the length of an array type).
    // Today the E0416 of these places has the note that points at the declaration of the parameter alone.
    check_notes(&["signature", "field", "alias", "annotation", "body const", "type const"], 60);
}

#[test]
fn a_generated_type_meets_the_kind_it_has() {
    // `Params` and `Config` are Copy (§11.6): the bound `Copy` is met in every place, and no note is given.
    for ty in ["g.Params", "g.Config"] {
        for place in PLACES {
            let diags = diagnostics_of(&program("Copy", ty, place));
            let codes: Vec<&str> = diags.iter().map(code_of).collect();
            assert!(codes.is_empty(), "T: Copy x {ty} at {place}: {codes:?}");
        }
    }
}

#[test]
fn a_type_of_the_user_without_a_derive_has_no_note_of_a_generated_type() {
    // The note is about the types a flow generates alone: a struct written in the module with no derive fails
    // `T: Eq` in the same places with an E0416 that does not claim the type is generated.
    for place in PLACES {
        let diags = diagnostics_of(&program("Eq", "Plain", place));
        let e0416: Vec<&Value> = diags.iter().filter(|d| code_of(d) == "E0416").collect();
        assert_eq!(diags.len(), 1, "Plain at {place}: {:?}", diags.iter().map(code_of).collect::<Vec<_>>());
        assert_eq!(e0416.len(), 1, "Plain at {place}: the code of the diagnostic");
        assert!(
            !notes(e0416[0]).iter().any(|n| n.contains("a flow generates")),
            "Plain at {place}: {:?}",
            notes(e0416[0])
        );
    }
}
