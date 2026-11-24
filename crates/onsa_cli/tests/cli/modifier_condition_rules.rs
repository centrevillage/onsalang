//! The conditions of `.when~(c)` and `.reset_if~(r)` that the case files in `tests/spec/` cannot pin (W7-10 U2a/t; spec §11.2, §11.10, §18.1; S-1130, S-1209): the note and the missing candidate of the E0801 of a `^name` in
//! the condition of a modifier inside the first argument of a delay, and the forms of that place that are no error.
//!
//! The texts are written from the spec; none is taken from the output of the compiler. The checks run in this process, with no file written.

use crate::test_support::sweep::check_input_out;
use crate::test_support::{code_of, diagnostics, doc_of, fixes_of, notes_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

const PRELUDE: &str = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  x * 0.5 + prev~(x) * 0.5\n}\n\n";

/// A flow whose `let a` holds `rhs` and whose later `let` is the name that `rhs` reads (`c` of `Bool` or `d` of `F32`, by the name `rhs` has).
fn flow(rhs: &str) -> String {
    let later = if rhs.contains("^d") { "let d = a + 1.0" } else { "let c = a > 0.0" };
    format!(
        "{PRELUDE}pub flow f(x: F32 at sample, r: Bool at sample) -> F32 at sample {{\n  let a = {rhs}\n  {later}\n  a\n}}\n"
    )
}

fn diags(text: &str) -> Vec<Value> {
    let out = check_input_out(&PackageInput::single_file("a.onsa", text));
    assert!(out.code == 0 || out.code == 1, "onsa check ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

fn notes(d: &Value) -> String {
    notes_of(d).iter().map(|n| str_of(n, "message")).collect::<Vec<_>>().join("\n")
}

/// §11.2: "修飾子の条件も同じで、受け手が利用者の flow でも組込みの遅延でも E0801 である（`prev~(lp~(x).when~(^c))`、`prev~(prev~(x).reset_if~(^c))`。候補は無く、note で修飾子の呼び出しを `let l = lp~(x).when~(c)` に出して
/// `prev~(^l)` と書く形を示す）". The names stage reports it, for a built-in delay as the receiver too (open since W7-10 U3b), and it is the one diagnostic.
#[test]
fn a_caret_in_the_condition_of_a_modifier_in_a_delay_is_the_e0801_with_a_note_that_shows_the_let_and_no_candidate() {
    let rhs = [
        "prev~(lp~(x).when~(^c))",
        "prev~(lp~(x).reset_if~(^c))",
        "prev~(lp~(x).when~(r).when~(^c))",
        "prev~(lp~(x).when~(^d > 0.5 || ^d < -0.5))",
        "prev~(prev~(x).when~(^c))",
        "prev~(prev~(x).reset_if~(^c))",
        "prev~(delay~(x, 2).reset_if~(^c))",
        "delay~(lp~(x).when~(^c), 4)",
        "vdelay~(lp~(x).when~(^c), 2.0, 4)",
        "prev~(prev~(lp~(x).when~(^c)))",
    ];
    for rhs in rhs {
        let ds = diags(&flow(rhs));
        assert_eq!(ds.len(), 1, "{rhs}: one diagnostic: {ds:?}");
        assert_eq!(code_of(&ds[0]), "E0801", "{rhs}: {}", ds[0]);
        assert!(fixes_of(&ds[0]).is_empty(), "{rhs}: no candidate: {}", ds[0]);
        let text = notes(&ds[0]);
        assert!(text.contains("prev~(^"), "{rhs}: a note shows the form `prev~(^l)`: {text:?}");
        assert!(text.contains("let"), "{rhs}: a note shows the `let` that holds the modifier: {text:?}");
    }
}

/// §11.2: "印の無い前方参照は E0801。参照が遅延の第 1 引数の中にあるときだけ、`^` の挿入を修正候補にする" and the rule that a modifier condition takes no `^` (so there is no `^` to insert in its place): the forward name in the condition of a
/// modifier in a delay has no candidate.
#[test]
fn a_forward_name_in_the_condition_of_a_modifier_in_a_delay_has_no_candidate() {
    let rhs = [
        "prev~(lp~(x).when~(c))",
        "prev~(lp~(x).reset_if~(c))",
        "prev~(lp~(x).when~(r).when~(c))",
        "prev~(prev~(x).when~(c))",
        "delay~(lp~(x).when~(c), 4)",
        "lp~(x).when~(c)",
    ];
    for rhs in rhs {
        let ds = diags(&flow(rhs));
        assert_eq!(ds.len(), 1, "{rhs}: one diagnostic: {ds:?}");
        assert_eq!(code_of(&ds[0]), "E0801", "{rhs}: {}", ds[0]);
        assert!(fixes_of(&ds[0]).is_empty(), "{rhs}: no candidate: {}", ds[0]);
    }
}

/// §11.2: the delay that is inside the condition takes its own `^` (the condition is not the first argument of the outer delay, the first argument of the inner one is): no diagnostic.
#[test]
fn an_inner_delay_in_the_condition_takes_its_own_caret() {
    let rhs = ["prev~(lp~(x).when~(prev~(^d) > 0.0))", "prev~(lp~(x).when~(r).when~(prev~(^d) > 0.0))"];
    for rhs in rhs {
        let ds = diags(&flow(rhs));
        assert!(ds.is_empty(), "{rhs}: no diagnostic, got {ds:?}");
    }
}
