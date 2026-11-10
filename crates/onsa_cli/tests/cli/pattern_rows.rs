//! The rows of the patterns that the case files cannot tell apart, as both give one code: W5-24 U4.
//!
//! - S-845 (§7): an arm whose guard form makes no candidate is the E0002 of the row of the
//!   alternatives (`float_pattern_choice`, `range_pattern_choice`, `at_binding_complex`) when the arm
//!   has a choice `|` (also on the right of an `@`), and else the E0002 of the row of the form found
//!   (`float_pattern`, `range_pattern`, `at_binding`), whatever the reason (here a comment the
//!   candidate would lose). The two are told apart by their messages: those of the forms say "compare
//!   in a guard", those of the alternatives say why no guard is written.
//! - S-656 (§8.1, §2.3): a name of `[…]` that does not start with an uppercase letter (`_0`, `__`) is
//!   an effect-row variable, so its E0320 names that kind, not a type parameter.
//!
//! The inputs are the table of the tests' side (W5-24 U4/t, `rows/expect.md`).

use crate::test_support::sweep::check_file;

/// The message of the one diagnostic of `text`, which has `code` and no candidate.
fn message(text: &str, code: &str) -> String {
    let c = check_file("main.onsa", text);
    assert_eq!(
        c.diags.len(),
        1,
        "one diagnostic for {text}: {:?}",
        c.diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let d = &c.diags[0];
    assert_eq!((d.code.as_str(), d.fixes.len()), (code, 0), "{text}: {}", d.message);
    d.message.clone()
}

/// A `match` over `subject: ty` with the arm `arm` (its lines) and a `_` arm.
fn arm(subject: &str, arm: &str) -> String {
    format!("pub fn f(x: {subject}) -> I32 {{\n  match x {{\n{arm}\n    _ => 0,\n  }}\n}}\n")
}

#[test]
fn an_arm_with_no_candidate_is_reported_by_the_row_of_its_choice_or_of_its_form() {
    // (subject, arm, whether the arm has a choice)
    let cases = [
        ("F32", "    -(1.5 // c\n    ) => 1,", false),
        ("F32", "    0.5 | // c\n    1.5 => 1,", true),
        ("I32", "    k @ (1 // c\n    ) => k,", false),
        ("I32", "    k @ (1 | // c\n      2) => k,", true),
        ("I32", "    1..<(3 + // c\n      1) => 1,", false),
        ("I32", "    1..<3 | // c\n    5..<7 => 1,", true),
        ("I32", "    1..<3 /* c */ => 1,", false),
    ];
    for (subject, written, choice) in cases {
        let text = arm(subject, written);
        let m = message(&text, "E0002");
        assert_eq!(m.contains("compare in a guard"), !choice, "{written}: {m}");
    }
}

#[test]
fn a_name_of_type_parameters_with_no_letter_is_an_effect_row_variable() {
    let cases = [
        "pub fn f[_0](x: I32) -> I32 {\n  x\n}\n",
        "pub fn f[__](x: I32) -> I32 {\n  x\n}\n",
        "pub fn f[_0](g: fn(I32) -> I32 uses {_0}, x: I32) -> I32 uses {_0} {\n  g.(x)\n}\n",
    ];
    for text in cases {
        let m = message(text, "E0320");
        assert!(m.contains("effect-row variable") && !m.contains("type parameter") && !m.contains("UpperCamel"), "{m}");
    }
}
