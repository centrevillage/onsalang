//! The flow syntax outside a flow body around a name at which the names stage stops with no error (spec
//! §11.1, §18.1; S-675, S-692; W4-12 U3/i2): the check ends as a check does, with no internal error. The
//! names stage reports the E0821 of a form only flow bodies hold, after the parts of it that come first
//! in the text (the operand of `at`, the callee of a flow called as `f(x)`), and the types stage stops at
//! what the names stage did not, so a name it stops at silently in such a part must stop the types stage
//! there too. The sweep moved here from a script of the break side (`grid3.py`) that found an internal
//! error at the operand of `at`, which the gate had passed. The check runs in this process as the command
//! runs it, with no file written (`check_input`, X-16).
//!
//! The cases: five parts at which the names stage stops with no error (a name of a `use` that failed, a
//! method called on it, an associated function of an alias of a missing type, `unsafe`, `handle`) put in
//! seven forms (`at`, `par`, `if~`, `match~`, `f~(`, `f(x)` of a flow, an anonymous function with a
//! clock) in three places (an operand of `+`, a `let`, an argument). Which variant of a form and which
//! side of the `+` comes from a fixed seed, so that a failing case can be written again from it.
//!
//! The expected value is that one property only: what the check reports for each case is the business of
//! the case files (`tests/spec/negative/e0821_*`), and of §18.1 (S-675) for a name that stops silently.

mod test_support;

use test_support::sweep::*;

const PRE: &str = "use nope.thing
type Al = Nope
pub flow lp(x: F32 at sample) -> F32 at sample {
  x
}
pub fn f2(a: F32, b: F32) -> F32 {
  a
}
";

/// The parts at which the names stage stops with no error.
const HELD: [&str; 5] = ["thing", "thing.go(x)", "Al.new(x)", "(unsafe { x })", "(handle { x } with h)"];

/// The variants of each form, with `{H}` for the held part.
const FORMS: [&[&str]; 7] = [
    &["({H} at sample)", "(({H}) at block)", "({H}.m() at sample)", "({H} + 1.0 at sample)"],
    &["(par i in 0 ..< 2 { {H} })", "(par i in 0 ..< {H} { x })"],
    &["(if~ {H} { x } else { x })", "(if~ c { {H} } else { x })"],
    &["(match~ {H} { _ => x })", "(match~ c { _ => {H} })"],
    &["lp~({H})", "lp~(x, {H})", "prev~({H}, 0.0)"],
    &["lp({H})"],
    &[
        "(fn(y: F32 at sample) -> F32 { {H} })",
        "(fn(y: F32) -> F32 at block { {H} })",
        "(fn(y: F32) -> F32 { {H} at sample })",
    ],
];

/// The places, with `{A}` and `{B}` for the form and `x` (in either order) or `{F}` for the form.
const PLACES: [&str; 3] = ["{A} + {B}", "let v = {F}\n  v", "f2(x, {F})"];

#[test]
fn a_part_the_names_stage_stops_at_silently_is_no_internal_error_in_the_flow_syntax_outside_a_flow() {
    let mut rng = Rng::new(0x0821);
    let mut failed = Vec::new();
    let mut n = 0;
    for held in HELD {
        for form in FORMS {
            let form = rng.pick(form).replace("{H}", held);
            for place in PLACES {
                let (a, b) = if rng.chance(50) { (form.as_str(), "x") } else { ("x", form.as_str()) };
                let body = place.replace("{A}", a).replace("{B}", b).replace("{F}", &form);
                let text = format!("{PRE}pub fn u(x: F32, c: Bool) -> F32 {{\n  {body}\n}}\n");
                let texts = Texts::from([("main.onsa".to_string(), text.clone())]);
                let c = check_input(&input_of("held", &texts));
                n += 1;
                if !ended_well(&c) {
                    failed.push(format!("{text}=> exit {}: {}", c.code, c.stderr));
                }
            }
        }
    }
    assert_eq!(n, HELD.len() * FORMS.len() * PLACES.len(), "every case ran");
    assert!(failed.is_empty(), "{} of {n} cases ended badly:\n{}", failed.len(), failed.join("\n"));
}
