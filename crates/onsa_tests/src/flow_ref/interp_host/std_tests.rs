//! The std functions through the wrappers of the interpreter host (W7-19 U1b): a `target` function, a method, a
//! member of a type and a generic function of a module, the case having a Core or not, the types of the user's
//! package, and the wrappers kept. The values are worked out by hand from the spec in the comment of each.

use super::wrap;
use super::*;
use crate::flow_ref::expr::{Eval, Frame, Stop};
use crate::flow_ref::expr_tests::{def_named, i32v, is, with_checked};
use crate::flow_ref::sema_view::View;
use onsa_core::IntKind;

const SRC: &str = "
use std.math.floor
use std.math.sum

struct P { x: I32 }

const D: F64 = 0.1
const NEG: F32 = -0.5
const X275: F32 = 2.75
const NX275: F32 = -2.75
const ONE: F32 = 1.0
const NZ: F32 = -0.0
const NAN: F32 = F32.NAN
const BIGF: F32 = 30000000000.0
const SOME_P: Option[P] = Some(P { x: 1 })

const FL: F32 = floor(2.75)
const FL_NEG: F32 = floor(NEG)
const FL_D: F64 = floor(2.5)
const FL_AGAIN: F32 = floor(1.5)
const ROUND_BIG: F32 = F32.round_from(16777217)
const ROUND_D: F32 = F32.round_from(D)
const TRUNC: I32 = I32.trunc_from(X275)
const TRUNC_NEG: I32 = I32.trunc_from(NX275)
const TRUNC_NAN: I32 = I32.trunc_from(NAN)
const TRUNC_BIG: I32 = I32.trunc_from(BIGF)
const SAT_BIG: I32 = I32.trunc_sat_from(BIGF)
const SAT_NAN: I32 = I32.trunc_sat_from(NAN)
const BITS_ONE: U32 = ONE.to_bits()
const BITS_NZ: U32 = NZ.to_bits()
const SUM_F: F32 = sum([1.0, 2.0, 3.0, 4.0])
const SUM_I: I32 = sum([1, 2, 3])
const OPT_P: P = SOME_P.unwrap()
const I8_MIN: I8 = -128
const I8_MAX: I8 = 127
const CHK_ADD: Option[I8] = I8_MIN.checked_add(1)
const CHK_ADD_OVER: Option[I8] = I8_MAX.checked_add(1)
const CHK_MUL: Option[I8] = I8_MIN.checked_mul(-1)
const CHK_DIV_ZERO: Option[I8] = I8_MAX.checked_div(0)
";

fn run(names: &[&'static str], core: bool, wrappers: &'static str) -> Vec<Eval> {
    let names = names.to_vec();
    with_checked(SRC, true, move |a| {
        let module = core.then(|| onsa_driver::lower_core(a).expect("the case lowers"));
        let wrappers_made = Wrappers::default();
        let mut host = InterpHost::new(module.as_ref(), &wrappers_made);
        let view = View::new(a);
        let out = names
            .iter()
            .map(|n| {
                let (body, init) = view.const_init(def_named(a, n)).expect("a const with its tables");
                let mut frame = Frame::new(body);
                frame.host = Some(&mut host as &mut dyn FnHost);
                frame.eval(init)
            })
            .collect();
        // The number of the wrappers made, as the test says it expects (`"1"`), when it says.
        assert!(wrappers.is_empty() || wrappers_made.len().to_string() == wrappers, "{} wrappers", wrappers_made.len());
        out
    })
}

fn one(name: &'static str) -> Eval {
    run(&[name], true, "").remove(0)
}

fn host_panic(r: &Eval) -> bool {
    matches!(r, Err(Stop { fault: Fault::Panic(PanicKind::Host), .. }))
}

#[test]
fn a_target_function_of_a_module_gives_its_value() {
    // §3.3 / std.math: `floor` is the greatest integer not above: 2.75 -> 2.0, -0.5 -> -1.0, and 2.5 of an F64 -> 2.0.
    assert!(is(&one("FL"), &Value::F32(2.0)));
    assert!(is(&one("FL_NEG"), &Value::F32(-1.0)));
    assert!(is(&one("FL_D"), &Value::F64(2.0)));
}

#[test]
fn the_members_of_a_type_and_the_methods_are_called() {
    // `round_from` rounds to the nearest, a tie to the even (§3.3): 16777217 is between 16777216 and 16777218, and the
    // even one of the two is 16777216. 0.1 of an F64 is the F32 that is nearest to it, as the literal 0.1 of an F32 is.
    assert!(is(&one("ROUND_BIG"), &Value::F32(16777216.0)));
    assert!(is(&one("ROUND_D"), &Value::F32(0.1)));
    // `trunc_from` cuts toward zero (§3.3): 2.75 -> 2, -2.75 -> -2; `trunc_sat_from` saturates and has 0 for a NaN.
    assert!(is(&one("TRUNC"), &i32v(2)));
    assert!(is(&one("TRUNC_NEG"), &i32v(-2)));
    assert!(is(&one("SAT_BIG"), &i32v(i32::MAX as i128)));
    assert!(is(&one("SAT_NAN"), &i32v(0)));
    // `to_bits` of 1.0 is 0x3f800000 and of -0.0 it is the sign bit alone, 0x80000000.
    assert!(is(&one("BITS_ONE"), &Value::int(IntKind::U32, 0x3f80_0000)));
    assert!(is(&one("BITS_NZ"), &Value::int(IntKind::U32, 0x8000_0000)));
}

#[test]
fn a_method_of_the_std_whose_body_calls_a_private_target_function_is_called_whole() {
    // §3.4: `checked_add` is the sum, or `None` when it does not fit: -128 + 1 = -127 and 127 + 1 = 128 (out of an I8);
    // `checked_mul`: -128 * -1 = 128 (out); `checked_div` by 0 is `None`. `Some` is variant 1 of `Option`, `None` 0.
    let some = |n| Value::Enum { tag: 1, fields: vec![Value::int(IntKind::I8, n)] };
    let none = Value::Enum { tag: 0, fields: vec![] };
    assert!(is(&one("CHK_ADD"), &some(-127)));
    for n in ["CHK_ADD_OVER", "CHK_MUL", "CHK_DIV_ZERO"] {
        assert!(is(&one(n), &none), "{n}");
    }
}

#[test]
fn a_conversion_that_panics_is_a_host_panic() {
    // §3.3: `trunc_from` panics on a NaN and on a value the type does not hold (3.0e10 is above I32::MAX).
    assert!(host_panic(&one("TRUNC_NAN")));
    assert!(host_panic(&one("TRUNC_BIG")));
}

#[test]
fn a_generic_function_of_a_module_is_called_in_each_of_its_instances() {
    // `sum` of [F32; 4] is 1 + 2 + 3 + 4 = 10, of [I32; 3] is 1 + 2 + 3 = 6: two wrappers, as the types differ.
    assert!(is(&one("SUM_F"), &Value::F32(10.0)));
    assert!(is(&one("SUM_I"), &i32v(6)));
}

#[test]
fn a_case_with_no_core_calls_the_std_functions_all_the_same() {
    // The functions of the user's package would be `Unavailable` (the other file); the std ones do not need the Core.
    let got = run(&["FL", "TRUNC", "SUM_F", "BITS_ONE"], false, "");
    assert!(is(&got[0], &Value::F32(2.0)) && is(&got[1], &i32v(2)) && is(&got[2], &Value::F32(10.0)));
    assert!(is(&got[3], &Value::int(IntKind::U32, 0x3f80_0000)));
}

#[test]
fn the_wrapper_of_a_text_is_made_once() {
    // `floor` of an F32 three times (the arguments differ, the types and the callee do not): one wrapper; of an F64:
    // another one. Two calls of the same function in other types are not the same wrapper.
    run(&["FL", "FL_NEG", "FL_AGAIN"], true, "1");
    run(&["FL", "FL_NEG", "FL_AGAIN", "FL_D"], true, "2");
}

#[test]
fn a_std_call_that_has_a_type_of_the_package_is_unavailable() {
    // `Option[P]` is written in a package that has no `P`: the wrapper does not analyze, and the call is not guessed.
    match one("OPT_P") {
        Err(Stop { fault: Fault::Unavailable(w), .. }) => assert!(w.contains("type of the package"), "{w}"),
        other => panic!("not unavailable: {other:?}"),
    }
}

#[test]
fn a_wrapper_the_checker_refuses_for_another_reason_is_told_from_one_of_a_user_type() {
    // The text of a wrapper that has `add_parts`, private to its module (E0303), is not a type of the user: its reason
    // is the other one. A wrapper that is right is built, and a type that is not found (E0302) is the first reason.
    let reason = |text: &str| match wrap::build(text) {
        Err(Fault::Unavailable(w)) => w,
        Err(other) => panic!("not unavailable: {other:?}"),
        Ok(_) => "built",
    };
    assert!(
        reason("use std.core.num.add_parts\nrt fn w(a0: I8, a1: I8) -> (Bool, I8) { add_parts(a0, a1) }")
            .contains("refuses")
    );
    assert!(reason("rt fn w(a0: P) -> P { a0 }").contains("type of the package"));
    assert_eq!(reason("rt fn w(a0: I8) -> I8 { a0 }"), "built");
}
