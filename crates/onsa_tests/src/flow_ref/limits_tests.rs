//! The tests of the limits of the evaluator (W7-01 U4 fix, `Limits`): the stack it keeps back, and the places a value
//! made by `[e; N]` or read from a row of a constant holds. The limits are the evaluator's own (the spec has none), and
//! a test gives smaller ones, so that nothing here nests deep or builds much: with the guard off, the deepest input
//! below (a chain of 40 constants) uses about 3 MB of the 64 MiB of the thread.

use super::expr::{Limits, Stop};
use super::expr_tests::{consts_with, flow_with, i32v, is};
use super::scalar::Fault;
use super::value::Value;

/// The stack left to the thread now less `margin`: what a test keeps back, so that a few levels of nesting pass and
/// a few hundred stop.
fn keep_back(margin: usize) -> Limits {
    let left = onsa_diag::stack::remaining().expect("a thread of `onsa_diag::stack`");
    Limits { reserve: left - margin, most: super::expr::LIMITS.most }
}

fn unavailable<T: std::fmt::Debug>(r: &Result<T, Stop>) -> bool {
    matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. }))
}

/// `x + (x + (x + ... x))` with `n` levels of operators and parentheses (each level is one `eval` of the operator and
/// one of the parentheses).
fn nest(n: usize) -> String {
    format!("flow f(x: I32 at sample) -> I32 at sample {{ {}x{} }}", "x + (".repeat(n), ")".repeat(n))
}

#[test]
fn the_evaluator_stops_with_unavailable_when_the_stack_left_is_under_what_it_keeps_back() {
    let run = |src: &str, limits: fn() -> Limits| flow_with(src, "f", vec![("x", i32v(1))], limits);
    // The reserve is more than the whole stack: not even `x` is evaluated.
    let r = run(&nest(0), || Limits { reserve: usize::MAX, most: 1 });
    assert!(unavailable(&r), "{r:?}");
    // The reserve is 100 K under what is left: 5 levels (about 20 K) pass and 120 (about 400 K) stop, before they use
    // the 64 MiB of the thread, which they never come near.
    let r = run(&nest(5), || keep_back(100 << 10));
    assert!(is(&r, &i32v(6)), "{r:?}");
    let r = run(&nest(120), || keep_back(100 << 10));
    assert!(unavailable(&r), "{r:?}");
    // With the reserve of the evaluator the same 120 levels have their value: the limit is the thread's, not the nest's.
    assert!(is(&run(&nest(120), || super::expr::LIMITS), &i32v(121)));
}

#[test]
fn a_chain_of_constants_is_stopped_by_the_stack_it_uses_and_not_by_its_length_alone() {
    // 40 constants, each an initializer 20 levels deep that reads the one before: no constant is long, and the chain is
    // under the 256 of `CHAIN`, but the frames of them all are on the stack at once (about 40 * 20 * 2 K).
    let level = |prev: &str| format!("{}{prev}{}", "1 + (".repeat(20), ")".repeat(20));
    let mut src = format!("const C0: I32 = {}\n", level("1"));
    for k in 1..=40 {
        src += &format!("const C{k}: I32 = {}\n", level(&format!("C{}", k - 1)));
    }
    let names: &'static [&'static str] = &["C1", "C40"];
    let got = consts_with(&src, names, || keep_back(400 << 10));
    assert!(is(&got[0], &i32v(41)), "C1: {:?}", got[0]);
    assert!(unavailable(&got[1]), "C40: {:?}", got[1]);
    // With the reserve of the evaluator the chain has its value: each of the 41 constants adds 20 ones.
    let got = consts_with(&src, names, || super::expr::LIMITS);
    assert!(is(&got[1], &i32v(20 * 41 + 1)), "C40: {:?}", got[1]);
}

const MOST: fn() -> Limits = || Limits { reserve: 0, most: 100 };

fn array(n: &str) -> String {
    format!("struct P {{ x: I32, y: I32 }}\nflow f(a: I32 at sample) -> I32 at sample {{ let xs = {n}\n 7 }}")
}

#[test]
fn what_an_array_holds_in_all_is_bounded_not_each_level() {
    let run = |e: &str| flow_with(&array(e), "f", vec![("a", i32v(1))], MOST);
    // 100 places is the limit given: the places of the elements are counted, not the length of each level.
    for ok in
        ["[a; 100]", "[[a; 10]; 10]", "[[a; 4]; 25]", "[[[a; 4]; 5]; 5]", "[[a; 0]; 100]", "[P { x: a, y: a }; 50]"]
    {
        let r = run(ok);
        assert!(is(&r, &i32v(7)), "{ok}: {r:?}");
    }
    // One place more, in each shape: a level at 101, 11 rows of 10, 125 in three levels, 101 empty arrays (an array
    // that holds nothing is still one place), and 51 structs of two fields.
    for over in ["[a; 101]", "[[a; 10]; 11]", "[[[a; 5]; 5]; 5]", "[[a; 0]; 101]", "[P { x: a, y: a }; 51]"] {
        let r = run(over);
        assert!(unavailable(&r), "{over}: {r:?}");
    }
    // The nesting that the old limit (each level 2^20) let through is stopped without being built: the places are
    // counted from the value of the element, whatever its length (here 2^20 * 2^20, which would not fit).
    let big = "[[a; 1048576]; 1048576]";
    let r = flow_with(&array(big), "f", vec![("a", i32v(1))], || super::expr::LIMITS);
    assert!(unavailable(&r), "{big}: {r:?}");
}

#[test]
fn a_constant_read_from_the_table_is_held_to_the_same_limit() {
    // A constant by its name is read from its row of the checker when the row is not over the limit given (100 places),
    // else its initializer is evaluated here: a `[e; N]` over the limit is `Unavailable` there as in a flow, and a
    // literal is evaluated whatever its size (the limit is on what `[e; N]` makes and on the rows, not on every value).
    let defs = "
const OK: [[U8; 10]; 10] = [[1; 10]; 10]
const OVER: [[U8; 10]; 11] = [[1; 10]; 11]
const TUP: ([U8; 60], [U8; 41]) = ([1; 60], [2; 41])
const LIT: [[U8; 6]; 20] = [[1, 2, 3, 4, 5, 6]; 20]
const EMPTY: [[U8; 0]; 101] = [[1; 0]; 101]
";
    let body = |name: &str, e: &str| format!("flow {name}(a: I32 at sample) -> U8 at sample {{ {e} }}\n");
    let flows = [
        ("ok", "OK[9][9]"),
        ("over", "OVER[0][0]"),
        ("tup", "TUP.0[0]"),
        ("lit", "LIT[0][0]"),
        ("empty", "let e = EMPTY\n 1"),
    ];
    let src = flows.iter().fold(defs.to_string(), |s, (n, e)| s + &body(n, e));
    let run = |name: &'static str| flow_with(&src, name, vec![("a", i32v(0))], MOST);
    let one = Value::int(super::value::IntKind::U8, 1);
    // The row at the limit (100) is read.
    assert!(is(&run("ok"), &one), "{:?}", run("ok"));
    // 110 places in the row and in the initializer; 120 in both; 101 arrays that hold nothing (one place each) in both.
    for name in ["over", "lit", "empty"] {
        let r = run(name);
        assert!(unavailable(&r), "{name}: {r:?}");
    }
    // The row of the tuple is 101 places, over: its initializer is a tuple literal of two `[e; N]` that are each under
    // the limit, so the constant has its value.
    assert!(is(&run("tup"), &one), "{:?}", run("tup"));
}
