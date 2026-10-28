//! `onsa check` ends, with an exit code, on a type that holds itself by value (W4-05 U1/b, F1 and
//! F2): the walks through the declarations a type holds (kinds, layouts, the drops of `rt`) stop
//! at the depth of a chain of every declaration and at a number of steps, not after a time
//! exponential in that depth. Such a type is an E0311 (spec §4.4) from W4-05 U2; the first test
//! asks only that the check ends, in time, by an exit code of §18.2.

mod test_support;

use test_support::{Dir, run_limited};

/// The least forms the break side found: two places that hold the type itself (a struct, a tuple,
/// an enum, two structs holding each other, a generic type), and a generic type that holds itself
/// with ever larger arguments, its parameter read first.
const CASES: &[(&str, &str)] = &[
    ("two_fields_moved", "pub struct X { a: X, b: X }\npub fn f(move x: X) {}\n"),
    ("two_fields_local", "pub struct X { a: X, b: X }\npub fn f() {\n  let x: Option[X] = None\n}\n"),
    ("tuple_moved", "pub struct S { w: (S, S) }\npub fn f(move x: S) {}\n"),
    ("enum_two", "pub enum T { N(T, T), Leaf }\npub fn f() {\n  let x = T.Leaf\n}\n"),
    ("mutual", "pub struct A { b: B, c: B }\npub struct B { a: A, d: A }\npub fn f(move x: A) {}\n"),
    ("alias_pair", "type A = (S, S)\npub struct S { a: A }\npub fn f() {\n  let x: Option[S] = None\n}\n"),
    ("generic_two", "pub struct W[T: ?Dup] { a: T, b: T }\npub struct S { w: W[S] }\npub fn f(move x: S) {}\n"),
    (
        "generic_grows",
        "pub struct R[T: ?Dup] { t: T, a: R[(T, T)] }\npub fn f(x: R[I32]) -> (R[I32], R[I32]) { (x, x) }\n",
    ),
    (
        "generic_grows_option",
        "pub struct R[T: ?Dup] { t: T, a: Option[R[(T, T)]] }\npub fn f(x: R[I32]) -> (R[I32], R[I32]) { (x, x) }\n",
    ),
    ("generic_grows_drop", "pub struct R[T: ?Dup] { t: T, a: R[(T, T)] }\npub fn f(move x: R[Str]) uses {Alloc} {}\n"),
];

#[test]
fn check_ends_on_a_type_that_holds_itself() {
    for (name, src) in CASES {
        let dir = Dir::pkg(name);
        dir.write("main.onsa", src);
        let out = run_limited(dir.root(), &["check", &dir.arg()], 5);
        assert!((0..=2).contains(&out.code), "{name}: exit {}\n{}", out.code, out.stderr);
    }
}

/// Long chains and a ring of aliases (W4-05 U2): each alias is lowered once, in the order of the
/// declarations, and one that is the error type is not lowered again at each use, so the check ends
/// in a short time with the one diagnostic of spec §4.4 and §18.1. A ring of 300 aliases is one E0311
/// (R-303: the time doubled with each alias); a chain of pairs `type Bk = (B(k-1), B(k-1))` passes
/// the size 4096 at one alias, its E0422, the rest using the error type (F3 of W4-05 U1/b: 40 did not
/// end in 20 seconds); a chain of 3000 `Option` passes the depth 256 at one alias (about 3 seconds in
/// 2296e83). The same forms are cases (`tests/spec/types/stop_*`); here they have a time limit.
#[test]
fn check_ends_on_long_chains_of_aliases() {
    let ring: String = (0..300).map(|i| format!("type C{i} = C{}\n", (i + 1) % 300)).collect();
    let chain = |n: usize, form: &dyn Fn(usize) -> String| {
        let mut src = String::from("type B0 = F32\n");
        (1..=n).for_each(|k| src.push_str(&format!("type B{k} = {}\n", form(k - 1))));
        src
    };
    let pair = |k: usize| format!("(B{k}, B{k})");
    let option = |k: usize| format!("Option[B{k}]");
    let cases = [
        ("ring_300", ring, "E0311"),
        ("pairs_40", chain(40, &pair), "E0422"),
        ("pairs_1000", chain(1000, &pair), "E0422"),
    ];
    for (name, src, code) in cases.into_iter().chain([("option_3000", chain(3000, &option), "E0422")]) {
        let dir = Dir::pkg(name);
        dir.write("main.onsa", &src);
        let out = run_limited(dir.root(), &["check", &dir.arg()], 5);
        let errors: Vec<&str> =
            out.stdout.lines().chain(out.stderr.lines()).filter(|l| l.contains(": error[")).collect();
        assert_eq!(out.code, 1, "{name}: exit {}\n{}{}", out.code, out.stdout, out.stderr);
        assert!(errors.len() == 1 && errors[0].contains(&format!("error[{code}]")), "{name}: {errors:?}");
    }
}
