//! `onsa check` ends, with an exit code, on a type that holds itself by value (W4-05 U1/b, F1 and
//! F2): the walks through the declarations a type holds (kinds, layouts, the drops of `rt`) stop
//! at the depth of a chain of every declaration and at a number of steps, not after a time
//! exponential in that depth. Such a type is an E0311 (spec §4.4) from W4-05 U2; until then the
//! check may accept it, so the test asks only that it ends, in time, by an exit code of §18.2.

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
