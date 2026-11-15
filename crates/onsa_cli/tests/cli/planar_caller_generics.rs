//! An array literal passed where a callee takes an array (§5.3, §4.5; W6-04 U4): whether it is a planar
//! literal of `Span` values is read from the callee's declaration and the literal, not from the caller. A
//! type parameter of the caller that nothing uses (`t[U: ?Escape]`, `t[V, U: ?Escape]`) changes nothing:
//! the caller has the codes of the diagnostics, line by line, of the same caller with no type parameter.
//! Before U4 the modes stage read the callee's type parameter `T` of `[T; N]` by the bounds of the
//! caller's type parameter of the same number, so they differed (`c[T: ?Escape, const N: U32](xs: [T; N])`
//! with `c([a, b])` of two `Span[F32]` in `t[U: ?Escape]`, and the second of `c[A, T: ?Escape, …]` in
//! `t[V, U: ?Escape]`).
//!
//! The codes themselves are not fixed here (S-1070 decides some of them), only that the callers with type
//! parameters have those of the one with none. Each file holds one callee and one caller for each argument
//! drawn, each its own unit. The inputs are programs in memory (`check_file`, nothing is written,
//! `rules/common.md` 3.7).

use crate::test_support::sweep::{check_file, ended_well};

/// The callees, each with the arguments written before the array.
const CALLEES: &[(&str, &str)] = &[
    ("pub fn c(xs: [Span[F32]; 2]) -> U32 { 0 }", ""),
    ("pub fn c[T: Copy, const N: U32](xs: [Span[T]; N]) -> U32 { N }", ""),
    ("pub fn c[T, const N: U32](xs: [T; N]) -> U32 { N }", ""),
    ("pub fn c[T: ?Escape, const N: U32](xs: [T; N]) -> U32 { N }", ""),
    ("pub fn c[T: Copy, const N: U32](xs: [T; N]) -> U32 { N }", ""),
    ("pub fn c[A, T: ?Escape, const N: U32](y: A, xs: [T; N]) -> U32 { N }", "true, "),
];

const ARGS: &[&str] = &["[a, b]", "([a, b])", "[a, a]"];

/// The lines and codes of the diagnostics of `callee` and its callers, one for each of `ARGS`, each with
/// the type parameters `generics`.
fn codes((callee, before): (&str, &str), generics: &str) -> Vec<(u64, String)> {
    let callers = ARGS
        .iter()
        .enumerate()
        .map(|(i, arg)| format!("pub fn t{i}{generics}(a: Span[F32], b: Span[F32]) -> U32 {{ c({before}{arg}) }}\n"));
    let src = format!("{callee}\n{}", callers.collect::<String>());
    let c = check_file("a.onsa", &src);
    assert!(ended_well(&c), "{src}{}", c.stderr);
    c.diags.iter().map(|d| (d.line, d.code.clone())).collect()
}

#[test]
fn a_type_parameter_of_the_caller_changes_no_code_of_a_planar_argument() {
    let mut found = 0;
    for &callee in CALLEES {
        let plain = codes(callee, "");
        for generics in ["[U: ?Escape]", "[V, U: ?Escape]"] {
            assert_eq!(plain, codes(callee, generics), "{}: without and with `{generics}`", callee.0);
        }
        found += plain.len();
    }
    assert!(found > 0, "no callee had a diagnostic: the inputs reach no check");
}
