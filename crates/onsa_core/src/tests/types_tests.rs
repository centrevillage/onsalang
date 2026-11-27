//! The maker of the types of the instances (W8-14): the order of the ids is
//! that of a recursion through the fields, an instance that holds a type
//! lowering does not lower is the same E0200 at each use, whatever order
//! they come in, and a chain of declarations takes no stack of Rust.

use crate::ir::*;

use super::{core, core_err};

/// The names of the types of `src`, in the order of their ids.
fn type_names(src: &str) -> Vec<String> {
    core(src).types.iter().map(|t| t.name.clone()).collect()
}

/// The lines of the diagnostics of `src`, sorted, with their codes.
fn lines(src: &str) -> Vec<(usize, onsa_diag::Code)> {
    let mut l: Vec<_> =
        core_err(src).iter().map(|d| (src[..d.span.start as usize].matches('\n').count() + 1, d.code)).collect();
    l.sort();
    l
}

/// Depth first and in the order of the fields: a type made in a field is
/// filled before the next field, and an argument before the type it is of.
#[test]
fn the_ids_of_the_types_are_in_the_order_of_their_fields() {
    let src = "pub struct X {\n  k: U32,\n}\npub struct A {\n  x: X,\n}\npub struct B {\n  k: U32,\n}\n\
               pub struct P {\n  a: A,\n  b: B,\n}\npub fn f(p: P) -> U32 {\n  0\n}\n";
    assert_eq!(type_names(src), ["t.P", "t.A", "t.X", "t.B"]);
    // Two new instances in one field (`Option[Voice]`, `(Pair, Last)`): the
    // first is filled before the second is made (review/probe/order.onsa).
    let src = "pub struct Env {\n  a: F32,\n}\npub struct Voice {\n  env: Env,\n  g: F32,\n}\n\
               pub struct Outer {\n  v: Option[Voice],\n  w: (Pair, Last),\n}\npub struct Pair {\n  x: Inner,\n}\n\
               pub struct Inner {\n  k: U32,\n}\npub struct Last {\n  z: U32,\n}\npub fn f(o: Outer) -> U32 {\n  3\n}\n";
    let want = ["t.Outer", "t.Voice", "t.Env", "std.core.Option__t_Voice", "t.Pair", "t.Inner", "t.Last"];
    assert_eq!(type_names(src), want);
}

const C_Q_P: [&str; 3] = [
    "pub struct C {\n  s: Str,\n}\n",
    "pub struct Q {\n  c: C,\n  n: U32,\n}\n",
    "pub struct P {\n  a: (Q, C),\n  k: U32,\n}\n",
];

/// An instance that holds a type lowering does not lower, by a field or by
/// one of its parts, is an E0200 at each item that uses it, whichever is
/// lowered first (review/probe/sibling_q_first.onsa): `Q`, which `P` makes
/// in the field it makes `C` in too, is not left made.
#[test]
fn an_instance_of_an_unlowered_type_is_an_e0200_at_each_use_in_either_order() {
    let uses = ["pub fn g(q: Q) -> U32 {\n  q.n\n}\n", "pub fn first(p: P) -> U32 {\n  p.k\n}\n"];
    for order in [[0, 1], [1, 0]] {
        let src = format!("{}{}{}", C_Q_P.concat(), uses[order[0]], uses[order[1]]);
        let got = lines(&src);
        assert_eq!(got.len(), 2, "{order:?}: {got:?}");
        assert!(got.iter().all(|(_, c)| *c == onsa_diag::Code::E0200), "{order:?}: {got:?}");
    }
}

/// R-335: a use of such an instance after the first, in another item or in
/// the next attempt of the same item (S-67), is the same E0200, not an
/// internal error of a type left opaque.
#[test]
fn a_later_use_of_an_unlowered_instance_is_the_same_e0200() {
    let two_items = format!(
        "{}{}pub fn n(q: Q) -> U32 {{\n  q.n\n}}\npub fn m(q: Q) -> U32 {{\n  q.n + 1\n}}\n",
        C_Q_P[0], C_Q_P[1]
    );
    let got = lines(&two_items);
    assert_eq!(got.iter().map(|(l, _)| *l).collect::<Vec<_>>(), [9, 12], "{got:?}");
    let attempts = format!(
        "{}pub fn mk() -> U32 uses {{Alloc}} {{\n  let _ = C {{ s: \"a\" }}\n  let _ = C {{ s: \"b\" }}\n  3\n}}\n",
        C_Q_P[0]
    );
    let got = lines(&attempts);
    assert_eq!(got.iter().map(|(l, _)| *l).collect::<Vec<_>>(), [5, 6], "{got:?}");
    assert!(got.iter().all(|(_, c)| *c == onsa_diag::Code::E0200), "{got:?}");
}

/// R-319: a chain of 10000 declarations, of structs and of enums, is
/// lowered on the thread of a command (`onsa_diag::stack`): the fields of
/// an instance are filled on a stack of the maker, not of Rust.
#[test]
fn a_chain_of_ten_thousand_declarations_is_lowered() {
    let mut src = String::from("pub struct S0 {\n  x: U32,\n}\npub enum E0 {\n  A(U32),\n}\n");
    for i in 1..10000 {
        let p = i - 1;
        src.push_str(&format!(
            "pub struct S{i} {{\n  a: S{p},\n  n: U32,\n}}\npub enum E{i} {{\n  A(E{p}),\n  B,\n}}\n"
        ));
    }
    src.push_str("pub fn f(s: S9999, e: E9999) -> U32 {\n  0\n}\n");
    let m = onsa_diag::stack::spawn("chain", move || core(&src)).unwrap().join().unwrap();
    assert_eq!(m.types.len(), 20000);
    assert_eq!(m.types[0].name, "t.S9999");
    let TypeDefKind::Struct { fields } = &m.types[1].kind else { panic!("{:?}", m.types[1]) };
    assert_eq!(m.tys.kind(fields[0].1), &TyKind::Struct(TypeId(2)));
}
