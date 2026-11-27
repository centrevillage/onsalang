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

/// R-335: a use of such an instance after the first, in another item, is
/// the same E0200, not an internal error of a type left opaque: each unit is
/// stopped at its binding, with a note at the `Str` written in `C`, and one
/// with no binding of it at its first expression of it (§18.1, S-67).
#[test]
fn each_unit_that_uses_an_unlowered_instance_has_its_e0200() {
    let two_items = format!(
        "{}{}pub fn n(q: Q) -> U32 {{\n  q.n\n}}\npub fn m(q: Q) -> U32 {{\n  q.n + 1\n}}\n",
        C_Q_P[0], C_Q_P[1]
    );
    let got = lines(&two_items);
    assert_eq!(got.iter().map(|(l, _)| *l).collect::<Vec<_>>(), [8, 11], "{got:?}");
    for d in core_err(&two_items) {
        let notes: Vec<_> = d.notes.iter().map(|n| (n.span.map(|s| s.start), n.message.as_str())).collect();
        let at = two_items.find("Str").map(|i| i as u32);
        assert_eq!(notes, [(at, "the field `s` of `C` has the type `Str`")], "{d:?}");
    }
    let attempts = format!(
        "{}pub fn mk() -> U32 uses {{Alloc}} {{\n  let _ = C {{ s: \"a\" }}\n  let _ = C {{ s: \"b\" }}\n  3\n}}\n",
        C_Q_P[0]
    );
    let got = lines(&attempts);
    assert_eq!(got.iter().map(|(l, _)| *l).collect::<Vec<_>>(), [5], "{got:?}");
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

/// A `Ptr` held by a field is a type lowering does not lower too: each unit
/// that uses it has its E0200 at its binding, with the note at the `Ptr`
/// written in `C` (W8-14 A3/b `bad5`), and the instances that hold it are not
/// left made.
#[test]
fn a_ptr_held_by_a_field_is_an_e0200_with_its_note_at_each_unit() {
    let src = "pub struct C {\n  s: Ptr[U32],\n}\npub struct Q {\n  c: C,\n  n: U32,\n}\n\
               pub fn g(q: Q) -> U32 {\n  q.n\n}\npub fn use_c(c: C) -> U32 {\n  1\n}\n";
    let diags = core_err(src);
    let mut at: Vec<_> = diags.iter().map(|d| d.span.start).collect();
    at.sort();
    assert_eq!(at, [src.find("q: Q").unwrap() as u32, src.find("c: C) ->").unwrap() as u32], "{diags:?}");
    for d in &diags {
        let notes: Vec<_> = d.notes.iter().map(|n| (n.span.map(|s| s.start), n.message.as_str())).collect();
        let written = src.find("Ptr[U32]").map(|i| i as u32);
        assert_eq!(notes, [(written, "the field `s` of `C` has the type `Ptr[U32]`")], "{d:?}");
    }
}

/// The field of a variant is named by its variant, whichever variant holds
/// it (`B` after the fields of `A`), and a type written at the use has no note.
#[test]
fn the_note_names_the_variant_and_a_type_at_the_use_has_none() {
    let src = "pub enum E {\n  A(U32, U8),\n  B(Str),\n}\npub fn f(e: E, s: Str) -> U32 {\n  0\n}\n";
    let mut diags = core_err(src);
    diags.sort_by_key(|d| d.span.start);
    let notes: Vec<Vec<&str>> = diags.iter().map(|d| d.notes.iter().map(|n| n.message.as_str()).collect()).collect();
    assert_eq!(notes, [vec!["a field of the variant `B` of `E` has the type `Str`"], vec![]], "{diags:?}");
}

/// The Core type of a function type keeps its parameters and its result
/// apart (`fn(U8) -> F32`).
#[test]
fn a_function_type_has_its_parameters_then_its_result() {
    let m = core("pub fn take(f: fn(U8) -> F32) -> U32 {\n  0\n}\n");
    let take = m.fns.iter().find(|f| f.name.ends_with(".take")).expect("take");
    let TyKind::FnPtr(sig) = m.tys.kind(take.params[0].ty) else { panic!("{:?}", m.tys.kind(take.params[0].ty)) };
    let params: Vec<CTy> = sig.params.iter().map(|&(_, t)| t).collect();
    assert_eq!((params, sig.ret), (vec![Types::int(IntKind::U8)], Types::float(FloatKind::F32)));
}

/// The notes of an E0422 in a declaration go out from the innermost field:
/// the field of `E` that holds `G`, then that of `D` (W8-14 A3/b `notes3`).
#[test]
fn the_notes_of_an_e0422_in_a_declaration_go_out_from_the_innermost_field() {
    let deep = (0..255).fold("I32".to_string(), |t, _| format!("Option[{t}]"));
    let src = format!(
        "type O = {deep}\npub struct G[T: ?Dup] {{\n  x: Option[Option[T]],\n}}\npub struct E[T: ?Dup] {{\n  b: G[T],\n}}\n\
         pub struct D[T: ?Dup] {{\n  a: E[T],\n}}\npub fn h(x: D[O]) -> U32 {{\n  0\n}}\n"
    );
    let at = |s: &str| src.find(s).map(|i| i as u32);
    let want = [at("G[T],"), at("E[T],")];
    let d = onsa_diag::stack::spawn("deep", move || super::the_one_limit(&src, u32::MAX)).unwrap().join().unwrap();
    assert_eq!(d.code, onsa_diag::Code::E0422);
    let notes: Vec<_> = d.notes.iter().filter_map(|n| n.span.map(|s| s.start)).collect();
    assert_eq!(notes, want.map(Option::unwrap), "{:?}", d.notes);
}

/// The binding of a type lowering does not lower is where it is declared
/// (§18.1, S-67): the type of a constant (`Option[Ptr[U32]]` passes the
/// checks), the name of a parameter `_` after its mode, and the written
/// result of a function; one for each unsupported part of a unit.
#[test]
fn the_e0200_of_a_binding_is_at_its_declaration() {
    let src = "const R: Option[Ptr[U32]] = None\npub fn f(inout _: Str, k: U32) -> Option[Ptr[U8]] {\n  None\n}\n";
    let mut at: Vec<u32> = core_err(src).iter().map(|d| d.span.start).collect();
    at.sort();
    let pos = |s: &str| src.find(s).unwrap() as u32;
    assert_eq!(at, [pos("Option[Ptr[U32]]"), pos("_: Str"), pos("Option[Ptr[U8]]")]);
}

/// A constant or a flow a type stops is lowered once and reported once,
/// however many units read it (S-67): the diagnostics of lowering, before the
/// driver removes the duplicates.
#[test]
fn a_stopped_constant_or_flow_is_reported_once() {
    let consts =
        "const L: U32 = \"abc\".len()\npub fn a(x: U32) -> U32 {\n  L + x\n}\npub fn b(x: U32) -> U32 {\n  L * x\n}\n";
    assert_eq!(lines(consts), [(1, onsa_diag::Code::E0200)]);
    let flows = "pub flow g(x: F32 at sample) -> F32 at sample {\n  let n = \"abc\".len()\n  x * F32.round_from(n)\n}\n\
                 pub flow f(x: F32 at sample) -> F32 at sample {\n  g~(x) + g~(x)\n}\n\
                 pub flow h(x: F32 at sample) -> F32 at sample {\n  f~(x) + g~(x)\n}\n";
    assert_eq!(lines(flows), [(2, onsa_diag::Code::E0200)]);
}

/// A constant that is lowered whole, with an E0200 of a form, keeps it when
/// the unit that read it first is stopped later by a type: the E0200s that
/// are dropped are those in the stopped unit only (ca10 of W8-16/i).
#[test]
fn the_e0200_of_a_constant_read_by_a_stopped_unit_is_kept() {
    let src = "pub struct W[T] {\n  v: T,\n}\nconst A: [I32; 2] = [1, 2]\nimpl[T] W[T] {\n  const K: (Bool, U32) = (A < [1, 3], 2)\n}\n\
               pub fn reader(x: U32) -> U32 {\n  let k = W::[U32].K.1\n  k + x + \"q\".len()\n}\n";
    assert_eq!(lines(src), [(6, onsa_diag::Code::E0200), (10, onsa_diag::Code::E0200)]);
}
