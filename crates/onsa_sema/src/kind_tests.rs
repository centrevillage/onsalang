//! Unit tests of the kinds (§4.6): of the structure of a type, of generic
//! types by their arguments, and in a body.

use onsa_diag::Code;

use crate::Kind;
use crate::def::DefKind;
use crate::tests::{check, codes, def};
use crate::ty::{BuiltinTy, FloatKind, Len, Ty};

#[test]
fn kinds_from_structure() {
    let a = check(
        "pub struct P { x: F32, y: F32 }\npub struct S { name: Str, n: U32 }\npub struct B { buf: Buf[F32] }\n\
         pub enum E { A(P), B(S) }\npub struct T { v: F32 }\npub flow f(x: F32 at sample) -> F32 at sample { x }\n\
         pub struct W { s: f.State }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    // Interning happens when the struct types are referenced; reference them here.
    let mut a = a;
    let p = a.types.intern(Ty::Named(def(&a, "P"), vec![]));
    let s = a.types.intern(Ty::Named(def(&a, "S"), vec![]));
    let b = a.types.intern(Ty::Named(def(&a, "B"), vec![]));
    let e = a.types.intern(Ty::Named(def(&a, "E"), vec![]));
    let t = a.types.intern(Ty::Named(def(&a, "T"), vec![]));
    let w = a.types.intern(Ty::Named(def(&a, "W"), vec![]));
    assert_eq!(a.kind_of(p), Some(Kind::Copy));
    assert_eq!(a.kind_of(s), Some(Kind::Shared));
    assert_eq!(a.kind_of(b), Some(Kind::Affine));
    assert_eq!(a.kind_of(e), Some(Kind::Shared));
    assert_eq!(a.kind_of(t), Some(Kind::Copy));
    assert_eq!(a.kind_of(w), Some(Kind::Affine), "flow State is Affine (§4.6)");
    let f32 = a.types.float(FloatKind::F32);
    let arr = a.types.intern(Ty::Array(f32, Len::Const(4)));
    assert_eq!(a.kind_of(arr), Some(Kind::Copy));
    let opt = a.types.intern(Ty::Named(def(&a, "Option"), vec![s]));
    assert_eq!(a.kind_of(opt), Some(Kind::Shared));
    let span = a.types.builtin(BuiltinTy::Span, vec![f32]);
    assert_eq!(a.kind_of(span), None);
}

/// The kinds of generic types by their arguments (§4.6, R-30, R-310): the
/// tables of the break side of W4-05 U1 (`kcases`, the arguments through
/// aliases, const lengths, enums and function types; `xcases`, arguments
/// passed on to other generic types in another order). Each type is written
/// as an alias, whose type is the written one.
#[test]
fn kinds_of_generic_types_by_their_arguments() {
    let decls = "pub struct W[T: ?Dup] { a: T }\n\
        pub struct Pair2[A: ?Dup, B: ?Dup] { a: A, b: B }\n\
        pub struct Ring[T: ?Dup, const N: U32] { data: [T; N], head: U32 }\n\
        pub enum E[T: ?Dup] { A(T), B }\n\
        pub struct HT[T: ?Dup] { items: (T, U32) }\n\
        pub struct FH[T: ?Dup] { f: fn(T) -> T, n: I32 }\n\
        pub struct Mk[T: ?Dup, const N: U32] { w: W[[T; N]] }\n\
        type BB = Buf[F32]\ntype WB = W[Buf[F32]]\ntype WWB = W[WB]\ntype SS = Str\n\
        pub struct Holds { w: W[W[Buf[F32]]] }\n\
        pub struct HoldsS { w: Option[W[Str]] }\n\
        pub struct Sw[A: ?Dup, B: ?Dup] { a: W[B], b: W[(A, I32)] }\n\
        pub struct Inner[U: ?Dup] { u: U }\n\
        pub struct Outer[T: ?Dup] { i: Inner[W[T]] }\n\
        pub struct Outer2[T: ?Dup, U: ?Dup] { i: Inner[Sw[U, T]] }\n\
        pub struct Cn[T: ?Dup, const N: U32, const M: U32] { x: [[T; M]; N] }\n\
        pub struct CnW[T: ?Dup, const N: U32] { c: Cn[T, N, 2], d: Cn[W[T], 3, N] }\n\
        pub enum En[T: ?Dup, U: ?Dup] { L(U), R(W[T]), N }\n\
        pub struct Fnp[T: ?Dup] { f: fn(T) -> W[T], g: [fn(T); 2] }\n\
        pub struct Hold[T: ?Dup, const N: U32] { items: [(T, U32); N] }\n";
    // The types of each kind, `|` between them: kcases, then xcases.
    let table = [
        (
            Kind::Copy,
            "W[I32] | W[W[I32]] | W[(I32, F32)] | W[[I32; 4]] | Ring[I32, 4] | E[I32] | E[E[I32]] | \
            Option[W[I32]] | Result[W[I32], I32] | W[Option[I32]] | Pair2[I32, W[F32]] | HT[I32] | \
            FH[I32] | Mk[I32, 3] | FH[Buf[F32]] | Ring[Ring[I32, 2], 3] | Sw[I32, I32] | Outer[I32] | \
            Outer2[I32, I32] | Cn[I32, 2, 3] | CnW[I32, 4] | En[I32, I32] | Fnp[Buf[F32]] | \
            Hold[I32, 3]",
        ),
        (
            Kind::Shared,
            "W[SS] | W[Str] | W[W[Str]] | Option[W[Str]] | E[Str] | HT[Str] | Pair2[W[Str], I32] | \
            HoldsS | Mk[Str, 2] | Sw[Str, I32] | Outer[Str] | CnW[Str, 4] | \
            En[Option[En[I32, I32]], Str] | (Outer[Str], Outer2[I32, I32])",
        ),
        (
            Kind::Affine,
            "W[Buf[F32]] | W[W[Buf[F32]]] | Ring[Buf[F32], 4] | E[Buf[F32]] | Option[W[Buf[F32]]] | \
            Result[W[Buf[F32]], I32] | Pair2[I32, Buf[F32]] | Pair2[Pair2[I32, Buf[F32]], I32] | \
            HT[Buf[F32]] | W[(Buf[F32], U32)] | [W[Buf[F32]]; 2] | (W[Buf[F32]], I32) | \
            W[[Buf[F32]; 2]] | E[E[Buf[F32]]] | W[BB] | WB | WWB | W[WB] | Holds | Mk[Buf[F32], 2] | \
            Mk[W[Buf[F32]], 2] | W[E[W[Pair2[I32, Buf[F32]]]]] | Ring[W[Ring[Buf[F32], 2]], 3] | \
            Sw[Buf[F32], I32] | Sw[I32, Buf[F32]] | Outer[Buf[F32]] | Outer[W[Buf[F32]]] | \
            Outer2[Buf[F32], I32] | Outer2[I32, Buf[F32]] | Cn[Buf[F32], 2, 3] | CnW[Buf[F32], 4] | \
            En[Buf[F32], I32] | En[I32, Buf[F32]] | En[W[Buf[F32]], W[I32]] | Hold[Buf[F32], 3] | \
            Option[Outer2[W[Buf[F32]], I32]] | [Outer[Buf[F32]]; 2]",
        ),
    ];
    let table: Vec<(&str, Kind)> =
        table.iter().flat_map(|&(kind, ts)| ts.split('|').map(move |t| (t.trim(), kind))).collect();
    assert_eq!(table.len(), 48 + 27);
    let src: String = table.iter().enumerate().map(|(i, (t, _))| format!("type K{i} = {t}\n")).collect();
    let a = check(&format!("{decls}{src}"));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    for (i, (t, kind)) in table.iter().enumerate() {
        let DefKind::Alias(ty) = a.def(def(&a, &format!("K{i}"))).kind else { panic!("K{i}") };
        assert_eq!(a.kind_of(ty), Some(*kind), "{t}");
    }
}

/// The kind in a body asked by the modes (R-30): a walk past its steps is
/// Affine (`G11` holds the one before with arguments of two forms, each
/// kept, about 3^11 steps), so `(move h, move h)` is an E0704; a walk with no answer
/// of an error keeps quiet (§18.1): a field whose type is not found, a type
/// that holds itself, a field of a declaration whose type parameters a
/// syntax error cut.
#[test]
fn a_kind_in_a_body_is_affine_only_past_the_steps() {
    let mut src = String::from("pub struct G0[T] { v: T }\n");
    for k in 1..=11 {
        src.push_str(&format!("pub struct G{k}[T] {{ x: G{0}[(T, U8)], y: G{0}[(T, T)] }}\n", k - 1));
    }
    src.push_str("pub fn f(move h: G11[F32]) -> (G11[F32], G11[F32]) { (move h, move h) }\n");
    let mut a = check(&src);
    assert_eq!(codes(&a), [Code::E0704]);
    let f32 = a.types.float(FloatKind::F32);
    let g11 = a.types.intern(Ty::Named(def(&a, "G11"), vec![f32]));
    assert_eq!((a.kind_of(g11), crate::kind::kind_in_body(&a, g11, &[])), (None, Some(Kind::Affine)));
    let quiet = [
        ("pub struct S { a: Nope }\npub fn f(s: S) -> S { s }\n", vec![Code::E0302]),
        ("pub struct Node { v: I32, next: Node }\npub fn f(n: Node) -> Node { n }\n", vec![Code::E0311]),
        ("struct S[T: ] { a: T }\nfn f(s: S[F32]) -> F32 { s.a }\n", vec![]),
    ];
    for (src, want) in quiet {
        assert_eq!(codes(&check(src)), want, "{src}");
    }
}
