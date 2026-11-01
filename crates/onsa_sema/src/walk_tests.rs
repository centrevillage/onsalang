//! Unit tests of the walk the kinds, the layouts and the drops read
//! (`walk.rs`): generic fields under their arguments, a type that holds
//! itself, the steps of a walk and the answers it keeps.

use crate::tests::{check, codes, def};
use crate::ty::{BuiltinTy, FloatKind, IntKind, Ty};
use crate::{Analysis, Kind};

/// A generic type nested in itself has the kind and the layout of what it
/// holds (R-310), and a generic type with an Affine argument is Affine
/// whether the substituted field types were interned elsewhere or not
/// (R-30: the walks read the fields under the arguments, W4-05 U1).
#[test]
fn kinds_and_layouts_read_generic_fields_under_their_arguments() {
    let mut a = check("pub struct Pair[T] { a: T }\npub struct Holder[T: ?Dup] { items: (T, U32) }\n");
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let i32 = a.types.int(IntKind::I32);
    let inner = a.types.intern(Ty::Named(def(&a, "Pair"), vec![i32]));
    let outer = a.types.intern(Ty::Named(def(&a, "Pair"), vec![inner]));
    let outer3 = a.types.intern(Ty::Named(def(&a, "Pair"), vec![outer]));
    for t in [inner, outer, outer3] {
        assert_eq!(a.kind_of(t), Some(Kind::Copy));
        assert_eq!(a.layout_of(t).map(|l| l.size), Some(4));
    }
    let f32 = a.types.float(FloatKind::F32);
    let buf = a.types.builtin(BuiltinTy::Buf, vec![f32]);
    let holder = a.types.intern(Ty::Named(def(&a, "Holder"), vec![buf]));
    let field = Ty::Tuple(vec![buf, a.types.int(IntKind::U32)]);
    assert_eq!(a.types.find(&field), None, "the field type is not interned");
    assert_eq!(a.kind_of(holder), Some(Kind::Affine));
    a.types.intern(field);
    assert_eq!(a.kind_of(holder), Some(Kind::Affine));
    assert!(crate::rt::needs_alloc_drop(&a, holder));
    let pair_of_str = a.types.builtin(BuiltinTy::Str, vec![]);
    let p1 = a.types.intern(Ty::Named(def(&a, "Pair"), vec![pair_of_str]));
    let p2 = a.types.intern(Ty::Named(def(&a, "Pair"), vec![p1]));
    assert!(crate::rt::needs_alloc_drop(&a, p2), "`Pair[Pair[Str]]` holds a `Str`");
    // A const argument is read as the length of a field.
    let mut a = check("pub struct R[const N: U32] { xs: [F32; N] }\n");
    let three = a.types.intern(Ty::ConstVal(3));
    let r = a.types.intern(Ty::Named(def(&a, "R"), vec![three]));
    assert_eq!(a.layout_of(r).map(|l| l.size), Some(12));
}

/// A type that holds itself by value (an E0311 from W4-05 U2) has no kind
/// and no layout: the walks stop at the depth of `walk::Walk::enter`, not at a
/// signal (on the stack of a command, which its safety net reads).
#[test]
fn a_type_that_holds_itself_has_no_kind_and_no_layout() {
    let srcs =
        ["pub struct Node { v: I32, next: Node }\n", "pub struct W[T] { a: T }\npub struct Node { w: W[Node] }\n"];
    for src in srcs {
        let run = move || {
            let mut a = check(src);
            let node = a.types.intern(Ty::Named(def(&a, "Node"), vec![]));
            (a.kind_of(node), a.layout_of(node).is_none(), crate::rt::needs_alloc_drop(&a, node))
        };
        assert_eq!(onsa_diag::stack::spawn("t", run).unwrap().join().unwrap(), (None, true, false), "{src}");
    }
}

/// A chain whose every step holds the step before twice (R-313), of
/// declarations with no parameter (`A_k`) and with one (`G_k[T]`): each walk
/// finds what a declaration used with closed arguments holds once
/// (`walk::Known`), so the kind, the layout and the drops of the 64th have an
/// answer, where a walk that expands the chain stops past its steps at about
/// 20. A size past `U32` (from the 30th) is no layout (S-88), so the layout
/// is of the 29th.
#[test]
fn a_chain_that_doubles_each_step_has_its_answers() {
    let mut src = String::from("pub struct A0 { v: F32 }\npub struct G0[T] { v: T }\n");
    for k in 1..=64 {
        src.push_str(&format!("pub struct A{k} {{ x: A{0}, y: A{0} }}\n", k - 1));
        src.push_str(&format!("pub struct G{k}[T] {{ x: G{0}[T], y: G{0}[T] }}\n", k - 1));
    }
    let run = move || {
        let mut a = check(&src);
        assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
        let f32 = a.types.float(FloatKind::F32);
        for (k, name, args) in [(29, "A", vec![]), (29, "G", vec![f32]), (64, "A", vec![]), (64, "G", vec![f32])] {
            let d = def(&a, &format!("{name}{k}"));
            let t = a.types.intern(Ty::Named(d, args.clone()));
            assert_eq!(a.kind_of(t), Some(Kind::Copy), "{name}{k}");
            assert!(!crate::rt::needs_alloc_drop(&a, t));
            assert_eq!(
                a.known.drops.borrow().get(&(d, args, crate::walk::Under::Closed)),
                Some(&(Some(false), false)),
                "{name}{k}: the drops are found"
            );
            assert_eq!(a.layout_of(t).map(|l| l.size), (k == 29).then_some(4 << 29), "{name}{k}");
        }
    };
    onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
}

/// A kind found near the steps of a walk is the same whichever declaration
/// is asked first (§18.1; W4-05 U2b/b): `Z` holds three expansions of about
/// a third of the steps each (each step holds the one before with arguments
/// of two forms, so none is kept twice, R-317), `Q` holds `Z` and two more,
/// so `Q` has its answer only if `Z`'s is found with steps of its own.
#[test]
fn a_kind_near_the_steps_does_not_hang_on_the_order() {
    let mut src = String::from("pub struct G0[T] { v: T }\n");
    for k in 1..=10 {
        src.push_str(&format!("pub struct G{k}[T] {{ x: G{0}[Option[T]], y: G{0}[(T, T)] }}\n", k - 1));
    }
    src.push_str("pub struct Z { f0: G10[F32], f1: G10[I32], f2: G10[U8] }\n");
    src.push_str("pub struct Q { z: Z, g0: G10[Bool], g1: G10[I8] }\n");
    let kind_of_q = |z_first: bool| {
        let mut a = check(&src);
        let ty = |a: &mut Analysis, name| a.types.intern(Ty::Named(def(a, name), vec![]));
        let (z, q) = (ty(&mut a, "Z"), ty(&mut a, "Q"));
        if z_first {
            a.kind_of(z);
        }
        a.kind_of(q)
    };
    assert_eq!(kind_of_q(true), kind_of_q(false));
    assert_eq!(kind_of_q(false), Some(Kind::Copy));
}

/// The items read under the environment of an item go when it is found
/// (R-317, `walk::Known`): after 20 bodies ask `G6` of 20 arguments, each
/// walk keeping about 2^7 such items, the tables keep the answers of the
/// roots and of the closed types only, not more for each root.
#[test]
fn the_kinds_kept_do_not_grow_with_the_roots() {
    let mut src = String::from("pub struct G0[T] { v: T }\n");
    for k in 1..=6 {
        src.push_str(&format!("pub struct G{k}[T] {{ x: G{0}[Option[T]], y: G{0}[[T; 2]] }}\n", k - 1));
    }
    let mut shape = String::from("T");
    for n in 0..20 {
        shape = if n % 2 == 0 { format!("Option[{shape}]") } else { format!("({shape}, U8)") };
        src.push_str(&format!("pub fn f{n}[T: Copy](g: G6[{shape}]) -> (G6[{shape}], G6[{shape}]) {{ (g, g) }}\n"));
    }
    let a = check(&src);
    assert_eq!(codes(&a), []);
    let kinds = a.known.kinds.borrow();
    let under = |u: fn(&crate::walk::Under) -> bool| kinds.keys().filter(|k| u(&k.2)).count();
    assert_eq!(under(|u| matches!(u, crate::walk::Under::Body(_))), 20, "each root is kept");
    assert_eq!(under(|u| matches!(u, crate::walk::Under::Item(_))), 0);
    assert!(kinds.len() <= 20 + 7, "{} kept", kinds.len());
}

/// The answer of a declaration is found from the depth 0, whatever depth
/// the walk that asks it is at (W4-05 U2b/i3): a chain of 300 asked from its
/// top finds the kind of each (each step is `W` and a `P`, so the chain is
/// past the depth of a walk). A type that holds itself through a `Ptr` has
/// no answer as it is entered again, so its drops end at once.
#[test]
fn an_answer_does_not_hang_on_the_depth_it_is_asked_at() {
    let mut src = String::from("pub struct W[T] { t: T }\npub struct P0 { v: F32 }\n");
    for k in (1..=300).rev() {
        src.push_str(&format!("pub struct P{k} {{ w: W[P{}] }}\n", k - 1));
    }
    src.push_str("pub struct N { p: Ptr[N] }\n");
    let run = move || {
        let mut a = check(&src);
        let ty = |a: &mut Analysis, name| a.types.intern(Ty::Named(def(a, name), vec![]));
        let (p300, p20, n) = (ty(&mut a, "P300"), ty(&mut a, "P20"), ty(&mut a, "N"));
        assert_eq!((a.kind_of(p300), a.kind_of(p20)), (Some(Kind::Copy), Some(Kind::Copy)));
        assert!(!crate::rt::needs_alloc_drop(&a, n));
    };
    onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
}
