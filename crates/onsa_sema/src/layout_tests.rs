//! Unit tests of the layouts (§12.4).

use crate::tests::{check, def, named};
use crate::ty::{FloatKind, IntKind, Len, Ty};

#[test]
fn layouts_follow_declaration_order() {
    let mut a = check(
        "pub struct S { a: U8, b: F32 }\npub struct N { x: F64, y: U8 }\npub enum E { A, B(U8) }\n\
         pub enum Big { A(F64), B(U8, U8) }\npub struct Pair { l: F32, r: F32 }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let s = a.types.intern(Ty::Named(def(&a, "S"), vec![]));
    let l = a.layout_of(s).unwrap();
    assert_eq!((l.size, l.align), (8, 4));
    assert_eq!(l.fields, vec![("a".to_string(), 0), ("b".to_string(), 4)]);
    let n = a.types.intern(Ty::Named(def(&a, "N"), vec![]));
    assert_eq!(a.layout_of(n).map(|l| (l.size, l.align)), Some((16, 8)));
    let f32 = a.types.float(FloatKind::F32);
    let delay = a.types.intern(Ty::Array(f32, Len::Const(96001)));
    assert_eq!(a.layout_of(delay).map(|l| (l.size, l.align)), Some((384004, 4)));
    let u8 = a.types.int(IntKind::U8);
    let opt = a.types.intern(Ty::Named(def(&a, "Option"), vec![u8]));
    assert_eq!(a.layout_of(opt).map(|l| (l.size, l.align)), Some((2, 1)));
    let e = a.types.intern(Ty::Named(def(&a, "E"), vec![]));
    assert_eq!(a.layout_of(e).map(|l| (l.size, l.align)), Some((2, 1)));
    let big = a.types.intern(Ty::Named(def(&a, "Big"), vec![]));
    assert_eq!(a.layout_of(big).map(|l| (l.size, l.align)), Some((16, 8)));
    let pair = a.types.intern(Ty::Named(def(&a, "Pair"), vec![]));
    let tuple = a.types.intern(Ty::Tuple(vec![pair, u8]));
    assert_eq!(a.layout_of(tuple).map(|l| (l.size, l.align)), Some((12, 4)));
    assert_eq!(a.layout_of(named(&a, "Pair")).map(|l| l.size), Some(8));
}

/// A value of no elements or no fields takes the bytes its C takes (R-504, as
/// `onsa_core::layout`): an array of none one element, `()` and a record of no
/// fields one byte; an empty variant adds no payload.
#[test]
fn no_value_is_of_no_bytes() {
    let mut a = check(
        "pub struct Nothing {}\npub struct Fields { none: [F32; 0], v: F32 }\n\
         pub enum E { A, B([F32; 0]) }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f32 = a.types.float(FloatKind::F32);
    let none = a.types.intern(Ty::Array(f32, Len::Const(0)));
    let nested = a.types.intern(Ty::Array(none, Len::Const(4)));
    let unit = a.types.unit();
    let empty = a.types.intern(Ty::Tuple(vec![]));
    let pair = a.types.intern(Ty::Tuple(vec![unit, f32]));
    let [nothing, fields, e] = ["Nothing", "Fields", "E"].map(|n| a.types.intern(Ty::Named(def(&a, n), vec![])));
    let size = |a: &crate::Analysis, t| a.layout_of(t).map(|l| (l.size, l.align));
    assert_eq!(size(&a, none), Some((4, 4)));
    assert_eq!(size(&a, nested), Some((16, 4)));
    assert_eq!(size(&a, unit), Some((1, 1)));
    assert_eq!(size(&a, empty), Some((1, 1)));
    assert_eq!(size(&a, pair), Some((8, 4)));
    assert_eq!(size(&a, nothing), Some((1, 1)));
    assert_eq!(size(&a, fields), Some((8, 4)));
    assert_eq!(size(&a, e), Some((8, 4)));
}
