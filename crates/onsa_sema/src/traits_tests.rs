//! The tables of the traits against §6.3 and against each other.

use crate::Package;
use crate::body::bounds::Bounds;
use crate::def::{Bound, DefKind, Derive, TRAITS};
use crate::flow_tests::std_package;
use crate::tests::analyze;
use crate::traits::{Class, IMPLS, SUPERS, implies};
use crate::ty::{BuiltinTy, EffectSet, FloatKind, FnTy, IntKind, Len, Ty};

const NUMBER_TRAITS: [Bound; 5] = [Bound::AnyNum, Bound::Num, Bound::Float, Bound::Int, Bound::Unsigned];

/// `b` and what it requires, each path walked: a repeated bound on a path is a cycle.
fn walk(b: Bound, path: &mut Vec<Bound>) {
    assert!(!path.contains(&b), "a cycle in SUPERS: {path:?} then {b:?}");
    path.push(b);
    for &s in SUPERS.iter().filter(|(x, _)| *x == b).flat_map(|(_, s)| s.iter()) {
        walk(s, path);
    }
    path.pop();
}

#[test]
fn supers_have_no_cycle() {
    for (b, _) in SUPERS {
        walk(*b, &mut Vec::new());
    }
}

#[test]
fn a_row_of_each_table_is_one_of_its_trait() {
    for (k, (b, _)) in SUPERS.iter().enumerate() {
        assert!(!SUPERS[..k].iter().any(|(x, _)| x == b), "two rows of {b:?}");
    }
    for (k, (c, _)) in IMPLS.iter().enumerate() {
        assert!(!IMPLS[..k].iter().any(|(x, _)| x == c), "two rows of {c:?}");
    }
    assert_eq!(IMPLS.len(), 12, "the rows of the table of §6.3");
}

/// §6.3: a type implements what its traits require ("上位の trait を満たさない型への
/// `impl` は E0416"), but for the kind constraints, which are not in the table.
#[test]
fn a_row_has_what_its_traits_require() {
    for (c, row) in IMPLS {
        for &b in *row {
            assert!(!b.is_kind_constraint(), "{c:?} has the kind constraint {b:?}");
            for want in TRAITS.iter().filter_map(|(_, t)| *t).filter(|&want| implies(b, want)) {
                assert!(c.implements(want), "{c:?} has {b:?}, which requires {want:?}");
            }
        }
    }
}

#[test]
fn the_number_traits_hold_as_section_6_3_says() {
    for b in NUMBER_TRAITS {
        assert!(implies(b, Bound::Copy) && implies(b, Bound::Dup), "{b:?} requires `Copy`");
        assert!(implies(b, Bound::AnyNum), "{b:?}");
    }
    // The way an `impl` of `T: Float` is Copy (§6.6, the `const` of a type parameter).
    assert!(implies(Bound::Float, Bound::Num) && implies(Bound::Num, Bound::AnyNum));
    assert!(implies(Bound::AnyNum, Bound::Add) && !implies(Bound::AnyNum, Bound::Neg));
    assert!(implies(Bound::Num, Bound::Neg) && !implies(Bound::Int, Bound::Neg));
    assert!(implies(Bound::Unsigned, Bound::Int) && !implies(Bound::Unsigned, Bound::Num));
    assert!(implies(Bound::Int, Bound::Ord) && !implies(Bound::Float, Bound::Eq));
    assert!(!implies(Bound::Add, Bound::Copy), "an operator trait does not require `Copy`");
    // R-169.
    assert!(Class::Signed.implements(Bound::Num) && Class::Signed.implements(Bound::Neg));
    assert!(Class::Unsigned.implements(Bound::Unsigned));
    assert!(!Class::Unsigned.implements(Bound::Num) && !Class::Unsigned.implements(Bound::Neg));
    assert!(!Class::Signed.implements(Bound::Unsigned));
}

#[test]
fn only_four_traits_are_no_bound() {
    let none: Vec<&str> = TRAITS.iter().filter(|(_, b)| b.is_none()).map(|(n, _)| *n).collect();
    assert_eq!(none, ["Iter", "IntoIter", "Drop", "Ordinal"]);
    for (name, b) in TRAITS.iter().filter_map(|(n, b)| b.map(|b| (n, b))) {
        assert_eq!(b.name(), *name);
    }
}

/// The row of `Option` and `Result` is what their declarations derive: `satisfies` reads
/// the derives, as of any named type.
#[test]
fn the_derived_row_is_the_derives_of_option_and_result() {
    let a = analyze(&Package::new("t", Vec::new(), vec![std_package()]));
    let row: &[(Bound, Derive)] = &[
        (Bound::PartialEq, Derive::PartialEq),
        (Bound::Eq, Derive::Eq),
        (Bound::PartialOrd, Derive::PartialOrd),
        (Bound::Ord, Derive::Ord),
        (Bound::Hash, Derive::Hash),
        (Bound::Show, Derive::Show),
        (Bound::Default, Derive::Default),
    ];
    let mut found = 0;
    for name in ["Option", "Result"] {
        for d in a.defs.iter().filter(|d| d.name == name && a.modules.is_std(d.module)) {
            let DefKind::Enum(e) = &d.kind else { continue };
            let derives = e.derives.as_deref().unwrap_or(&[]);
            for (b, x) in row {
                assert_eq!(Class::Derived.implements(*b), derives.contains(x), "{name} and {b:?}");
            }
            found += 1;
        }
    }
    assert_eq!(found, 2);
}

/// The kind constraints: the arms of the types that `satisfies` had before they went to
/// the kind (§6.3), type by type.
#[test]
fn a_kind_constraint_is_the_kind_of_a_builtin_type() {
    let mut a = analyze(&Package::new("t", Vec::new(), vec![std_package()]));
    let t = &mut a.types;
    let i32_ = t.intern(Ty::Int(IntKind::I32));
    let u8_ = t.intern(Ty::Int(IntKind::U8));
    let f32_ = t.intern(Ty::Float(FloatKind::F32));
    let bool_ = t.intern(Ty::Bool);
    let char_ = t.intern(Ty::Char);
    let unit = t.intern(Ty::Unit);
    let str_ = t.intern(Ty::Builtin(BuiltinTy::Str, vec![]));
    let bytes = t.intern(Ty::Builtin(BuiltinTy::Bytes, vec![]));
    let buf = t.intern(Ty::Builtin(BuiltinTy::Buf, vec![f32_]));
    let span = t.intern(Ty::Builtin(BuiltinTy::Span, vec![f32_]));
    let ptr = t.intern(Ty::Builtin(BuiltinTy::Ptr, vec![f32_]));
    let array = t.intern(Ty::Builtin(BuiltinTy::Array, vec![buf]));
    let map = t.intern(Ty::Builtin(BuiltinTy::Map, vec![str_, buf]));
    let set = t.intern(Ty::Builtin(BuiltinTy::Set, vec![str_]));
    let func = t.intern(Ty::Fn(FnTy { rt: false, params: vec![], ret: i32_, effects: EffectSet::default() }));
    let pair = t.intern(Ty::Tuple(vec![i32_, f32_]));
    let shared_pair = t.intern(Ty::Tuple(vec![i32_, str_]));
    let affine_pair = t.intern(Ty::Tuple(vec![i32_, buf]));
    let of_ints = t.intern(Ty::Array(i32_, Len::Const(2)));
    let of_strs = t.intern(Ty::Array(str_, Len::Const(2)));
    let of_bufs = t.intern(Ty::Array(buf, Len::Const(2)));
    let of_spans = t.intern(Ty::Array(span, Len::Const(2)));
    // What is known of a part is what a part not read keeps quiet on (§18.1).
    let error = t.intern(Ty::Error);
    let unknown_pair = t.intern(Ty::Tuple(vec![i32_, error]));
    let unknown_array = t.intern(Ty::Array(error, Len::Const(2)));
    let const_val = t.intern(Ty::ConstVal(3));
    let var = t.intern(Ty::Var(0));
    let bounds = Bounds { a: &a, generics: &[] };
    for (ty, copy, dup) in [
        (i32_, true, true),
        (u8_, true, true),
        (f32_, true, true),
        (bool_, true, true),
        (char_, true, true),
        (unit, true, true),
        (func, true, true),
        (ptr, true, true),
        (str_, false, true),
        (bytes, false, true),
        (array, false, true),
        (map, false, true),
        (set, false, true),
        (buf, false, false),
        (span, false, false),
        (pair, true, true),
        (shared_pair, false, true),
        (affine_pair, false, false),
        (of_ints, true, true),
        (of_strs, false, true),
        (of_bufs, false, false),
        (of_spans, false, false),
        (unknown_pair, true, true),
        (unknown_array, true, true),
        (const_val, false, false),
        (var, false, false),
    ] {
        let shown = a.types.get(ty);
        assert_eq!(bounds.satisfies(ty, Bound::Copy), copy, "{shown:?} and `Copy`");
        assert_eq!(bounds.satisfies(ty, Bound::Dup), dup, "{shown:?} and `Dup`");
    }
}

#[test]
fn the_parts_decide_a_trait_of_a_tuple_and_an_array() {
    let mut a = analyze(&Package::new("t", Vec::new(), vec![std_package()]));
    let t = &mut a.types;
    let i32_ = t.intern(Ty::Int(IntKind::I32));
    let f32_ = t.intern(Ty::Float(FloatKind::F32));
    let of_ints = t.intern(Ty::Tuple(vec![i32_, i32_]));
    let of_floats = t.intern(Ty::Array(f32_, Len::Const(2)));
    let array = t.intern(Ty::Builtin(BuiltinTy::Array, vec![i32_]));
    let bounds = Bounds { a: &a, generics: &[] };
    assert!(bounds.satisfies(of_ints, Bound::Eq) && bounds.satisfies(of_ints, Bound::Hash));
    assert!(bounds.satisfies(of_floats, Bound::PartialOrd) && !bounds.satisfies(of_floats, Bound::Eq));
    assert!(!bounds.satisfies(of_ints, Bound::Add), "the operators of the numbers are not of the parts");
    assert!(bounds.satisfies(array, Bound::Eq) && !bounds.satisfies(array, Bound::Hash));
}
