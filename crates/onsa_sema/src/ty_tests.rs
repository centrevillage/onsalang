//! Unit tests of the table of types: the depth and the size of §4.4, and
//! the rate types (S-120).

use crate::tests::check;
use crate::ty::{BuiltinTy, FloatKind, Len, Ty};

/// The depth and the size of §4.4 (S-264), held once per type: a chain of
/// pairs doubles its size each step without being expanded.
#[test]
fn types_hold_their_depth_and_size() {
    let mut a = check("pub fn f() {}\n");
    let t = &mut a.types;
    let f32 = t.float(FloatKind::F32);
    assert_eq!((t.depth(f32), t.size(f32)), (0, 1));
    let mut pair = f32;
    for k in 1..=11 {
        pair = t.intern(Ty::Tuple(vec![pair, pair]));
        assert_eq!((t.depth(pair), t.size(pair)), (k, (1 << (k + 1)) - 1));
    }
    assert!(!t.over_limit(pair));
    let over = t.intern(Ty::Tuple(vec![pair, pair]));
    assert!(t.over_limit(over));
    assert_eq!(t.size(over), crate::ty::TYPE_SIZE_LIMIT + 1, "held at the limit + 1");
    let arr = t.intern(Ty::Array(f32, Len::Const(4)));
    assert_eq!((t.depth(arr), t.size(arr)), (1, 3));
    let mut deep = f32;
    for _ in 0..crate::ty::TYPE_DEPTH_LIMIT {
        deep = t.builtin(BuiltinTy::Option, vec![deep]);
    }
    assert!(!t.over_limit(deep));
    let deeper = t.builtin(BuiltinTy::Option, vec![deep]);
    assert!(t.over_limit(deeper) && t.depth(deeper) == crate::ty::TYPE_DEPTH_LIMIT + 1);
    let err = t.error();
    let with_err = t.intern(Ty::Tuple(vec![deeper, err]));
    assert!(t.has_error(with_err) && !t.has_error(deeper));
}

/// `Rate::of_type_name` pairs `Rate::ALL` with `RATE_TYPES` by position
/// (S-120): the two lists have one length and one order.
#[test]
fn the_rate_types_are_the_rates_in_their_order() {
    use crate::ty::Rate;
    use onsa_syntax::foreign::RATE_TYPES;
    assert_eq!(Rate::ALL.len(), RATE_TYPES.len());
    for (rate, name) in Rate::ALL.into_iter().zip(RATE_TYPES) {
        assert_eq!(format!("{rate:?}"), name);
        assert_eq!(Rate::of_type_name(name), Some(rate));
    }
}
