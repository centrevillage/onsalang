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
        deep = t.builtin(BuiltinTy::Span, vec![deep]);
    }
    assert!(!t.over_limit(deep));
    let deeper = t.builtin(BuiltinTy::Span, vec![deep]);
    assert!(t.over_limit(deeper) && t.depth(deeper) == crate::ty::TYPE_DEPTH_LIMIT + 1);
    let err = t.error();
    let with_err = t.intern(Ty::Tuple(vec![deeper, err]));
    assert!(t.has_error(with_err) && !t.has_error(deeper));
}

/// The measure of a type with variables (§4.4, S-264, S-849): an unbound
/// variable is a name, a bound one its type; a shared part with a variable
/// is walked once, and the walk stops below the depth limit.
#[test]
fn a_measure_follows_the_bound_variables() {
    use crate::infer::{Cause, Infer, LitKind, Walk};
    let walk = || Walk::default();
    use crate::ty::{TYPE_DEPTH_LIMIT, TYPE_SIZE_LIMIT};
    let mut a = check("pub fn f() {}\n");
    let (t, mut inf) = (&mut a.types, Infer::default());
    let f32 = t.float(FloatKind::F32);
    let (v, lit) = (inf.fresh(t, None), inf.fresh(t, Some(LitKind::Int)));
    assert!(t.holds_infer_var(v) && !t.holds_infer_var(f32));
    let pair = t.intern(Ty::Tuple(vec![v, lit]));
    let m = inf.measure(t, pair, &mut walk());
    assert!((m.measure.depth, m.measure.size, m.waits, m.error) == (1, 3, true, false));
    // Doubled 11 times over `v`: 2^12 - 1 parts with `v` a name, walked once each.
    let mut dbl = v;
    for _ in 0..11 {
        dbl = t.intern(Ty::Tuple(vec![dbl, dbl]));
    }
    assert!(!inf.measure(t, dbl, &mut walk()).measure.over_limit());
    let cause = Cause::At { span: onsa_diag::Span::new(onsa_diag::FileId(0), 0, 0), why: None };
    inf.unify(t, v, pair, &cause).unwrap_err();
    inf.unify(t, v, f32, &cause).unwrap();
    let m = inf.measure(t, dbl, &mut walk());
    assert!(!m.waits && m.measure.size == (1 << 12) - 1);
    // A variable bound to a pair doubles each leaf: over the size limit.
    let w = inf.fresh(t, None);
    let mut big = w;
    for _ in 0..11 {
        big = t.intern(Ty::Tuple(vec![big, big]));
    }
    let wide = t.intern(Ty::Tuple(vec![f32, f32]));
    inf.unify(t, w, wide, &cause).unwrap();
    assert_eq!(inf.measure(t, big, &mut walk()).measure.size, TYPE_SIZE_LIMIT + 1);
    // A chain of variables deeper than the limit is cut at the limit.
    let (mut deep, mut chain) = (inf.fresh(t, None), Vec::new());
    for _ in 0..TYPE_DEPTH_LIMIT + 10 {
        let x = inf.fresh(t, None);
        let up = t.builtin(BuiltinTy::Span, vec![deep]);
        inf.unify(t, x, up, &cause).unwrap();
        (deep, chain) = (x, [chain, vec![x]].concat());
    }
    let shared = &mut walk();
    let m = inf.measure(t, deep, shared);
    assert_eq!(u32::from(m.measure.depth), TYPE_DEPTH_LIMIT + 1);
    // What the cut walk kept is measured whole: a part within the limit is read right after it.
    let m = inf.measure(t, chain[5], shared);
    assert!(m.waits && m.measure.depth == 6 && !m.measure.over_limit());
    let err = t.error();
    let with_err = t.intern(Ty::Tuple(vec![deep, err]));
    assert!(inf.measure(t, with_err, &mut walk()).error);
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
