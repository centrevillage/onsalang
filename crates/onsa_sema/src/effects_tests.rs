//! Unit tests for T3-13 (E0601) and of the effect rows (R-83 (2)).

use onsa_diag::Code;

use crate::tests::{check, codes};

#[test]
fn calling_an_alloc_fn_needs_alloc_in_the_row() {
    let src = "pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\npub fn bad() -> U32 { mk(4).len() }\n";
    let a = check(src);
    assert_eq!(codes(&a), vec![Code::E0601]);
    let d = &a.diagnostics[0];
    assert_eq!(d.found.as_deref(), Some("bad() -> U32"));
    assert_eq!(d.fixes.len(), 1);
    assert_eq!(crate::fixed_region(src, d, 0), "bad() -> U32 uses {Alloc}");
    assert!(d.notes[0].message.contains("calls `mk`"));
}

#[test]
fn alloc_row_test_body_and_rt_are_fine_or_other_codes() {
    // With the row: fine.
    let a = check(
        "pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\npub fn ok() -> U32 uses {Alloc} { mk(4).len() }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    // A test body gets `Alloc` from the runner (D-08).
    let a =
        check("pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\ntest \"t\" { assert mk(4).len() == 4 }\n");
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    // An rt function reports E0901, not E0601.
    let a =
        check("pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\npub rt fn r() -> U32 { mk(4).len() }\n");
    assert_eq!(codes(&a), vec![Code::E0901]);
}

#[test]
fn zeroed_interpolation_and_drops() {
    let a = check("pub fn z() -> U32 { let b: Buf[F32] = Buf.zeroed(4)\n b.len() }\n");
    assert_eq!(codes(&a), vec![Code::E0601]);
    let a = check("pub fn owns(move b: Buf[F32]) -> U32 { b.len() }\n");
    assert_eq!(codes(&a), vec![Code::E0601]);
    // Moving the value on is not a drop.
    let a = check(
        "pub fn take(move b: Buf[F32]) -> U32 uses {Alloc} { b.len() }\npub fn pass(move b: Buf[F32]) -> U32 uses {Alloc} { take(move b) }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
}

/// R-83 (2): an effect row is the set of the ids of the declarations of its
/// effects. `Alloc` is told by the lang item, written alone or with another
/// effect; a user's effect (an E0200) is kept by its declaration, a name that
/// is no effect (an E0308) by name, and a name not found is left out
/// (S-691). The row is shown in the order of the declarations, the names
/// that are no effect after them.
#[test]
fn an_effect_row_is_a_set_of_declarations() {
    let src = "pub effect Tick {}\npub fn a() -> U32 uses {Alloc} { 1 }\npub fn t() -> U32 uses {I32, Tick, Alloc, Tick} { 1 }\npub fn n() -> U32 uses {Nope} { 1 }\npub fn e() -> U32 { 1 }\n";
    let a = check(src);
    let row = |name: &str| a.def(crate::tests::def(&a, name)).as_fn().unwrap().effects.clone();
    let alloc = a.alloc.expect("std declares `Alloc`");
    let tick = crate::tests::def(&a, "Tick");
    let (ra, rt, rn, re) = (row("a"), row("t"), row("n"), row("e"));
    assert_eq!((ra.effects(), ra.not_effects.as_slice()), (&[alloc][..], &[][..]));
    assert_eq!((rt.effects(), rt.not_effects.as_slice()), (&[alloc, tick][..], &["I32".to_string()][..]));
    assert!(rn.is_empty() && re.is_empty());
    let uses: Vec<bool> = [&ra, &rt, &rn, &re].iter().map(|r| a.uses_alloc(r)).collect();
    assert_eq!(uses, vec![true, true, false, false]);
    let shown = rt.names(&|d| a.def(d).name.clone(), &|v| format!("<{v}>"));
    assert_eq!(shown, vec!["Alloc", "Tick", "I32"]);
    assert!(ra.within(&rt) && !rt.within(&ra) && re.within(&ra));
}

/// The set of a row: an effect is in it once, in the order of the ids
/// whatever the order of insertion, and the union of two rows keeps that
/// order and the names that are no effect once each (the join, §4.7).
#[test]
fn effect_rows_are_ordered_sets() {
    use crate::DefId;
    use crate::ty::EffectSet;
    let mut r = EffectSet::default();
    [DefId(7), DefId(3), DefId(7), DefId(5)].into_iter().for_each(|d| r.insert(d));
    assert_eq!(r.effects(), &[DefId(3), DefId(5), DefId(7)]);
    assert!(r.has(DefId(5)) && !r.has(DefId(4)));
    let mut s = EffectSet::default();
    (s.not_effects, s.vars) = (vec!["S".into()], vec![0]);
    s.insert(DefId(4));
    let mut u = r.clone();
    u.union(&s);
    u.union(&s);
    assert_eq!(
        (u.effects(), u.not_effects.as_slice()),
        (&[DefId(3), DefId(4), DefId(5), DefId(7)][..], &["S".to_string()][..])
    );
    // The union does not add the variables (they are not compared, R-27 (3)).
    assert!(u.vars.is_empty() && r.within(&u) && s.within(&u) && !u.within(&s) && s.is_open());
}
