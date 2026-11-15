//! Unit tests for T3-13 (E0601) and of the effect rows (R-83 (2)).

use onsa_diag::Code;

use crate::tests::{check, codes};

/// The text of `src` after the fix `k` of `d`.
fn fixed(src: &str, d: &onsa_diag::Diagnostic, k: usize) -> String {
    let edits: Vec<&onsa_diag::Edit> = d.fixes[k].edits().iter().collect();
    onsa_diag::apply_text(src, &edits).expect("the candidate applies")
}

/// S-82, S-783: the E0601 of a function that is not `rt` is at the first use
/// of `Alloc`, and its fix inserts the row into the signature.
#[test]
fn calling_an_alloc_fn_needs_alloc_in_the_row() {
    let src = "pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }
pub fn bad() -> U32 {
  let n = 1
  mk(4).len() + n
}
";
    let a = check(src);
    assert_eq!(codes(&a), vec![Code::E0601]);
    let d = &a.diagnostics[0];
    assert_eq!(d.found.as_deref(), Some("mk(4)"));
    assert!(d.message.contains("calls `mk`") && d.message.contains("`bad`"), "{}", d.message);
    assert_eq!(d.fixes.len(), 1);
    assert!(fixed(src, d, 0).contains("pub fn bad() -> U32 uses {Alloc} {\n  let n"), "{}", fixed(src, d, 0));
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
}

/// S-77, §10 rule 1: in an `rt` function, what needs `Alloc` is an E0601 at
/// the use, with no fix and a note of the rule: an owned local (before the
/// E0901 of `Buf.zeroed`, which is not `rt`) and an interpolation.
#[test]
fn an_rt_function_that_allocates_is_an_e0601_with_no_fix() {
    for (body, found) in
        [("let b: Buf[F32] = Buf.zeroed(n)\n  b.len()", "b"), ("let s = 1\n  \"{n}\".len()", "\"{n}\"")]
    {
        let a = check(&format!("pub rt fn r(n: U32) -> U32 {{\n  {body}\n}}\n"));
        let d = a.diagnostics.iter().min_by(|x, y| x.unit_order().cmp(&y.unit_order())).expect("a diagnostic");
        assert_eq!(d.code, Code::E0601, "{body}");
        assert_eq!((d.found.as_deref(), d.fixes.len()), (Some(found), 0), "{body}");
        assert!(d.notes.iter().any(|n| n.message.contains("§10 rule 1")), "{:?}", d.notes);
    }
}

/// B3 (S-783), and the call of a function that is not `rt` whose value is
/// dropped (S-783, a supplement): one use is both an E0601 (§8.1) and an
/// E0901 (§10 rule 4); both are made at one place, and the order of the
/// diagnostics, which chooses the one of a unit (§18.1), puts the E0601 first.
#[test]
fn a_call_in_rt_that_needs_alloc_is_both_and_the_e0601_comes_first() {
    for callee in ["pub fn mk(n: U32) -> Str uses {Alloc} { \"a\" }", "pub fn mk(n: U32) -> Str { \"a\" }"] {
        let a = check(&format!("{callee}\npub rt fn r(n: U32) -> U32 {{\n  mk(n).len()\n}}\n"));
        let mut ds: Vec<_> = a.diagnostics.iter().filter(|d| d.found.as_deref() == Some("mk(n)")).collect();
        ds.sort_by(|x, y| x.unit_order().cmp(&y.unit_order()));
        let got: Vec<_> = ds.iter().map(|d| d.code).collect();
        assert_eq!(got, [Code::E0601, Code::E0901], "{callee}: {:?}", a.diagnostics);
        assert_eq!(ds[0].span, ds[1].span);
    }
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
    let alloc = a.alloc().expect("std declares `Alloc`");
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

/// S-691, S-1062 (W6-03 U7a): a name not read in a row (an E0304, a name
/// not found) keeps in the type the effects of its last name it may have
/// meant, which the row admits where it is wanted but does not have nor show;
/// a name of no effect (`Aloc`) keeps none.
#[test]
fn a_name_not_read_keeps_what_it_may_have_meant() {
    let src = "pub enum Alloc { A }\npub fn r(g: fn() uses {Random}) -> U32 { 0 }\npub fn s(g: fn() uses {Aloc}) -> U32 { 0 }\npub fn t(g: fn() uses {Alloc}) -> U32 { 0 }\n";
    let a = check(src);
    assert_eq!(codes(&a), vec![Code::E0302, Code::E0302, Code::E0304]);
    let row = |name: &str| {
        let ty = a.def(crate::tests::def(&a, name)).as_fn().unwrap().params[0].ty;
        let crate::ty::Ty::Fn(f) = a.types.get(ty) else { panic!("{name}: no function type") };
        f.effects.clone()
    };
    let effect = |name: &str| {
        let is = |d: &crate::def::Def| d.name == name && matches!(d.kind, crate::def::DefKind::Effect { .. });
        crate::DefId(a.defs.iter().position(is).expect("std declares it") as u32)
    };
    let (random, alloc) = (effect("Random"), a.alloc().expect("std declares `Alloc`"));
    let (rr, rs, rt) = (row("r"), row("s"), row("t"));
    assert!(rr.admits(random) && !rr.has(random) && rr.is_empty(), "{rr:?}");
    assert!(rt.admits(alloc) && !rt.has(alloc) && rt.is_empty(), "{rt:?}");
    assert_eq!(rs, crate::ty::EffectSet::default());
    let mut real = crate::ty::EffectSet::default();
    real.insert(alloc);
    // Of the row wanted only: an `Alloc` fits where `t`'s row is, not the other way.
    assert!(real.within(&rt) && rt.within(&crate::ty::EffectSet::default()) && !real.within(&rr));
}
