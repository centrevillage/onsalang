//! Unit tests of the Core layout (§12.4).

use super::*;
use crate::ir::{FnSig, Mode, TypeDef, Types};

const F32: CTy = Types::float(FloatKind::F32);

fn arr(m: &mut Module, e: CTy, n: u32) -> CTy {
    m.tys.intern(TyKind::Array(e, n))
}

/// A value of no elements or no fields takes the bytes its C takes (R-504): an
/// array of none one element (`a[1]`), `()` and a record of no fields one byte
/// (`onsa_unit`, `uint8_t onsa_empty`).
#[test]
fn no_value_is_of_no_bytes() {
    let mut m = Module::default();
    let none = arr(&mut m, F32, 0);
    m.types.push(TypeDef { name: "t.Nothing".into(), kind: TypeDefKind::Struct { fields: Vec::new() } });
    m.types.push(TypeDef {
        name: "t.Fields".into(),
        kind: TypeDefKind::Struct { fields: vec![("none".into(), none), ("v".into(), F32)] },
    });
    m.types.push(TypeDef {
        name: "t.Opt".into(),
        kind: TypeDefKind::Enum { variants: vec![("None".into(), Vec::new()), ("Some".into(), vec![none])] },
    });
    let (four, f64s) = (arr(&mut m, F32, 4), arr(&mut m, Types::float(FloatKind::F64), 0));
    let kinds = [
        TyKind::Tuple(Box::new([])),
        TyKind::Tuple(Box::new([Types::UNIT, F32])),
        TyKind::Tuple(Box::new([none, F32])),
        TyKind::Struct(TypeId(0)),
        TyKind::Struct(TypeId(1)),
        TyKind::Enum(TypeId(2)),
    ]
    .map(|k| m.tys.intern(k));
    let cases = [
        (none, (4, 4)),
        (f64s, (8, 8)),
        (arr(&mut m, none, 4), (16, 4)),
        (arr(&mut m, four, 0), (16, 4)),
        (Types::UNIT, (1, 1)),
        (kinds[0], (1, 1)),
        (kinds[1], (8, 4)),
        (kinds[2], (8, 4)),
        (kinds[3], (1, 1)),
        (kinds[4], (8, 4)),
        (kinds[5], (8, 4)),
        (arr(&mut m, F32, 3), (12, 4)),
    ];
    m.fill_all_facts();
    for (ty, want) in cases {
        assert_eq!(size_align(&m, ty), want, "{:?}", m.tys.kind(ty));
    }
}

/// The state of a delay of `[F32; 0]` (the flow of R-504): its field takes four
/// bytes, so the marks follow at 4 and 5.
#[test]
fn a_delay_of_no_elements_takes_one() {
    let m = crate::tests::core(
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let z: [F32; 0] = ([] at sample)\n  \
         let p = prev~(z, [])\n  x + F32.round_from(p.len())\n}\n",
    );
    let l = &m.flows[0].layout;
    let at = |n: &str| l.fast_fields.iter().find(|f| f.name == n).map(|f| (f.offset, f.size));
    assert_eq!((l.size, l.align), (8, 4));
    assert_eq!(at("_poisoned"), Some((4, 1)));
    assert_eq!(at("_initialized"), Some((5, 1)));
}

/// The internal error `f` stops with ([`onsa_diag::internal::bug`]).
fn internal_error_of(f: impl FnOnce()) -> String {
    let payload = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).expect_err("an internal error");
    match payload.downcast::<onsa_diag::internal::InternalBug>() {
        Ok(b) => b.message,
        Err(p) => std::panic::resume_unwind(p),
    }
}

/// The module of the types of the tests of the facts at the pointer width
/// `ptr`: `S { v: Span[F32], k: U8 }` (`TypeId(0)`), `E { A, B(Span[F32]) }`
/// (`TypeId(1)`), `O` opaque (`TypeId(2)`), and its types by name.
fn of_width(ptr: u32) -> (Module, std::collections::HashMap<&'static str, CTy>) {
    let mut m = Module { facts: Facts::new(ptr), ..Module::default() };
    let span = m.tys.intern(TyKind::Span(F32));
    let u8t = Types::int(IntKind::U8);
    let def = |name: &str, kind| TypeDef { name: name.into(), kind };
    m.types.push(def("t.S", TypeDefKind::Struct { fields: vec![("v".into(), span), ("k".into(), u8t)] }));
    m.types.push(def("t.E", TypeDefKind::Enum { variants: vec![("A".into(), vec![]), ("B".into(), vec![span])] }));
    m.types.push(def("t.O", TypeDefKind::Opaque));
    let fn_ = TyKind::FnPtr(Box::new(FnSig { rt: false, params: vec![(Mode::Borrow, span)], ret: span }));
    let kinds = [
        ("span", TyKind::Span(F32)),
        ("buf", TyKind::Buf(span)),
        ("fn", fn_),
        ("planar", TyKind::Array(span, 2)),
        ("pair", TyKind::Tuple(Box::new([u8t, span]))),
        ("s", TyKind::Struct(TypeId(0))),
        ("e", TyKind::Enum(TypeId(1))),
        ("o", TyKind::Struct(TypeId(2))),
        ("f32s", TyKind::Array(F32, 2)),
        ("span_of_span", TyKind::Span(span)),
    ];
    let names = kinds.into_iter().map(|(n, k)| (n, m.tys.intern(k))).collect();
    m.fill_all_facts();
    (m, names)
}

/// Spec §12.4, §5.3: a `Span` is a pointer and a length, a `Buf` and a
/// function value a pointer, of the width the module is lowered for; what
/// holds them is laid out at that width too.
#[test]
fn the_facts_are_at_the_pointer_width_of_the_module() {
    for (ptr, want) in [
        (
            8,
            [
                ("span", (16, 8)),
                ("buf", (8, 8)),
                ("fn", (8, 8)),
                ("planar", (32, 8)),
                ("pair", (24, 8)),
                ("s", (24, 8)),
            ],
        ),
        (
            4,
            [("span", (8, 4)), ("buf", (4, 4)), ("fn", (4, 4)), ("planar", (16, 4)), ("pair", (12, 4)), ("s", (12, 4))],
        ),
    ] {
        let (m, ty) = of_width(ptr);
        for (name, sa) in want {
            assert_eq!(size_align(&m, ty[name]), sa, "`{name}` at {ptr}");
        }
        // `E`: a tag of one byte, then the payload at its alignment.
        assert_eq!(size_align(&m, ty["e"]), (3 * ptr, ptr), "`e` at {ptr}");
        assert_eq!(size_align(&m, ty["o"]), (0, 1));
    }
}

/// A value holds a view when it is a `Span` or holds one by value: in an
/// element, a part, a field or a payload; not the element of a `Buf` or what
/// a function value takes or gives, nor a type of no fields known.
#[test]
fn a_value_views_by_what_it_holds() {
    let (m, ty) = of_width(8);
    let views = |n: &str| m.facts(ty[n]).views;
    for n in ["span", "planar", "pair", "s", "e", "span_of_span"] {
        assert!(views(n), "`{n}` holds a view");
    }
    for n in ["buf", "fn", "o", "f32s"] {
        assert!(!views(n), "`{n}` holds no view");
    }
    assert!(!m.facts(Types::UNIT).views && !m.facts(F32).views);
}

/// The facts are read once they are filled, and filled once: a type met
/// again on the way down holds itself by value, which the check rejects, so
/// lowering stops with an internal error rather than going on.
#[test]
fn a_type_that_holds_itself_or_has_no_facts_is_an_internal_error() {
    let mut m = Module::default();
    let s = m.tys.intern(TyKind::Struct(TypeId(0)));
    let pair = m.tys.intern(TyKind::Tuple(Box::new([F32, s])));
    m.types.push(TypeDef { name: "t.S".into(), kind: TypeDefKind::Struct { fields: vec![("p".into(), pair)] } });
    assert_eq!(
        internal_error_of(|| {
            m.facts(F32);
        }),
        "the facts of `F32` read before they are filled"
    );
    let message = internal_error_of(|| m.clone().fill_facts(s));
    assert!(message.ends_with("holds itself by value"), "{message}");
    // Filled twice, the facts are the same, and no part is met again.
    let mut m = Module::default();
    let pair = m.tys.intern(TyKind::Tuple(Box::new([F32, Types::UNIT])));
    m.fill_facts(pair);
    m.fill_facts(pair);
    m.fill_all_facts();
    assert_eq!(m.facts(pair), TyFacts { size: 8, align: 4, views: false });
}

/// The verifier holds the facts to cover the type table (V-20): a slot
/// empty or open, the table of facts shorter, or longer by a filled slot,
/// is rejected.
#[test]
fn the_verifier_rejects_facts_that_do_not_cover_the_types() {
    let m = crate::tests::core("pub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n");
    assert!(m.has_all_facts());
    let last = m.facts.of.len() - 1;
    for i in 0..5 {
        let mut m = m.clone();
        let of = &mut m.facts.of;
        match i {
            0 => of[0] = Slot::Empty,
            1 => of[3] = Slot::Open,
            2 => of[last] = Slot::Empty,
            3 => assert!(of.pop().is_some()),
            _ => of.push(of[0]),
        }
        let err = crate::verify(&m).expect_err("facts");
        assert!(err.rule == crate::Rule::V20 && err.message.contains("the facts do not cover"), "{i}: {err}");
    }
}

/// The tag of an enum is the smallest of U8, U16, U32 for its number of variants.
#[test]
fn the_tag_of_an_enum_by_its_variants() {
    for (n, want) in [(2usize, (2, 1)), (256, (2, 1)), (257, (4, 2)), (65536, (4, 2)), (65537, (8, 4))] {
        let mut m = Module::default();
        let u8t = Types::int(IntKind::U8);
        let variants = (0..n).map(|i| (format!("V{i}"), vec![u8t])).collect();
        m.types.push(TypeDef { name: "t.E".into(), kind: TypeDefKind::Enum { variants } });
        let e = m.tys.intern(TyKind::Enum(TypeId(0)));
        m.fill_all_facts();
        assert_eq!(size_align(&m, e), want, "{n} variants");
    }
}

/// Char is four bytes.
#[test]
fn a_char_is_four_bytes() {
    let mut m = Module::default();
    let t = m.tys.intern(TyKind::Tuple(Box::new([Types::CHAR, Types::UNIT])));
    m.fill_all_facts();
    assert_eq!(size_align(&m, Types::CHAR), (4, 4));
    assert_eq!(size_align(&m, t), (8, 4));
}

/// The bulk of a state at the threshold; a bulk array wider than the pointer sets the alignment.
#[test]
fn bulk_at_the_threshold_and_its_alignment() {
    let mut m = Module { facts: Facts::new(4), ..Module::default() };
    let f64t = Types::float(FloatKind::F64);
    let arr = m.tys.intern(TyKind::Array(f64t, 512));
    m.types.push(TypeDef { name: "t.S".into(), kind: TypeDefKind::Struct { fields: vec![("a".into(), arr)] } });
    m.fill_all_facts();
    let at = flow_layout(&m, TypeId(0), Some(4096));
    assert_eq!((at.bulk_size, at.size, at.align), (4096, 4, 8), "{at:?}");
    assert_eq!(flow_layout(&m, TypeId(0), Some(4097)).bulk_size, 0);
}
