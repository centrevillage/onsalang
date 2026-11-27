//! Unit tests of the Core layout (§12.4).

use super::*;
use crate::ir::{TypeDef, Types};

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
