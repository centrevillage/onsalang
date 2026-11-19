//! Unit tests of the Core layout (§12.4).

use super::*;
use crate::ir::TypeDef;

fn f32() -> Ty {
    Ty::Float(FloatKind::F32)
}

fn arr(e: Ty, n: u32) -> Ty {
    Ty::Array(Box::new(e), n)
}

/// A value of no elements or no fields takes the bytes its C takes (R-504): an
/// array of none one element (`a[1]`), `()` and a record of no fields one byte
/// (`onsa_unit`, `uint8_t onsa_empty`).
#[test]
fn no_value_is_of_no_bytes() {
    let mut m = Module::default();
    m.types.push(TypeDef { name: "t.Nothing".into(), kind: TypeDefKind::Struct { fields: Vec::new() } });
    m.types.push(TypeDef {
        name: "t.Fields".into(),
        kind: TypeDefKind::Struct { fields: vec![("none".into(), arr(f32(), 0)), ("v".into(), f32())] },
    });
    m.types.push(TypeDef {
        name: "t.Opt".into(),
        kind: TypeDefKind::Enum { variants: vec![("None".into(), Vec::new()), ("Some".into(), vec![arr(f32(), 0)])] },
    });
    let cases = [
        (arr(f32(), 0), (4, 4)),
        (arr(Ty::Float(FloatKind::F64), 0), (8, 8)),
        (arr(arr(f32(), 0), 4), (16, 4)),
        (arr(arr(f32(), 4), 0), (16, 4)),
        (Ty::Unit, (1, 1)),
        (Ty::Tuple(Vec::new()), (1, 1)),
        (Ty::Tuple(vec![Ty::Unit, f32()]), (8, 4)),
        (Ty::Tuple(vec![arr(f32(), 0), f32()]), (8, 4)),
        (Ty::Struct(TypeId(0)), (1, 1)),
        (Ty::Struct(TypeId(1)), (8, 4)),
        (Ty::Enum(TypeId(2)), (8, 4)),
        (arr(f32(), 3), (12, 4)),
    ];
    for (ty, want) in cases {
        assert_eq!(size_align(&m, &ty), want, "{ty:?}");
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
