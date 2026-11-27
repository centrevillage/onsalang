//! The two places of the rules of layout agree (W7-07 U2b, R-504): the size
//! and alignment `onsa interface` shows of a type (`onsa_sema::layout`) are
//! those of the Core type the lowering makes of it (`onsa_core::layout`,
//! which lays out the states of flows, §12.4), on a fixed set of types:
//! scalars, arrays of no element and of some, `()`, tuples, a struct of no
//! field, enums by their number of variants (the tag of 1 and 2 bytes) and
//! payloads, a function value, and these nested.

use onsa_core::layout::size_align;
use onsa_core::{TyKind, TypeDefKind};
use onsa_sema::def::DefKind;
use onsa_sema::layout::layout_of_def;

use crate::{Loaded, PackageInput};

const TYPES: &str = "\
struct Ints { a: I8, b: U16, c: I32, d: U64, e: I16, f: U8, g: I64, h: U32 }
struct Others { a: F32, b: Bool, c: F64, d: Char }
struct Mix { a: U8, b: F64, c: U16 }
struct NoElems { x: [F32; 0], y: U8 }
struct Elems { x: [U8; 3], y: [F64; 2], z: [Bool; 1] }
struct Empty {}
struct Units { u: (), t: (U8, F64), e: Empty, n: (U16, (U8, F32)) }
enum One { A }
enum Two { A, B(F64) }
enum Payloads { A(U8, U32), B(F64), C, D(Mix), E((U8, U16)) }
struct Handles { f: fn(F32) -> F32, b: Bool }
struct Nest { two: Two, mix: Mix, arr: [Units; 2], pay: [Payloads; 3], h: Handles, z: NoElems, w: Wide }
fn touch(n: Nest, a: Ints, o: Others, e: Elems, one: One) -> U8 {
  0
}
";

/// The types of [`TYPES`] and the enum `Wide`, of 257 variants (a tag of
/// 2 bytes) and one payload of 1 byte (so that the tag shows in the size).
const NAMES: &[&str] = &[
    "Ints", "Others", "Mix", "NoElems", "Elems", "Empty", "Units", "One", "Two", "Payloads", "Handles", "Nest", "Wide",
];

#[test]
fn the_sizes_interface_shows_are_those_of_the_core_types() {
    let variants: Vec<String> = (0..256).map(|i| format!("V{i}")).chain(["P(U8)".to_string()]).collect();
    let text = format!("{TYPES}enum Wide {{ {} }}\n", variants.join(", "));
    let mut loaded = Loaded::from_input(PackageInput::single_file("m.onsa", &text)).expect("the input loads");
    let analyzed = crate::analyze_loaded(&mut loaded).expect("no internal error");
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    let mut module = crate::lower_core(&analyzed).expect("the package lowers");
    let a = &analyzed.analysis;
    let mut compared = Vec::new();
    for (i, d) in a.defs.iter().enumerate() {
        if !(matches!(d.kind, DefKind::Struct(_) | DefKind::Enum(_)) && NAMES.contains(&d.name.as_str())) {
            continue;
        }
        let id = onsa_sema::DefId(i as u32);
        let sema = layout_of_def(a, id, &[]).unwrap_or_else(|| panic!("no layout of `{}`", d.name));
        let name = a.qualified_name(id);
        let (at, core) = module.types.iter().enumerate().find(|(_, t)| t.name == name).expect("a Core type of it");
        let at = onsa_core::TypeId(at as u32);
        let ty = if matches!(core.kind, TypeDefKind::Enum { .. }) { TyKind::Enum(at) } else { TyKind::Struct(at) };
        let ty = module.tys.intern(ty);
        assert_eq!((sema.size, sema.align), size_align(&module, ty), "`{name}`: sema, Core");
        compared.push(d.name.clone());
    }
    compared.sort();
    let mut all: Vec<String> = NAMES.iter().map(|n| n.to_string()).collect();
    all.sort();
    assert_eq!(compared, all, "every type is compared once");
}
