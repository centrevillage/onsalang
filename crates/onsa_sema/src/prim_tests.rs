//! The table of the `std` `target` declarations against the embedded std
//! (S-69 (2), W5-02 U3a): one row per declaration and one declaration per
//! row, with the same arity and `rt`; a primitive at every builtin type the
//! bounds of the declaration admit; and the E0200 of a use at a type the row
//! has no primitive for (spec §15.2).

use std::collections::BTreeMap;
use std::sync::Arc;

use onsa_diag::{Code, FileId};

use crate::body::bounds::Bounds;
use crate::def::{DefId, DefKind, FnDef, GenericKind};
use crate::flow_tests::std_package;
use crate::prim::{MathFn, PrimRow, Scalar, key_of, row, rows};
use crate::ty::{FloatKind, IntKind, Ty, TyId};
use crate::{Analysis, Module, Package, analyze};

fn module(segments: &[&str], file: u32, src: &str) -> Module {
    Module {
        segments: segments.iter().map(|s| s.to_string()).collect(),
        file: FileId(file),
        text: src.to_string(),
        parsed: onsa_syntax::parse(FileId(file), src),
    }
}

/// The `target` declarations of std, by their keys.
fn std_targets(a: &Analysis) -> BTreeMap<String, (DefId, FnDef)> {
    let mut out = BTreeMap::new();
    for i in 0..a.defs.len() {
        let def = DefId(i as u32);
        let d = a.def(def);
        if let DefKind::Fn(f) = &d.kind
            && f.target
            && a.modules.is_std(d.module)
        {
            assert!(out.insert(key_of(a, def), (def, f.clone())).is_none(), "two declarations of one key");
        }
    }
    out
}

fn analyzed_std() -> Analysis {
    let a = analyze(&Package::new("t", vec![module(&["main"], 0, "")], vec![std_package()]));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    a
}

#[test]
fn every_target_declaration_of_std_has_one_row_and_every_row_one_declaration() {
    let a = analyzed_std();
    let decls = std_targets(&a);
    let keys: Vec<&String> = decls.keys().collect();
    let mut row_keys: Vec<&String> = rows().iter().map(|r| &r.key).collect();
    row_keys.sort();
    assert_eq!(keys, row_keys);
    assert!(!keys.is_empty());
    // The members of the `impl`s of std, by their types (§6.6).
    for member in ["F32.from_bits", "F64.from_bits"] {
        assert!(decls.contains_key(member), "no declaration `{member}` in {keys:?}");
    }
    for (key, (def, f)) in &decls {
        let r = row(key).unwrap_or_else(|| panic!("no row of `{key}`"));
        assert_eq!(usize::from(r.arity), f.params.len(), "the arity of `{key}`");
        assert_eq!(r.rt, f.rt, "the `rt` of `{key}`");
        assert_eq!(a.prims.get(def), Some(&r.prim), "the row recorded for `{key}`");
    }
}

/// The builtin types a type argument is tried at.
fn builtins(a: &mut Analysis) -> Vec<TyId> {
    let ints =
        [IntKind::I8, IntKind::I16, IntKind::I32, IntKind::I64, IntKind::U8, IntKind::U16, IntKind::U32, IntKind::U64];
    let mut v: Vec<TyId> = ints.iter().map(|&k| a.types.int(k)).collect();
    v.extend([a.types.float(FloatKind::F32), a.types.float(FloatKind::F64), a.types.bool(), a.types.unit()]);
    v.push(a.types.intern(Ty::Char));
    v
}

#[test]
fn every_row_gives_a_primitive_at_every_builtin_type_its_bounds_admit() {
    let mut a = analyzed_std();
    let candidates = builtins(&mut a);
    let len = a.types.intern(Ty::ConstVal(4));
    let (mut tried, mut members) = (0, 0);
    for (key, (def, f)) in std_targets(&a) {
        let r = a.prims[&def];
        members += usize::from(crate::prim::row_self(&a, def).is_some());
        // The type arguments each generic parameter is tried at.
        let mut choices: Vec<Vec<TyId>> = Vec::new();
        for g in &f.generics {
            choices.push(match &g.kind {
                GenericKind::Type { bounds, dup, unknown: false } => candidates
                    .iter()
                    .copied()
                    .filter(|&t| {
                        let b = Bounds { a: &a, generics: &[] };
                        bounds.iter().all(|&x| b.satisfies(t, x)) && (!*dup || b.satisfies(t, crate::def::Bound::Dup))
                    })
                    .collect(),
                GenericKind::Const(_) => vec![len],
                other => panic!("`{key}` has the generic {other:?}"),
            });
        }
        let mut combos: Vec<Vec<TyId>> = vec![Vec::new()];
        for c in &choices {
            assert!(!c.is_empty(), "no builtin type meets a bound of `{key}`");
            combos = combos.iter().flat_map(|p| c.iter().map(move |&t| [p.clone(), vec![t]].concat())).collect();
        }
        for args in combos {
            // A member reads its `Self` first (`F32` of `F32.from_bits`).
            let scalars = Scalar::of_use(&a, def, &args).expect("closed");
            assert!(r.provides(&scalars), "`{key}` gives no primitive at {scalars:?}");
            // The primitive leads back to its row, and so to the declaration
            // an E0200 names.
            if let Some(p) = r.instantiate(&scalars) {
                assert_eq!(p.row_prim(), Some(r), "`{key}` at {scalars:?}");
                assert_eq!(p.std_name().as_deref(), Some(format!("std.{key}").as_str()));
            }
            tried += 1;
        }
    }
    assert!(tried > 40, "only {tried} uses tried");
    assert!(members > 0, "no member of an `impl` tried");
}

#[test]
fn a_row_has_no_primitive_for_what_its_family_lacks() {
    let sqrt = PrimRow::Math(MathFn::Sqrt);
    assert!(sqrt.provides(&[Scalar::Float(FloatKind::F32)]));
    assert!(!sqrt.provides(&[Scalar::Int(IntKind::I32)]));
    assert!(!sqrt.provides(&[Scalar::Other]));
    assert!(PrimRow::Math(MathFn::Max).provides(&[Scalar::Int(IntKind::U8)]));
    assert!(PrimRow::FromFn.instantiate(&[Scalar::Other, Scalar::Other]).is_none());
    assert!(PrimRow::FromFn.provides(&[Scalar::Other, Scalar::Other]));
}

/// A std whose bound admits a type the row has no primitive for (none of the
/// embedded std does, its bounds stop them first): the use at a closed type
/// is E0200 at the types stage, with the function and the type (spec
/// §15.2); a use in a generic body is not judged (lowering's).
#[test]
fn a_use_at_a_type_without_a_primitive_is_e0200() {
    let std = Arc::new(Package::std(vec![module(&["math"], 100, "pub target rt fn sqrt[T: Num](x: T) -> T\n")]));
    let check = |src: &str| analyze(&Package::new("t", vec![module(&["main"], 0, src)], vec![std.clone()]));
    let a = check("use std.math\n\nfn f() -> I32 {\n  math.sqrt(4)\n}\n");
    let [d] = a.diagnostics.as_slice() else { panic!("{:?}", a.diagnostics) };
    assert_eq!(d.code, Code::E0200);
    assert!(d.message.contains("`std.math.sqrt` for the type `I32`"), "{}", d.message);
    assert_eq!(
        &"use std.math\n\nfn f() -> I32 {\n  math.sqrt(4)\n}\n"[d.span.start as usize..d.span.end as usize],
        "math.sqrt(4)"
    );
    let a =
        check("use std.math\n\nfn f() -> F64 {\n  math.sqrt(4.0)\n}\n\nfn g[T: Num](x: T) -> T {\n  math.sqrt(x)\n}\n");
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
}
