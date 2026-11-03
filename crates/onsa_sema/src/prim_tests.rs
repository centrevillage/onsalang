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
use crate::prim::{INTS, MathFn, Prim, PrimRow, Scalar, key_of, row, rows};
use crate::ty::{BuiltinTy, FloatKind, IntKind, Ty, TyId};
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
    // The members of the `impl`s of std, by their types (§6.6, §3.3, §3.4),
    // and the helpers of `narrow_*` and `checked_*` (S-71).
    for member in [
        "F32.from_bits",
        "F64.from_bits",
        "F64.to_bits",
        "F32.trunc_u8_sat",
        "F64.round_f32",
        "U64.round_f64",
        "I8.div_euclid",
        "core.num.narrow_parts",
        "core.num.div_parts",
        // The members of `Span[T]` (§5.3, `std/core/seq.onsa`).
        "Span.len",
        "Span.slice",
        "Span.fill",
        "Span.copy_from",
        "Span.add_from",
        // `Buf.zeroed` and `Str.len` (§5.3, §4.2, R-104, R-96).
        "Buf.zeroed",
        "Str.len",
    ] {
        assert!(decls.contains_key(member), "no declaration `{member}` in {keys:?}");
    }
    for (key, (def, f)) in &decls {
        let r = row(key).unwrap_or_else(|| panic!("no row of `{key}`"));
        assert_eq!(usize::from(r.arity), f.params.len(), "the arity of `{key}`");
        assert_eq!(r.rt, f.rt, "the `rt` of `{key}`");
        assert_eq!(a.prims.get(def), Some(&r.prim), "the row recorded for `{key}`");
    }
}

/// The builtin types a type argument is tried at: a Shared and an Affine one
/// too, which `Copy` keeps out (`Span[T]`, S-853).
fn builtins(a: &mut Analysis) -> Vec<TyId> {
    let mut v: Vec<TyId> = INTS.iter().map(|&k| a.types.int(k)).collect();
    v.extend([a.types.float(FloatKind::F32), a.types.float(FloatKind::F64), a.types.bool(), a.types.unit()]);
    v.push(a.types.intern(Ty::Char));
    let (f32, s) = (a.types.float(FloatKind::F32), a.types.builtin(BuiltinTy::Str, vec![]));
    v.extend([s, a.types.builtin(BuiltinTy::Buf, vec![f32])]);
    v
}

#[test]
fn every_row_gives_a_primitive_at_every_builtin_type_its_bounds_admit() {
    let mut a = analyzed_std();
    let candidates = builtins(&mut a);
    let ints: Vec<TyId> = INTS.iter().map(|&k| a.types.int(k)).collect();
    let len = a.types.intern(Ty::ConstVal(4));
    let (mut tried, mut members) = (0, 0);
    for (key, (def, f)) in std_targets(&a) {
        let r = a.prims[&def];
        members += usize::from(crate::prim::row_self(&a, def).is_some());
        // The type arguments each generic parameter is tried at.
        let mut choices: Vec<Vec<TyId>> = Vec::new();
        for g in &f.generics {
            choices.push(match &g.kind {
                GenericKind::Type { bounds, dup, unknown: false } => {
                    let met: Vec<TyId> = candidates
                        .iter()
                        .copied()
                        .filter(|&t| {
                            let b = Bounds { a: &a, generics: &[] };
                            bounds.iter().all(|&x| b.satisfies(t, x))
                                && (!*dup || b.satisfies(t, crate::def::Bound::Dup))
                        })
                        .collect();
                    // A bound that keeps no builtin type out is no bound: the
                    // walk would try every type at it (D4).
                    assert!(bounds.is_empty() || met.len() < candidates.len(), "a bound of `{key}` keeps nothing out");
                    // The helpers of `narrow_*` and `checked_*` take the integers (`Int`, D4).
                    if key.starts_with("core.num.") {
                        assert_eq!(met, ints, "`{key}` at {:?}", g.name);
                    }
                    met
                }
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
    assert!(tried > 200, "only {tried} uses tried");
    assert!(members > 0, "no member of an `impl` tried");
}

/// The declarations of `Buf.zeroed` and `Str.len` give their primitives at
/// the types of their declarations (`Buf[F32]`, `Str`): what lowering reads.
#[test]
fn zeroed_and_the_len_of_a_str_instantiate_at_their_declarations() {
    let mut a = analyzed_std();
    let decls = std_targets(&a);
    let f32 = a.types.float(FloatKind::F32);
    for (key, args, prim) in [("Buf.zeroed", vec![f32], Prim::BufZeroed), ("Str.len", vec![], Prim::StrLen)] {
        let (def, f) = &decls[key];
        assert_eq!(a.prims[def].instantiate(&Scalar::of_use(&a, *def, &args).expect("closed")), Some(prim));
        // `zeroed` allocates (§12), `len` reads (§10).
        assert_eq!((f.effects.alloc, f.rt), (key == "Buf.zeroed", key == "Str.len"), "`{key}`");
    }
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

/// The conversion methods of the scalars against `as` (spec §3.3, memo 2.3):
/// of every pair of number types, `narrow_<B>()` (an `Option[B]`) of the
/// integers and `round_<B>()` to the floats where `as` does not convert, and
/// `trunc_<B>()` and `trunc_<B>_sat()` of the floats to every integer; no
/// other conversion method, and none where `as` converts.
#[test]
fn the_conversion_methods_are_where_as_does_not_convert() {
    let mut a = analyzed_std();
    let ints: Vec<TyId> = INTS.iter().map(|&k| a.types.int(k)).collect();
    let floats = [a.types.float(FloatKind::F32), a.types.float(FloatKind::F64)];
    let numbers: Vec<TyId> = ints.iter().chain(&floats).copied().collect();
    let (mut methods, mut casts) = (0, 0);
    for &from in &numbers {
        let mut want: BTreeMap<String, TyId> = BTreeMap::new();
        for &to in &numbers {
            let lower = scalar_name(&a, to).to_lowercase();
            if crate::cast::cast_allowed(&a.types, from, to) {
                casts += 1;
                continue;
            }
            match (a.types.get(from), a.types.get(to)) {
                (Ty::Int(_), Ty::Int(_)) => {
                    let opt = a.types.builtin(BuiltinTy::Option, vec![to]);
                    want.insert(format!("narrow_{lower}"), opt);
                }
                (_, Ty::Float(_)) => {
                    want.insert(format!("round_{lower}"), to);
                }
                (Ty::Float(_), Ty::Int(_)) => {
                    want.insert(format!("trunc_{lower}"), to);
                    want.insert(format!("trunc_{lower}_sat"), to);
                }
                other => panic!("no conversion of {other:?}"),
            }
        }
        let table = a.modules.assoc_builtin.get(&from).expect("the members of a scalar");
        // The method the E0411 of a rejected `as` suggests is one of them
        // (`crate::cast`, W5-14 decides the suggestions).
        for &to in &numbers {
            if !crate::cast::cast_allowed(&a.types, from, to) {
                let m = crate::cast::cast_suggestion(&a.types, from, to).expect("a suggestion");
                let name = m.strip_prefix('.').and_then(|m| m.strip_suffix("()")).expect("`.name()`");
                assert!(table.contains_key(name), "`{m}` of `{}`", scalar_name(&a, from));
            }
        }
        let conversion = |n: &str| ["narrow_", "round_", "trunc_"].iter().any(|p| n.starts_with(p));
        let found: BTreeMap<String, TyId> = table
            .iter()
            .filter(|(n, _)| conversion(n))
            .map(|(n, &d)| {
                let DefKind::Fn(f) = &a.def(d).kind else { panic!("`{n}` is no method") };
                assert!(f.self_mode.is_some() && f.params.is_empty() && f.rt, "the heading of `{n}`");
                (n.clone(), f.ret)
            })
            .collect();
        assert_eq!(found, want, "the conversions of `{}`", scalar_name(&a, from));
        methods += found.len();
    }
    // 38 `narrow_*`, 7 `round_*`, 32 `trunc_*` (§3.3).
    assert_eq!((methods, casts), (77, 39));
}

fn scalar_name(a: &Analysis, t: TyId) -> &'static str {
    match a.types.get(t) {
        Ty::Int(k) => k.name(),
        Ty::Float(k) => k.name(),
        other => panic!("{other:?} is no number type"),
    }
}
