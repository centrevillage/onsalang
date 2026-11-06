//! The table of the `std` `target` declarations against the embedded std
//! (S-69 (2), W5-02 U3a): one row per declaration and one declaration per
//! row, with the same arity and `rt`; a primitive at every builtin type the
//! bounds of the declaration admit; the E0200 of a use at a type the row
//! has no primitive for (spec §15.2); and the `else` bodies of std, checked as
//! generic functions, at `Num` and `AnyNum`, which a user's type can meet (S-669).

use std::collections::BTreeMap;
use std::sync::Arc;

use onsa_diag::{Code, FileId};

use crate::body::bounds::Bounds;
use crate::cast::Instead;
use crate::def::{Bound, DefId, DefKind, FnDef, GenericKind};
use crate::flow_tests::std_package;
use crate::prim::{INTS, MathFn, NARROW_FROM, Prim, PrimRow, Scalar, key_of, row, rows};
use crate::tests::analyze;
use crate::traits::no_impl;
use crate::ty::{BuiltinTy, FloatKind, IntKind, Ty, TyId};
use crate::{Analysis, Module, Package};

fn module(segments: &[&str], file: u32, src: &str) -> Module {
    Module::new(
        segments.iter().map(|s| s.to_string()).collect(),
        FileId(file),
        src.to_string(),
        onsa_syntax::parse(FileId(file), src),
    )
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

pub(crate) fn analyzed_std() -> Analysis {
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
    // and the helpers of `narrow_from` and `checked_*` (S-71).
    for member in [
        "F32.from_bits",
        "F64.from_bits",
        "F64.to_bits",
        "F64.round_from",
        "U8.trunc_sat_from",
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
        // The float predicates (§3.4, S-98 (5)).
        "math.is_nan",
        "math.is_finite",
    ] {
        assert!(decls.contains_key(member), "no declaration `{member}` in {keys:?}");
    }
    // The float `%` is the operator, no function (§3.4, S-98): its primitive
    // has no row, and its E0200 would name no declaration.
    assert!(!decls.contains_key("math.fmod"));
    assert_eq!(Prim::Math(MathFn::Fmod, FloatKind::F32).std_name(), None);
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
                GenericKind::Type { bounds, dup, unknown: false, .. } => {
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
                    // The helpers of `narrow_from` and `checked_*` take the integers (`Int`, D4).
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
                assert_eq!(p.row_prim(), r, "`{key}` at {scalars:?}");
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
    // A conversion reads its `Self`, then its source (§3.3).
    let (f32, f64, i32) = (Scalar::Float(FloatKind::F32), Scalar::Float(FloatKind::F64), Scalar::Int(IntKind::I32));
    let round = PrimRow::RoundFrom(FloatKind::F32);
    assert_eq!(round.instantiate(&[f32, f32]), Some(Prim::FloatToFloat { from: FloatKind::F32, to: FloatKind::F32 }));
    assert_eq!(round.instantiate(&[f32, i32]), Some(Prim::IntToFloat { from: IntKind::I32, to: FloatKind::F32 }));
    assert!(!round.provides(&[f64, i32]));
    assert!(!round.provides(&[f32, Scalar::Other]));
    let trunc = PrimRow::TruncFrom { to: IntKind::I32, sat: true };
    assert!(trunc.provides(&[i32, f64]));
    assert!(!trunc.provides(&[i32, i32]));
    assert!(!trunc.provides(&[Scalar::Int(IntKind::I8), f64]));
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

/// The functions the E0411 of a rejected `as` names, of every pair of number
/// types (spec §3.3): std's conversion functions of the target type, and
/// `narrow_from` in the note of a narrowing of the integers.
#[test]
fn the_e0411_suggests_the_conversion_functions_of_std() {
    let mut a = analyzed_std();
    let ints: Vec<TyId> = INTS.iter().map(|&k| a.types.int(k)).collect();
    let floats = [a.types.float(FloatKind::F32), a.types.float(FloatKind::F64)];
    let numbers: Vec<TyId> = ints.iter().chain(&floats).copied().collect();
    let (mut casts, mut narrowings, mut suggested) = (0, 0, 0);
    for &from in &numbers {
        for &to in &numbers {
            if crate::cast::cast_allowed(&a.types, from, to) {
                casts += 1;
                continue;
            }
            let table = a.modules.assoc_builtin.get(&to).expect("the members of a scalar");
            let instead = crate::cast::cast_instead(&Bounds { a: &a, generics: &[] }, from, to);
            let names = match instead {
                Instead::Calls(names) => names,
                Instead::Narrowing => &[NARROW_FROM],
                Instead::Nothing => panic!("`{}` to `{}`", scalar_name(&a, from), scalar_name(&a, to)),
            };
            for f in names {
                let d = *table.get(*f).unwrap_or_else(|| panic!("`{f}`"));
                assert_eq!(crate::prim::conversion_target(&a, d), Some(to), "`{f}`");
            }
            match instead {
                Instead::Narrowing => narrowings += 1,
                _ => suggested += names.len(),
            }
        }
    }
    // 7 `round_from`, and 16 pairs of the two of a float to an integer.
    assert_eq!((casts, narrowings, suggested), (39, 38, 39));
}

/// The 26 conversion functions (§3.3, S-231): `round_from` of the floats and
/// the three of the integers, none of them a method, each `rt`, each
/// converting to its type; no other member of a number has such a name.
#[test]
fn the_conversion_functions_of_the_numbers_are_the_list_of_the_spec() {
    let mut a = analyzed_std();
    let ints: Vec<TyId> = INTS.iter().map(|&k| a.types.int(k)).collect();
    let floats = [a.types.float(FloatKind::F32), a.types.float(FloatKind::F64)];
    let mut found = 0;
    for &to in ints.iter().chain(&floats) {
        let want: &[&str] = match a.types.get(to) {
            Ty::Float(_) => &["round_from"],
            _ => &["narrow_from", "trunc_from", "trunc_sat_from"],
        };
        let table = a.modules.assoc_builtin.get(&to).expect("the members of a scalar");
        let mut names: Vec<&str> = Vec::new();
        for (n, &d) in table {
            let old = ["narrow_", "round_", "trunc_"].iter().any(|p| n.starts_with(p));
            if old || crate::prim::conversion_target(&a, d).is_some() {
                assert_eq!(crate::prim::conversion_target(&a, d), Some(to), "`{n}`");
                let DefKind::Fn(f) = &a.def(d).kind else { panic!("`{n}` is no function") };
                assert!(f.self_mode.is_none() && f.params.len() == 1 && f.rt, "the heading of `{n}`");
                names.push(n);
            }
        }
        names.sort();
        assert_eq!(names, want, "the conversions to `{}`", scalar_name(&a, to));
        found += names.len();
    }
    assert_eq!(found, 26);
}

fn scalar_name(a: &Analysis, t: TyId) -> &'static str {
    match a.types.get(t) {
        Ty::Int(k) => k.name(),
        Ty::Float(k) => k.name(),
        other => panic!("{other:?} is no number type"),
    }
}

/// The table of the names this version has not holds no name std declares:
/// the work that declares one takes its row off (R-294).
#[test]
fn no_missing_name_is_a_member_of_std() {
    let a = analyzed_std();
    for (&key, members) in &a.modules.assoc_builtin {
        for name in members.keys() {
            assert_eq!(crate::builtin::missing(&a.types, key, name), None, "{name} of {:?}", a.types.get(key));
        }
    }
    let of = a.builtin_key[&BuiltinTy::Str];
    assert!(crate::builtin::missing(&a.types, of, "from_utf8").is_some());
}

/// The `else` body of `abs` in the embedded std.
const ABS: &str = "pub target rt fn abs[T: Num](x: T) -> T else {\n  if x < T.ZERO { -x } else { x }\n}\n";

/// The codes of the embedded std with `ABS` replaced by `abs`.
fn codes_of_abs(abs: &str) -> Vec<Code> {
    let modules = (crate::std_modules().iter().enumerate()).map(|(i, m)| {
        let text = if m.segments == ["math"] { m.text.replacen(ABS, abs, 1) } else { m.text.to_string() };
        assert!(m.segments != ["math"] || m.text.contains(ABS), "no `abs` to replace");
        module(m.segments, 100 + i as u32, &text)
    });
    let std = Arc::new(Package::std(modules.collect()));
    let a = analyze(&Package::new("t", vec![module(&["main"], 0, "")], vec![std]));
    a.diagnostics.iter().map(|d| d.code).collect()
}

/// The `else` bodies are checked as the bodies of generic functions: the
/// three of the embedded std at every stage, without an error; and the
/// stages report an error of such a body (spec §15.2, S-669).
#[test]
fn the_else_bodies_of_std_are_checked_as_generic_functions() {
    let a = analyzed_std();
    let decls = std_targets(&a);
    for key in ["math.abs", "math.min", "math.max"] {
        let def = decls[key].0;
        let body = a.bodies.get(&def).unwrap_or_else(|| panic!("no body of `{key}`"));
        assert!(body.complete, "the body of `{key}` is cut");
    }
    assert_eq!(codes_of_abs(ABS), [], "the embedded `abs`");
    let abs =
        |bound: &str, value: &str| format!("pub target rt fn abs[T: {bound}](x: T) -> T else {{\n  {value}\n}}\n");
    // The types: `AnyNum` has no `Neg`, and `T` no integer literal.
    assert_eq!(codes_of_abs(&abs("AnyNum", "-x")), [Code::E0401]);
    assert_eq!(codes_of_abs(&abs("Num", "1")), [Code::E0401]);
    // The names, `rt`, and the modes of a value that does not `Dup`.
    assert_eq!(codes_of_abs(&abs("Num", "y")), [Code::E0302]);
    let plain = format!("fn plain[T: Num](x: T) -> T {{\n  x\n}}\n\n{}", abs("Num", "plain(x)"));
    assert_eq!(codes_of_abs(&plain), [Code::E0901]);
    assert_eq!(codes_of_abs("pub target rt fn abs[T: ?Dup](x: T) -> (T, T) else {\n  (x, x)\n}\n"), [Code::E0711]);
    // The effects: a body out of its declared row.
    let alloc = "pub target fn abs[T: Num](x: T) -> T else {\n  let b: Buf[T] = Buf.zeroed(1)\n  b[0] + x\n}\n";
    assert_eq!(codes_of_abs(alloc), [Code::E0601]);
}

/// The number traits §6.3 opens to a user's type, which the E0307 of
/// [`no_impl`] leaves open. It leaves `Int` and `Unsigned` too, of which §6.3
/// shows no user's type: the declarations bounded by them are not read here.
const OPEN_NUMBERS: [Bound; 2] = [Bound::AnyNum, Bound::Num];

/// The `target` declarations with an open bound and no `else` body. §15.2
/// says such a declaration is usable at every type of its bound as a
/// principle, no strong promise: opening the user's number types adds an
/// E0200 or a body to each (`tasks/phase2.md`, S-669).
const NO_ELSE_BODY: [&str; 3] = ["F32.round_from", "F64.round_from", "Span.add_from"];

/// The bounds of a declaration not closed against the user's types have an
/// `else` body (S-669): those of its parameters and of those of its `impl`.
#[test]
fn a_target_declaration_with_an_open_bound_has_an_else_body() {
    assert!(OPEN_NUMBERS.into_iter().all(|b| !no_impl(b)) && no_impl(Bound::Float));
    let a = analyzed_std();
    let (mut bodies, mut missing) = (Vec::new(), Vec::new());
    for (key, (def, f)) in std_targets(&a) {
        let owner = a.def(def).owner.map(|o| a.def(o).generics()).unwrap_or_default();
        let open = |g: &crate::def::GenericDef| match &g.kind {
            GenericKind::Type { bounds, .. } => bounds.iter().any(|b| OPEN_NUMBERS.contains(b)),
            _ => false,
        };
        if f.generics.iter().chain(owner).any(open) {
            if f.body.is_some() { bodies.push(key) } else { missing.push(key) }
        }
    }
    assert_eq!(bodies, ["math.abs", "math.max", "math.min"]);
    assert_eq!(missing, NO_ELSE_BODY, "an item that left the list leaves it here too");
}
