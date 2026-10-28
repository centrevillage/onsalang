//! Unit tests for T2-2 .. T2-4: kinds, layouts, bounds, and name diagnostics.

use std::collections::{BTreeSet, HashSet};

use onsa_diag::{Code, FileId};

use crate::def::DefKind;
use crate::ty::{BuiltinTy, FloatKind, IntKind, Len, Ty};
use crate::{Analysis, Kind, Module, Package, analyze};

fn pkg(files: &[(&str, &str)]) -> Package {
    let modules = files
        .iter()
        .enumerate()
        .map(|(i, (path, text))| Module {
            segments: path.split('.').map(str::to_string).collect(),
            file: FileId(i as u32),
            text: text.to_string(),
            parsed: onsa_syntax::parse(FileId(i as u32), text),
        })
        .collect();
    Package::new("t", modules, Vec::new())
}

fn check(src: &str) -> Analysis {
    analyze(&pkg(&[("main", src)]))
}

fn codes(a: &Analysis) -> Vec<Code> {
    let mut v: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
    v.sort();
    v
}

fn named(a: &Analysis, name: &str) -> crate::TyId {
    let d = a.defs.iter().position(|d| d.name == name && d.owner.is_none()).unwrap_or_else(|| panic!("no def {name}"));
    a.types.find(&Ty::Named(crate::DefId(d as u32), Vec::new())).unwrap_or_else(|| panic!("{name} not interned"))
}

/// The guard-form candidates of the syntax stage bind names no identifier of
/// the file spells (`onsa_syntax::foreign::guard_name`, S-253): visible
/// without being written are only the names of the prelude, and none of them
/// is one of those.
#[test]
fn the_prelude_has_no_name_of_the_guard_candidates() {
    let a = check("pub fn f() -> I32 {\n  1\n}\n");
    assert!(!a.prelude.is_empty());
    for n in 1..=100 {
        let name = onsa_syntax::foreign::guard_name(n);
        assert!(!a.prelude.contains_key(&name), "{name} is a name of the prelude");
    }
}

#[test]
fn kinds_from_structure() {
    let a = check(
        "pub struct P { x: F32, y: F32 }\npub struct S { name: Str, n: U32 }\npub struct B { buf: Buf[F32] }\n\
         pub enum E { A(P), B(S) }\npub struct T { v: F32 }\npub flow f(x: F32 at sample) -> F32 at sample { x }\n\
         pub struct W { s: f.State }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    // Interning happens when the struct types are referenced; reference them here.
    let mut a = a;
    let p = a.types.intern(Ty::Named(def(&a, "P"), vec![]));
    let s = a.types.intern(Ty::Named(def(&a, "S"), vec![]));
    let b = a.types.intern(Ty::Named(def(&a, "B"), vec![]));
    let e = a.types.intern(Ty::Named(def(&a, "E"), vec![]));
    let t = a.types.intern(Ty::Named(def(&a, "T"), vec![]));
    let w = a.types.intern(Ty::Named(def(&a, "W"), vec![]));
    assert_eq!(a.kind_of(p), Some(Kind::Copy));
    assert_eq!(a.kind_of(s), Some(Kind::Shared));
    assert_eq!(a.kind_of(b), Some(Kind::Affine));
    assert_eq!(a.kind_of(e), Some(Kind::Shared));
    assert_eq!(a.kind_of(t), Some(Kind::Copy));
    assert_eq!(a.kind_of(w), Some(Kind::Affine), "flow State is Affine (§4.6)");
    let f32 = a.types.float(FloatKind::F32);
    let arr = a.types.intern(Ty::Array(f32, Len::Const(4)));
    assert_eq!(a.kind_of(arr), Some(Kind::Copy));
    let opt = a.types.builtin(BuiltinTy::Option, vec![s]);
    assert_eq!(a.kind_of(opt), Some(Kind::Shared));
    let span = a.types.builtin(BuiltinTy::Span, vec![f32]);
    assert_eq!(a.kind_of(span), None);
}

fn def(a: &Analysis, name: &str) -> crate::DefId {
    crate::DefId(a.defs.iter().position(|d| d.name == name && d.owner.is_none()).unwrap() as u32)
}

#[test]
fn layouts_follow_declaration_order() {
    let mut a = check(
        "pub struct S { a: U8, b: F32 }\npub struct N { x: F64, y: U8 }\npub enum E { A, B(U8) }\n\
         pub enum Big { A(F64), B(U8, U8) }\npub struct Pair { l: F32, r: F32 }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let s = a.types.intern(Ty::Named(def(&a, "S"), vec![]));
    let l = a.layout_of(s).unwrap();
    assert_eq!((l.size, l.align), (8, 4));
    assert_eq!(l.fields, vec![("a".to_string(), 0), ("b".to_string(), 4)]);
    let n = a.types.intern(Ty::Named(def(&a, "N"), vec![]));
    assert_eq!(a.layout_of(n).map(|l| (l.size, l.align)), Some((16, 8)));
    let f32 = a.types.float(FloatKind::F32);
    let delay = a.types.intern(Ty::Array(f32, Len::Const(96001)));
    assert_eq!(a.layout_of(delay).map(|l| (l.size, l.align)), Some((384004, 4)));
    let u8 = a.types.int(IntKind::U8);
    let opt = a.types.builtin(BuiltinTy::Option, vec![u8]);
    assert_eq!(a.layout_of(opt).map(|l| (l.size, l.align)), Some((2, 1)));
    let e = a.types.intern(Ty::Named(def(&a, "E"), vec![]));
    assert_eq!(a.layout_of(e).map(|l| (l.size, l.align)), Some((2, 1)));
    let big = a.types.intern(Ty::Named(def(&a, "Big"), vec![]));
    assert_eq!(a.layout_of(big).map(|l| (l.size, l.align)), Some((16, 8)));
    let pair = a.types.intern(Ty::Named(def(&a, "Pair"), vec![]));
    let tuple = a.types.intern(Ty::Tuple(vec![pair, u8]));
    assert_eq!(a.layout_of(tuple).map(|l| (l.size, l.align)), Some((12, 4)));
    assert_eq!(a.layout_of(named(&a, "Pair")).map(|l| l.size), Some(8));
}

/// A generic type nested in itself has the kind and the layout of what it
/// holds (R-310), and a generic type with an Affine argument is Affine
/// whether the substituted field types were interned elsewhere or not
/// (R-30: the walks read the fields under the arguments, W4-05 U1).
#[test]
fn kinds_and_layouts_read_generic_fields_under_their_arguments() {
    let mut a = check("pub struct Pair[T] { a: T }\npub struct Holder[T: ?Dup] { items: (T, U32) }\n");
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let i32 = a.types.int(IntKind::I32);
    let inner = a.types.intern(Ty::Named(def(&a, "Pair"), vec![i32]));
    let outer = a.types.intern(Ty::Named(def(&a, "Pair"), vec![inner]));
    let outer3 = a.types.intern(Ty::Named(def(&a, "Pair"), vec![outer]));
    for t in [inner, outer, outer3] {
        assert_eq!(a.kind_of(t), Some(Kind::Copy));
        assert_eq!(a.layout_of(t).map(|l| l.size), Some(4));
    }
    let f32 = a.types.float(FloatKind::F32);
    let buf = a.types.builtin(BuiltinTy::Buf, vec![f32]);
    let holder = a.types.intern(Ty::Named(def(&a, "Holder"), vec![buf]));
    let field = Ty::Tuple(vec![buf, a.types.int(IntKind::U32)]);
    assert_eq!(a.types.find(&field), None, "the field type is not interned");
    assert_eq!(a.kind_of(holder), Some(Kind::Affine));
    a.types.intern(field);
    assert_eq!(a.kind_of(holder), Some(Kind::Affine));
    assert!(crate::rt::needs_alloc_drop(&a, holder));
    let pair_of_str = a.types.builtin(BuiltinTy::Str, vec![]);
    let p1 = a.types.intern(Ty::Named(def(&a, "Pair"), vec![pair_of_str]));
    let p2 = a.types.intern(Ty::Named(def(&a, "Pair"), vec![p1]));
    assert!(crate::rt::needs_alloc_drop(&a, p2), "`Pair[Pair[Str]]` holds a `Str`");
    // A const argument is read as the length of a field.
    let mut a = check("pub struct R[const N: U32] { xs: [F32; N] }\n");
    let three = a.types.intern(Ty::ConstVal(3));
    let r = a.types.intern(Ty::Named(def(&a, "R"), vec![three]));
    assert_eq!(a.layout_of(r).map(|l| l.size), Some(12));
}

/// The kinds of generic types by their arguments (§4.6, R-30, R-310): the
/// tables of the break side of W4-05 U1 (`kcases`, the arguments through
/// aliases, const lengths, enums and function types; `xcases`, arguments
/// passed on to other generic types in another order). Each type is written
/// as an alias, whose type is the written one.
#[test]
fn kinds_of_generic_types_by_their_arguments() {
    let decls = "pub struct W[T: ?Dup] { a: T }\n\
        pub struct Pair2[A: ?Dup, B: ?Dup] { a: A, b: B }\n\
        pub struct Ring[T: ?Dup, const N: U32] { data: [T; N], head: U32 }\n\
        pub enum E[T: ?Dup] { A(T), B }\n\
        pub struct HT[T: ?Dup] { items: (T, U32) }\n\
        pub struct FH[T: ?Dup] { f: fn(T) -> T, n: I32 }\n\
        pub struct Mk[T: ?Dup, const N: U32] { w: W[[T; N]] }\n\
        type BB = Buf[F32]\ntype WB = W[Buf[F32]]\ntype WWB = W[WB]\ntype SS = Str\n\
        pub struct Holds { w: W[W[Buf[F32]]] }\n\
        pub struct HoldsS { w: Option[W[Str]] }\n\
        pub struct Sw[A: ?Dup, B: ?Dup] { a: W[B], b: W[(A, I32)] }\n\
        pub struct Inner[U: ?Dup] { u: U }\n\
        pub struct Outer[T: ?Dup] { i: Inner[W[T]] }\n\
        pub struct Outer2[T: ?Dup, U: ?Dup] { i: Inner[Sw[U, T]] }\n\
        pub struct Cn[T: ?Dup, const N: U32, const M: U32] { x: [[T; M]; N] }\n\
        pub struct CnW[T: ?Dup, const N: U32] { c: Cn[T, N, 2], d: Cn[W[T], 3, N] }\n\
        pub enum En[T: ?Dup, U: ?Dup] { L(U), R(W[T]), N }\n\
        pub struct Fnp[T: ?Dup] { f: fn(T) -> W[T], g: [fn(T); 2] }\n\
        pub struct Hold[T: ?Dup, const N: U32] { items: [(T, U32); N] }\n";
    // The types of each kind, `|` between them: kcases, then xcases.
    let table = [
        (
            Kind::Copy,
            "W[I32] | W[W[I32]] | W[(I32, F32)] | W[[I32; 4]] | Ring[I32, 4] | E[I32] | E[E[I32]] | \
            Option[W[I32]] | Result[W[I32], I32] | W[Option[I32]] | Pair2[I32, W[F32]] | HT[I32] | \
            FH[I32] | Mk[I32, 3] | FH[Buf[F32]] | Ring[Ring[I32, 2], 3] | Sw[I32, I32] | Outer[I32] | \
            Outer2[I32, I32] | Cn[I32, 2, 3] | CnW[I32, 4] | En[I32, I32] | Fnp[Buf[F32]] | \
            Hold[I32, 3]",
        ),
        (
            Kind::Shared,
            "W[SS] | W[Str] | W[W[Str]] | Option[W[Str]] | E[Str] | HT[Str] | Pair2[W[Str], I32] | \
            HoldsS | Mk[Str, 2] | Sw[Str, I32] | Outer[Str] | CnW[Str, 4] | \
            En[Option[En[I32, I32]], Str] | (Outer[Str], Outer2[I32, I32])",
        ),
        (
            Kind::Affine,
            "W[Buf[F32]] | W[W[Buf[F32]]] | Ring[Buf[F32], 4] | E[Buf[F32]] | Option[W[Buf[F32]]] | \
            Result[W[Buf[F32]], I32] | Pair2[I32, Buf[F32]] | Pair2[Pair2[I32, Buf[F32]], I32] | \
            HT[Buf[F32]] | W[(Buf[F32], U32)] | [W[Buf[F32]]; 2] | (W[Buf[F32]], I32) | \
            W[[Buf[F32]; 2]] | E[E[Buf[F32]]] | W[BB] | WB | WWB | W[WB] | Holds | Mk[Buf[F32], 2] | \
            Mk[W[Buf[F32]], 2] | W[E[W[Pair2[I32, Buf[F32]]]]] | Ring[W[Ring[Buf[F32], 2]], 3] | \
            Sw[Buf[F32], I32] | Sw[I32, Buf[F32]] | Outer[Buf[F32]] | Outer[W[Buf[F32]]] | \
            Outer2[Buf[F32], I32] | Outer2[I32, Buf[F32]] | Cn[Buf[F32], 2, 3] | CnW[Buf[F32], 4] | \
            En[Buf[F32], I32] | En[I32, Buf[F32]] | En[W[Buf[F32]], W[I32]] | Hold[Buf[F32], 3] | \
            Option[Outer2[W[Buf[F32]], I32]] | [Outer[Buf[F32]]; 2]",
        ),
    ];
    let table: Vec<(&str, Kind)> =
        table.iter().flat_map(|&(kind, ts)| ts.split('|').map(move |t| (t.trim(), kind))).collect();
    assert_eq!(table.len(), 48 + 27);
    let src: String = table.iter().enumerate().map(|(i, (t, _))| format!("type K{i} = {t}\n")).collect();
    let a = check(&format!("{decls}{src}"));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    for (i, (t, kind)) in table.iter().enumerate() {
        let DefKind::Alias(ty) = a.def(def(&a, &format!("K{i}"))).kind else { panic!("K{i}") };
        assert_eq!(a.kind_of(ty), Some(*kind), "{t}");
    }
}

/// A type that holds itself by value (an E0311 from W4-05 U2) has no kind
/// and no layout: the walks stop at the depth of `walk::Walk::enter`, not at a
/// signal (on the stack of a command, which its safety net reads).
#[test]
fn a_type_that_holds_itself_has_no_kind_and_no_layout() {
    let srcs =
        ["pub struct Node { v: I32, next: Node }\n", "pub struct W[T] { a: T }\npub struct Node { w: W[Node] }\n"];
    for src in srcs {
        let run = move || {
            let mut a = check(src);
            let node = a.types.intern(Ty::Named(def(&a, "Node"), vec![]));
            (a.kind_of(node), a.layout_of(node).is_none(), crate::rt::needs_alloc_drop(&a, node))
        };
        assert_eq!(onsa_diag::stack::spawn("t", run).unwrap().join().unwrap(), (None, true, false), "{src}");
    }
}

/// A chain whose every step holds the step before twice (R-313), of
/// declarations with no parameter (`A_k`) and with one (`G_k[T]`): each walk
/// finds what a declaration used with closed arguments holds once
/// (`walk::Known`), so the kind, the layout and the drops of the 64th have an
/// answer, where a walk that expands the chain stops past its steps at about
/// 20. A size past `U32` (from the 30th) is no layout (S-88), so the layout
/// is of the 29th.
#[test]
fn a_chain_that_doubles_each_step_has_its_answers() {
    let mut src = String::from("pub struct A0 { v: F32 }\npub struct G0[T] { v: T }\n");
    for k in 1..=64 {
        src.push_str(&format!("pub struct A{k} {{ x: A{0}, y: A{0} }}\n", k - 1));
        src.push_str(&format!("pub struct G{k}[T] {{ x: G{0}[T], y: G{0}[T] }}\n", k - 1));
    }
    let run = move || {
        let mut a = check(&src);
        assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
        let f32 = a.types.float(FloatKind::F32);
        for (k, name, args) in [(29, "A", vec![]), (29, "G", vec![f32]), (64, "A", vec![]), (64, "G", vec![f32])] {
            let d = def(&a, &format!("{name}{k}"));
            let t = a.types.intern(Ty::Named(d, args.clone()));
            assert_eq!(a.kind_of(t), Some(Kind::Copy), "{name}{k}");
            assert!(!crate::rt::needs_alloc_drop(&a, t));
            assert_eq!(a.known.drops.borrow().get(&(d, args)), Some(&Some(false)), "{name}{k}: the drops are found");
            assert_eq!(a.layout_of(t).map(|l| l.size), (k == 29).then_some(4 << 29), "{name}{k}");
        }
    };
    onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
}

/// A kind found near the steps of a walk is the same whichever declaration
/// is asked first (§18.1; W4-05 U2b/b): `Z` holds three expansions of about
/// a third of the steps each, `Q` holds `Z` and two more, so `Q` has its
/// answer only if `Z`'s is found with steps of its own.
#[test]
fn a_kind_near_the_steps_does_not_hang_on_the_order() {
    let mut src = String::from("pub struct G0[T] { v: T }\n");
    for k in 1..=13 {
        src.push_str(&format!("pub struct G{k}[T] {{ x: G{0}[Option[T]], y: G{0}[Option[T]] }}\n", k - 1));
    }
    src.push_str("pub struct Z { f0: G13[F32], f1: G13[I32], f2: G13[U8] }\n");
    src.push_str("pub struct Q { z: Z, g0: G13[Bool], g1: G13[I8] }\n");
    let kind_of_q = |z_first: bool| {
        let mut a = check(&src);
        let ty = |a: &mut Analysis, name| a.types.intern(Ty::Named(def(a, name), vec![]));
        let (z, q) = (ty(&mut a, "Z"), ty(&mut a, "Q"));
        if z_first {
            a.kind_of(z);
        }
        a.kind_of(q)
    };
    assert_eq!(kind_of_q(true), kind_of_q(false));
}

/// The answer of a declaration is found from the depth 0, whatever depth
/// the walk that asks it is at (W4-05 U2b/i3): a chain of 300 asked from its
/// top finds the kind of each (each step is `W` and a `P`, so the chain is
/// past the depth of a walk). A type that holds itself through a `Ptr` has
/// no answer as it is entered again, so its drops end at once.
#[test]
fn an_answer_does_not_hang_on_the_depth_it_is_asked_at() {
    let mut src = String::from("pub struct W[T] { t: T }\npub struct P0 { v: F32 }\n");
    for k in (1..=300).rev() {
        src.push_str(&format!("pub struct P{k} {{ w: W[P{}] }}\n", k - 1));
    }
    src.push_str("pub struct N { p: Ptr[N] }\n");
    let run = move || {
        let mut a = check(&src);
        let ty = |a: &mut Analysis, name| a.types.intern(Ty::Named(def(a, name), vec![]));
        let (p300, p20, n) = (ty(&mut a, "P300"), ty(&mut a, "P20"), ty(&mut a, "N"));
        assert_eq!((a.kind_of(p300), a.kind_of(p20)), (Some(Kind::Copy), Some(Kind::Copy)));
        assert!(!crate::rt::needs_alloc_drop(&a, n));
    };
    onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
}

/// A chain of 20 000 aliases (R-298) is lowered in the order of the
/// declarations, sinks first, each once: no lowering recurses through the
/// chain, so the check ends with no diagnostic (an alias adds nothing to the
/// depth, §4.4), on the stack of a command (`rules/common.md` 3.2: it ended by
/// a signal before W4-05 U2).
#[test]
fn a_chain_of_twenty_thousand_aliases_ends() {
    let mut src: String = (0..20_000).map(|i| format!("type A{i} = A{}\n", i + 1)).collect();
    src.push_str("type A20000 = F32\npub fn f(x: A0) -> A0 { x }\n");
    let run = move || codes(&check(&src));
    assert_eq!(onsa_diag::stack::spawn("t", run).unwrap().join().unwrap(), Vec::<Code>::new());
}

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
        deep = t.builtin(BuiltinTy::Option, vec![deep]);
    }
    assert!(!t.over_limit(deep));
    let deeper = t.builtin(BuiltinTy::Option, vec![deep]);
    assert!(t.over_limit(deeper) && t.depth(deeper) == crate::ty::TYPE_DEPTH_LIMIT + 1);
    let err = t.error();
    let with_err = t.intern(Ty::Tuple(vec![deeper, err]));
    assert!(t.has_error(with_err) && !t.has_error(deeper));
}

#[test]
fn generics_and_bounds() {
    let a = check(
        "pub fn clamp[T: PartialOrd](x: T, lo: T, hi: T) -> T { x }\npub struct Ring[T, const N: U32] { data: [T; N], head: U32 }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let clamp = a.def(def(&a, "clamp")).as_fn().unwrap();
    assert_eq!(clamp.generics.len(), 1);
    assert!(matches!(a.types.get(clamp.params[0].ty), Ty::Param(0)));
    let ring = a.def(def(&a, "Ring")).as_struct().unwrap();
    assert_eq!(ring.generics.len(), 2);
    match &ring.fields {
        crate::def::Fields::Named(fs) => assert!(matches!(a.types.get(fs[0].ty), Ty::Array(_, Len::Param(1)))),
        _ => panic!(),
    }
    let a = check("pub fn f[T: Iter](x: T) -> T { x }\n");
    assert_eq!(codes(&a), vec![Code::E0200]);
    let a = check("pub fn f[const N: I32]() {}\n");
    assert_eq!(codes(&a), vec![Code::E0200]);
}

#[test]
fn flow_namespace_items() {
    let a = check(
        "pub flow voice(@param(min: 0.0, max: 1.0, default: 0.5) gain: F32 at block, time: F32 at init) -> F32 at sample { 1.0 }\n\
         pub flow echo(x: F32 at sample, t: F32 at block) -> F32 at sample { x }\n\
         pub struct Poly { voices: [voice.State; 4], p: voice.Params }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let voice = a.def(def(&a, "voice")).as_flow().unwrap();
    let names: Vec<&str> = voice.members.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        vec![
            "State",
            "Config",
            "Params",
            "Out",
            "SIZE",
            "BULK_SIZE",
            "init",
            "reset",
            "process",
            "render",
            "params_default"
        ]
    );
    let echo = a.def(def(&a, "echo")).as_flow().unwrap();
    let names: Vec<&str> = echo.members.iter().map(|(n, _)| n.as_str()).collect();
    assert!(names.contains(&"process_inplace") && !names.contains(&"params_default"));
    let render = echo.members.iter().find(|(n, _)| n == "render").map(|(_, d)| a.def(*d).as_fn().unwrap()).unwrap();
    assert!(render.effects.alloc);
    assert_eq!(
        render.params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(),
        vec!["cfg", "params", "x", "sample_rate"]
    );
    let process = voice.members.iter().find(|(n, _)| n == "process").map(|(_, d)| a.def(*d).as_fn().unwrap()).unwrap();
    assert_eq!(process.params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), vec!["s", "params", "out"]);
    assert!(process.rt);
    assert_eq!(voice.inputs[0].param.as_ref().unwrap().default, Some(0.5));
}

#[test]
fn name_diagnostics() {
    let a = check("pub fn f(x: Missing) {}\n");
    assert_eq!(codes(&a), vec![Code::E0302]);
    let a = check("pub fn f() {}\npub fn f() {}\n");
    assert_eq!(codes(&a), vec![Code::E0304]);
    let a = check("pub flow v(x: F32 at sample) -> F32 at sample { x }\npub fn v() {}\n");
    assert_eq!(codes(&a), vec![Code::E0305]);
    let a = check("test \"a\" { assert true }\ntest \"a\" { assert true }\n");
    assert_eq!(codes(&a), vec![Code::E0306]);
    let a = check("pub fn f(x: Str) uses {Fs} {}\n");
    assert_eq!(codes(&a), vec![Code::E0302]);
    let a = analyze(&pkg(&[("a", "use b.{g}\npub fn f() {}\n"), ("b", "use a.{f}\npub fn g() {}\n")]));
    assert_eq!(codes(&a), vec![Code::E0310]);
    // A `priv` item is within its module (§15.1, S-36).
    let a =
        analyze(&pkg(&[("a", "priv fn hidden() {}\npub fn shown() {}\n"), ("b", "use a.{hidden}\nuse a.{shown}\n")]));
    assert_eq!(codes(&a), vec![Code::E0303]);
    let a = analyze(&pkg(&[("a", "use a.{x}\n")]));
    assert_eq!(codes(&a), vec![Code::E0302]);
}

#[test]
fn impl_registers_associated_items() {
    let a = check(
        "pub struct P { x: F32 }\nimpl P {\n  pub fn new(x: F32) -> P { P { x: x } }\n  pub rt fn norm(self) -> F32 { self.x }\n  const ZERO: F32 = 0.0\n}\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let p = def(&a, "P");
    let assoc = &a.modules.assoc[&p];
    assert_eq!(assoc.len(), 3);
    let norm = a.def(assoc["norm"]).as_fn().unwrap();
    assert_eq!(norm.self_mode, Some(onsa_syntax::ast::Mode::Borrow));
    assert!(norm.rt);
    assert!(matches!(a.def(assoc["ZERO"]).kind, DefKind::Const(_)));
}

/// R-88 (1): `flatten` lists the dependencies first, depth-first, the package
/// last, and a package that several packages depend on (the same value) once,
/// where it is first reached.
#[test]
fn flatten_lists_a_shared_package_once() {
    use std::sync::Arc;
    let leaf = |name: &str| Arc::new(Package::new(name, Vec::new(), Vec::new()));
    let s = leaf("s");
    let x = leaf("x");
    let a = Arc::new(Package::new("a", Vec::new(), vec![s.clone(), x.clone()]));
    let b = Arc::new(Package::new("b", Vec::new(), vec![x.clone(), s.clone()]));
    let root = Package::new("t", Vec::new(), vec![a, s.clone(), b]);
    let names: Vec<&str> = crate::flatten(&root).iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, ["s", "x", "a", "b", "t"]);
}

/// R-88 (1): packages are the same when they are the same value, not when
/// their names are: two values named alike are two packages.
#[test]
fn flatten_tells_packages_apart_by_value_not_by_name() {
    use std::sync::Arc;
    let one = Arc::new(Package::new("s", Vec::new(), Vec::new()));
    let other = Arc::new(Package::new("s", Vec::new(), Vec::new()));
    let root = Package::new("t", Vec::new(), vec![one.clone(), other, one]);
    let flat = crate::flatten(&root);
    assert_eq!(flat.len(), 3);
    assert!(!std::ptr::eq(flat[0], flat[1]));
}

/// The role, not the name, marks the embedded std (R-88 (1)): a package
/// named `std` that depends on it is an ordinary one.
#[test]
fn the_role_marks_std() {
    let std = std::sync::Arc::new(Package::std(Vec::new()));
    let a = crate::analyze(&Package::new(crate::STD_PACKAGE, Vec::new(), vec![std]));
    assert_eq!(a.modules.names, [crate::STD_PACKAGE, crate::STD_PACKAGE]);
    assert!(a.modules.is_std(a.modules.roots[0]));
    assert!(!a.modules.is_std(a.modules.roots[1]));
}

/// S-666 (until it is decided): a `use` takes the module of a directory with
/// no file of its own (`a` and `a.b` of `a/b/c.onsa` alone) like a module with
/// no items, and a path through it takes what is under it.
#[test]
fn a_use_takes_the_module_of_a_directory_only_and_goes_through_it() {
    let c = ("a.b.c", "pub fn f() -> I32 {\n  1\n}\n");
    for head in ["use a\n", "use a.{b}\n", "use a.b\n"] {
        let a = analyze(&pkg(&[c, ("main", head)]));
        assert_eq!(codes(&a), [], "{head}: {:?}", a.diagnostics);
    }
    let a = analyze(&pkg(&[c, ("main", "use a.b.c.{f}\n\npub fn g() -> I32 {\n  f()\n}\n")]));
    assert_eq!(codes(&a), [], "{:?}", a.diagnostics);
}

/// A package of the modules `files`, their files numbered from `first`.
fn pkg_at(name: &str, first: u32, files: &[(&str, &str)], deps: Vec<std::sync::Arc<Package>>) -> Package {
    let mut p = pkg(files);
    for (k, m) in p.modules.iter_mut().enumerate() {
        m.file = FileId(first + k as u32);
        m.parsed = onsa_syntax::parse(m.file, &m.text);
    }
    Package::new(name, p.modules, deps)
}

/// R-39, R-88: a body names another module or a package through a `use`
/// alone. The E0302 of a head that a `use` could name has the candidate that
/// adds that `use` (after the last `use`, or before the first item), unless
/// it closes a cycle of imports; a package the package does not depend on is
/// no head (§15.1).
#[test]
fn a_body_names_modules_and_packages_through_a_use_alone() {
    use std::sync::Arc;
    let s = Arc::new(pkg_at("s", 10, &[("m", "pub fn f() -> I32 {\n  1\n}\n")], Vec::new()));
    let mid = Arc::new(pkg_at("mid", 20, &[("x", "pub fn g() -> I32 {\n  1\n}\n")], vec![s]));
    let user = |main: &str| analyze(&pkg_at("t", 0, &[("main", main)], vec![mid.clone()]));
    let one = |a: &Analysis| -> (String, Vec<(u32, String)>) {
        assert_eq!(codes(a), [Code::E0302], "{:?}", a.diagnostics);
        let d = &a.diagnostics[0];
        let edits = d.fixes.iter().flat_map(|f| f.edits()).map(|e| (e.span.start, e.replace.clone())).collect();
        (d.found.clone().unwrap_or_default(), edits)
    };
    let body = "pub fn h() -> I32 {\n  NAME\n}\n";
    let a = user(&body.replace("NAME", "s.m.f()"));
    assert_eq!(one(&a), ("s".into(), Vec::new()));
    let a = user(&body.replace("NAME", "mid.x.g()"));
    assert_eq!(one(&a), ("mid".into(), vec![(0, "use mid\n".into())]));
    let a = user(&format!("use mid.x.{{g}}\n\n{}", body.replace("NAME", "mid.x.g()")));
    assert_eq!(one(&a), ("mid".into(), vec![(13, "\nuse mid".into())]));
    let fixed = user(&format!("use mid\n\n{}", body.replace("NAME", "mid.x.g()")));
    assert_eq!(codes(&fixed), [], "{:?}", fixed.diagnostics);
    // `b` names `a`, which imports `b`: `use a` in `b` would close a cycle.
    let b = ("b", "pub fn g() -> I32 {\n  a.f()\n}\n");
    for (a_src, fixes) in [("use b\n\npub fn f() -> I32 {\n  1\n}\n", 0), ("pub fn f() -> I32 {\n  1\n}\n", 1)] {
        let an = analyze(&pkg(&[("a", a_src), b]));
        assert_eq!(codes(&an), [Code::E0302], "{:?}", an.diagnostics);
        assert_eq!(an.diagnostics[0].fixes.len(), fixes, "{a_src}");
    }
}

/// R-39: the candidate that adds `use X` is for a path with no `use`, where a
/// member follows the head (`util.f()`, `util.SIZE`), and not when the rest is
/// not found (`util.nosuch`, R-268: applying it would leave an E0302). A module
/// or a package alone at the place of a type, a value, a callee, the type of
/// an `impl` or an array length is not fixed by the `use`: E0302 with none
/// (W4-03 U2b/b: `j_type_std`, `j_value_util`, `j_call_std`, `j_impl_util`,
/// `j_arr_len`, `j_field_util`, and a call of the name of the module itself).
#[test]
fn the_candidate_of_a_use_needs_a_member_after_the_head() {
    let util = ("util", "pub const SIZE: U32 = 4\n\npub fn double(x: I32) -> I32 {\n  x * 2\n}\n");
    let cases = [
        ("pub fn k(x: util) -> I32 {\n  1\n}\n", 0),
        ("pub fn k() -> I32 {\n  let x = util\n  1\n}\n", 0),
        ("pub fn k() -> I32 {\n  util()\n}\n", 0),
        ("impl util {\n}\n", 0),
        ("pub fn k(a: [I32; util]) -> I32 {\n  1\n}\n", 0),
        ("pub fn k() -> I32 {\n  main(1)\n}\n", 0),
        ("pub fn k() -> I32 {\n  util.nosuch\n}\n", 0),
        ("pub fn k() -> I32 {\n  util.double(2)\n}\n", 1),
        ("pub fn k() -> U32 {\n  util.SIZE\n}\n", 1),
        ("pub fn k(a: [I32; util.SIZE]) -> I32 {\n  1\n}\n", 1),
    ];
    for (main, fixes) in cases {
        let a = analyze(&pkg(&[("main", main), util]));
        let e0302: Vec<_> = a.diagnostics.iter().filter(|d| d.code == Code::E0302).collect();
        assert_eq!(e0302.len(), 1, "{main}: {:?}", a.diagnostics);
        assert_eq!(e0302[0].fixes.len(), fixes, "{main}: {:?}", e0302[0]);
    }
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

/// A length reads a constant of the type `U32` alone (§4.5, E0401), the
/// constant of the module or a member of an `impl`, of its type written or
/// through an alias, written before or after what reads it: the constants
/// are lowered in the order of the declarations (W4-05 U2/i3, B-1).
#[test]
fn a_length_reads_the_type_of_a_constant_wherever_it_is_declared() {
    let readers = [
        "type A = [F32; R]",
        "const C: [U8; R] = [0, 0, 0]",
        "struct Q { a: [F32; R] }",
        "fn f(a: [F32; R]) -> I32 { 0 }",
    ];
    for reader in readers {
        for member in [false, true] {
            for ty in ["U32", "I32", "J"] {
                for after in [false, true] {
                    let (decl, name) = match member {
                        false => (format!("const K: {ty} = 3"), "K"),
                        true => (format!("struct S {{ x: I32 }}\nimpl S {{ const K: {ty} = 3 }}"), "S.K"),
                    };
                    let reader = reader.replace('R', name);
                    let (a, b) = if after { (decl, reader) } else { (reader, decl) };
                    let src = format!("type J = I32\n{a}\n{b}\n");
                    let want = if ty == "U32" { vec![] } else { vec![Code::E0401] };
                    assert_eq!(codes(&check(&src)), want, "{src}");
                }
            }
        }
    }
}

/// A type of a generated program; `W` is a form of its parts at the `#`.
#[derive(Clone)]
enum G {
    I,
    P(usize),
    Al(usize),
    D(usize, Vec<G>),
    W(&'static str, Vec<G>),
}

impl G {
    fn show(&self) -> String {
        match self {
            G::I => "I32".into(),
            G::P(i) => format!("T{i}"),
            G::Al(i) => format!("A{i}"),
            G::D(d, args) if args.is_empty() => format!("D{d}"),
            G::D(d, args) => format!("D{d}[{}]", args.iter().map(G::show).collect::<Vec<_>>().join(", ")),
            G::W(f, ts) => ts.iter().fold(f.to_string(), |s, t| s.replacen('#', &t.show(), 1)),
        }
    }

    fn subst(&self, env: &[G]) -> G {
        match self {
            G::P(i) => env[*i].clone(),
            G::D(d, args) => G::D(*d, args.iter().map(|a| a.subst(env)).collect()),
            G::W(f, ts) => G::W(f, ts.iter().map(|a| a.subst(env)).collect()),
            t => t.clone(),
        }
    }

    /// The declarations and aliases held as values (§4.4), or anywhere.
    fn held(&self, anywhere: bool, out: &mut Vec<G>) {
        match self {
            G::D(_, args) if anywhere => args.iter().for_each(|a| a.held(true, out)),
            G::D(..) | G::Al(_) => out.push(self.clone()),
            G::W(f, ts) if anywhere || f.starts_with(['O', '(', '[']) => ts.iter().for_each(|t| t.held(anywhere, out)),
            _ => {}
        }
    }
}

/// The random programs of [`G`]: declarations of their `arity` and `m`
/// aliases.
struct Gen {
    seed: u64,
    m: usize,
    arity: Vec<usize>,
}

impl Gen {
    fn rng(&mut self, n: usize) -> usize {
        self.seed = self.seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.seed >> 33) as usize % n
    }

    /// A type `depth` deep in a declaration of `np` parameters.
    fn ty(&mut self, depth: u32, np: usize) -> G {
        let (c, m) = (self.rng(100), self.m);
        match c {
            _ if depth >= 3 && np > 0 && c < 40 => G::P(self.rng(np)),
            _ if depth >= 3 && m > 0 && c < 70 => G::Al(self.rng(m)),
            _ if depth >= 3 || c < 8 => G::I,
            _ if c < 20 && np > 0 => G::P(self.rng(np)),
            _ if c < 38 && m > 0 => G::Al(self.rng(m)),
            _ if c < 60 => {
                let d = self.rng(self.arity.len());
                G::D(d, (0..self.arity[d]).map(|_| self.ty(depth + 1, np)).collect())
            }
            _ => {
                let forms = ["Array[#]", "Option[#]", "(#, #)", "[#; 2]", "fn(#) -> I32"];
                let f = forms[self.rng(forms.len())];
                G::W(f, (0..f.matches('#').count()).map(|_| self.ty(depth + 1, np)).collect())
            }
        }
    }
}

/// The E0311 of random programs of generic structs and enums and aliases
/// against an oracle that expands the arguments: a declaration is in a cycle
/// when it holds itself as a value, through its arguments read, and an alias
/// also when it names itself anywhere (§4.4, §18.1; W4-05 U2/b).
#[test]
fn the_cycles_of_random_generic_declarations_are_those_the_arguments_expand_to() {
    let (mut g, mut cycles) = (Gen { seed: 0x5eed, m: 0, arity: Vec::new() }, 0);
    for _ in 0..80 {
        let n = 1 + g.rng(4);
        g.m = g.rng(4);
        g.arity = (0..n).map(|_| [0, 0, 1, 1, 2][g.rng(5)]).collect();
        let decls: Vec<(bool, Vec<G>)> =
            (0..n).map(|d| (g.rng(2) == 0, (0..1 + g.rng(3)).map(|_| g.ty(0, g.arity[d])).collect())).collect();
        let aliases: Vec<G> = (0..g.m).map(|_| g.ty(0, 0)).collect();
        // The lines, shuffled: (declaration or alias, its index, its text).
        let mut lines: Vec<(bool, usize, String)> = Vec::new();
        for (d, (is_struct, fs)) in decls.iter().enumerate() {
            let gs = G::D(d, (0..g.arity[d]).map(G::P).collect()).show();
            let (kw, field) = if *is_struct { ("struct", "f#: #") } else { ("enum", "V#(#)") };
            let fs: Vec<String> =
                (fs.iter().enumerate()).map(|(j, f)| G::W(field, vec![G::P(j), f.clone()]).show()).collect();
            lines.push((true, d, format!("{kw} {gs} {{ {} }}", fs.join(", "))));
        }
        lines.extend(aliases.iter().enumerate().map(|(i, t)| (false, i, format!("type A{i} = {}", t.show()))));
        for i in (1..lines.len()).rev() {
            lines.swap(i, g.rng(i + 1));
        }
        // The oracle: whether `start` reaches a declaration of its own name.
        let reaches = |start: G, anywhere: bool| {
            let name = |g: &G| g.show().split('[').next().map(str::to_string);
            let (mut seen, mut queue) = (HashSet::new(), std::collections::VecDeque::from([start.clone()]));
            while let Some(cur) = queue.pop_front() {
                let shown = cur.show();
                if seen.len() > 3000 || shown.len() > 400 || !seen.insert(shown) {
                    continue;
                }
                let (body, env) = match &cur {
                    G::Al(i) => (vec![aliases[*i].clone()], Vec::new()),
                    G::D(d, args) => (decls[*d].1.clone(), args.clone()),
                    _ => unreachable!(),
                };
                let mut out = Vec::new();
                body.iter().for_each(|f| f.subst(&env).held(anywhere, &mut out));
                out.retain(|g| !anywhere || matches!(g, G::Al(_)));
                if out.iter().any(|g| name(g) == name(&start)) {
                    return true;
                }
                queue.extend(out);
            }
            false
        };
        let want: BTreeSet<usize> = (lines.iter().enumerate())
            .filter(|(_, (decl, i, _))| match decl {
                true => reaches(G::D(*i, vec![G::I; g.arity[*i]]), false),
                false => reaches(G::Al(*i), false) || reaches(G::Al(*i), true),
            })
            .map(|(k, _)| k + 1)
            .collect();
        let src: String = lines.iter().map(|l| format!("{}\n", l.2)).collect();
        let a = check(&src);
        let line = |s: onsa_diag::Span| src[..s.start as usize].matches('\n').count() + 1;
        let mut got = BTreeSet::new();
        for d in &a.diagnostics {
            assert_eq!(d.code, Code::E0311, "{src}{:?}", a.diagnostics);
            got.insert(line(d.span));
            got.extend(d.notes.iter().filter_map(|n| n.span).map(line));
        }
        assert_eq!(got, want, "{src}");
        cycles += !want.is_empty() as u32;
    }
    assert!((10..80).contains(&cycles), "{cycles} of 80 with a cycle");
}

/// What the order of the declarations reports (§4.4, §18.1; W4-05 U2/i3):
/// a constant at the position of a type is an E0308 and no edge; a cycle in
/// one module stays an E0311 when an alias joins it to a cycle the E0310 of
/// the imports reports; the arguments of a type whose parameters are an
/// E0304 are not read; the E0310 names no other name of its own `use` (R-315).
#[test]
fn the_order_of_the_declarations_reports_each_cycle_once() {
    for src in ["const K: A = 1\ntype A = K\n", "const K: S = 1\nstruct S { k: K }\n"] {
        assert!(codes(&check(src)).contains(&Code::E0308) && !codes(&check(src)).contains(&Code::E0311), "{src}");
    }
    for (head, w) in
        [("W[T, T] { a: T }", "W[S, I32]"), ("W[Option] { a: Option }", "W[S]"), ("W[S] { a: S }", "W[I32]")]
    {
        let src = format!("struct {head}\nstruct S {{ w: {w} }}\n");
        assert_eq!(codes(&check(&src)), vec![Code::E0304], "{src}");
    }
    let a = analyze(&pkg(&[
        ("a", "use b.{B}\npub type X = (B, Array[X])\npub struct A { x: X }\n"),
        ("b", "use a.{A}\npub struct B { a: A }\n"),
    ]));
    assert_eq!(codes(&a), vec![Code::E0310, Code::E0311]);
    let a = analyze(&pkg(&[
        ("a", "use b.{g, h}\n\npub fn f() -> I32 { g() + h() }\n"),
        ("b", "use a.{f}\nuse a\n\npub fn g() -> I32 { f() }\npub fn h() -> I32 { a.f() }\n"),
    ]));
    let [d] = &a.diagnostics[..] else { panic!("{:?}", a.diagnostics) };
    let at: Vec<FileId> = d.notes.iter().filter_map(|n| n.span).map(|s| s.file).collect();
    assert_eq!((d.code, at), (Code::E0310, vec![FileId(1), FileId(1)]));
}
