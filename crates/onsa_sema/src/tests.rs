//! Unit tests for T2-2 .. T2-4: kinds, layouts, bounds, and name diagnostics.

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
