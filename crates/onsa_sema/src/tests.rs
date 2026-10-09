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
            path: path.to_string(),
            file: FileId(i as u32),
            text: text.to_string(),
            parsed: onsa_syntax::parse(FileId(i as u32), text),
        })
        .collect();
    Package { name: "t".into(), modules, deps: Vec::new(), is_std: false }
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
         pub enum E { A(P), B(S) }\npub struct T(F32)\npub flow f(x: F32 at sample) -> F32 at sample { x }\n\
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
    assert_eq!(codes(&a), vec![Code::E0200]);
    let a = analyze(&pkg(&[("a", "use b.{g}\npub fn f() {}\n"), ("b", "use a.{f}\npub fn g() {}\n")]));
    assert_eq!(codes(&a), vec![Code::E0310]);
    let a = analyze(&pkg(&[("a", "fn hidden() {}\npub(pkg) fn pk() {}\n"), ("b", "use a.{hidden}\nuse a.{pk}\n")]));
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
