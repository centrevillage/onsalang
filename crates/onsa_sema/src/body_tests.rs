//! Unit tests for the body checker (T2-5 .. T2-7, T2-10, T2-11).

use onsa_diag::{Code, FileId};

use crate::body::{LocalKind, Target};
use crate::consteval::ConstValue;
use crate::ty::{BuiltinTy, FloatKind, IntKind, Len, Ty};
use crate::{Analysis, Module, Package, analyze};

fn check(src: &str) -> Analysis {
    let modules = vec![Module {
        path: "main".into(),
        file: FileId(0),
        text: src.to_string(),
        parsed: onsa_syntax::parse(FileId(0), src),
    }];
    analyze(&Package { name: "t".into(), modules, deps: Vec::new(), is_std: false })
}

fn codes(src: &str) -> Vec<Code> {
    let a = check(src);
    let mut v: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
    v.sort();
    v
}

fn ok(src: &str) -> Analysis {
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "unexpected diagnostics: {:?}", a.diagnostics);
    a
}

fn def(a: &Analysis, name: &str) -> crate::DefId {
    crate::DefId(a.defs.iter().position(|d| d.name == name).unwrap_or_else(|| panic!("no def {name}")) as u32)
}

#[test]
fn literal_resolved_by_later_statement() {
    let a = ok("pub fn f(xs: [F32; 4]) -> F32 {\n  var acc = 0.0\n  for i in 0..4 { acc = acc + xs[i] }\n  acc\n}\n");
    let body = &a.bodies[&def(&a, "f")];
    let acc = body.locals.iter().find(|l| l.name == "acc").unwrap();
    assert!(matches!(a.types.get(acc.ty), Ty::Float(FloatKind::F32)));
    assert_eq!(acc.kind, LocalKind::Var);
    assert!(acc.mutable);
    let i = body.locals.iter().find(|l| l.name == "i").unwrap();
    assert!(matches!(a.types.get(i.ty), Ty::Int(IntKind::U32)));
    assert!(body.complete);
}

#[test]
fn unresolved_float_literal_is_e0405() {
    // S-22: floats have no default (§2.4); integers default to I32 (below).
    assert_eq!(codes("pub fn f() {\n  var acc = 0.0\n}\n"), vec![Code::E0405]);
    assert_eq!(codes("pub fn f() {\n  let a = 1.0\n}\n"), vec![Code::E0405]);
}

#[test]
fn unresolved_integer_literal_defaults_to_i32() {
    // S-22 (§2.4, §4.7): applied at the end of the body only.
    assert_eq!(codes("pub fn f() {\n  let a = 1\n}\n"), vec![]);
    assert_eq!(codes("test \"t\" { assert 1 == 1 }\n"), vec![]);
    assert_eq!(codes("pub fn f() {\n  for i in 0..4 {\n  }\n}\n"), vec![]);
    let a = check("pub fn f() {\n  let a = 1\n}\n");
    let body = a.bodies.values().next().unwrap();
    let int = body.locals.iter().find(|l| l.name == "a").unwrap().ty;
    assert!(matches!(a.types.get(int), Ty::Int(IntKind::I32)));
    // Out of the I32 range: E0408 with the annotation hint.
    let a = check("pub fn f() {\n  let x = 3_000_000_000\n}\n");
    assert_eq!(a.diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(), vec![Code::E0408]);
    assert!(a.diagnostics[0].message.contains("annotation"), "{}", a.diagnostics[0].message);
    // Mid-body operations still need the type (E0420): the default is not eager.
    assert_eq!(codes("pub fn f() -> F32 {\n  0.round_f32()\n}\n"), vec![Code::E0420]);
    assert_eq!(codes("pub fn f() -> F32 {\n  var acc = 0.0\n  acc.round_f32()\n}\n"), vec![Code::E0420]);
}

#[test]
fn literal_ranges() {
    assert_eq!(codes("pub fn f() -> U8 {\n  let x: U8 = 300\n  x\n}\n"), vec![Code::E0408]);
    ok("pub fn f() -> I8 {\n  let x: I8 = -128\n  x\n}\n");
    assert_eq!(codes("pub fn f() -> I8 {\n  let x: I8 = -129\n  x\n}\n"), vec![Code::E0408]);
    assert_eq!(codes("pub fn f() -> U32 {\n  let x: U32 = -1\n  x\n}\n"), vec![Code::E0401]);
}

#[test]
fn operations_need_known_types() {
    assert_eq!(
        codes("pub fn f(x: F32) -> F32 {\n  var acc = 0.0\n  let r = acc.round_f32()\n  acc = x\n  r\n}\n"),
        vec![Code::E0420]
    );
    assert_eq!(codes("pub fn f() -> U32 {\n  let xs = []\n  1\n}\n"), vec![Code::E0420]);
    assert_eq!(codes("pub fn f() -> I64 {\n  1 as I64\n}\n"), vec![Code::E0420]);
    ok("pub fn f() -> [F32; 0] {\n  let xs: [F32; 0] = []\n  xs\n}\n");
}

#[test]
fn generics_from_arguments_and_expected_type() {
    let src = "pub fn id[T](x: T) -> T { x }\npub fn parse[T](s: Str) -> T { parse(s) }\n";
    let a = ok(&format!("{src}pub fn g() -> I32 {{\n  let n: I32 = parse(\"3\")\n  id(n)\n}}\n"));
    let body = &a.bodies[&def(&a, "g")];
    assert_eq!(body.instances.len(), 2);
    let i32 = a.types.find(&Ty::Int(IntKind::I32)).unwrap();
    assert!(body.instances.iter().all(|i| i.args == vec![i32]));
    assert_eq!(codes(&format!("{src}pub fn g() -> I32 {{\n  let n = parse(\"3\")\n  n\n}}\n")), vec![Code::E0406]);
    assert_eq!(
        codes(
            "pub fn largest[T: Ord](a: T, b: T) -> T { if a < b { b } else { a } }\npub fn g() -> F32 { largest(1.0, 2.0) }\n"
        ),
        vec![Code::E0416]
    );
    ok("pub fn largest[T: Ord](a: T, b: T) -> T { if a < b { b } else { a } }\npub fn g() -> I32 { largest(1, 2) }\n");
    // Operators inside generic bodies need the bound.
    assert_eq!(codes("pub fn f[T](a: T, b: T) -> Bool { a < b }\n"), vec![Code::E0401]);
    ok("pub fn f[T: PartialOrd](a: T, b: T) -> Bool { a < b }\n");
    ok("pub fn f[T: Num](a: T, b: T) -> T { a + b }\n");
}

#[test]
fn const_generics_and_arrays() {
    let a = ok(
        "pub fn sum[const N: U32](xs: [F32; N]) -> F32 {\n  var acc: F32 = 0.0\n  for i in 0..N { acc = acc + xs[i] }\n  acc\n}\npub fn g(ys: [F32; 4]) -> F32 { sum(ys) }\n",
    );
    let body = &a.bodies[&def(&a, "g")];
    assert_eq!(body.instances.len(), 1);
    assert!(matches!(a.types.get(body.instances[0].args[0]), Ty::ConstVal(4)));
    let a = ok("const N: U32 = 8\npub fn g() -> [U32; 8] { [0; N] }\n");
    let body = &a.bodies[&def(&a, "g")];
    assert_eq!(body.repeats.len(), 1);
    let _ = a;
}

#[test]
fn closures_take_types_from_the_expected_function_type() {
    let a =
        ok("pub fn apply(f: fn(U32) -> U32) -> U32 { f(1) }\npub fn g(k: U32) -> U32 {\n  apply(fn(i) { i + k })\n}\n");
    let body = &a.bodies[&def(&a, "g")];
    let (closure, captures) = body.captures.iter().next().unwrap();
    assert_eq!(captures.len(), 1);
    assert_eq!(body.locals[captures[0].0 as usize].name, "k");
    assert!(matches!(a.types.get(body.expr_types[closure]), Ty::Fn(_)));
    assert_eq!(codes("pub fn g() -> U32 {\n  let f = fn(i) { i }\n  1\n}\n"), vec![Code::E0420]);
    ok("pub fn g() -> U32 {\n  let f = fn(i: U32) -> U32 { i }\n  f(1)\n}\n");
    assert_eq!(
        codes("pub fn apply(f: fn(U32) -> U32) -> U32 { f(1) }\npub fn g() -> U32 { apply(fn(i, j) { i }) }\n"),
        vec![Code::E0412]
    );
}

#[test]
fn shadowing_rules() {
    ok(
        "pub fn f(xs: [F32; 4]) -> F32 {\n  var s: F32 = 0.0\n  for i in 0..4 { s = s + xs[i] }\n  for i in 0..4 { s = s + xs[i] }\n  s\n}\n",
    );
    assert_eq!(codes("pub fn f(xs: [F32; 4]) {\n  for i in 0..4 { let i = 1 }\n}\n"), vec![Code::E0304]);
    assert_eq!(codes("pub fn f(x: I32) -> I32 {\n  let x = x + 1\n  x\n}\n"), vec![Code::E0304]);
    ok(
        "pub fn f(o: Option[U8]) -> U8 {\n  match o {\n    Some(x) => x,\n    None => 0,\n  }\n}\npub fn g(o: Option[U8]) -> U8 {\n  let a = match o { Some(x) => x, None => 0 }\n  let b = match o { Some(x) => x, None => 1 }\n  a + b\n}\n",
    );
}

#[test]
fn match_exhaustiveness() {
    let shapes = "pub enum Shape { Circle(F32), Rect(F32, F32) }\n";
    assert_eq!(
        codes(&format!("{shapes}pub fn f(s: Shape) -> F32 {{ match s {{ Shape.Circle(r) => r }} }}\n")),
        vec![Code::E0501]
    );
    ok(&format!(
        "{shapes}pub fn f(s: Shape) -> F32 {{ match s {{ Shape.Circle(r) => r, Shape.Rect(w, h) => w * h }} }}\n"
    ));
    ok(&format!("{shapes}pub fn f(s: Shape) -> F32 {{ match s {{ Shape.Circle(r) => r, _ => 0.0 }} }}\n"));
    // Guards do not count.
    assert_eq!(codes("pub fn f(b: Bool) -> U8 { match b { true => 1, false if b => 0 } }\n"), vec![Code::E0501]);
    // Literals need a wildcard.
    assert_eq!(codes("pub fn f(n: U8) -> U8 { match n { 0 => 1, 1 => 2 } }\n"), vec![Code::E0501]);
    ok("pub fn f(n: U8) -> U8 { match n { 0 => 1, _ => 2 } }\n");
    ok(
        "pub fn f(t: (Bool, Option[U8])) -> U8 { match t { (true, _) => 1, (false, Some(n)) => n, (false, None) => 0 } }\n",
    );
    assert_eq!(
        codes("pub fn f(t: (Bool, Option[U8])) -> U8 { match t { (true, _) => 1, (false, Some(n)) => n } }\n"),
        vec![Code::E0501]
    );
    assert_eq!(codes("pub fn f(o: Option[U8]) -> U8 { let Some(n) = o\n n }\n"), vec![Code::E0502]);
    ok("pub struct P { x: F32, y: F32 }\npub fn f(p: P) -> F32 { let P { x: a, y: _ } = p\n a }\n");
}

#[test]
fn conversions() {
    ok(
        "pub fn f(i: I32, x: F64, y: F32, n: U8) -> F64 {\n  let a = i as I64\n  let b = x.round_f32()\n  let c = y.trunc_i32_sat()\n  let d = y.to_bits()\n  let e = F32.from_bits(d)\n  let g = n as F32\n  (i as F64) + x\n}\n",
    );
    assert_eq!(codes("pub fn f(x: I64) -> I32 { x as I32 }\n"), vec![Code::E0411]);
    assert_eq!(codes("pub fn f(x: I64) -> F64 { x as F64 }\n"), vec![Code::E0411]);
    assert_eq!(codes("pub fn f(x: F32) -> I32 { x as I32 }\n"), vec![Code::E0411]);
    let src = "pub fn f(x: F32) -> I32 { x as I32 }\n";
    let a = check(src);
    let d = &a.diagnostics[0];
    assert!((0..d.fixes.len()).any(|k| crate::fixed_region(src, d, k) == "x.trunc_i32()"));
}

#[test]
fn operators_and_groups() {
    ok("pub fn f(a: U32, b: U32, p: U32) -> U32 { ((a +% 1) % 8) + (b << 2) + (p & 3) }\n");
    assert_eq!(codes("pub fn f(a: F32) -> F32 { a +% 1.0 }\n"), vec![Code::E0401]);
    assert_eq!(codes("pub fn f(a: F32, b: U32) -> F32 { a + b }\n"), vec![Code::E0401]);
    ok("pub fn f(a: F32, b: F32) -> Bool { (a == b) && !(a < b) }\n");
    assert_eq!(codes("pub fn f(a: Bool) -> Bool { a < a }\n"), vec![Code::E0401]);
    ok("pub fn f(a: U32) -> U32 { !a }\n");
    assert_eq!(codes("pub fn f(a: U32) -> U32 { -a }\n"), vec![Code::E0401]);
    assert_eq!(codes("pub fn f() -> U32 { -1 }\n"), vec![Code::E0401]);
    ok("@derive(PartialEq)\npub struct P { x: F32 }\npub fn f(a: P, b: P) -> Bool { a == b }\n");
    assert_eq!(codes("pub struct P { x: F32 }\npub fn f(a: P, b: P) -> Bool { a == b }\n"), vec![Code::E0401]);
    ok("pub fn f(a: Option[U8], b: Option[U8]) -> Bool { a == b }\n");
}

#[test]
fn methods_and_associated_items() {
    let a = ok(
        "pub struct P { x: F32, y: F32 }\nimpl P {\n  pub fn new(x: F32, y: F32) -> P { P { x: x, y: y } }\n  pub rt fn norm2(self) -> F32 { (self.x * self.x) + (self.y * self.y) }\n  pub rt fn scale(inout self, k: F32) { self.x = self.x * k }\n  const ORIGIN_X: F32 = 0.0\n}\npub fn g() -> F32 {\n  var p = P.new(1.0, 2.0)\n  p.scale!(2.0)\n  p.norm2() + P.ORIGIN_X + F32.PI\n}\n",
    );
    let body = &a.bodies[&def(&a, "g")];
    assert!(body.targets.values().any(|t| matches!(t, Target::Method { .. })));
    assert!(body.targets.values().any(|t| matches!(t, Target::BuiltinConst { name, .. } if name == "PI")));
    assert!(body.targets.values().any(|t| matches!(t, Target::Const(_))));
    assert_eq!(
        codes(
            "pub struct P { x: F32 }\nimpl P { pub fn new(x: F32) -> P { P { x: x } } }\npub fn g(p: P) -> P { p.new(1.0) }\n"
        ),
        vec![Code::E0413]
    );
    assert_eq!(
        codes(
            "pub struct P { x: F32 }\nimpl P { pub fn norm(self) -> F32 { self.x } }\npub fn g(p: P) -> F32 { P.norm(p) }\n"
        ),
        vec![Code::E0401]
    );
    ok(
        "pub fn g(xs: [F32; 4], inout out: Span[F32]) -> U32 {\n  out.fill!(0.0)\n  out.add_from!(xs)\n  xs.len() + xs.slice(0, 2).len()\n}\n",
    );
    assert_eq!(codes("pub fn g(xs: [F32; 4]) -> F32 { xs.nope() }\n"), vec![Code::E0413]);
    assert_eq!(codes("pub fn g(s: Str) -> U8 { s[0] }\n"), vec![Code::E0413]);
}

#[test]
fn span_parameters_accept_arrays_and_bufs() {
    ok(
        "pub fn total(xs: Span[F32]) -> U32 { xs.len() }\npub fn g(a: [F32; 4], b: Span[F32]) -> U32 { total(a) + total(b) }\n",
    );
    assert_eq!(
        codes("pub fn total(xs: Span[F32]) -> U32 { xs.len() }\npub fn g(a: [U8; 4]) -> U32 { total(a) }\n"),
        vec![Code::E0401]
    );
    ok("pub fn planar(ch: [Span[F32]; 2]) -> U32 { ch[0].len() }\npub fn g(a: [[F32; 4]; 2]) -> U32 { planar(a) }\n");
}

#[test]
fn enums_options_results_and_try() {
    ok(
        "pub enum Shape { Circle(F32), Unit }\npub fn g() -> Shape { Shape.Circle(1.0) }\npub fn h() -> Shape { Shape.Unit }\npub fn k() -> fn(F32) -> Shape { Shape.Circle }\n",
    );
    ok(
        "pub fn f(o: Option[U8]) -> Option[U8] { let n = o?\n Some(n + 1) }\npub fn g(r: Result[U8, Str]) -> Result[U32, Str] { let n = r?\n Ok(n as U32) }\n",
    );
    assert_eq!(codes("pub fn f(o: Option[U8]) -> U8 { let n = o?\n n }\n"), vec![Code::E0414]);
    assert_eq!(
        codes("pub fn g(r: Result[U8, Str]) -> Result[U32, U8] { let n = r?\n Ok(n as U32) }\n"),
        vec![Code::E0414]
    );
    ok("pub fn f(xs: [Option[U8]; 4]) -> Bool { xs[0] == Some(1) }\n");
}

#[test]
fn statements() {
    assert_eq!(codes("pub fn f() { break }\n"), vec![Code::E0002]);
    // `a` is a place; its mutability (a borrowed parameter) is T2-8's check (E0701).
    assert_eq!(codes("pub fn f(a: U32) { a = 1 }\n"), vec![Code::E0701]);
    assert_eq!(codes("pub fn f() -> U32 { return 1.0 }\n"), vec![Code::E0401]);
    ok("pub fn f(c: Bool) -> U32 {\n  while c { if c { break } else { continue } }\n  return 1\n}\n");
}

#[test]
fn places_and_assignment() {
    ok("pub struct P { x: F32 }\npub fn f(inout p: P, q: P) {\n  p.x = q.x\n  var r = q\n  r.x = 1.0\n}\n");
    assert_eq!(codes("pub fn f(p: U32) { 1 = 2 }\n"), vec![Code::E0415]);
}

#[test]
fn borrow_bindings_are_flagged() {
    let a = ok(
        "pub struct P { x: F32, xs: [F32; 2] }\npub fn f(p: P) -> F32 {\n  let y = p.x\n  let z = p.xs[0]\n  let w = y + z\n  for v in p.xs { }\n  w\n}\n",
    );
    let body = &a.bodies[&def(&a, "f")];
    let flag = |n: &str| body.locals.iter().find(|l| l.name == n).unwrap().borrow;
    assert!(flag("y") && flag("z") && flag("v"));
    assert!(!flag("w"));
}

#[test]
fn const_values() {
    let a = ok(
        "const N: U32 = 8\nconst NEG: I32 = -3\nconst T: [F32; 2] = [1.0, 2.0]\npub struct P { x: F32, y: F32 }\nconst O: P = P { y: 2.0, x: 1.0 }\nconst B: Bool = true\n",
    );
    assert_eq!(a.const_values[&def(&a, "N")], ConstValue::Int(8));
    assert_eq!(a.const_values[&def(&a, "NEG")], ConstValue::Int(-3));
    assert_eq!(a.const_values[&def(&a, "T")], ConstValue::Array(vec![ConstValue::Float(1.0), ConstValue::Float(2.0)]));
    assert_eq!(a.const_values[&def(&a, "O")], ConstValue::Struct(vec![ConstValue::Float(1.0), ConstValue::Float(2.0)]));
    assert_eq!(a.const_values[&def(&a, "B")], ConstValue::Bool(true));
    let a = ok("const S: [F32; 4] = make()\npub fn make() -> [F32; 4] { [0.0; 4] }\n");
    assert!(!a.const_values.contains_key(&def(&a, "S")));
    assert_eq!(codes("const X: U32 = 1.0\n"), vec![Code::E0401]);
}

#[test]
fn typed_hole_reports_candidates() {
    let a = check("pub fn f(x: F32, n: U32) -> F32 { _ }\n");
    assert_eq!(a.diagnostics.len(), 1);
    assert_eq!(a.diagnostics[0].code, Code::E0421);
    assert!(a.diagnostics[0].message.contains("`F32`") && a.diagnostics[0].message.contains("x"));
    assert!(!a.diagnostics[0].message.contains(", n"));
}

#[test]
fn tables_are_resolved() {
    let a = ok("pub fn f(xs: [F32; 4]) -> F32 {\n  var acc = 0.0\n  for i in 0..4 { acc = acc + xs[i] }\n  acc\n}\n");
    let body = &a.bodies[&def(&a, "f")];
    for &t in body.expr_types.values() {
        assert!(!matches!(a.types.get(t), Ty::Var(_)), "unresolved expression type");
    }
    let xs = body.locals.iter().find(|l| l.name == "xs").unwrap();
    assert!(matches!(a.types.get(xs.ty), Ty::Array(_, Len::Const(4))));
    assert_eq!(xs.kind, LocalKind::Param(onsa_syntax::ast::Mode::Borrow));
    assert!(body.targets.values().filter(|t| matches!(t, Target::Local(_))).count() >= 5);
    let _ = BuiltinTy::Option;
}
