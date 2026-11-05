//! Unit tests for the body checker (T2-5 .. T2-7, T2-10, T2-11).

use onsa_diag::{Code, FileId};

use crate::body::{LocalKind, Target};
use crate::consteval::ConstValue;
use crate::tests::analyze;
use crate::ty::{FloatKind, IntKind, Len, Ty};
use crate::{Analysis, Module, Package};

/// The analysis of `src` with std, whose bodies are in the tables too.
fn check_in(src: &str) -> Analysis {
    let modules =
        vec![Module::new(vec!["main".into()], FileId(0), src.to_string(), onsa_syntax::parse(FileId(0), src))];
    analyze(&Package::new("t", modules, vec![crate::flow_tests::std_package()]))
}

fn check(src: &str) -> Analysis {
    check_in(src)
}

/// The codes, with std: its `Alloc` is in the prelude (S-659).
fn codes(src: &str) -> Vec<Code> {
    let a = check_in(src);
    let mut v: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
    v.sort();
    v
}

fn ok(src: &str) -> Analysis {
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "unexpected diagnostics: {:?}", a.diagnostics);
    a
}

fn ok_with_std(src: &str) -> Analysis {
    let a = check_in(src);
    assert!(a.diagnostics.is_empty(), "unexpected diagnostics: {:?}", a.diagnostics);
    a
}

fn def(a: &Analysis, name: &str) -> crate::DefId {
    crate::DefId(a.defs.iter().rposition(|d| d.name == name).unwrap_or_else(|| panic!("no def {name}")) as u32)
}

#[test]
fn literal_resolved_by_later_statement() {
    let a = ok("pub fn f(xs: [F32; 4]) -> F32 {\n  var acc = 0.0\n  for i in 0..<4 { acc = acc + xs[i] }\n  acc\n}\n");
    let body = &a.bodies[&def(&a, "f")];
    let acc = body.locals.iter().find(|l| l.name == "acc").unwrap();
    assert!(matches!(a.types.get(acc.ty), Ty::Float(FloatKind::F32)));
    assert_eq!(acc.kind, LocalKind::Var);
    assert_eq!(acc.state, crate::binding::Bind::OwnedMut);
    let i = body.locals.iter().find(|l| l.name == "i").unwrap();
    assert!(matches!(a.types.get(i.ty), Ty::Int(IntKind::U32)));
    assert!(body.complete);
}

#[test]
fn unresolved_float_literal_is_e0405() {
    // S-22: floats have no default (§2.4); integers default to I32 (below).
    assert_eq!(codes("pub fn f() {\n  var acc = 0.0\n  let _ = acc\n}\n"), vec![Code::E0405]);
    assert_eq!(codes("pub fn f() {\n  let _ = 1.0\n}\n"), vec![Code::E0405]);
}

#[test]
fn unresolved_integer_literal_defaults_to_i32() {
    // S-22 (§2.4, §4.7): applied at the end of the body only.
    assert_eq!(codes("pub fn f() {\n  let _ = 1\n}\n"), vec![]);
    assert_eq!(codes("test \"t\" { assert 1 == 1 }\n"), vec![]);
    assert_eq!(codes("pub fn f() {\n  for _ in 0..<4 {\n  }\n}\n"), vec![]);
    let a = check("pub fn f() {\n  let a = 1\n}\n");
    let body = &a.bodies[&def(&a, "f")];
    let int = body.locals.iter().find(|l| l.name == "a").unwrap().ty;
    assert!(matches!(a.types.get(int), Ty::Int(IntKind::I32)));
    // Out of the I32 range: E0408 with the annotation hint.
    let a = check("pub fn f() {\n  let _ = 3_000_000_000\n}\n");
    assert_eq!(a.diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(), vec![Code::E0408]);
    assert!(a.diagnostics[0].message.contains("annotation"), "{}", a.diagnostics[0].message);
    // Mid-body operations still need the type (E0420): the default is not eager.
    assert_eq!(codes("pub fn f() -> Option[I32] {\n  0.checked_add(1)\n}\n"), vec![Code::E0420]);
    assert_eq!(codes("pub fn f() -> U32 {\n  var acc = 0.0\n  acc.to_bits()\n}\n"), vec![Code::E0420]);
    // The argument of a conversion function does not (§4.7, S-231): an integer
    // literal takes its default, a float one has no source (§2.4).
    assert_eq!(codes("pub fn f() -> F32 {\n  F32.round_from(0)\n}\n"), vec![]);
    assert_eq!(codes("pub fn f() -> F32 {\n  var acc = 0.0\n  F32.round_from(acc)\n}\n"), vec![Code::E0405]);
}

#[test]
fn literal_ranges() {
    assert_eq!(codes("pub fn f() -> U8 {\n  let x: U8 = 300\n  x\n}\n"), vec![Code::E0408]);
    ok("pub fn f() -> I8 {\n  let x: I8 = -128\n  x\n}\n");
    assert_eq!(codes("pub fn f() -> I8 {\n  let x: I8 = -129\n  x\n}\n"), vec![Code::E0408]);
    assert_eq!(codes("pub fn f() -> U32 {\n  let x: U32 = -1\n  x\n}\n"), vec![Code::E0401]);
}

#[test]
fn float_literal_ranges() {
    // §2.4, R-45, S-211: E0408 when the type is decided and the value is not
    // finite, or a literal that is not 0 rounds to 0; a subnormal value is one.
    let f = |ty: &str, lit: &str| format!("pub fn f() -> {ty} {{\n  let x: {ty} = {lit}\n  x\n}}\n");
    assert_eq!(codes(&f("F32", "1.0e40")), vec![Code::E0408]);
    assert_eq!(codes(&f("F32", "-1.0e40")), vec![Code::E0408]);
    assert_eq!(codes(&f("F32", "1.0e-50")), vec![Code::E0408]);
    assert_eq!(codes(&f("F64", "1e-400")), vec![Code::E0408]);
    ok(&f("F32", "1.0e-40"));
    ok(&f("F32", "0.0e-99"));
    ok(&f("F64", "1.0e40"));
    // The type a later statement decides; a `const`.
    assert_eq!(codes("pub fn f() -> F32 {\n  let a = 1.0e40\n  let b: F32 = a\n  b\n}\n"), vec![Code::E0408]);
    assert_eq!(codes("const A: F32 = 1e60\npub fn f() -> F32 {\n  A\n}\n"), vec![Code::E0408]);
    assert_eq!(codes("const A: F32 = -1e-60\npub fn f() -> F32 {\n  A\n}\n"), vec![Code::E0408]);
    // R-20: the value of a `const` is the literal rounded once to its type.
    let a = ok("pub const K: F32 = 1.0000000596046447753906250001\n");
    assert_eq!(a.const_values[&def(&a, "K")], ConstValue::Float(f64::from(1.000_000_1_f32)));
}

#[test]
fn float_literal_of_a_type_parameter_notes() {
    // §6.6, S-881: what the literal cannot be says why; the notes are of no case's
    // expectation (the cases do not hold the words of a diagnostic).
    let of = |src: &str| {
        let a = check_in(src);
        let [d] = &a.diagnostics[..] else { panic!("{src}: {:?}", a.diagnostics) };
        (d.code, d.fixes.len(), d.notes.iter().map(|n| n.message.clone()).collect::<Vec<_>>())
    };
    let bound = "a float literal is a value of `T` only when the bounds of `T` include `Float` (§6.6)";
    for src in [
        "pub fn f[T: Num](x: T) -> T { x * 0.5 }\n",
        "pub fn f[T: Num](x: T) -> T { 0.5 * x }\n",
        "pub fn f[T: Int](x: T) -> Option[T] { Some(0.5) }\n",
        "pub fn f[T](x: T) -> T { 0.5 }\n",
    ] {
        assert_eq!(of(src), (Code::E0401, 0, vec![bound.to_string()]), "{src}");
    }
    // The integer literal and a float type are not of this rule.
    assert_eq!(of("pub fn f[T: Float](x: T) -> T { x * 2 }\n").2.len(), 0);
    assert_eq!(of("pub fn f(x: U32) -> U32 { x * 0.5 }\n").2.len(), 0);
    // The source of a conversion to `T`, as it is written; to a type that is not `T: Float`, the rule of a literal.
    let to = |t: &str, lit: &str| {
        format!(
            "a float literal is a value of `{t}` by itself: write it where `{t}` is expected (`let x: {t} = {lit}`) (§6.6)"
        )
    };
    for (src, t, lit) in
        [("T.round_from(0.5)", "T", "0.5"), ("T.round_from(-0.5)", "T", "-0.5"), ("T.round_from((0.5))", "T", "0.5")]
    {
        let src = format!("pub fn f[T: Float](x: T) -> T {{ {src} }}\n");
        assert_eq!(of(&src), (Code::E0405, 0, vec![to(t, lit)]), "{src}");
    }
    let plain = "a literal takes no annotation of its own: give it its type in a binding (`let x: F32 = 0.5`)";
    let literal = of("pub fn f[T: Int](x: T) -> T { T.trunc_from(0.5) }\n");
    assert_eq!(literal, (Code::E0405, 0, vec![plain.to_string()]));
    // The candidate of a removed method reads the same rule as the unification (`may_fit`).
    let removed =
        |bound: &str| format!("pub fn f[T: {bound}](x: T, y: T) -> T {{\n  var k = 0.5\n  k = x.min(y)\n  k\n}}\n");
    assert_eq!(of(&removed("Float")).1, 1);
    assert_eq!(of(&removed("Num")).1, 0);
}

#[test]
fn param_values_out_of_the_type_are_e0408() {
    // §11.7: a number of `@param` is a value of the input's type (§2.4).
    let src = |v: &str| {
        format!(
            "pub flow g(\n  x: F32 at sample,\n  @param(min: 0.0, max: {v}, default: 0.5)\n  level: F32 at block,\n) -> F32 at sample {{\n  x * level\n}}\n"
        )
    };
    assert_eq!(codes(&src("1.0e40")), vec![Code::E0408]);
    assert_eq!(codes(&src("1.0e-50")), vec![Code::E0408]);
    ok(&src("1.0"));
}

#[test]
fn operations_need_known_types() {
    assert_eq!(
        codes("pub fn f(x: F32) -> U32 {\n  var acc = 0.0\n  let r = acc.to_bits()\n  acc = x\n  r\n}\n"),
        vec![Code::E0420]
    );
    // A conversion function waits for its source: here the same type, decided later (§3.3).
    assert_eq!(
        codes("pub fn f(x: F32) -> F32 {\n  var acc = 0.0\n  let r = F32.round_from(acc)\n  acc = x\n  r\n}\n"),
        vec![Code::E0413]
    );
    // The element type of `[]` may be decided later; left open, it is E0406 at `[]` (S-226).
    assert_eq!(codes("pub fn f() -> U32 {\n  let _ = []\n  1\n}\n"), vec![Code::E0406]);
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
    // A later statement may decide the type parameter (S-174); one left open is E0406 at the call.
    ok(&format!("{src}pub fn g() -> I32 {{\n  let n = parse(\"3\")\n  n\n}}\n"));
    assert_eq!(
        codes(&format!("{src}pub fn g() -> I32 {{\n  let n = parse(\"3\")\n  let _ = n\n  2\n}}\n")),
        vec![Code::E0406]
    );
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
        "pub fn sum[const N: U32](xs: [F32; N]) -> F32 {\n  var acc: F32 = 0.0\n  for i in 0..<N { acc = acc + xs[i] }\n  acc\n}\npub fn g(ys: [F32; 4]) -> F32 { sum(ys) }\n",
    );
    let body = &a.bodies[&def(&a, "g")];
    assert_eq!(body.instances.len(), 1);
    assert!(matches!(a.types.get(body.instances[0].args[0]), Ty::ConstVal(4)));
    ok("const N: U32 = 8\npub fn g() -> [U32; 8] { [0; N] }\n");
    // The element of `[e; N]` must be Dup (§2.4), checked in sema once it is decided (S-235).
    assert_eq!(
        codes("pub struct O { b: Buf[F32] }\npub fn g(move o: O) -> U32 uses {Alloc} {\n  let _ = [o; 2]\n  0\n}\n"),
        vec![Code::E0416]
    );
}

#[test]
fn closures_take_types_from_the_expected_function_type() {
    let a = ok(
        "pub fn apply(f: fn(U32) -> U32) -> U32 { f.(1) }\npub fn g(k: U32) -> U32 {\n  apply(fn(i) { i + k })\n}\n",
    );
    let body = &a.bodies[&def(&a, "g")];
    let (closure, captures) = body.captures.iter().next().unwrap();
    assert_eq!(captures.len(), 1);
    assert_eq!(body.locals[captures[0].0 as usize].name, "k");
    assert!(matches!(a.types.get(body.expr_types[closure]), Ty::Fn(_)));
    assert_eq!(codes("pub fn g() -> U32 {\n  let _ = fn(i) { i }\n  1\n}\n"), vec![Code::E0420]);
    ok("pub fn g() -> U32 {\n  let f = fn(i: U32) -> U32 { i }\n  f.(1)\n}\n");
    assert_eq!(
        codes("pub fn apply(f: fn(U32) -> U32) -> U32 { f.(1) }\npub fn g() -> U32 { apply(fn(i, j) { i }) }\n"),
        vec![Code::E0401]
    );
}

#[test]
fn shadowing_rules() {
    ok(
        "pub fn f(xs: [F32; 4]) -> F32 {\n  var s: F32 = 0.0\n  for i in 0..<4 { s = s + xs[i] }\n  for i in 0..<4 { s = s + xs[i] }\n  s\n}\n",
    );
    assert_eq!(codes("pub fn f(xs: [F32; 4]) {\n  for i in 0..<4 { let i = 1 }\n}\n"), vec![Code::E0304]);
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
    // With std, which declares `F32.from_bits` (§3.3).
    ok_with_std(
        "pub fn f(i: I32, x: F64, y: F32, n: U8) -> F64 {\n  let _ = i as I64\n  let _ = F32.round_from(x)\n  let _ = I32.trunc_sat_from(y)\n  let d = y.to_bits()\n  let _ = F32.from_bits(d)\n  let _ = n as F32\n  (i as F64) + x\n}\n",
    );
    assert_eq!(codes("pub fn f(x: I64) -> I32 { x as I32 }\n"), vec![Code::E0411]);
    assert_eq!(codes("pub fn f(x: I64) -> F64 { x as F64 }\n"), vec![Code::E0411]);
    assert_eq!(codes("pub fn f(x: F32) -> I32 { x as I32 }\n"), vec![Code::E0411]);
    let src = "pub fn f(x: F32) -> I32 { x as I32 }\n";
    let a = check(src);
    let d = &a.diagnostics[0];
    assert!((0..d.fixes.len()).any(|k| crate::fixed_region(src, d, k) == "I32.trunc_from(x)"));
}

/// The E0411 says what the pair is (spec §3.3): only the number types have
/// another way to convert, so a type parameter's text says it has no `as`, and
/// the text of another type names no way (R-159, R-257). An integer
/// narrowing has no candidate; its note has the `Option` of `narrow_from`.
#[test]
fn the_text_of_the_e0411_goes_by_the_pair() {
    let of = |src: &str| {
        let a = check(src);
        let [d] = a.diagnostics.as_slice() else { panic!("{:?}", a.diagnostics) };
        assert_eq!(d.code, Code::E0411, "{src}");
        (d.message.clone(), d.fixes.len(), d.notes.iter().map(|n| n.message.clone()).collect::<Vec<_>>())
    };
    let (number, fixes, _) = of("pub fn f(x: F32) -> I32 { x as I32 }\n");
    assert!(number.contains("`F32` to `I32` needs a conversion function"), "{number}");
    assert_eq!(fixes, 2);
    let (param, fixes, _) = of("pub fn f[T: Float](x: T) -> T { x as T }\n");
    assert!(param.starts_with("a type parameter has no `as`"), "{param}");
    assert_eq!(fixes, 1);
    let (target, fixes, _) = of("pub fn f[T: Float](x: F32) -> T { x as T }\n");
    assert!(target.starts_with("a type parameter has no `as`"), "{target}");
    assert_eq!(fixes, 0);
    for src in ["pub fn f(c: Char) -> U8 { c as U8 }\n", "pub fn f(b: Bool) -> I32 { b as I32 }\n"] {
        let (other, fixes, notes) = of(src);
        assert!(other.contains("only converts between number types") && !other.contains("function"), "{other}");
        assert_eq!((fixes, notes.len()), (0, 0), "{src}");
    }
    let (_, fixes, notes) = of("pub fn f(n: I64) -> I32 { n as I32 }\n");
    assert_eq!(fixes, 0);
    assert!(notes[0].starts_with("`I32.narrow_from(…)` gives an `Option[I32]`"), "{notes:?}");
}

/// A bound a failed `use` left unknown decides no conversion function
/// (spec §3.3); the same type needs none.
#[test]
fn an_unknown_bound_gives_the_e0411_no_call() {
    let fixes = |body: &str| {
        let a = check(&format!("use nowhere.Nope\n\npub fn f[T: Nope](x: T) {body}\n"));
        a.diagnostics.iter().find(|d| d.code == Code::E0411).expect("E0411").fixes.len()
    };
    assert_eq!(fixes("-> F32 { x as F32 }"), 0);
    assert_eq!(fixes("-> I32 { x as I32 }"), 0);
    assert_eq!(fixes("-> T { x as T }"), 1);
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
    ok("pub struct P: PartialEq { x: F32 }\npub fn f(a: P, b: P) -> Bool { a == b }\n");
    assert_eq!(codes("pub struct P { x: F32 }\npub fn f(a: P, b: P) -> Bool { a == b }\n"), vec![Code::E0401]);
    ok("pub fn f(a: Option[U8], b: Option[U8]) -> Bool { a == b }\n");
}

/// The trait of an operator waits for the statement that decides its operand type (§4.7, §6.3,
/// S-235, R-55): the message names the decided type, the error is at the operator, and a type
/// left open is reported by E0406 / E0405 alone.
#[test]
fn operator_traits_wait_for_the_decided_type() {
    // The one diagnostic of `src`, with the text at its position.
    let one = |src: &str| {
        let a = check(src);
        assert_eq!(a.diagnostics.len(), 1, "{:?}", a.diagnostics);
        let d = a.diagnostics[0].clone();
        let at = src[d.span.start as usize..d.span.end as usize].to_string();
        (d.code, at, d.message)
    };
    // Literals inside a composite type: the default decides them at the end.
    ok("pub fn f() -> Bool { Some(1) == Some(2) }\n");
    ok("pub fn f() -> Bool { [1, 2] == [1, 2] && (1, 2) != (2, 1) }\n");
    ok("pub fn f(v: [I32; 2]) -> Bool { [1, 2] == v }\n");
    ok("pub fn f() -> Bool {\n  let v: [I32; 2] = [1, 2]\n  v == [1, 2]\n}\n");
    ok("pub fn f() -> Bool {\n  let o = None\n  let e = o == None\n  let _: Option[F32] = o\n  e\n}\n");
    // Not met: the decided type in the message, no `?` of a variable.
    let (code, at, msg) = one("pub fn f() -> Bool { Some(1) < Some(2) }\n");
    assert_eq!((code, at.as_str()), (Code::E0401, "<"));
    assert!(msg.contains("`Option[I32]`") && !msg.contains('?'), "{msg}");
    // A later statement decides a type without the trait: E0401 at the operator.
    let make = "fn make[T]() -> T { make() }\n";
    let (code, at, msg) =
        one(&format!("{make}pub fn f() -> Bool {{\n  let v = make()\n  let _ = v + v\n  let b: Bool = v\n  b\n}}\n"));
    assert_eq!((code, at.as_str()), (Code::E0401, "+"));
    assert!(msg.contains("`Bool`"), "{msg}");
    let (code, at, _) =
        one(&format!("{make}pub fn f() -> U8 {{\n  let v = make()\n  let _ = -v\n  let u: U8 = v\n  u\n}}\n"));
    assert_eq!((code, at.as_str()), (Code::E0401, "-v"));
    // Never decided: E0406 at the expression that made the variable, the operator is not judged.
    let (code, at, _) = one(&format!("{make}pub fn f() -> Bool {{\n  let v = make()\n  let _ = v < v\n  true\n}}\n"));
    assert_eq!((code, at.as_str()), (Code::E0406, "make()"));
    // A float literal left open: E0405 at the literal.
    let (code, at, _) = one("pub fn f() -> Bool { [1.5, 2.0] == [1.5, 2.0] }\n");
    assert_eq!((code, at.as_str()), (Code::E0405, "1.5"));
}

/// S-854: an operation whose answer the kind of a literal variable decides reports the error of an
/// annotated type, with the type named `an integer` / `a float`; a method, `as` and another
/// variable stay E0420. R-353: no internal `?N` in a message.
#[test]
fn literal_subjects_and_shown_variables() {
    // The one diagnostic of the type stage (the unused bindings of the stage after it aside).
    let one = |src: &str| {
        let a = check(src);
        let ds: Vec<_> = a.diagnostics.iter().filter(|d| d.code != Code::E0309).collect();
        assert_eq!(ds.len(), 1, "{ds:?}");
        (ds[0].code, ds[0].message.clone())
    };
    let body = |b: &str| format!("pub fn f(x: F32) -> Option[F32] {{\n  let n = 1\n  let m = 1.5\n  {b}\n  None\n}}\n");
    for (b, code, msg) in [
        ("let _ = n.(x)", Code::E0401, "an integer is not a function and cannot be called"),
        ("let _ = m.(x)", Code::E0401, "a float is not a function and cannot be called"),
        ("let _ = n.x", Code::E0413, "an integer has no field `x`"),
        ("let _ = m.0", Code::E0413, "a float has no element `0`"),
        ("let _ = n[0]", Code::E0413, "an integer cannot be indexed"),
        ("let _ = m?", Code::E0414, "`?` needs an `Option` or `Result`; found a float"),
        ("let _ = \"{n.x}\"", Code::E0413, "an integer has no field `x`"),
        (
            "let _ = n.checked_add(1)",
            Code::E0420,
            "the type of this receiver must be known here; add an annotation (§4.7)",
        ),
        (
            "let _ = n as F32",
            Code::E0420,
            "the type of this operand of `as` must be known here; add an annotation (§4.7)",
        ),
    ] {
        assert_eq!(one(&body(b)), (code, msg.to_string()), "{b}");
    }
    // Another variable still needs its type (E0420).
    let (code, _) = one("fn make[T]() -> T { make() }\npub fn f() -> F32 {\n  let v = make()\n  let _ = v.x\n  v\n}\n");
    assert_eq!(code, Code::E0420);
    // R-353: the literal variables and the others inside a type.
    let (_, msg) = one("pub fn f() -> U32 {\n  let o = Some(1)\n  let _ = o.x\n  1\n}\n");
    assert_eq!(msg, "`Option[{integer}]` has no field `x`");
    let (_, msg) = one("pub fn f(x: F32) -> U32 {\n  let _ = [1.5, 2.5].(x)\n  1\n}\n");
    assert_eq!(msg, "`[{float}; 2]` is not a function and cannot be called");
    let (_, msg) = one("pub fn f(x: F32) -> U32 {\n  let o = None\n  let _ = o.(x)\n  1\n}\n");
    assert_eq!(msg, "`Option[_]` is not a function and cannot be called");
}

/// S-860: iterating a literal variable, a tuple pattern on one and passing one as a `Span` (and
/// a planar array of them) report the E0401 of an annotated type, the type named `an integer` /
/// `a float`; another variable stays E0420.
#[test]
fn literal_subjects_of_iteration_tuple_patterns_and_spans() {
    let one = |src: &str| {
        let a = check(src);
        let ds: Vec<_> = a.diagnostics.iter().filter(|d| d.code != Code::E0309).collect();
        assert_eq!(ds.len(), 1, "{src}: {ds:?}");
        (ds[0].code, ds[0].message.clone())
    };
    let decls = "fn takes(s: Span[I32]) -> I32 { 0 }\nfn planar(s: [Span[F32]; 2]) -> F32 { 0.0 }\n";
    let body = |b: &str| format!("{decls}pub fn f() -> I32 {{\n  let n = 17\n  let m = 1.5\n  {b}\n  0\n}}\n");
    let span = |t: &str, found: &str| {
        format!("expected `{t}` (or an array / `Buf` of the same element), found {found} (§5.3)")
    };
    for (b, msg) in [
        ("for i in n { }", "an integer cannot be iterated (§7)".to_string()),
        ("for i in 1.5 { }", "a float cannot be iterated (§7)".to_string()),
        ("let (a, b) = n", "expected a tuple pattern target, found an integer".to_string()),
        ("for (a, b) in [1, 2] { }", "expected a tuple pattern target, found an integer".to_string()),
        (
            "match Some(m) {\n    Some((a, b)) => 1,\n    None => 0,\n  }",
            "expected a tuple pattern target, found a float".into(),
        ),
        ("let _ = takes(17)", span("Span[I32]", "an integer")),
        ("let _ = planar([1.5, 2.5])", span("Span[F32]", "a float")),
        ("let _ = planar(m)", span("[Span[F32]; 2]", "a float")),
    ] {
        assert_eq!(one(&body(b)), (Code::E0401, msg), "{b}");
    }
    let flow = "pub flow g(x: F32 at sample) -> F32 at sample {\n  let (p, q) = 1.5\n  x\n}\n";
    assert_eq!(one(flow), (Code::E0401, "expected a tuple pattern target, found a float".to_string()));
    // Another variable still needs its type (E0420).
    let make = "fn make[T]() -> T { make() }\n";
    for b in ["for i in v { }", "let (a, b) = v", "let _ = takes(v)"] {
        let src = format!("{make}{decls}pub fn f() -> I32 {{\n  let v = make()\n  {b}\n  0\n}}\n");
        assert_eq!(one(&src).0, Code::E0420, "{b}");
    }
}

/// R-355 (§6.4): a generic type meets a derived trait only when its type arguments meet it.
#[test]
fn derives_of_a_generic_type_ask_its_arguments() {
    let decl = "pub struct Plain { x: F32 }\npub struct Pair[T]: PartialEq { a: T, b: T }\n";
    assert_eq!(codes(&format!("{decl}pub fn f(p: Pair[Plain]) -> Bool {{ p == p }}\n")), vec![Code::E0401]);
    ok(&format!("{decl}pub fn f(p: Pair[F32]) -> Bool {{ p == p }}\n"));
    ok(&format!("{decl}pub fn f[T: PartialEq](p: Pair[T]) -> Bool {{ p == p }}\n"));
    assert_eq!(codes(&format!("{decl}pub fn f[T](p: Pair[T]) -> Bool {{ p == p }}\n")), vec![Code::E0401]);
    ok(&format!("{decl}pub fn f(p: Pair[Pair[U8]]) -> Bool {{ p == p }}\n"));
}

#[test]
fn methods_and_associated_items() {
    // With std, which declares `F32.PI` (§6.6).
    let a = ok_with_std(
        "pub struct P { x: F32, y: F32 }\nimpl P {\n  pub fn new(x: F32, y: F32) -> P { P { x: x, y: y } }\n  pub rt fn norm2(self) -> F32 { (self.x * self.x) + (self.y * self.y) }\n  pub rt fn scale(inout self, k: F32) { self.x = self.x * k }\n  const ORIGIN_X: F32 = 0.0\n}\npub fn g() -> F32 {\n  var p = P.new(1.0, 2.0)\n  p.scale!(2.0)\n  p.norm2() + P.ORIGIN_X + F32.PI\n}\n",
    );
    let body = &a.bodies[&def(&a, "g")];
    assert!(body.targets.values().any(|t| matches!(t, Target::Method { .. })));
    let consts: Vec<&str> = (body.targets.values())
        .filter_map(|t| match t {
            Target::Const { def, .. } => Some(a.def(*def).name.as_str()),
            _ => None,
        })
        .collect();
    assert!(consts.contains(&"PI") && consts.contains(&"ORIGIN_X"), "{consts:?}");
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
        vec![Code::E0308]
    );
    ok_with_std(
        "pub fn g(xs: [F32; 4], inout out: Span[F32]) -> U32 {\n  out.fill!(0.0)\n  out.add_from!(xs)\n  xs.len() + xs.slice(0, 2).len()\n}\n",
    );
    assert_eq!(codes("pub fn g(xs: [F32; 4]) -> F32 { xs.nope() }\n"), vec![Code::E0413]);
    assert_eq!(codes("pub fn g(s: Str) -> U8 { s[0] }\n"), vec![Code::E0413]);
}

#[test]
fn span_parameters_accept_arrays_and_bufs() {
    ok_with_std(
        "pub fn total(xs: Span[F32]) -> U32 { xs.len() }\npub fn g(a: [F32; 4], b: Span[F32]) -> U32 { total(a) + total(b) }\n",
    );
    assert_eq!(
        codes("pub fn total(xs: Span[F32]) -> U32 { xs.len() }\npub fn g(a: [U8; 4]) -> U32 { total(a) }\n"),
        vec![Code::E0401]
    );
    ok_with_std(
        "pub fn planar(ch: [Span[F32]; 2]) -> U32 { ch[0].len() }\npub fn g(a: [[F32; 4]; 2]) -> U32 { planar(a) }\n",
    );
}

#[test]
fn enums_options_results_and_try() {
    ok(
        "pub enum Shape { Circle(F32), Unit }\npub fn g() -> Shape { Shape.Circle(1.0) }\npub fn h() -> Shape { Shape.Unit }\npub fn k() -> fn(move F32) -> Shape { Shape.Circle }\n",
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
    ok(
        "pub struct P { x: F32 }\npub fn f(inout p: P, q: P) {\n  p.x = q.x\n  var r = q\n  r.x = 1.0\n  let _ = r\n}\n",
    );
    assert_eq!(codes("pub fn f(p: U32) { 1 = 2 }\n"), vec![Code::E0415]);
    // A tuple on the left (S-180): E0415 with the form of `let` and one assignment each, a
    // note with no position; none for another place that is not.
    let notes = |src: &str| {
        let a = check(src);
        assert_eq!(a.diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(), [Code::E0415], "{src}");
        a.diagnostics[0].notes.iter().map(|n| (n.span, n.message.clone())).collect::<Vec<_>>()
    };
    let swap = "pub fn f() -> U32 {\n  var p: U32 = 1\n  var q: U32 = 2\n  ((p, q)) = (q, p)\n  p + q\n}\n";
    let want = "a tuple is not a place; take the value apart with `let (v0, v1) = (q, p)`, then assign each: `p = v0`, `q = v1` (§5.1)";
    assert_eq!(notes(swap), [(None, want.to_string())]);
    // In words only when a part is no place (a tuple too) or the value is of more lines.
    let words = "a tuple is not a place; take the value apart with `let`, then assign each part to its place (§5.1)";
    for body in
        ["(p, (q, r)) = (1, (2, 3))", "(p, 1) = (1, 2)", "(p, q) = if true {\n    (1, 2)\n  } else {\n    (3, 4)\n  }"]
    {
        let src = format!(
            "pub fn f() {{\n  var p: U32 = 1\n  var q: U32 = 2\n  var r: U32 = 3\n  {body}\n  let _ = p + q + r\n}}\n"
        );
        assert_eq!(notes(&src), [(None, words.to_string())], "{body}");
    }
    assert_eq!(notes("const K: U32 = 1\npub fn f() { K = 2 }\n"), []);
}

#[test]
fn borrow_bindings_are_flagged() {
    let a = ok(
        "pub struct P { x: F32, xs: [F32; 2] }\npub fn f(p: P) -> F32 {\n  let y = p.x\n  let z = p.xs[0]\n  let w = y + z\n  for v in p.xs { let _ = v }\n  w\n}\n",
    );
    let body = &a.bodies[&def(&a, "f")];
    let flag = |n: &str| {
        matches!(body.locals.iter().find(|l| l.name == n).unwrap().state, crate::binding::Bind::Borrow { .. })
    };
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
    let a = ok("pub fn f(xs: [F32; 4]) -> F32 {\n  var acc = 0.0\n  for i in 0..<4 { acc = acc + xs[i] }\n  acc\n}\n");
    let body = &a.bodies[&def(&a, "f")];
    for &t in body.expr_types.values() {
        assert!(!matches!(a.types.get(t), Ty::Var(_)), "unresolved expression type");
    }
    let xs = body.locals.iter().find(|l| l.name == "xs").unwrap();
    assert!(matches!(a.types.get(xs.ty), Ty::Array(_, Len::Const(4))));
    assert_eq!(xs.kind, LocalKind::Param(onsa_syntax::ast::Mode::Borrow));
    assert!(body.targets.values().filter(|t| matches!(t, Target::Local(_))).count() >= 5);
}

/// The notes of E0416 (S-235): the reason of a binding is said only for the expected type it
/// came from (an argument, an annotation, the result); a merge of branches, a statement inside
/// a block or a receiver gets a note with its position alone (W2-06/b).
#[test]
fn notes_of_a_late_requirement_name_only_their_own_reason() {
    let notes = |src: &str| -> Vec<String> {
        let a = check(src);
        let d = a.diagnostics.iter().find(|d| d.code == Code::E0416).expect("E0416");
        d.notes.iter().map(|n| n.message.clone()).collect()
    };
    let need = "fn need_f[T: Float](o: Option[T]) -> Bool { true }\nfn take_oi(o: Option[I32]) -> Bool { true }\n";
    let by_argument =
        notes(&format!("{need}pub fn f() -> Bool {{\n  let o = None\n  let _ = need_f(o)\n  take_oi(o)\n}}\n"));
    assert!(by_argument[0].ends_with("as an argument of `take_oi`"), "{by_argument:?}");
    let by_annotation = notes(&format!(
        "{need}pub fn f() -> Bool {{\n  let o = None\n  let a = need_f(o)\n  let p: Option[U8] = o\n  a\n}}\n"
    ));
    assert!(by_annotation[0].ends_with("as the annotation of `p`"), "{by_annotation:?}");
    // The `else` branch is merged with the `then` branch: no reason, inside a block or not.
    let merged = notes(
        "pub fn f(c: Bool, bb: Option[Buf[F32]]) -> U32 {\n  let w: U32 = {\n    let o = None\n    let z = [o; 2]\n    let p = if c { o } else { bb }\n    3\n  }\n  w\n}\n",
    );
    assert!(merged[0].ends_with("here"), "{merged:?}");
    let receiver = notes(
        "pub struct W[T] { v: Option[T] }\nimpl[T: Float] W[T] {\n  fn only_float(self) -> U32 { 1 }\n}\npub fn c2(w: W[I32]) -> U32 {\n  let n = w.only_float()\n  n\n}\n",
    );
    assert!(receiver[0].ends_with("here"), "{receiver:?}");
}

/// What a syntax error left unread gets no diagnostic where it is used (§18.1, S-59, R-71,
/// S-260): the uses of a failed item are checked against what was read only.
#[test]
fn the_uses_of_failed_items_get_no_diagnostic() {
    // The error type: no literal waits for it, `as` does not check it (F-3).
    assert_eq!(
        codes(
            "struct P { x: F32, y: , z: F32 }\nfn f1(p: P) -> F32 { p.y * 2.0 }\nfn f2(p: P) -> I32 { p.y as I32 }\n\
             const K: F32 = )\nfn f3() -> Bool { K > 0.5 }\nfn bad(x: F32) -> { x }\nfn f4(x: F32) -> F32 { bad(x) + 1.0 }\n"
        ),
        []
    );
    // A variant that was not read, called (F-2), and a type whose generics were cut (F-6).
    assert_eq!(codes("enum E { A, B(I32), C(, D(I32) }\nfn f(e: E) -> I32 {\n  let x = E.D(1)\n  1\n}\n"), []);
    assert_eq!(
        codes(
            "struct S[T: ] { a: T }\nenum F[T: ] { A(T), B }\nfn f1(s: S[F32]) -> F32 { s.a }\nfn f2() -> F[F32] { F.A(1.0) }\n"
        ),
        []
    );
    // An element of a failed struct, as a field (`.0`; a tuple struct is one, S-39).
    assert_eq!(
        codes("struct P { x: F32, y: , }\nfn f(p: P) -> F32 { p.0 }\nstruct Hz(F32)\nfn g(h: Hz) -> F32 { h.0 }\n"),
        []
    );
    // The namespace of a flow whose heading was cut (F-4).
    assert_eq!(
        codes(
            "pub flow g(x: ) -> F32 at sample {\n  x\n}\ntest \"t\" {\n  let _ = g.init\n  let _ = g.Config {}\n}\nfn h(s: g.State) -> I32 { 1 }\n"
        ),
        []
    );
}

/// An item read whole whose unit has another syntax error (a `;` after it, S-254) is known
/// whole: its uses are checked (S-260 does not apply, F-7).
#[test]
fn an_item_read_whole_is_checked_where_it_is_used() {
    assert_eq!(
        codes(
            "struct S { a: I32 };\nenum E { A, B };\nfn f1(s: S) -> I32 { s.zzz }\nfn f2() -> S { S { } }\n\
             fn f3(e: E) -> I32 {\n  match e {\n    E.A => 1,\n  }\n}\n"
        ),
        [Code::E0410, Code::E0413, Code::E0501]
    );
}

/// The error type matches any type in any position, and the rest of a type around it is
/// still checked (W3-03/b N-1): a length, a tuple against `Bool`, an array against `I32`.
#[test]
fn the_type_around_the_error_type_is_checked() {
    let src = "struct P { x: F32, y: , z: F32 }\nfn u(p: P) -> I32 {\n  let _: [I32; 3] = [p.y, p.y]\n  1\n}\n\
               fn v(p: P) -> I32 {\n  let _: Bool = (p.y, 1)\n  1\n}\nfn w(p: P) -> I32 {\n  let _: I32 = [p.y]\n  1\n}\n";
    let a = check(src);
    let got: Vec<(Code, &str)> = a.diagnostics.iter().map(|d| (d.code, d.message.as_str())).collect();
    assert_eq!(got.len(), 3, "{got:?}");
    assert!(got.iter().all(|(c, _)| *c == Code::E0401), "{got:?}");
    assert_eq!(got[0].1, "expected `[I32; 3]`, found `[_; 2]`");
}

#[test]
fn for_ranges() {
    let f = |head: &str| codes(&format!("pub fn f(n: U32) {{\n  for _ in {head} {{ }}\n}}\n"));
    assert_eq!(f("0..<n"), vec![]);
    // The bounds are integers (§7).
    assert_eq!(f("0.0..<1.0"), vec![Code::E0401]);
    // `..=` is E0200 until the loop that ends at the type's maximum (W8-03,
    // S-224), after the checks of the bounds; never read as `..<` (R-81).
    let d = check("pub fn f(n: U32) {\n  for _ in 0..=n { }\n}\n").diagnostics;
    assert_eq!(d.iter().map(|d| d.code).collect::<Vec<_>>(), vec![Code::E0200]);
    assert!(d[0].message.contains("`a..=b`") && d[0].message.contains("`for`"), "{}", d[0].message);
    assert_eq!(f("0.0..=1.0"), vec![Code::E0401]);
    // The form of an end is named, not a type variable (`?0`).
    for head in [
        "1.5..<2",
        "0..<1.5",
        "(1, 2)..<(3, 4)",
        "0..<\"a\"",
        "[1]..<n",
        "(1.5)..<n",
        "-1.5..<3",
        "0..<1.5 + 2.5",
        "1.5 + 2.5..<n",
    ] {
        let d = check(&format!("pub fn f(n: U32) {{\n  for _ in {head} {{ }}\n}}\n")).diagnostics;
        assert_eq!(d.iter().map(|d| d.code).collect::<Vec<_>>(), vec![Code::E0401], "{head}");
        assert!(!d[0].message.contains('?') && d[0].message.contains("integers"), "{head}: {}", d[0].message);
    }
}

/// The E0200 of a name the spec gives a builtin type names it, as written,
/// at each place it is named (§18.1, R-294); a name the spec does not give
/// stays the error of what does not exist.
#[test]
fn a_name_of_the_spec_this_version_has_not_is_its_e0200() {
    let one = |src: &str| {
        let a = check_in(src);
        assert_eq!(a.diagnostics.len(), 1, "{src}: {:?}", a.diagnostics);
        (a.diagnostics[0].code, a.diagnostics[0].message.clone())
    };
    let cases = [
        ("pub fn f() -> F32 {\n  F32.default()\n}\n", "the builtin value `F32.default`"),
        ("type K = F32\npub fn f() -> F32 {\n  K.default()\n}\n", "the builtin value `K.default`"),
        ("const Z: I32 = I32.default()\npub fn f() -> I32 { 1 }\n", "the builtin value `I32.default`"),
        ("pub fn f(x: [F32; U32.default]) -> F32 {\n  1.0\n}\n", "`U32.default`"),
        ("pub fn f(b: Bytes) {\n  let _ = Str.from_utf8(b)\n}\n", "the builtin name `Str.from_utf8`"),
        ("pub fn f(s: Str) -> Bytes {\n  s.as_bytes()\n}\n", "the builtin name `Str.as_bytes`"),
        ("pub fn f(b: Bytes) -> U32 {\n  b.len()\n}\n", "the builtin name `Bytes.len`"),
        ("pub fn f(a: Array[F32]) -> U32 {\n  a.len()\n}\n", "the builtin name `Array.len`"),
    ];
    for (src, name) in cases {
        let (code, message) = one(src);
        assert_eq!(code, Code::E0200, "{src}");
        assert!(message.contains(name), "{src}: {message}");
    }
    // Of the kind of what it is, as any member (§15.1).
    assert_eq!(one("pub fn f(x: F32.ZERO) {\n}\n").0, Code::E0308);
    assert_eq!(one("pub fn f(s: Str) -> Bytes {\n  Str.as_bytes(s)\n}\n").0, Code::E0308);
    // Not the name of another type, or not called (§6.1).
    assert_eq!(one("pub fn f() -> Char {\n  Char.default()\n}\n").0, Code::E0302);
    assert_eq!(one("pub fn f(a: Array[F32]) {\n  a.fill!(1.0)\n}\n").0, Code::E0413);
    assert_eq!(one("pub fn f(x: I32) -> I32 {\n  x.default()\n}\n").0, Code::E0413);
}

/// The note of a type an argument decides names the callee as it is written;
/// of what has no name it says "an argument" (§18.1, R-364).
#[test]
fn the_note_of_an_argument_names_the_callee_it_can() {
    let id = "fn id[T: Num](x: T) -> T {\n  x\n}\n";
    let ends = |src: String, end: &str| {
        let a = check(&src);
        let notes: Vec<_> = a.diagnostics.iter().flat_map(|d| &d.notes).map(|n| n.message.clone()).collect();
        assert!(notes.iter().any(|n| n.ends_with(end)), "{src}: {notes:?}");
    };
    ends(format!("{id}pub fn f() -> Bool {{\n  (id).(true)\n}}\n"), "here as an argument");
    ends(format!("{id}pub fn f() -> Bool {{\n  let g = id\n  g.(true)\n}}\n"), "here as an argument of `g`");
    let chain = "pub struct W { }\nimpl W {\n  pub fn me(self, n: U32) -> W {\n    W { }\n  }\n  pub fn go[T: Num](self, x: T) -> U32 {\n    1\n  }\n}\n";
    ends(format!("{chain}pub fn f(w: W) -> U32 {{\n  w.me(1).go(true)\n}}\n"), "here as an argument of `go`");
    ends(format!("{chain}pub fn f(w: W) -> U32 {{\n  w.go(true)\n}}\n"), "here as an argument of `w.go`");
    // The receiver is a call: the name is of the method, not of the receiver's
    // callee (R-362), with a parameter that a function type decides.
    let mapped = "pub struct R { }\nimpl R {\n  pub fn conv[F](self, f: fn(U32) -> F) -> U32 {\n    1\n  }\n}\n\
        pub struct H {\n  b: Buf[F32],\n}\nfn mk() -> R {\n  R { }\n}\nfn full(n: U32) -> H {\n  full(n)\n}\n";
    ends(format!("{mapped}pub fn f() -> U32 {{\n  mk().conv(full)\n}}\n"), "here as an argument of `conv`");
    ends(format!("{mapped}pub fn f(r: R) -> U32 {{\n  r.conv(full)\n}}\n"), "here as an argument of `r.conv`");
}

/// The candidate of an anonymous function written as an argument (§8.1): of
/// the outer one when its body has arguments of its own, of a `_` parameter;
/// none when more than the modes differ.
#[test]
fn an_anonymous_function_at_an_argument_has_the_candidate_of_move() {
    let candidates = |arg: &str| {
        let ap = "fn ap(f: fn(move U32) -> U32, x: U32) -> U32 {\n  f.(x)\n}\n";
        let src = format!("{ap}pub fn run() -> U32 {{\n  ap({arg}, 2)\n}}\n");
        let d = check_in(&src).diagnostics.remove(0);
        assert_eq!(d.code, Code::E0401, "{src}");
        d.fixes.len()
    };
    assert_eq!(candidates("fn(k: U32) -> U32 { ap(fn(move j: U32) -> U32 { j }, k) }"), 1);
    assert_eq!(candidates("fn(_: U32) -> U32 { 1 }"), 1);
    assert_eq!(candidates("fn(k: U32) -> U32 uses {Alloc} { k }"), 0);
}

/// The messages of the requirements of a type a later statement decides show
/// it as it is decided, and the way out the user has (§18.1; W5-02 U5b, U6).
#[test]
fn a_requirement_shows_what_is_decided_and_what_can_be_done() {
    let first = |src: &str| check_in(src).diagnostics.remove(0);
    let late = first("pub fn f() {\n  let xs = []\n  let _ = xs.get(0)\n  let _: [Buf[F32]; 0] = xs\n}\n");
    assert!(late.message.starts_with("`[Buf[F32]; 0]` has `get` only with"), "{}", late.message);
    assert!(late.notes[0].message.contains("as the annotation"), "{:?}", late.notes);
    let planar = first("pub fn f(xs: [Span[F32]; 2]) {\n  let _ = xs.get(0)\n}\n");
    assert_eq!(planar.code, Code::E0710);
    assert!(planar.notes.iter().any(|n| n.message.contains("`xs[k].get(i)`")), "{:?}", planar.notes);
    // `Buf.zeroed` called and as a value say the same.
    let held = "pub struct H {\n  b: Buf[F32],\n}\nfn eat(move b: Buf[H]) {\n}\n";
    for body in ["eat(Buf.zeroed(2))", "let g = Buf.zeroed\n  eat(g.(2))"] {
        let a = check_in(&format!("{held}pub fn f() uses {{Alloc}} {{\n  {body}\n}}\n"));
        // The first is of the heading of `eat`.
        let d = a.diagnostics.iter().rfind(|d| d.code == Code::E0416).expect("E0416");
        assert_eq!(d.message, "the element type of `Buf` must be Copy; `H` is not (§4.5)", "{body}");
    }
    // A parameter of std's is not one the user declares `?Dup`.
    let of_std = "use std.test.{Gen}\npub struct H {\n  b: Buf[F32],\n}\npub fn f(g: Gen[H]) {\n}\n";
    let d = check_in(of_std).diagnostics.remove(0);
    assert_eq!(d.message, "`H` is not Copy or Shared, so it does not satisfy `T: Dup` of `Gen` (§4.5)");
    let user = check_in(&format!("{held}fn own[T](x: T) {{ }}\npub fn f(move h: H) {{\n  own(h)\n}}\n"));
    let d = user.diagnostics.iter().rfind(|d| d.code == Code::E0416).expect("E0416");
    assert!(d.message.contains("unless it is declared `T: ?Dup`"), "{}", d.message);
}

/// A mismatch of function types shows the types its parts decide (§18.1),
/// and a float literal's E0405 says where its type goes (§2.4).
#[test]
fn the_text_of_function_types_and_of_an_open_literal() {
    let src = "fn c(g: fn(U32) -> Buf[F32]) -> U32 {\n  1\n}\npub fn f() -> U32 {\n  c(Buf.zeroed)\n}\n";
    let d = check_in(src).diagnostics.remove(0);
    assert_eq!(d.message, "expected `fn(U32) -> Buf[F32]`, found `fn(U32) -> Buf[F32] uses {Alloc}`");
    let d = check_in("pub fn f() -> I32 {\n  I32.trunc_from(2.5)\n}\n").diagnostics.remove(0);
    assert_eq!(d.code, Code::E0405);
    assert!(d.notes[0].message.contains("`let x: F32 = 2.5`"), "{:?}", d.notes);
}

#[test]
fn a_literal_in_a_part_of_the_types_is_the_text_of_the_types() {
    let take = "fn take[T](y: T, h: fn(T)) -> U32 {\n  1\n}\n";
    let cases = [
        ("fn g(inout x: F32) {\n}\n", "take(1, g)", "expected `fn({integer})`, found `fn(inout F32)`"),
        ("fn g(x: F32) {\n}\n", "take(1, g)", "expected `fn({integer})`, found `fn(F32)`"),
        ("fn g(x: F32) uses {Alloc} {\n}\n", "take(1, g)", "expected `fn({integer})`, found `fn(F32) uses {Alloc}`"),
        ("fn g(x: I32) uses {Alloc} {\n}\n", "take(1.5, g)", "expected `fn({float})`, found `fn(I32) uses {Alloc}`"),
    ];
    for (g, call, text) in cases {
        let src = format!("{g}{take}pub fn f() -> U32 {{\n  {call}\n}}\n");
        let d = check_in(&src).diagnostics.remove(0);
        assert_eq!((d.code, d.message.as_str()), (Code::E0401, text), "{src}");
    }
    // A literal itself keeps its own text.
    let d = check_in("pub fn f() -> Bool {\n  1\n}\n").diagnostics.remove(0);
    assert!(d.message.contains("literal cannot have type `Bool`"), "{}", d.message);
}

#[test]
fn the_receiver_of_an_e0710_shows_what_is_decided() {
    let src = "pub fn f() {\n  let xs = []\n  let _ = xs.get(0)\n  let _: [Span[F32]; 0] = xs\n}\n";
    let d = check_in(src).diagnostics.remove(0);
    assert_eq!(d.code, Code::E0710);
    assert!(d.message.contains("the element type of `get` of `[Span[F32]; 0]`"), "{}", d.message);
}

#[test]
fn a_path_over_lines_shows_its_names() {
    let cases = [
        ("pub fn f() -> F32 {\n  F32 // c\n    .default()\n}\n", Code::E0200, "the builtin value `F32.default`"),
        ("pub fn f(x: [F32; U32 // c\n  .default]) {\n}\n", Code::E0200, "`U32.default`"),
        ("pub fn f() -> Str {\n  Str\n    .default()\n}\n", Code::E0200, "the builtin value `Str.default`"),
        ("pub fn f(s: Str) -> Bytes {\n  Str // c\n    .as_bytes(s)\n}\n", Code::E0308, "`Str.as_bytes` is a method"),
    ];
    for (src, code, text) in cases {
        let d = check_in(src).diagnostics.remove(0);
        assert_eq!(d.code, code, "{src}");
        assert!(d.message.contains(text) && !d.message.contains('\n'), "{src}: {}", d.message);
    }
}

#[test]
fn only_a_call_of_a_missing_function_has_a_literal_to_write() {
    let d = check_in("pub fn f() -> F32 {\n  F32.default()\n}\n").diagnostics.remove(0);
    assert!(d.message.contains("the builtin value `F32.default`"), "{}", d.message);
    assert!(d.notes.iter().any(|n| n.message.contains("write the value as a literal")), "{:?}", d.notes);
    for src in ["pub fn f() {\n  let _ = F32.default\n}\n", "pub fn f(x: [F32; F32.default]) {\n}\n"] {
        let d = check_in(src).diagnostics.remove(0);
        assert_eq!(d.code, Code::E0200, "{src}");
        assert!(d.message.contains("the builtin name `F32.default`"), "{src}: {}", d.message);
        assert!(d.notes.is_empty(), "{src}: {:?}", d.notes);
    }
}

/// The text after each candidate of the one diagnostic of `src`.
fn after_candidates(src: &str) -> Vec<String> {
    let a = check(src);
    let [d] = &a.diagnostics[..] else { panic!("{src}: {:?}", a.diagnostics) };
    let applied = |f: &onsa_diag::Fix| onsa_diag::apply_text(src, &f.edits().iter().collect::<Vec<_>>()).unwrap();
    d.fixes.iter().map(applied).collect()
}

/// §6.1, §18.1: the line break becomes the operator; a comment in it stays,
/// and what is left of the line of `-b` too.
#[test]
fn the_joined_line_keeps_the_comments() {
    let head = "fn f(a: I32, b: I32) -> I32 {\n  a";
    for (rest, joined) in [
        ("\n  -b\n}\n", " - b\n}\n"),
        ("\n\n\n  -b\n}\n", " - b\n}\n"),
        ("\n  -b // c\n}\n", " - b // c\n}\n"),
        (" // c\n  -b\n}\n", " - b // c\n}\n"),
        (" // c\n\n  // d\n  -b // e\n}\n", " - b // c\n\n  // d\n  // e\n}\n"),
        (" // c\n  -b }\n", " - b // c\n  }\n"),
    ] {
        let src = format!("{head}{rest}");
        assert_eq!(after_candidates(&src)[1], format!("{head}{joined}"), "{rest}");
    }
}

/// §6.1: `a - b` is the reading of the joined line only when `a` is the left
/// operand there: the groups of §3.1, no `as` (an E0011 unparenthesized,
/// §3.1), and no block form (§3.3).
#[test]
fn the_joined_line_needs_a_left_operand() {
    for a in ["if c { a } else { b }", "{ a }", "match c { _ => a }", "a & b", "a % b", "a as I32"] {
        let src = format!("fn f(c: Bool, a: I32, b: I32) -> I32 {{\n  {a}\n  -b\n}}\n");
        assert_eq!(after_candidates(&src).len(), 1, "{a}");
    }
    for a in ["a + b", "a * b", "-a"] {
        let src = format!("fn f(c: Bool, a: I32, b: I32) -> I32 {{\n  {a}\n  -b\n}}\n");
        assert_eq!(after_candidates(&src).len(), 2, "{a}");
    }
}

/// §7, §18.1: the candidate takes the items after the statement and leaves
/// a comment at the end of the statement; `let` keeps its initializer.
#[test]
fn the_rest_of_the_block_goes_from_its_first_token() {
    let (head, rest) = ("fn f() -> I32 {\n  return 1 // why\n  ", "\n}\n");
    let src = format!("{head}let a = 2 // c\n  a{rest}");
    assert_eq!(after_candidates(&src), [format!("{head}{rest}")]);
    let src = "fn f() -> I32 {\n  let x = { return 1 } // why\n  x\n}\n";
    assert_eq!(after_candidates(src), ["fn f() -> I32 {\n  { return 1 } // why\n  \n}\n"]);
}

/// S-876: the look at the end of the body leaves no trace. A later trial
/// reads the literal as it was (`n` is a `U8` after the join), and a trial
/// around the E0503 keeps it to itself (§18.1: one diagnostic).
#[test]
fn the_look_at_the_end_of_the_body_is_undone() {
    let src = "fn g(x: U8) {}\nfn f() {\n  let n = 1\n  return\n  g(n)\n}\n";
    assert_eq!(after_candidates(src).len(), 2);
    let src = "fn f(a: I32) -> I32 {\n  a\n  -({ return 1\n    2 })\n}\n";
    assert_eq!(codes(src), [Code::E0418]);
}

/// §7, §18.1, S-886: the line after a `return` joins it, and a comment
/// between them stays where it is, as of E0418 above.
#[test]
fn the_joined_return_keeps_the_comments() {
    let head = "fn f(x: I32) -> I32 {\n  return";
    for (rest, joined) in [
        ("\n  x * 2\n}\n", " x * 2\n}\n"),
        ("\n\n  x * 2 // c\n}\n", " x * 2 // c\n}\n"),
        (" // c\n  x * 2\n}\n", " x * 2 // c\n}\n"),
        (" // c\n  x * 2 // d\n}\n", " x * 2 // c\n  // d\n}\n"),
    ] {
        let src = format!("{head}{rest}");
        assert_eq!(after_candidates(&src), [format!("{head}{joined}")], "{rest}");
    }
}

#[test]
fn the_e0406_of_a_constant_says_how_to_give_the_arguments() {
    let a = check_in(
        "pub struct R[T] { x: T }\nimpl[T] R[T] {\n  pub const A: U32 = 1\n  pub fn f(self) -> U32 { R.A }\n}\npub fn g() -> U32 { R.A }\n",
    );
    let notes: Vec<Vec<&str>> = (a.diagnostics.iter())
        .map(|d| {
            assert_eq!((d.code, d.fixes.len()), (Code::E0406, 0), "{d:?}");
            d.notes.iter().map(|n| n.message.as_str()).collect()
        })
        .collect();
    let alias = "give the type its arguments by an alias: `type R = R[…]`, then `R.A`";
    assert_eq!(notes, [vec![format!("{alias}; inside this `impl`, `Self.A`").as_str()], vec![alias]]);
}

#[test]
fn a_read_of_a_constant_of_a_bad_heading_is_not_held_to_its_arguments() {
    let src = "pub struct F[T, const N: U32] { a: [T; N] }\nimpl F[F32, 4] {\n  pub const X: U32 = 1\n}\ntype A = F[F32, 8]\npub fn g() -> U32 { A.X }\n";
    assert_eq!(codes(src), [Code::E0307]);
}

/// §4.5, S-898: `T.BITS` has no value before `T` is instantiated, in a
/// signature as in a body; a name the bounds do not give is not found there too.
#[test]
fn a_member_of_a_type_parameter_is_no_constant_expression() {
    let cases = [
        ("pub fn f[T: Int](x: [F32; T.BITS]) {\n}\n", Code::E0417),
        ("pub fn f[T: Int]() -> [F32; T.BITS + 1] {\n  [0.0; 1]\n}\n", Code::E0417),
        ("pub fn f[T: Int]() {\n  let _ = [0.0; T.BITS]\n}\n", Code::E0417),
        ("pub fn f[T: Int]() {\n  let _: [F32; T.BITS] = [0.0; 1]\n}\n", Code::E0417),
        ("pub struct R[T: Int] {\n  a: [F32; T.BITS],\n}\n", Code::E0417),
        ("pub fn f[T: Num](x: [F32; T.ONE]) {\n}\n", Code::E0302),
        ("pub fn f[T: Num]() {\n  let _ = [0.0; T.ONE]\n}\n", Code::E0302),
    ];
    for (src, code) in cases {
        let a = check_in(src);
        assert_eq!(a.diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(), [code], "{src}");
    }
}

/// S-238: the method a bound does not give says where it is, with no
/// candidate: `checked_neg`, of the signed integers, gives the form of `Int`.
#[test]
fn a_method_of_a_number_trait_the_bounds_do_not_give() {
    let cases = [
        ("pub fn f[T: Int](x: T) -> Option[T] {\n  x.checked_neg()\n}\n", "`T.ZERO.checked_sub(x)`"),
        ("pub fn f[T: Num + Int](x: T) -> Option[T] {\n  x.checked_neg()\n}\n", "`T.ZERO.checked_sub(x)`"),
        ("pub fn f[T: Num](x: T) -> Option[T] {\n  x.checked_add(x)\n}\n", "of `Int`"),
        ("pub fn f[T: Float](x: T) -> T {\n  x.div_euclid(x)\n}\n", "of `Int`"),
    ];
    for (src, text) in cases {
        let d = check_in(src).diagnostics.remove(0);
        assert_eq!(d.code, Code::E0413, "{src}");
        assert!(d.fixes.is_empty(), "{src}: {:?}", d.fixes);
        assert!(d.notes.iter().any(|n| n.message.contains(text)), "{src}: {:?}", d.notes);
    }
}
