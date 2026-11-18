//! The tests of the interpreter host (W7-19 U1a). The functions have a `for` (so they go to the host: a body of
//! expressions only is the evaluator's), or are generic. Each value is worked out by hand from the spec in the comment
//! of its constant; the one that a table host also gives is compared to the row of the table.

use super::*;
use crate::flow_ref::expr::{Eval, Frame, Stop};
use crate::flow_ref::expr_tests::{def_named, i32v, is, with_checked};
use crate::flow_ref::host::TableHost;
use crate::flow_ref::sema_view::View;
use onsa_core::{IntKind, Module, TypeDef};

const SRC: &str = "
use std.math.floor

struct P { x: I32, y: I32 }
enum Mode { Off, On(I32), Both(I32, F32) }

rt fn loopy(n: I32) -> I32 {
  var s = 0
  for i in 0..<n { s = s + i }
  s
}
rt fn mk(n: I32) -> P {
  var p = P { x: n, y: 0 }
  for i in 0..<n { p.y = p.y + i }
  p
}
rt fn dot(xs: [F32; 3], ys: [F32; 3]) -> F32 {
  var s = 0.0
  for i in 0..<3 { s = s + xs[i] * ys[i] }
  s
}
rt fn ramp() -> [F32; 3] {
  var a = [0.0; 3]
  var x = 0.0
  for i in 0..<3 {
    a[i] = x
    x = x + 0.5
  }
  a
}
rt fn evens() -> [U32; 3] {
  var a = [0; 3]
  for i in 0..<3 { a[i] = i * 2 }
  a
}
rt fn nothing(k: I32) -> [F32; 0] {
  var n = 0
  for _ in 0..<k { n = n + 1 }
  []
}
rt fn first_of(xs: [F32; 0]) -> I32 {
  var n = 5
  for _ in 0..<1 { n = n + 0 }
  n
}
rt fn bump(m: Mode) -> Mode {
  var k = 0
  for _ in 0..<2 { k = k + 1 }
  match m {
    Mode.Off => Mode.On(k),
    Mode.On(v) => Mode.Both(v, 1.5),
    Mode.Both(_, _) => Mode.Off,
  }
}
rt fn some_sum(n: I32) -> Option[I32] {
  var s = 0
  for i in 0..<n { s = s + i }
  if s > 0 { Some(s) } else { None }
}
rt fn keep(x: F32) -> F32 {
  var y = x
  for _ in 0..<1 { y = y * 1.0 }
  y
}
rt fn keep_u64(x: U64) -> U64 {
  var y = x
  for _ in 0..<1 { y = y }
  y
}
rt fn keep_i8(x: I8) -> I8 {
  var y = x
  for _ in 0..<1 { y = y }
  y
}
rt fn ident[T](x: T) -> T { x }
rt fn gadd[T: Int](x: T, y: T) -> Option[T] { x.checked_add(y) }
rt fn optn[T](o: Option[T]) -> I32 {
  var k = 0
  for _ in 0..<2 { k = k + 1 }
  match o {
    None => k,
    Some(_) => k + 10,
  }
}
rt fn zero_of[T: Num](x: [T; 0]) -> T {
  var s = T.ZERO
  for _ in 0..<1 { s = s + T.ZERO }
  s
}
rt fn count(xs: Span[F32]) -> I32 {
  var n = 0
  for _ in 0..<xs.len() { n = n + 1 }
  n
}
rt fn boom(n: I32) -> I32 {
  var s = 0
  for i in 0..<n { s = s + 10 / (3 - i) }
  s
}

const SUM5: I32 = loopy(5)
const MK: P = mk(4)
const DOT: F32 = dot([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])
const RAMP: [F32; 3] = ramp()
const EVENS: [U32; 3] = evens()
const NOTHING: [F32; 0] = nothing(2)
const EMPTY: [F32; 0] = []
const FIRST: I32 = first_of(EMPTY)
const B0: Mode = bump(Mode.Off)
const B1: Mode = bump(Mode.On(5))
const B2: Mode = bump(Mode.Both(1, 2.0))
const S0: Option[I32] = some_sum(0)
const S4: Option[I32] = some_sum(4)
const NZ: F32 = keep(-0.0)
const NAN: F32 = keep(F32.NAN)
const BIG: U64 = keep_u64(18446744073709551615)
const LOW: I8 = keep_i8(-128)
const ID_I: I32 = ident(7)
const ID_F: F32 = ident(2.5)
rt fn g8() -> I32 {
  let a: I8 = 100
  match gadd(a, a) {
    None => -1,
    Some(w) => w as I32,
  }
}
rt fn g32() -> I32 {
  let a: I32 = 100
  match gadd(a, a) {
    None => -1,
    Some(w) => w,
  }
}
rt fn view() -> I32 {
  let xs = [1.0, 2.0]
  count(xs)
}
const G8: I32 = g8()
const G32: I32 = g32()
const O_NONE_I: Option[I32] = None
const O_NONE_F: Option[F32] = None
const O_SOME: Option[I32] = Some(3)
const OPT_NONE_I: I32 = optn(O_NONE_I)
const OPT_NONE_F: I32 = optn(O_NONE_F)
const OPT_SOME: I32 = optn(O_SOME)
const ZERO_F: F32 = zero_of([])
const ZERO_I: I32 = zero_of([])
const EMPTY_I: [I32; 0] = ident([])
const EMPTY_F: [F32; 0] = ident([])
const VIEW: I32 = view()
const FLOOR: F32 = floor(2.75)
";

/// The constants `names` of `SRC`, evaluated with the interpreter host over the Core of the case (`core`), or over
/// none.
fn run(names: &[&'static str], core: bool) -> Vec<Eval> {
    let names = names.to_vec();
    with_checked(SRC, true, move |a| {
        let module = core.then(|| onsa_driver::lower_core(a).expect("the case lowers"));
        let wrappers = Wrappers::default();
        let mut host = InterpHost::new(module.as_ref(), &wrappers);
        let view = View::new(a);
        names
            .iter()
            .map(|n| {
                let (body, init) = view.const_init(def_named(a, n)).expect("a const with its tables");
                let mut frame = Frame::new(body);
                frame.host = Some(&mut host as &mut dyn FnHost);
                frame.eval(init)
            })
            .collect()
    })
}

fn one(name: &'static str) -> Eval {
    run(&[name], true).remove(0)
}

fn unavailable(r: &Eval, why: &str) {
    match r {
        Err(Stop { fault: Fault::Unavailable(w), .. }) => assert!(w.contains(why), "{w} does not say {why}"),
        other => panic!("not unavailable ({why}): {other:?}"),
    }
}

fn f32s(xs: &[f32]) -> Value {
    Value::Array(xs.iter().map(|x| Value::F32(*x)).collect())
}

#[test]
fn a_function_with_a_for_is_run_by_the_interpreter() {
    // §10 `for i in 0..<5`: 0 + 1 + 2 + 3 + 4 = 10, the same as the row a test writes by hand for the table host.
    let got = one("SUM5");
    assert!(is(&got, &i32v(10)), "{got:?}");
    let by_table = with_checked(SRC, true, move |a| {
        let row = TableHost::default().with("t.loopy", |a| match &a[0] {
            Value::Int(_, n, _) => Ok(i32v((0..*n).sum())),
            _ => Err(Fault::Internal("not an integer")),
        });
        let view = View::new(a);
        let (body, init) = view.const_init(def_named(a, "SUM5")).expect("a const");
        let (mut frame, mut host) = (Frame::new(body), row);
        frame.host = Some(&mut host as &mut dyn FnHost);
        frame.eval(init)
    });
    assert!(is(&got, by_table.as_ref().expect("the table gives a value")));
}

#[test]
fn a_struct_an_array_and_an_enum_come_back_as_the_evaluator_holds_them() {
    // `mk(4)`: x is 4, y is 0 + 1 + 2 + 3 = 6, in the order of the declaration.
    assert!(is(&one("MK"), &Value::Struct(vec![i32v(4), i32v(6)])));
    // 1*4 + 2*5 + 3*6 = 32, exact in an F32.
    assert!(is(&one("DOT"), &Value::F32(32.0)));
    // 0.0 and then 0.5 more each turn (an array of F32 is the interpreter's fast form: it is an array here).
    assert!(is(&one("RAMP"), &f32s(&[0.0, 0.5, 1.0])));
    // i * 2 for i = 0, 1, 2 (the index of a `for` over `0..<3` is a U32).
    let u32v = |n| Value::int(IntKind::U32, n);
    assert!(is(&one("EVENS"), &Value::Array(vec![u32v(0), u32v(2), u32v(4)])));
    // The number of a variant is its place in the declaration (§4.1): Off 0, On 1, Both 2; k is 2 after two turns.
    assert!(is(&one("B0"), &Value::Enum { tag: 1, fields: vec![i32v(2)] }));
    assert!(is(&one("B1"), &Value::Enum { tag: 2, fields: vec![i32v(5), Value::F32(1.5)] }));
    assert!(is(&one("B2"), &Value::Enum { tag: 0, fields: vec![] }));
    // `Option` is `{ None, Some(T) }`: 0 + 1 + 2 + 3 = 6 is a `Some`, a sum of nothing is `None`.
    assert!(is(&one("S4"), &Value::Enum { tag: 1, fields: vec![i32v(6)] }));
    assert!(is(&one("S0"), &Value::Enum { tag: 0, fields: vec![] }));
}

#[test]
fn the_edges_of_the_scalars_and_the_empty_array_go_through_whole() {
    // §3.4: `-0.0 * 1.0` is `-0.0` (the sign is kept, and `same` tells it from `0.0`); a NaN stays a NaN.
    assert!(is(&one("NZ"), &Value::F32(-0.0)));
    assert!(!is(&one("NZ"), &Value::F32(0.0)));
    assert!(is(&one("NAN"), &Value::F32(f32::NAN)));
    // The ends of the integers: U64::MAX does not go through an `i64`, and I8::MIN is the least of its kind.
    assert!(is(&one("BIG"), &Value::int(IntKind::U64, u64::MAX as i128)));
    assert!(is(&one("LOW"), &Value::int(IntKind::I8, -128)));
    // `[F32; 0]` as an argument (the function says 5) and as the value back.
    assert!(is(&one("FIRST"), &i32v(5)));
    assert!(is(&one("NOTHING"), &Value::Array(vec![])));
}

#[test]
fn the_instance_of_a_generic_function_is_the_one_the_arguments_fit() {
    // `ident` has an instance for I32 and one for F32 (the same declaration).
    assert!(is(&one("ID_I"), &i32v(7)));
    assert!(is(&one("ID_F"), &Value::F32(2.5)));
    // `checked_add` of the instance for I8 is the one of I8: 100 + 100 = 200 is out of 127, `None` (-1 here); of I32 it is
    // 200. Run in the other instance, the answer would be the other one.
    assert!(is(&one("G8"), &i32v(-1)));
    assert!(is(&one("G32"), &i32v(200)));
    // `Some(3)` of an `Option[I32]` fits the instance for I32 only: k = 2 and `Some` adds 10.
    assert!(is(&one("OPT_SOME"), &i32v(12)));
}

#[test]
fn values_that_do_not_tell_the_instance_are_told_by_the_type_the_checker_gave_the_call() {
    // `None` fits `optn` of I32 and of F32 alike, and `optn(None)` is the `None` arm, k = 2 after two turns, in both.
    // `zero_of([])` has only the type of the call to tell the instance: T.ZERO is 0.0 of an F32 and 0 of an I32.
    assert!(is(&one("OPT_NONE_I"), &i32v(2)) && is(&one("OPT_NONE_F"), &i32v(2)));
    assert!(is(&one("ZERO_F"), &Value::F32(0.0)) && !is(&one("ZERO_F"), &Value::F32(-0.0)));
    assert!(is(&one("ZERO_I"), &i32v(0)));
}

#[test]
fn what_the_interpreter_cannot_be_given_or_found_is_unavailable() {
    // Two instances of `ident` (`[I32; 0]` and `[F32; 0]`) and a `[]`, which fits both and whose type is not a scalar the
    // names of the instances tell: it is not guessed.
    let both = run(&["EMPTY_I", "EMPTY_F"], true);
    both.iter().for_each(|r| unavailable(r, "two instances"));
    // A view has no form in the evaluator (the argument is an array, which the parameter takes as a view).
    unavailable(&one("VIEW"), "view");
    // A `target` function (`floor`) is no function of Core: its wrapper gives 2.0 (std_tests.rs has the std functions).
    assert!(is(&one("FLOOR"), &Value::F32(2.0)));
    // No Core: a case that does not lower.
    let none = run(&["SUM5", "ID_I"], false);
    none.iter().for_each(|r| unavailable(r, "no Core"));
}

/// The module of the test: a struct, an enum and a type with no fields known.
fn small_module() -> Module {
    let ty = |name: &str, kind| TypeDef { name: name.into(), kind };
    Module {
        types: vec![
            ty("S", TypeDefKind::Struct { fields: vec![("a".into(), Ty::Int(IntKind::U8)), ("b".into(), Ty::Bool)] }),
            ty("E", TypeDefKind::Enum { variants: vec![("A".into(), vec![]), ("B".into(), vec![Ty::Char])] }),
            ty("O", TypeDefKind::Opaque),
        ],
        consts: vec![],
        fns: vec![],
        messages: vec![],
        flows: vec![],
        moves: vec![],
    }
}

#[test]
fn a_value_that_is_not_of_the_type_of_its_place_is_an_internal_error() {
    let m = small_module();
    let internal = |t: &Ty, v: &Value| matches!(to_interp(&m, t, v), Err(Fault::Internal(_)));
    // An integer of another kind, a float of another width, an array of another length, a variant out of the enum,
    // a variant with an element fewer, a struct with a field fewer, a type with no fields known.
    assert!(internal(&Ty::Int(IntKind::I32), &Value::int(IntKind::U32, 1)));
    assert!(internal(&Ty::Float(FloatKind::F64), &Value::F32(1.0)));
    assert!(internal(&Ty::Array(Box::new(Ty::Bool), 2), &Value::Array(vec![Value::Bool(true)])));
    assert!(internal(&Ty::Enum(TypeId(1)), &Value::Enum { tag: 2, fields: vec![] }));
    assert!(internal(&Ty::Enum(TypeId(1)), &Value::Enum { tag: 1, fields: vec![] }));
    assert!(internal(&Ty::Struct(TypeId(0)), &Value::Struct(vec![Value::int(IntKind::U8, 1)])));
    assert!(internal(&Ty::Struct(TypeId(2)), &Value::Struct(vec![])));
    // And what fits goes through: S { a: 255, b: true }, B('x'), with the number of the variant kept.
    let s =
        to_interp(&m, &Ty::Struct(TypeId(0)), &Value::Struct(vec![Value::int(IntKind::U8, 255), Value::Bool(true)]));
    assert!(matches!(s, Ok(IValue::Struct(f)) if matches!(f[..], [IValue::U8(255), IValue::Bool(true)])));
    let e = to_interp(&m, &Ty::Enum(TypeId(1)), &Value::Enum { tag: 1, fields: vec![Value::Char('x')] });
    assert!(matches!(e, Ok(IValue::Enum { tag: 1, fields }) if matches!(fields[..], [IValue::Char('x')])));
}

#[test]
fn the_value_back_is_made_from_itself_and_a_view_has_no_form() {
    // Every kind of integer, by its own width; a tuple of none is the unit; an F32 array is an array of F32.
    let back = |v: IValue| from_interp(&v).expect("a value with a form");
    assert!(back(IValue::I16(-3)).same(&Value::int(IntKind::I16, -3)));
    assert!(back(IValue::U32(u32::MAX)).same(&Value::int(IntKind::U32, u32::MAX as i128)));
    assert!(back(IValue::Tuple(vec![])).same(&Value::Unit));
    assert!(back(IValue::Array(ArrayData::F32(vec![1.0, -0.0]))).same(&f32s(&[1.0, -0.0])));
    assert!(matches!(from_interp(&IValue::Fn(FnId(0))), Err(Fault::Unavailable(_))));
}

#[test]
fn a_panic_of_the_interpreter_is_a_host_panic() {
    // `boom(n)` sums 10 / (3 - i) for i in 0..<n: it divides by zero at i = 3 (§9.2), so `boom(4)` panics and
    // `boom(3)` is 10/3 + 10/2 + 10/1 = 3 + 5 + 10 = 18 (integer division truncates).
    let src = format!("{SRC}\nflow f(n: I32 at init) -> I32 at sample {{ boom(n) }}\n");
    let at = |n: i128| {
        with_checked(&src, true, move |a| {
            let module = onsa_driver::lower_core(a).expect("the case lowers");
            let wrappers = Wrappers::default();
            let mut host = InterpHost::new(Some(&module), &wrappers);
            let (view, def) = (View::new(a), def_named(a, "f"));
            let onsa_sema::DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("not a flow") };
            let body = view.body(def).expect("a flow with its tables");
            let mut frame = Frame::new(body);
            frame.host = Some(&mut host as &mut dyn FnHost);
            frame.locals.insert(body.input("n").expect("an input"), i32v(n));
            frame.eval(decl.body)
        })
    };
    assert!(is(&at(3), &i32v(18)));
    assert!(matches!(at(4), Err(Stop { fault: Fault::Panic(PanicKind::Host), .. })));
}
