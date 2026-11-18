//! The tests of the calls of the evaluator (W7-01 U5): the functions it evaluates itself (a body of expressions, §6.1,
//! §11.5), the ones it hands to the host (statements, a generic or `target` function, `move self`), the order of the
//! arguments (§3.5), where a panic is (§9.2) and the limit of 128 nested calls (§12.5). The values are worked out by hand
//! from the spec, in the comment of each; the rows of the table host are Rust, and give the value a call of that function
//! has by the spec.

use super::call::{DEPTH, evaluated};
use super::expr::{Eval, Frame, Limits, Stop};
use super::expr_tests::{consts, consts_with, def_named, i32v, is, panic_at, with_checked};
use super::host::{FnHost, HostCall, TableHost};
use super::limits_tests::keep_back;
use super::scalar::{Fault, PanicKind};
use super::sema_view::View;
use super::value::{IntKind, Value};
use onsa_sema::{DefKind, Ty};
use onsa_syntax::ast::{ExprKind, StmtKind};

/// Functions of every kind of body (the recursive ones are `fn`, which §10 lets recurse and §11.5 lets a flow call with
/// arguments at `init`: the inputs of `f` are at `init`). A body of `let`s and expressions is the evaluator's; `loopy`, `take`, `scaled`,
/// `ident` and `eat` have a statement, a generic or a `move self` and go to the host.
const FUNCS: &str = "
use std.math.floor
use std.math.abs
use std.math.min
use std.math.max

const K: I32 = rec(127)
const K2: I32 = loopy(4)

struct W[T] { v: T }
impl[T] W[T] {
  rt fn get(self) -> T { self.v }
}

struct P { x: I32, y: I32 }
impl P {
  rt fn new(x: I32) -> P { P { x: x, y: 0 } }
  rt fn sum(self) -> I32 { self.x + self.y }
  rt fn add(self, o: I32) -> I32 { self.x + o }
  rt fn scaled(self, k: I32) -> I32 {
    var s = 0
    for _ in 0..<k { s = s + self.x }
    s
  }
  rt fn eat(move self) -> I32 { self.x }
}
rt fn eat2(move p: P) -> I32 { p.x }
rt fn tried(o: Option[I32]) -> Option[I32] {
  let v = o?
  Some(v + 1)
}
rt fn early(x: I32) -> I32 {
  if x < 0 { return 0 }
  x
}
rt fn applied(x: I32) -> I32 {
  let g: rt fn(I32) -> I32 = fn(y: I32) -> I32 { y + 1 }
  g.(x)
}
rt fn mk(x: I32) -> P { P { x: x, y: x * 2 } }
rt fn pair(a: I32, b: I32) -> (I32, I32) { (b, a + b) }
rt fn total(xs: [I32; 3]) -> I32 { xs[0] + xs[1] + xs[2] }
rt fn wrap01(x: F32) -> F32 { x - floor(x) }
rt fn clamp(x: I32, lo: I32, hi: I32) -> I32 { if x < lo { lo } else if x > hi { hi } else { x } }
rt fn sign(x: I32) -> I32 { match x { 0 => 0, n if n < 0 => -1, _ => 1 } }
rt fn same(a: I32, b: I32) -> Bool {
  let d = a - b
  d == 0
}
rt fn inc(x: I32) -> I32 { x + 1 }
rt fn twice(x: I32) -> I32 { inc(inc(x)) }
rt fn add2(a: I32, b: I32) -> I32 { a + b }
rt fn last(_: I32, y: I32) -> I32 { y }
rt fn boom(x: I32) -> I32 { 10 / x }
rt fn mid(x: I32) -> I32 { boom(x) + 1 }
fn rec(n: I32) -> I32 { if n == 0 { 0 } else { 1 + rec(n - 1) } }
fn forever(n: I32) -> I32 { forever(n + 1) }
fn readk(n: I32) -> I32 { if n == 0 { K } else { readk(n - 1) } }
fn deep_host(n: I32) -> I32 { if n == 0 { loopy(2) } else { deep_host(n - 1) } }
fn deep_floor(n: I32, x: F32) -> F32 { if n == 0 { floor(x) } else { deep_floor(n - 1, x) } }
rt fn via_host(n: I32) -> I32 { loopy(n) + 1 }
rt fn loopy(n: I32) -> I32 {
  var s = 0
  for i in 0..<n { s = s + i }
  s
}
rt fn take(a: I32, b: I32) -> I32 {
  var d = a
  d = d - b
  d
}
rt fn ident[T](x: T) -> T { x }
rt fn gadd[T: Int](x: T, y: T) -> Option[T] { x.checked_add(y) }
fn deep_prim(n: I32, x: I32) -> I32 { if n == 0 { abs(x) + min(x, 1) + max(x, 2) } else { deep_prim(n - 1, x) } }
struct R { x: I32 }
struct S { x: I32 }
impl R {
  rt fn lp(n: I32) -> I32 {
    var s = 0
    for i in 0..<n { s = s + i }
    s
  }
}
impl S {
  rt fn lp(n: I32) -> I32 {
    var s = 0
    for i in 0..<n { s = s + i }
    s
  }
}
";

/// The program with the flow `f` whose body is `body` (it may hold `let`s).
fn program(body: &str, ty: &str) -> String {
    format!(
        "{FUNCS}\nflow f(a: I32 at init, b: I32 at init, c: I32 at init, x: F32 at init, u: U32 at init) -> {ty} at sample {{\n{body}\n}}\n"
    )
}

/// The inputs of `f`: `a`, `b`, `c` and `x` (`u` is always 7).
type Ins = (i128, i128, i128, f32);

fn go(src: &str, ins: Ins, host: Option<TableHost>) -> Eval {
    go_with(src, ins, host, || super::expr::LIMITS)
}

fn go_with(src: &str, ins: Ins, host: Option<TableHost>, limits: fn() -> Limits) -> Eval {
    with_checked(src, true, move |a| {
        let (view, def) = (View::new(a), def_named(a, "f"));
        let DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("f is not a flow") };
        let body = view.body(def).expect("a flow with its tables");
        let mut host = host;
        let mut frame = Frame::new(body);
        frame.limits = limits();
        frame.host = host.as_mut().map(|h| h as &mut dyn FnHost);
        for (name, v) in [
            ("a", i32v(ins.0)),
            ("b", i32v(ins.1)),
            ("c", i32v(ins.2)),
            ("x", Value::F32(ins.3)),
            ("u", Value::int(super::value::IntKind::U32, 7)),
        ] {
            frame.locals.insert(body.input(name).expect("an input"), v);
        }
        frame.eval(decl.body)
    })
}

fn int(v: &[Value], at: usize) -> i128 {
    match &v[at] {
        Value::Int(_, i, _) => *i,
        other => panic!("not an integer: {other:?}"),
    }
}

fn row_floor(a: &[Value]) -> Result<Value, Fault> {
    match a {
        [Value::F32(x)] => Ok(Value::F32(x.floor())),
        _ => Err(Fault::Internal("floor of what is not an F32")),
    }
}

/// `loopy(n)` is the sum of `0 ..< n`.
fn row_loopy(a: &[Value]) -> Result<Value, Fault> {
    Ok(i32v((0..int(a, 0)).sum()))
}

/// `take(a, b)` is `a - b`.
fn row_take(a: &[Value]) -> Result<Value, Fault> {
    Ok(i32v(int(a, 0) - int(a, 1)))
}

/// `p.scaled(k)` is `k` times the first field.
fn row_scaled(a: &[Value]) -> Result<Value, Fault> {
    match &a[0] {
        Value::Struct(f) => Ok(i32v(int(f, 0) * int(a, 1))),
        other => panic!("not a struct: {other:?}"),
    }
}

/// The value `p.eat()` has when the host is the one to give it: not the field, so that the routing shows.
fn row_eat(_: &[Value]) -> Result<Value, Fault> {
    Ok(i32v(99))
}

/// The host's own value for `ident`, `early` and `applied`: not what the evaluator would give.
fn row_sentinel(_: &[Value]) -> Result<Value, Fault> {
    Ok(i32v(777))
}

/// `None`, the first variant of `Option` (the number of a variant is its place in the declaration).
fn row_none(_: &[Value]) -> Result<Value, Fault> {
    Ok(Value::Enum { tag: 0, fields: vec![] })
}

fn row_overflow(_: &[Value]) -> Result<Value, Fault> {
    Err(Fault::Panic(PanicKind::Overflow))
}

fn table() -> TableHost {
    TableHost::default()
        .with("math.floor", row_floor)
        .with("t.loopy", row_loopy)
        .with("t.take", row_take)
        .with("t.P.scaled", row_scaled)
        .with("t.P.eat", row_eat)
        .with("t.ident", row_sentinel)
        .with("t.early", row_sentinel)
        .with("t.applied", row_sentinel)
        .with("t.W.get", row_sentinel)
        .with("t.eat2", row_sentinel)
        .with("t.tried", row_none)
        .with("t.R.lp", |a| Ok(i32v(int(a, 0) + 100)))
        .with("t.S.lp", |a| Ok(i32v(int(a, 0) + 200)))
}

fn value(body: &str, ty: &str, ins: Ins) -> Eval {
    go(&program(body, ty), ins, Some(table()))
}

fn at(body: &str, ty: &str, ins: Ins) -> (PanicKind, String) {
    let src = program(body, ty);
    panic_at(&go(&src, ins, Some(table())), &src)
}

#[test]
fn a_body_of_expressions_is_evaluated_with_its_parameters_bound() {
    let ins = |a, b| (a, b, 0, 0.0);
    let v = |body: &str, a, b| value(body, "I32", ins(a, b));
    // §6.1 the value of a block is its last expression: `clamp(a, 0, 3)` takes the branch the comparisons choose.
    assert!(is(&v("clamp(a, 0, 3)", 5, 0), &i32v(3)));
    assert!(is(&v("clamp(a, 0, 3)", -2, 0), &i32v(0)));
    assert!(is(&v("clamp(a, 0, 3)", 2, 0), &i32v(2)));
    // §7 `match`: the guard of the arm `n if n < 0` is tried before `_`, and `0` first of all.
    assert!(is(&v("sign(a)", -7, 0), &i32v(-1)));
    assert!(is(&v("sign(a)", 0, 0), &i32v(0)));
    assert!(is(&v("sign(a)", 9, 0), &i32v(1)));
    // a `let` in the body: d = 5 - 3 = 2, 2 == 0 is false; d = 5 - 5 = 0 is true.
    assert!(is(&value("same(a, b)", "Bool", ins(5, 3)), &Value::Bool(false)));
    assert!(is(&value("same(a, b)", "Bool", ins(5, 5)), &Value::Bool(true)));
    // The parameters are bound by position, not by name: take is `a - b` of the arguments 9 and 4 (host), and
    // add2(a, b) of 7 and 1 is 8; the callee's `a` is not the caller's `a`.
    assert!(is(&v("add2(b, a)", 1, 7), &i32v(8)));
    // Nested calls: inc(inc(5)) is 7, and a call as an argument is evaluated before the call: inc(inc(inc(a))) = a + 3.
    assert!(is(&v("twice(a)", 5, 0), &i32v(7)));
    assert!(is(&v("inc(twice(inc(a)))", 5, 0), &i32v(9)));
    // A tuple returned: pair(3, 4) is (4, 3 + 4), and the elements read are 4 and 7: 11.
    assert!(is(&v("pair(a, b).0 + pair(a, b).1", 3, 4), &i32v(11)));
    // A struct returned and its field: mk(4) is P { x: 4, y: 8 }.
    assert!(is(&v("mk(a).y", 4, 0), &i32v(8)));
    // An array argument is a value: 1 + 2 + 3.
    assert!(is(&v("total([a, b, a + b])", 1, 2), &i32v(6)));
    // A parameter `_` is not bound, and the second is read: last(1, 9) is 9.
    assert!(is(&v("last(a, b)", 1, 9), &i32v(9)));
    // A float function whose body calls a `target` one (the host's `floor`): 2.75 - floor(2.75) = 0.75, and
    // -0.25 - floor(-0.25) = -0.25 + 1 = 0.75.
    assert!(is(&value("wrap01(x)", "F32", (0, 0, 0, 2.75)), &Value::F32(0.75)));
    assert!(is(&value("wrap01(x)", "F32", (0, 0, 0, -0.25)), &Value::F32(0.75)));
}

#[test]
fn associated_functions_and_methods_are_called_with_the_receiver_first() {
    let v = |body: &str, a, b| value(body, "I32", (a, b, 0, 0.0));
    // `P.new(3)` is P { x: 3, y: 0 }, and `.add(4)` is 3 + 4.
    assert!(is(&v("P.new(a).add(b)", 3, 4), &i32v(7)));
    // mk(4) is P { x: 4, y: 8 }: sum is 12; and the receiver of a method is any expression, here a method call.
    assert!(is(&v("mk(a).sum()", 4, 0), &i32v(12)));
    assert!(is(&v("P.new(mk(a).sum()).add(1)", 4, 0), &i32v(13)));
    // A method with statements is the host's, and it gets the receiver first: scaled(P { x: 3, y: 6 }, 4) = 12.
    assert!(is(&v("mk(a).scaled(b)", 3, 4), &i32v(12)));
}

#[test]
fn arguments_are_evaluated_from_the_left_and_before_the_call() {
    let ins = (7, 0, 0, 0.0);
    // §3.5: left to right, and the first panic is the one reported (§3.5 "panic しうる式が複数あるときは、この順"):
    // `xs[u]` (`u` is 7, an index out of 3) is before `1 / c`, and `1 / c` before `xs[u]` in the other order.
    let xs = "let xs = [a, b, c]\n";
    let (kind, text) = at(&format!("{xs}add2(xs[u], 1 / c)"), "I32", ins);
    assert_eq!((kind, text.as_str()), (PanicKind::Bounds, "xs[u]"));
    let (kind, text) = at(&format!("{xs}add2(1 / c, xs[u])"), "I32", ins);
    assert_eq!((kind, text.as_str()), (PanicKind::DivZero, "1 / c"));
    // The receiver before the arguments: `mk(5 / c)` is the receiver and panics before `6 / b` is evaluated.
    let (kind, text) = at("mk(5 / c).add(6 / b)", "I32", ins);
    assert_eq!((kind, text.as_str()), (PanicKind::DivZero, "5 / c"));
    // The arguments are evaluated before the body: `boom(1 / c)` panics at the argument, not in `boom` (`10 / x`).
    let (kind, text) = at("boom(1 / c)", "I32", ins);
    assert_eq!((kind, text.as_str()), (PanicKind::DivZero, "1 / c"));
    // An argument for a `_` is evaluated all the same: `last(10 / c, b)` with c = 0 panics, with c = 2 it is b.
    let (kind, text) = at("last(10 / c, b)", "I32", ins);
    assert_eq!((kind, text.as_str()), (PanicKind::DivZero, "10 / c"));
    assert!(is(&value("last(10 / c, b)", "I32", (0, 5, 2, 0.0)), &i32v(5)));
    // The arguments of the host's functions go in the order written: take(9, 4) is 9 - 4.
    assert!(is(&value("take(a, b)", "I32", (9, 4, 0, 0.0)), &i32v(5)));
}

#[test]
fn a_panic_inside_a_function_is_at_the_expression_of_its_body() {
    let ins = (0, 0, 0, 0.0);
    // §9.2: the position is the panicking expression, `10 / x` of `boom`; the calls it was in are `calls`. Through a
    // second call (`mid`) the position is the same.
    for body in ["boom(c)", "mid(c)", "twice(boom(c))"] {
        let (kind, text) = at(body, "I32", ins);
        assert_eq!((kind, text.as_str()), (PanicKind::DivZero, "10 / x"), "{body}");
    }
    // The value when the divisor is 5: boom is 10 / 5 = 2, mid is 3.
    assert!(is(&value("mid(c)", "I32", (0, 0, 5, 0.0)), &i32v(3)));
    // A call that is not made does not panic: the branch not taken, and the right side of `&&` that the left decides.
    assert!(is(&value("if c == 0 { 1 } else { boom(c) }", "I32", ins), &i32v(1)));
    assert!(is(&value("c != 0 && same(boom(c), b)", "Bool", ins), &Value::Bool(false)));
}

#[test]
fn what_the_evaluator_does_not_evaluate_goes_to_the_host() {
    let v = |body: &str, ty: &str, ins: Ins| value(body, ty, ins);
    // A `for` and a `var` in the body: loopy(4) is 0 + 1 + 2 + 3 = 6, and the call in the body of a plain function
    // goes to the host too: via_host(4) = 6 + 1.
    assert!(is(&v("loopy(a)", "I32", (4, 0, 0, 0.0)), &i32v(6)));
    assert!(is(&v("via_host(a)", "I32", (4, 0, 0, 0.0)), &i32v(7)));
    // A generic function, with its type argument written or inferred, and a `move self` method: the host's value (the
    // table's `eat` is 99, and the evaluator would give the field 3).
    assert!(is(&v("ident(a)", "I32", (4, 0, 0, 0.0)), &i32v(777)));
    assert!(is(&v("ident::[I32](a)", "I32", (4, 0, 0, 0.0)), &i32v(777)));
    assert!(is(&v("mk(a).eat()", "I32", (3, 0, 0, 0.0)), &i32v(99)));
    // A `move` parameter of a function that is not a method, and `?` in a body: the evaluator would give 4 and Some(10)
    // (the `Some` of the table is not the first variant: `None` is 0, which is the host's value, and 5 below).
    assert!(is(&v("eat2(mk(a))", "I32", (4, 0, 0, 0.0)), &i32v(777)));
    assert!(is(&v("match tried(Some(a)) { None => 5, Some(w) => w }", "I32", (9, 0, 0, 0.0)), &i32v(5)));
    // A method of a generic type has its type arguments in its instance, and is the host's though its own list is empty.
    assert!(is(&v("W { v: a }.get()", "I32", (4, 0, 0, 0.0)), &i32v(777)));
    // An early `return` and a closure in the body are not expressions of the list: 777 where the evaluator would have
    // the value of the branch not returned (4) and of the closure called (5).
    assert!(is(&v("early(a)", "I32", (4, 0, 0, 0.0)), &i32v(777)));
    assert!(is(&v("applied(a)", "I32", (4, 0, 0, 0.0)), &i32v(777)));
    // The host is given back after each call and after a `const`: the const `K2` is `loopy(4)` = 6 from the host, and
    // the call after it still has the host (6 + 6); a plain function's call to the host, then the host again, 7 + 6.
    assert!(is(&v("K2", "I32", (0, 0, 0, 0.0)), &i32v(6)));
    assert!(is(&v("K2 + loopy(a)", "I32", (4, 0, 0, 0.0)), &i32v(12)));
    assert!(is(&v("via_host(a) + loopy(a)", "I32", (4, 0, 0, 0.0)), &i32v(13)));
    // The panic of a host is at the call (the evaluator has no other position for it).
    let src = program("loopy(a) + 1", "I32");
    let table = TableHost::default().with("t.loopy", row_overflow);
    let r = go(&src, (4, 0, 0, 0.0), Some(table));
    assert_eq!(panic_at(&r, &src), (PanicKind::Overflow, "loopy(a)".to_string()));
}

/// A host that writes down what it is asked: the name of the function, whether it is a method, the type arguments and
/// the number of arguments (the receiver is the first), and answers 1.
#[derive(Default)]
struct Recorder(Vec<(String, bool, Vec<Ty>, usize)>);

impl FnHost for Recorder {
    fn call(&mut self, call: HostCall) -> Result<Value, Fault> {
        let (view, callee) = (call.view, call.callee);
        let args = callee.type_args.iter().map(|t| view.ty(*t).clone()).collect();
        self.0.push((view.qualified_name(callee.def), callee.method, args, call.args.len()));
        Ok(i32v(1))
    }
}

#[test]
fn the_host_is_told_the_function_the_kind_the_type_arguments_and_the_arguments() {
    let src = program("ident::[I32](a) + mk(a).eat() + take(a, b) + W { v: a }.get()", "I32");
    let rec = with_checked(&src, true, |a| {
        let (view, def) = (View::new(a), def_named(a, "f"));
        let DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("f is not a flow") };
        let body = view.body(def).expect("a flow with its tables");
        let mut rec = Recorder::default();
        let mut frame = Frame::new(body);
        frame.host = Some(&mut rec);
        for (name, v) in [("a", i32v(1)), ("b", i32v(2)), ("c", i32v(3)), ("x", Value::F32(0.5))] {
            frame.locals.insert(body.input(name).expect("an input"), v);
        }
        frame.locals.insert(body.input("u").expect("an input"), Value::int(super::value::IntKind::U32, 7));
        // The host answers 1 for each of the four calls: the sum is 4.
        assert!(is(&frame.eval(decl.body), &i32v(4)));
        rec.0
    });
    let i32t = Ty::Int(onsa_sema::ty::IntKind::I32);
    // In the order of the evaluation (§3.5): the generic function with its one type argument I32, the method with its
    // receiver (2 values), the function of two, and the method of the generic type with the argument of its instance.
    let want = [
        ("t.ident", false, vec![i32t.clone()], 1),
        ("t.P.eat", true, vec![], 1),
        ("t.take", false, vec![], 2),
        ("t.W.get", true, vec![i32t], 1),
    ];
    assert_eq!(rec.len(), 4, "{rec:?}");
    for (got, want) in rec.iter().zip(want) {
        assert_eq!((got.0.as_str(), got.1, &got.2, got.3), (want.0, want.1, &want.2, want.3));
    }
}

#[test]
fn without_a_host_or_a_row_a_call_to_it_is_unavailable() {
    let unavailable = |r: &Eval, what: &str| {
        assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(w), .. }) if w.contains(what)), "{r:?}");
    };
    // No host: a function with a `for` is `Unavailable("a call")`, a plain one still has its value, and so does one that
    // calls a `target` function only by way of the host (floor).
    let (loopy, twice, wrap) = (program("loopy(a)", "I32"), program("twice(a)", "I32"), program("wrap01(x)", "F32"));
    unavailable(&go(&loopy, (4, 0, 0, 0.0), None), "a call");
    assert!(is(&go(&twice, (4, 0, 0, 0.0), None), &i32v(6)));
    unavailable(&go(&wrap, (0, 0, 0, 2.5), None), "a call");
    // A table without the row of the function.
    unavailable(&go(&loopy, (4, 0, 0, 0.0), Some(TableHost::default())), "no row");
    unavailable(&go(&program("ident(a)", "I32"), (4, 0, 0, 0.0), Some(TableHost::default())), "no row");
}

#[test]
fn nested_calls_are_limited_to_128_and_the_129th_panics_at_the_call() {
    assert_eq!(DEPTH, 128);
    let rec = |n| go(&program("let r = rec(a)\nr", "I32"), (n, 0, 0, 0.0), Some(table()));
    // §12.5: the entry (the body of the flow) is 0. rec(127) calls rec(126) ... rec(0): 128 calls, the last at depth 128.
    assert!(is(&rec(127), &i32v(127)));
    // rec(128) would call rec(0) at depth 129: it panics at the call `rec(n - 1)` in the body, the interpreter's place.
    let src = program("let r = rec(a)\nr", "I32");
    let (kind, text) = panic_at(&rec(128), &src);
    assert_eq!((kind, text.as_str()), (PanicKind::Depth, "rec(n - 1)"));
    // Without an end the recursion stops there too, and never uses the stack the guard keeps.
    let src = program("let r = forever(a)\nr", "I32");
    let r = go(&src, (0, 0, 0, 0.0), Some(table()));
    assert_eq!(panic_at(&r, &src), (PanicKind::Depth, "forever(n + 1)".to_string()));
    // The calls the host answers are counted, as the interpreter counts the function it runs: deep_host(126) calls
    // loopy at depth 128 and has its value (loopy(2) = 0 + 1), deep_host(127) calls it at 129.
    let deep = |n| go(&program("let r = deep_host(a)\nr", "I32"), (n, 0, 0, 0.0), Some(table()));
    assert!(is(&deep(126), &i32v(1)));
    let (kind, text) = panic_at(&deep(127), &program("let r = deep_host(a)\nr", "I32"));
    assert_eq!((kind, text.as_str()), (PanicKind::Depth, "loopy(2)"));
    // A `target` function is a primitive and not a call (§12.5): floor at depth 128 is fine, the recursion above it is not.
    let src = program("let r = deep_floor(a, x)\nr", "F32");
    let floor = |n| go(&src, (n, 0, 0, 1.5), Some(table()));
    assert!(is(&floor(127), &Value::F32(1.0)));
    let (kind, text) = panic_at(&floor(128), &src);
    assert_eq!((kind, text.as_str()), (PanicKind::Depth, "deep_floor(n - 1, x)"));
}

#[test]
fn a_const_is_counted_from_its_own_entry() {
    // §12.5: K is rec(127), 128 calls deep by itself. readk(100) reads it at depth 101; had K counted from there, its
    // call would be at 229. Its own entry makes it 127.
    let src = program("let r = readk(a)\nr", "I32");
    assert!(is(&go(&src, (100, 0, 0, 0.0), Some(table())), &i32v(127)));
    // And the initializer of a const is evaluated the same way by itself.
    assert!(is(&consts(&program("0", "I32"), &["K"])[0], &i32v(127)));
}

#[test]
fn the_stack_guard_stops_a_deep_recursion_of_calls() {
    // The calls use stack as every nesting does (about a few KB for each level): with 100 K under what is left kept
    // back, 3 levels pass and 100 stop before the limit of 128 is near, whatever the limit of calls would say.
    let src = program("let r = rec(a)\nr", "I32");
    let run = |n| go_with(&src, (n, 0, 0, 0.0), Some(table()), || keep_back(100 << 10));
    assert!(is(&run(3), &i32v(3)));
    let r = run(100);
    assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })), "{r:?}");
}

#[test]
fn a_body_the_check_rules_out_is_not_evaluated() {
    // A function whose body has a type error, or a name that is not there: the tables of its body are not whole, and
    // the call to it is `Unavailable` (not a value, and not the host's), as is the flow that has the error itself.
    for bad in ["x + true", "y", "undefined_fn(x)"] {
        let src = program("mine(a)", "I32") + &format!("rt fn mine(x: I32) -> I32 {{ {bad} }}\n");
        let r = with_checked(&src, false, |a| {
            let (view, def) = (View::new(a), def_named(a, "f"));
            let DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("not a flow") };
            let mut frame = Frame::new(view.body(def).expect("the flow itself is whole"));
            frame.locals.insert(frame.body.input("a").expect("an input"), i32v(1));
            frame.eval(decl.body)
        });
        assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(w), .. }) if w.contains("tables")), "{bad}: {r:?}");
    }
    let src = program("1 + true", "I32");
    let flow = with_checked(&src, false, |a| View::new(a).body(def_named(a, "f")).is_err());
    assert!(flow, "the body of a flow with a type error has no whole tables");
}

/// A function for each form a body may be made of: `evaluated` of each by hand (a body of the forms of `evaluates` is the
/// evaluator's, any other goes to the host), and for the first group the value of `k(5)` by hand. The functions of the
/// second group are not called. A form of the syntax a function cannot write has no function: `_`, `^x`, `par~`, `f~(x)`
/// (flows only), `a..<b` (a `for` head, a statement) and `at` (E0821).
const KINDS: &str = "
struct P { x: I32, y: I32 }
impl P {
  rt fn sum(self) -> I32 { self.x + self.y }
  rt fn id(x: I32) -> I32 { x }
}
const THREE: I32 = 3
rt fn inc(x: I32) -> I32 { x + 1 }
rt fn ident[T](x: T) -> T { x }
rt fn ap(g: rt fn(I32) -> I32, x: I32) -> I32 { g.(x) }
rt fn k_paren(x: I32) -> I32 { (x) }
rt fn k_cast(x: I32) -> I64 { x as I64 }
rt fn k_tuple(x: I32) -> I32 { (x, x + 1).1 }
rt fn k_array(x: I32) -> I32 { [x, x + 1][1] }
rt fn k_repeat(x: I32) -> I32 { [x; 3][2] }
rt fn k_struct(x: I32) -> I32 { P { x: x, y: 7 }.y }
rt fn k_unary(x: I32) -> I32 { -x }
rt fn k_match(x: I32) -> I32 { match x { 5 => 50, _ => 0 } }
rt fn k_if(x: I32) -> I32 { if x > 3 { 2 } else { 3 } }
rt fn k_let(x: I32) -> I32 {
  let y = x + 1
  y
}
rt fn k_call(x: I32) -> I32 { inc(x) }
rt fn k_method(x: I32) -> I32 { P { x: x, y: 0 }.sum() }
rt fn k_assoc(x: I32) -> I32 { P.id(x) }
rt fn k_const(x: I32) -> I32 { THREE + x }
rt fn k_named(x: I32) -> F32 { F32.PI }
rt fn k_variant(x: I32) -> I32 { match Some(x) { Some(v) => v, None => 0 } }
rt fn k_typeargs(x: I32) -> I32 { ident::[I32](x) }
rt fn k_panic(x: I32) -> I32 { if x < 0 { panic(\"neg\") } else { x } }
rt fn k_str(x: I32) -> I32 {
  let _ = \"abc\"
  x
}
rt fn k_closure(x: I32) -> I32 {
  let g: rt fn(I32) -> I32 = fn(y: I32) -> I32 { y + 1 }
  g.(x)
}
rt fn k_fnvalue(x: I32) -> I32 { ap(inc, x) }
rt fn k_fnvalue2(x: I32) -> I32 { ap(P.id, x) }
rt fn k_valuecall(g: rt fn(I32) -> I32, x: I32) -> I32 { g.(x) }
rt fn k_try(x: I32) -> Option[I32] {
  let v = Some(x)?
  Some(v)
}
rt fn k_var(x: I32) -> I32 {
  var s = x
  s = s + 1
  s
}
rt fn k_return(x: I32) -> I32 {
  if x < 0 { return 0 }
  x
}
rt fn k_move(x: I32) -> I32 {
  let p = P { x: x, y: 0 }
  let q = move p
  q.x
}
";

#[test]
fn the_evaluator_evaluates_the_forms_of_the_list_and_hands_the_others_to_the_host() {
    // §6.1, §9.2 `evaluated` (what `plain` asks): true for a body of the forms of `evaluates` only.
    let routes = [
        ("k_paren", true),
        ("k_cast", true),
        ("k_tuple", true),
        ("k_array", true),
        ("k_repeat", true),
        ("k_struct", true),
        ("k_unary", true),
        ("k_match", true),
        ("k_if", true),
        ("k_let", true),
        ("k_call", true),
        ("k_method", true),
        ("k_assoc", true),
        ("k_const", true),
        ("k_named", true),
        ("k_variant", true),
        ("k_typeargs", true),
        ("k_panic", true),
        // A string, a closure, a function as a value, the call of one, `?`, `var`, `return` and `move` are not.
        ("k_str", false),
        ("k_closure", false),
        ("k_fnvalue", false),
        ("k_fnvalue2", false),
        ("k_valuecall", false),
        ("k_try", false),
        ("k_var", false),
        ("k_return", false),
        ("k_move", false),
    ];
    let seen = with_checked(KINDS, true, move |a| {
        let view = View::new(a);
        let mut seen = std::collections::BTreeSet::new();
        for (name, want) in routes {
            let def = def_named(a, name);
            let body = view.body(def).expect("a function with its tables");
            let expr = a.analysis.def(def).as_fn().and_then(|f| f.body).expect("a body");
            assert_eq!(evaluated(&body, expr), want, "{name}");
            let mut todo = vec![expr];
            while let Some(e) = todo.pop() {
                let kind = format!("{:?}", body.ast.expr(e).kind);
                seen.insert(kind.split(|c: char| !c.is_alphanumeric()).next().unwrap_or("").to_string());
                todo.extend(body.ast.sub_exprs(e));
            }
        }
        seen
    });
    // Every form of the syntax a function body can write is among those the bodies above are made of (`unsafe` and
    // `handle` are E0200 in this version).
    for form in [
        "Lit",
        "Path",
        "Paren",
        "Tuple",
        "Array",
        "Repeat",
        "Struct",
        "Block",
        "If",
        "Match",
        "Closure",
        "Binary",
        "Cast",
        "Unary",
        "Call",
        "Field",
        "TypeArgs",
        "TupleIndex",
        "Index",
        "Try",
        "Move",
    ] {
        assert!(seen.contains(form), "no body above has the form {form}: {seen:?}");
    }
}

/// The host of the functions of [`KINDS`]: it writes down the names it is asked for, and answers 1.
#[derive(Default)]
struct Names(Vec<String>);

impl FnHost for Names {
    fn call(&mut self, call: HostCall) -> Result<Value, Fault> {
        self.0.push(call.view.qualified_name(call.callee.def));
        Ok(i32v(1))
    }
}

#[test]
fn a_body_of_every_form_of_the_list_has_its_value_from_the_arm_of_the_form() {
    // §6.1 etc. by hand with x = 5: (5); 5 as I64; (5, 6).1; [5, 6][1]; [5; 3][2]; P { x: 5, y: 7 }.y; -5; the arm `5`;
    // 5 > 3; `let y = 6`; inc(5); P { x: 5, y: 0 }.sum(); P.id(5); THREE + 5; F32.PI; Some(5) read back; the host's 1 (the one
    // function `ident` it is asked for, whose type argument is written in the body of `k_typeargs`); x when x >= 0.
    let calls = "k_paren(a), k_cast(a), k_tuple(a), k_array(a), k_repeat(a), k_struct(a), k_unary(a), k_match(a), k_if(a), \
                 k_let(a), k_call(a), k_method(a), k_assoc(a), k_const(a), k_named(a), k_variant(a), k_typeargs(a), k_panic(a)";
    let src = format!("{KINDS}\nflow f(a: I32 at init) -> I32 at sample {{ let _ = ({calls})\n 0 }}\n");
    let (value, asked) = with_checked(&src, true, |a| {
        let mut names = Names::default();
        let (view, def) = (View::new(a), def_named(a, "f"));
        let DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("f is not a flow") };
        let body = view.body(def).expect("a flow with its tables");
        let mut frame = Frame::new(body);
        frame.host = Some(&mut names);
        frame.locals.insert(body.input("a").expect("an input"), i32v(5));
        // The tuple of the calls is the initializer of the first `let` of the body (a flow's output is not a tuple).
        let ExprKind::Block(block) = &body.ast.expr(decl.body).kind else { panic!("a block") };
        let StmtKind::Let { init, .. } = &body.ast.stmt(block.stmts[0]).kind else { panic!("a let") };
        let value = frame.eval(*init);
        (value, std::mem::take(&mut names.0))
    });
    let want = [5, 5, 6, 6, 5, 7, -5, 50, 2, 6, 6, 5, 5, 8].map(i32v);
    let Ok(Value::Tuple(got, _)) = value else { panic!("{value:?}") };
    for (k, (g, w)) in got.iter().zip(want).enumerate().filter(|(k, _)| *k != 1) {
        assert!(g.same(&w), "element {k}: {g:?} is not {w:?}");
    }
    assert!(got[1].same(&Value::int(IntKind::I64, 5)), "{:?}", got[1]);
    assert!(got[14].same(&Value::F32(std::f32::consts::PI)), "{:?}", got[14]);
    assert!(got[15].same(&i32v(5)) && got[16].same(&i32v(1)) && got[17].same(&i32v(5)), "{got:?}");
    // Only `ident` was the host's: every other function of the list was evaluated by the evaluator.
    assert_eq!(asked, ["t.ident"]);
}

#[test]
fn a_panic_in_the_body_of_a_function_is_the_call_of_panic_and_not_a_host_call() {
    // §9.2: `panic("neg")` is a panic at its own expression, the call; the message is a literal and not evaluated. The
    // body of `k_panic` is the evaluator's (no host here): the branch not taken is no panic, and the one taken is, through
    // a call too.
    let go = |body: &str, a| {
        let src = format!("{KINDS}\nflow f(a: I32 at init) -> I32 at sample {{ {body} }}\n");
        let r = with_checked(&src, true, move |an| {
            let (view, def) = (View::new(an), def_named(an, "f"));
            let DefKind::Flow(decl) = &an.analysis.def(def).kind else { panic!("f is not a flow") };
            let body = view.body(def).expect("a flow with its tables");
            let mut frame = Frame::new(body);
            frame.locals.insert(body.input("a").expect("an input"), i32v(a));
            frame.eval(decl.body)
        });
        (r, src)
    };
    assert!(is(&go("k_panic(a)", 3).0, &i32v(3)));
    assert!(is(&go("inc(k_panic(a))", 3).0, &i32v(4)));
    for body in ["k_panic(a)", "inc(k_panic(a))", "k_panic(a) + 1"] {
        let (r, src) = go(body, -3);
        assert_eq!(panic_at(&r, &src), (PanicKind::Explicit, "panic(\"neg\")".to_string()), "{body}");
    }
}

#[test]
fn the_functions_of_two_types_with_a_member_of_the_same_name_have_rows_of_their_own() {
    // `R.lp` and `S.lp` have a `for`, so they are the host's: the rows are `t.R.lp` (n + 100) and `t.S.lp` (n + 200), and
    // R.lp(1) * 1000 + S.lp(2) is 101 * 1000 + 202. Under one name for both the two would have the same row.
    let v = value("R.lp(a) * 1000 + S.lp(b)", "I32", (1, 2, 0, 0.0));
    assert!(is(&v, &i32v(101_202)), "{v:?}");
}

#[test]
fn a_target_function_with_a_body_is_not_a_call_at_the_depth_128() {
    // §12.5 `abs`, `min` and `max` of `I32` are `target` and have a body (`else`): at the depth 128 they are not counted, as
    // `floor` is not, and the host is given them (it answers 1 for each: 3). The recursion above is counted: the 129th call
    // is `deep_prim(n - 1, x)` with n = 128.
    let go = |n| {
        let src = program("let r = deep_prim(a, b)\nr", "I32");
        let src2 = src.clone();
        let (r, asked) = with_checked(&src, true, move |an| {
            let (view, def) = (View::new(an), def_named(an, "f"));
            let DefKind::Flow(decl) = &an.analysis.def(def).kind else { panic!("f is not a flow") };
            let body = view.body(def).expect("a flow with its tables");
            let (mut frame, mut names) = (Frame::new(body), Names::default());
            frame.host = Some(&mut names);
            frame.locals.insert(body.input("a").expect("an input"), i32v(n));
            frame.locals.insert(body.input("b").expect("an input"), i32v(-4));
            let r = frame.eval(decl.body);
            (r, std::mem::take(&mut names.0))
        });
        (r, asked, src2)
    };
    let (r, asked, _) = go(127);
    assert!(is(&r, &i32v(3)), "{r:?}");
    assert_eq!(asked.len(), 3, "{asked:?}");
    let (r, _, src) = go(128);
    assert_eq!(panic_at(&r, &src), (PanicKind::Depth, "deep_prim(n - 1, x)".to_string()));
}

#[test]
fn the_chain_of_constants_goes_on_into_the_function_that_reads_one() {
    // §2.5 of the limit of the evaluator: `Ck` is `gk()` and `gk` reads `C(k-1)` (the row of the checker is not read:
    // `most` is 0). The chain of 256 has its value, the 257th stops with `Unavailable`; had a call begun a chain of its
    // own, the chain would never be 256 long and the stack would stop it.
    let mut src = String::from("const C0: I32 = 1 + 0\n");
    for k in 1..=257 {
        src += &format!("fn g{k}() -> I32 {{ C{} + 1 }}\nconst C{k}: I32 = g{k}()\n", k - 1);
    }
    let names: &'static [&'static str] = &["C1", "C128", "C256", "C257"];
    let got = consts_with(&src, names, || Limits { reserve: super::expr::LIMITS.reserve, most: 0 });
    for ((name, got), want) in names.iter().zip(&got).zip([2, 129, 257]) {
        assert!(is(got, &i32v(want)), "{name}: {got:?}");
    }
    assert!(
        matches!(&got[3], Err(Stop { fault: Fault::Unavailable(w), .. }) if w.contains("too deep")),
        "{:?}",
        got[3]
    );
}

#[test]
fn the_arguments_are_bound_by_position_and_a_number_that_differs_is_an_internal_error() {
    let src = program("inc(a)", "I32");
    with_checked(&src, true, |an| {
        let (view, def) = (View::new(an), def_named(an, "f"));
        let DefKind::Flow(decl) = &an.analysis.def(def).kind else { panic!("f is not a flow") };
        let body = view.body(def).expect("a flow with its tables");
        let ExprKind::Block(block) = &body.ast.expr(decl.body).kind else { panic!("a block") };
        let call = block.tail.expect("the call");
        // The locals of `last(_: I32, y: I32)`: none for the `_`, and `y`; of `add(self, o: I32)`: `self` and `o`.
        let locals = |name: &str| {
            let (def, f) = (def_named(an, name), an.analysis.def(def_named(an, name)).as_fn().expect("a function"));
            let body = view.body(def).expect("a function with its tables");
            let names: Vec<_> = body
                .params(f)
                .expect("params")
                .into_iter()
                .map(|l| l.map(|l| body.info.locals[l.0 as usize].name.clone()))
                .collect();
            names
        };
        assert_eq!(locals("last"), [None, Some("y".to_string())]);
        assert_eq!(locals("pair"), [Some("a".to_string()), Some("b".to_string())]);
        assert_eq!(locals("add"), [Some("self".to_string()), Some("o".to_string())]);
        // Three arguments for a function of one parameter: the evaluator does not drop two of them.
        let mut frame = Frame::new(body);
        let callee = body.callee(call).expect("the callee");
        let r = frame.invoke(&callee, vec![i32v(1), i32v(2), i32v(3)], call, body.ast.expr(call).span);
        assert!(matches!(r, Err(Stop { fault: Fault::Internal(_), .. })), "{r:?}");
        let r = frame.invoke(&callee, vec![], call, body.ast.expr(call).span);
        assert!(matches!(r, Err(Stop { fault: Fault::Internal(_), .. })), "{r:?}");
    });
}

#[test]
fn a_member_of_the_bound_of_a_type_parameter_is_not_a_callee_the_evaluator_names() {
    // `x.checked_add(y)` in `gadd[T: Int]` is a member of the bound `Int`: the `def` of the table is that of a representative
    // type, not the function called, and the callee is `Unavailable` (a generic body is the host's, which never asks).
    with_checked(&program("0", "I32"), true, |an| {
        let (view, def) = (View::new(an), def_named(an, "gadd"));
        let body = view.body(def).expect("a function with its tables");
        let tail = an.analysis.def(def).as_fn().and_then(|f| f.body).expect("a body");
        let ExprKind::Block(block) = &body.ast.expr(tail).kind else { panic!("a block") };
        let r = body.callee(block.tail.expect("the call"));
        assert!(matches!(&r, Err(Fault::Unavailable(w)) if w.contains("bound")), "{:?}", r.err());
    });
}

#[test]
fn a_local_the_signature_has_no_parameter_for_is_not_dropped() {
    // `pair(a, b)` with its last parameter taken off the signature leaves the local of `b` over: an error, not a call with
    // an argument less.
    with_checked(&program("0", "I32"), true, |an| {
        let (view, def) = (View::new(an), def_named(an, "pair"));
        let body = view.body(def).expect("a function with its tables");
        let mut f = an.analysis.def(def).as_fn().expect("a function").clone();
        assert_eq!(body.params(&f).map(|p| p.len()), Ok(2));
        f.params.pop();
        assert!(matches!(body.params(&f), Err(Fault::Unavailable(w)) if w.contains("signature")));
    });
}
