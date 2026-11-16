//! The tests of the aggregates, the patterns and `match` of the evaluator (W7-01 U4). A small source is checked, a
//! `const` or the body of a flow is evaluated, and the value (or the panic and its position) is compared with the one
//! worked out by hand from §2.4, §3.5, §4.4, §7, §9.2 and §11.2. A source that the check rules out is not evaluated.

use onsa_sema::{ConstValue, DefKind, Ty};

use super::expr::{Eval, Frame, Stop, from_const};
use super::expr_tests::{consts, def_named, flow, i32v, is, panic_at, with_checked};
use super::scalar::{Fault, PanicKind};
use super::sema_view::View;
use super::value::{IntKind, Value};

fn u32v(v: i128) -> Value {
    Value::int(IntKind::U32, v)
}
fn f(x: f32) -> Value {
    Value::F32(x)
}
fn tup(vs: Vec<Value>) -> Value {
    Value::tuple(vs)
}
fn arr(vs: Vec<Value>) -> Value {
    Value::Array(vs)
}
fn st(vs: Vec<Value>) -> Value {
    Value::Struct(vs)
}
fn en(tag: u32, fields: Vec<Value>) -> Value {
    Value::Enum { tag, fields }
}
fn ints(vs: &[i128]) -> Vec<Value> {
    vs.iter().map(|v| i32v(*v)).collect()
}

const LITERALS: &str = "
struct P { x: F32, y: F32 }
struct Q { a: I32, b: I32 = 5, c: F32 = 1.0 + 0.5 }
enum Mode { Off, Gain(F32), Pair(I32, I32) }
enum Dir { Up, Down, Hold }
const T: (I32, F32) = (1 + 1, 0.5)
const A: [I32; 3] = [1, 2, 3 * 3]
const R: [U8; 3] = [7; 3]
const R0: [U8; 0] = [7; 0]
const S: P = P { y: 2.0, x: 1.0 }
const Q1: Q = Q { a: 1, ... }
const Q2: Q = Q { c: 2.5, a: 1, ... }
const Q3: Q = Q { a: 1, b: 9, ... }
const U: () = ()
const E0: Mode = Mode.Off
const E1: Mode = Mode.Gain(2.0)
const E2: Mode = Mode.Pair(1, 2 + 1)
const O1: Option[I32] = Some(3)
const O0: Option[I32] = None
const NEST: ((I32, I32), [P; 2]) = ((1, 2), [S, P { x: 3.0, y: 4.0 }])
const OT: Option[(I32, Mode)] = Some((1, Mode.Off))
const D2: Dir = Dir.Hold
const D1: [Dir; 2] = [Dir.Down, Dir.Up]
";

#[test]
fn the_literals_of_the_aggregates_by_hand() {
    let names =
        &["T", "A", "R", "R0", "S", "Q1", "Q2", "Q3", "U", "E0", "E1", "E2", "O1", "O0", "NEST", "OT", "D2", "D1"];
    let u8v = |v| Value::int(IntKind::U8, v);
    let want = [
        // §3.4: 1 + 1 is 2.
        tup(vec![i32v(2), f(0.5)]),
        arr(ints(&[1, 2, 9])),
        // §2.4: `[e; N]` copies `e` to N places.
        arr(vec![u8v(7), u8v(7), u8v(7)]),
        arr(vec![]),
        // §4.4: the fields are held in the order of the declaration, whatever the order they are written in.
        st(vec![f(1.0), f(2.0)]),
        // §4.4: `...` fills the fields that are not written with the default of their declaration (b = 5, c = 1.0 + 0.5).
        st(vec![i32v(1), i32v(5), f(1.5)]),
        st(vec![i32v(1), i32v(5), f(2.5)]),
        st(vec![i32v(1), i32v(9), f(1.5)]),
        Value::Unit,
        // §4.4: a variant is its number in the declaration (Off 0, Gain 1, Pair 2).
        en(0, vec![]),
        en(1, vec![f(2.0)]),
        en(2, ints(&[1, 3])),
        // §4.1: `enum Option[T] { None, Some(T) }`.
        en(1, ints(&[3])),
        en(0, vec![]),
        // A constant by its name is a struct again, and the aggregates nest.
        tup(vec![tup(ints(&[1, 2])), arr(vec![st(vec![f(1.0), f(2.0)]), st(vec![f(3.0), f(4.0)])])]),
        en(1, vec![tup(vec![i32v(1), en(0, vec![])])]),
        // A variant with no elements is a value too, and its number is its place in the declaration (Hold is 2).
        en(2, vec![]),
        arr(vec![en(1, vec![]), en(0, vec![])]),
    ];
    let got = consts(LITERALS, names);
    for ((name, got), want) in names.iter().zip(&got).zip(&want) {
        assert!(is(got, want), "{name}: got {got:?}, want {want:?}");
    }
}

const ORDER: &str = "
struct Pr { x: I32, y: I32 }
enum Mode { Off, Gain(I32), Pair(I32, I32) }
flow tuple(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let t = (100 / a, 100 / b)
  t.0 + t.1
}
flow array(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let xs = [100 / a, 100 / b]
  xs[0] + xs[1]
}
flow record(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let p = Pr { y: 100 / b, x: 100 / a }
  p.x + p.y
}
flow variant(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  match Mode.Pair(100 / a, 100 / b) {
    Mode.Pair(p, q) => p + q,
    _ => 0,
  }
}
flow repeat(a: I32 at sample) -> I32 at sample {
  let xs = [100 / a; 3]
  xs[0] + xs[1] + xs[2]
}
flow none(a: I32 at sample) -> I32 at sample {
  let _ = [100 / a; 0]
  1
}
flow blank(z: I32 at sample) -> I32 at sample {
  let _ = 1 / z
  7
}
";

fn order(name: &'static str, a: i128, b: i128) -> Eval {
    let inputs = vec![("a", i32v(a)), ("b", i32v(b))];
    flow(ORDER, name, if name == "repeat" || name == "none" { inputs[..1].to_vec() } else { inputs })
}

#[test]
fn the_elements_are_evaluated_in_the_order_they_are_written() {
    // §3.5: tuple, array and struct literals evaluate in the order written, and the first panic is the one reported.
    // 100 / 5 = 20 and 100 / 10 = 10.
    for name in ["tuple", "array", "record"] {
        assert!(is(&order(name, 5, 10), &i32v(30)), "{name}");
    }
    let div = |s: &str| (PanicKind::DivZero, s.to_string());
    for name in ["tuple", "array"] {
        assert_eq!(panic_at(&order(name, 0, 0), ORDER), div("100 / a"), "{name}");
        assert_eq!(panic_at(&order(name, 5, 0), ORDER), div("100 / b"), "{name}");
        assert_eq!(panic_at(&order(name, 0, 5), ORDER), div("100 / a"), "{name}");
    }
    // The struct literal is evaluated as written (y first), not in the order of the declaration (x first).
    assert_eq!(panic_at(&order("record", 0, 0), ORDER), div("100 / b"));
    assert_eq!(panic_at(&order("record", 0, 5), ORDER), div("100 / a"));
    // The elements of a variant, from the left.
    assert!(is(&order("variant", 5, 10), &i32v(30)));
    assert_eq!(panic_at(&order("variant", 0, 0), ORDER), div("100 / a"));
    assert_eq!(panic_at(&order("variant", 5, 0), ORDER), div("100 / b"));
}

#[test]
fn a_repeated_element_is_evaluated_once_even_when_the_length_is_zero() {
    // §2.4: `[e; N]` evaluates `e` once and copies it: three copies of 100 / 5, and a panic of `e` at `[e; 0]` too.
    assert!(is(&order("repeat", 5, 0), &i32v(60)));
    assert_eq!(panic_at(&order("repeat", 0, 0), ORDER), (PanicKind::DivZero, "100 / a".to_string()));
    assert!(is(&order("none", 5, 0), &i32v(1)));
    assert_eq!(panic_at(&order("none", 0, 0), ORDER), (PanicKind::DivZero, "100 / a".to_string()));
}

#[test]
fn a_let_of_an_underscore_evaluates_the_right_side_and_drops_it() {
    // §5.1: `let _ = e` is `e` evaluated: its panic is at its position, and with no panic the value is dropped.
    let blank = |z| flow(ORDER, "blank", vec![("z", i32v(z))]);
    assert!(is(&blank(1), &i32v(7)));
    assert_eq!(panic_at(&blank(0), ORDER), (PanicKind::DivZero, "1 / z".to_string()));
}

const ACCESS: &str = "
struct P { x: I32, y: I32 }
struct O { l: I32, ps: [P; 2] }
flow field(a: I32 at sample, b: I32 at sample, i: U32 at sample) -> I32 at sample {
  let o = O { l: a, ps: [P { x: a + 1, y: b }, P { x: b * 2, y: a }] }
  o.ps[i].x + o.l
}
flow pair(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let t = ((a, b), (b, a + 100))
  t.0.1 * 10 + t.1.1
}
flow grid(i: U32 at sample, j: U32 at sample) -> I32 at sample {
  let xs = [[1, 2], [3, 4]]
  xs[i][j]
}
flow both(z: I32 at sample, w: U32 at sample) -> I32 at sample {
  [100 / z, 1][100 / w]
}
";

#[test]
fn a_field_an_element_and_an_index_read_what_they_name() {
    let field = |i| flow(ACCESS, "field", vec![("a", i32v(3)), ("b", i32v(5)), ("i", u32v(i))]);
    // o.ps[0].x = a + 1 = 4 and o.ps[1].x = b * 2 = 10, plus o.l = a = 3.
    assert!(is(&field(0), &i32v(7)));
    assert!(is(&field(1), &i32v(13)));
    // t.0.1 is b = 5, t.1.1 is a + 100 = 103: 50 + 103.
    let pair = flow(ACCESS, "pair", vec![("a", i32v(3)), ("b", i32v(5))]);
    assert!(is(&pair, &i32v(153)), "{pair:?}");
    let grid = |i, j| flow(ACCESS, "grid", vec![("i", u32v(i)), ("j", u32v(j))]);
    assert!(is(&grid(0, 0), &i32v(1)));
    assert!(is(&grid(0, 1), &i32v(2)));
    assert!(is(&grid(1, 0), &i32v(3)));
    assert!(is(&grid(1, 1), &i32v(4)));
}

#[test]
fn an_index_out_of_the_array_is_a_panic_at_the_index_expression() {
    let at = |r: &Eval| panic_at(r, ACCESS);
    let bounds = |s: &str| (PanicKind::Bounds, s.to_string());
    // §9.2: the length is 2, so 2 is out and 1 is not.
    let field = |i| flow(ACCESS, "field", vec![("a", i32v(3)), ("b", i32v(5)), ("i", u32v(i))]);
    assert_eq!(at(&field(2)), bounds("o.ps[i]"));
    assert_eq!(at(&field(4_000_000_000)), bounds("o.ps[i]"));
    // §3.5: with `i` and `j` both out, `i` is reported (the inner index is the first to panic); with `j` only, the outer.
    let grid = |i, j| flow(ACCESS, "grid", vec![("i", u32v(i)), ("j", u32v(j))]);
    assert_eq!(at(&grid(5, 5)), bounds("xs[i]"));
    assert_eq!(at(&grid(1, 2)), bounds("xs[i][j]"));
    assert_eq!(at(&grid(2, 0)), bounds("xs[i]"));
    // §3.5: `xs[i]` evaluates `xs` and then `i`: the panic of the array comes before the panic of the index.
    let both = |z, w| flow(ACCESS, "both", vec![("z", i32v(z)), ("w", u32v(w))]);
    assert_eq!(at(&both(0, 0)), (PanicKind::DivZero, "100 / z".to_string()));
    assert_eq!(at(&both(5, 0)), (PanicKind::DivZero, "100 / w".to_string()));
    // 100 / 100 = 1 is the place of the 1, and 100 / 5 = 20 is out of the two.
    assert!(is(&both(1, 100), &i32v(1)));
    assert_eq!(at(&both(1, 5)), bounds("[100 / z, 1][100 / w]"));
}

const MATCHES: &str = "
const K: I32 = 3
struct P { x: I32, y: I32 }
struct Q { p: P, n: I32 }
type PA = P
enum Mode { Off, Gain(I32), Pair(I32, I32) }
enum Dir { Up, Down, Hold }
enum Two { A(I32), B(I32) }
flow lit(k: I32 at sample, z: I32 at sample) -> I32 at sample {
  match k {
    0 => 10,
    -1 => 20,
    K => 30,
    4 | 5 => 40,
    n if n > 100 => 100 / z,
    n => n,
  }
}
flow assoc(a: I32 at sample) -> I32 at sample {
  match a { I32.MAX => 1, I32.MIN => 2, _ => 3 }
}
flow guard(k: I32 at sample) -> I32 at sample {
  match k {
    0 => 1,
    n if 100 / n > 3 => 2,
    _ => 3,
  }
}
flow guard_first(k: I32 at sample) -> I32 at sample {
  match k { n if 100 / n > 3 => 2, _ => 3 }
}
flow taken(k: I32 at sample, z: I32 at sample) -> I32 at sample {
  match k { 1 => 100 / z, 2 => 5, _ => 7 }
}
flow scrutinee(z: I32 at sample) -> I32 at sample {
  match 100 / z { 1 => 1, _ => 2 }
}
flow choice(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  match (a, b) {
    (x, 0) | (0, x) => x,
    (x, _) => x + 1,
  }
}
flow same_arity(c: I32 at sample) -> I32 at sample {
  let t = if c == 0 { Two.A(7) } else { Two.B(7) }
  match t { Two.A(x) => x, Two.B(y) => y + 100 }
}
flow unit_pattern(u: () at init, a: I32 at sample) -> I32 at sample {
  let () = u
  match u { () => a }
}
flow unit(d: I32 at sample) -> I32 at sample {
  let v = if d == 0 { Dir.Up } else if d == 1 { Dir.Down } else { Dir.Hold }
  match v { Dir.Up => 10, Dir.Hold => 30, Dir.Down => 20 }
}
flow variant(c: I32 at sample, a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let m = if c == 0 { Mode.Off } else if c == 1 { Mode.Gain(a) } else { Mode.Pair(a, b) }
  match m {
    Mode.Off => 0,
    Mode.Gain(g) if g > 5 => g,
    Mode.Gain(_) => 5,
    Mode.Pair(p, q) => p * 10 + q,
  }
}
flow option(c: Bool at sample, a: I32 at sample) -> I32 at sample {
  let o: Option[(I32, Mode)] = if c { Some((a, Mode.Gain(a + 1))) } else { None }
  match o {
    Some((x, Mode.Gain(y))) => x * 100 + y,
    Some(_) => 1,
    None => -1,
  }
}
flow record(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let q = Q { p: P { x: a, y: b }, n: 9 }
  let Q { p: P { y: py, _ }, _ } = q
  let PA { x: px, _ } = P { x: b, y: a }
  let (u, _) = (px, py)
  u * 100 + py
}
flow tuple_let(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let ((l, r), s) = ((a, b), a + b)
  l * 100 + r * 10 + s
}
";

fn matches(name: &'static str, inputs: &[(&'static str, i128)]) -> Eval {
    flow(MATCHES, name, inputs.iter().map(|(n, v)| (*n, i32v(*v))).collect())
}

#[test]
fn a_match_takes_the_first_arm_that_matches() {
    let lit = |k| matches("lit", &[("k", k), ("z", 2)]);
    // 0 and -1 are literals (a negative one too, §7), K is the constant 3, `4 | 5` is a choice, the last binds.
    for (k, want) in [(0, 10), (-1, 20), (3, 30), (4, 40), (5, 40), (7, 7), (-2, -2), (100, 100)] {
        assert!(is(&lit(k), &i32v(want)), "k = {k}: {:?}", lit(k));
    }
    // 101 passes the guard `n > 100` of the arm before the last, whose body is 100 / 2.
    assert!(is(&lit(101), &i32v(50)));
    // §7: an associated constant is a pattern.
    for (a, want) in [(i32::MAX, 1), (i32::MIN, 2), (0, 3)] {
        assert!(is(&matches("assoc", &[("a", a.into())]), &i32v(want)), "a = {a}");
    }
}

#[test]
fn the_guard_is_evaluated_after_the_bindings_of_its_arm_and_only_for_an_arm_that_matches() {
    let guard = |k| matches("guard", &[("k", k)]);
    // 0 takes the first arm: the guard of the second, 100 / 0, is not evaluated.
    assert!(is(&guard(0), &i32v(1)));
    // 100 / 10 = 10 > 3 is true: the second arm. 100 / 50 = 2 > 3 is false: the guard is false, so the next arm.
    assert!(is(&guard(10), &i32v(2)));
    assert!(is(&guard(50), &i32v(3)));
    assert!(is(&guard(25), &i32v(2)));
    assert!(is(&guard(-10), &i32v(3)));
    // A guard that panics is a panic at the guard.
    let first = matches("guard_first", &[("k", 0)]);
    assert_eq!(panic_at(&first, MATCHES), (PanicKind::DivZero, "100 / n".to_string()));
    assert!(is(&matches("guard_first", &[("k", 20)]), &i32v(2)));
}

#[test]
fn only_the_arm_that_is_taken_is_evaluated() {
    let taken = |k, z| matches("taken", &[("k", k), ("z", z)]);
    // §3.5: the arms that are not taken may panic and do not.
    assert!(is(&taken(2, 0), &i32v(5)));
    assert!(is(&taken(3, 0), &i32v(7)));
    assert!(is(&taken(1, 4), &i32v(25)));
    assert_eq!(panic_at(&taken(1, 0), MATCHES), (PanicKind::DivZero, "100 / z".to_string()));
    // The scrutinee is evaluated first, and once: 100 / 0 panics at the scrutinee, 100 / 100 is 1.
    assert_eq!(panic_at(&matches("scrutinee", &[("z", 0)]), MATCHES), (PanicKind::DivZero, "100 / z".to_string()));
    assert!(is(&matches("scrutinee", &[("z", 100)]), &i32v(1)));
    assert!(is(&matches("scrutinee", &[("z", 3)]), &i32v(2)));
}

#[test]
fn the_choices_of_a_pattern_bind_the_same_names_and_the_first_that_matches_binds() {
    let choice = |a, b| matches("choice", &[("a", a), ("b", b)]);
    // (x, 0) matches (5, 0): x = 5. (0, 7) does not match the first choice, (0, x) with x = 7.
    assert!(is(&choice(5, 0), &i32v(5)));
    assert!(is(&choice(0, 7), &i32v(7)));
    // Both choices match (0, 0), and the first binds x = 0 (the second would too). (3, 4): the third arm, 3 + 1.
    assert!(is(&choice(0, 0), &i32v(0)));
    assert!(is(&choice(3, 4), &i32v(4)));
}

#[test]
fn the_variants_and_their_elements_are_matched_by_number() {
    let variant = |c, a, b| matches("variant", &[("c", c), ("a", a), ("b", b)]);
    assert!(is(&variant(0, 9, 9), &i32v(0)));
    assert!(is(&variant(1, 9, 0), &i32v(9)));
    // g = 5 is not > 5: the guard is false, the next arm of the same variant, 5.
    assert!(is(&variant(1, 5, 0), &i32v(5)));
    assert!(is(&variant(1, 2, 0), &i32v(5)));
    // p * 10 + q for Pair(a, b).
    assert!(is(&variant(2, 4, 3), &i32v(43)));
    let option = |c, a| flow(MATCHES, "option", vec![("c", Value::Bool(c)), ("a", i32v(a))]);
    // Some((7, Gain(8))) is 7 * 100 + 8, and None is -1.
    assert!(is(&option(true, 7), &i32v(708)));
    assert!(is(&option(false, 7), &i32v(-1)));
}

#[test]
fn the_variants_with_no_elements_are_told_apart_by_their_place() {
    // §4.4: Up, Down and Hold are 0, 1 and 2 of the declaration; the arms are written in another order.
    for (d, want) in [(0, 10), (1, 20), (2, 30)] {
        assert!(is(&matches("unit", &[("d", d)]), &i32v(want)), "d = {d}");
    }
}

#[test]
fn the_variants_of_the_same_arity_are_told_apart_by_their_number() {
    // `A(x)` and `B(y)` both hold one `I32`: only the number of the variant tells the arms apart.
    assert!(is(&matches("same_arity", &[("c", 0)]), &i32v(7)));
    assert!(is(&matches("same_arity", &[("c", 1)]), &i32v(107)));
}

#[test]
fn the_unit_pattern_matches_the_unit() {
    // §7: `()` matches a value of the type `()`, and nothing is bound.
    let r = flow(MATCHES, "unit_pattern", vec![("u", Value::Unit), ("a", i32v(5))]);
    assert!(is(&r, &i32v(5)), "{r:?}");
}

#[test]
fn an_array_is_built_up_to_the_limit_of_the_evaluator_and_not_past_it() {
    // The limit of the evaluator (2^20 places) is not one of the spec: 2^20 places are built, and one more is `Unavailable`.
    let src = |n: u32| format!("flow f(x: I32 at sample) -> I32 at sample {{ let xs = [x; {n}]\n xs[0] }}");
    let at = |n: u32| flow(&src(n), "f", vec![("x", i32v(4))]);
    assert!(is(&at(1 << 20), &i32v(4)));
    assert!(matches!(at((1 << 20) + 1), Err(Stop { fault: Fault::Unavailable(_), .. })));
}

#[test]
fn a_let_takes_a_struct_and_a_tuple_apart() {
    // §7, §11.2: `Q { p: P { y: py, _ }, _ }` binds py = b, and the alias `PA { x: px, _ }` of `P { x: b, y: a }` binds px = b.
    let r = matches("record", &[("a", 3), ("b", 5)]);
    assert!(is(&r, &i32v(505)), "{r:?}");
    // ((a, b), a + b) = ((3, 5), 8): 300 + 50 + 8.
    let t = matches("tuple_let", &[("a", 3), ("b", 5)]);
    assert!(is(&t, &i32v(358)), "{t:?}");
}

#[test]
fn a_value_agrees_with_the_type_of_its_aggregate_and_with_no_other() {
    let src = "
struct P { x: I32, y: F32 }
struct W[T] { a: T }
enum Mode { Off, Gain(F32), Pair(I32, I32) }
const TU: (I32, F32) = (1, 2.0)
const A: [I32; 3] = [1, 2, 3]
const S: P = P { x: 1, y: 2.0 }
const E: Mode = Mode.Off
const O: Option[I32] = None
const OO: Option[Option[I32]] = None
const OW: Option[W[I32]] = None
const OT: Option[(I32, Mode)] = None
struct W2[T] { a: Option[T] }
const OW2: W2[I32] = W2 { a: None }
";
    with_checked(src, true, |a| {
        let view = View::new(a);
        let ty = |name: &str| {
            let (body, init) = view.const_init(def_named(a, name)).expect("a const");
            body.ty(init).expect("a type").clone()
        };
        let (t, ar, s, e) = (ty("TU"), ty("A"), ty("S"), ty("E"));
        let (o, oo, ow, ot, ow2) = (ty("O"), ty("OO"), ty("OW"), ty("OT"), ty("OW2"));
        let ok = |v: &Value, ty: &Ty| v.agrees(ty, view) == Ok(true);
        // The tuple: the arity and the element types.
        assert!(ok(&tup(vec![i32v(1), f(2.0)]), &t));
        assert!(!ok(&tup(vec![i32v(1), f(2.0), f(3.0)]), &t));
        assert!(!ok(&tup(vec![f(2.0), i32v(1)]), &t));
        assert!(!ok(&Value::Array(vec![i32v(1), f(2.0)]), &t));
        // The array: the length of the type, and each element.
        assert!(ok(&arr(ints(&[1, 2, 3])), &ar));
        assert!(!ok(&arr(ints(&[1, 2])), &ar));
        assert!(!ok(&arr(ints(&[1, 2, 3, 4])), &ar));
        assert!(!ok(&arr(vec![i32v(1), i32v(2), f(3.0)]), &ar));
        assert!(!ok(&tup(ints(&[1, 2, 3])), &ar));
        // The struct: the number of the fields and each type.
        assert!(ok(&st(vec![i32v(1), f(2.0)]), &s));
        assert!(!ok(&st(vec![i32v(1)]), &s));
        assert!(!ok(&st(vec![i32v(1), f(2.0), f(3.0)]), &s));
        assert!(!ok(&st(vec![f(2.0), i32v(1)]), &s));
        // The enum: the variant is in the range of the declaration, with its number of elements and their types.
        assert!(ok(&en(0, vec![]), &e));
        assert!(ok(&en(1, vec![f(1.0)]), &e));
        assert!(ok(&en(2, ints(&[1, 2])), &e));
        assert!(!ok(&en(3, vec![]), &e));
        assert!(!ok(&en(0, vec![f(1.0)]), &e));
        assert!(!ok(&en(1, vec![]), &e));
        assert!(!ok(&en(2, ints(&[1])), &e));
        assert!(!ok(&en(1, vec![i32v(1)]), &e));
        // A type argument: the `T` of `Option[T]` is the first argument, one level and two.
        assert!(ok(&en(0, vec![]), &o) && ok(&en(1, ints(&[1])), &o));
        assert!(!ok(&en(1, vec![f(1.0)]), &o) && !ok(&en(2, ints(&[1])), &o));
        assert!(ok(&en(1, vec![en(1, ints(&[1]))]), &oo));
        assert!(ok(&en(1, vec![en(0, vec![])]), &oo));
        assert!(!ok(&en(1, vec![en(1, vec![f(1.0)])]), &oo));
        assert!(!ok(&en(1, ints(&[1])), &oo));
        // The type arguments of a type in the fields of a generic struct, and in a tuple of the argument.
        assert!(ok(&en(1, vec![st(ints(&[1]))]), &ow));
        assert!(!ok(&en(1, vec![st(vec![f(1.0)])]), &ow));
        assert!(ok(&en(1, vec![tup(vec![i32v(1), en(2, ints(&[1, 2]))])]), &ot));
        assert!(!ok(&en(1, vec![tup(vec![i32v(1), en(2, ints(&[1]))])]), &ot));
        // A parameter of a type that is written in a parameter of another: `a: Option[T]` of `W2[I32]`.
        assert!(ok(&st(vec![en(1, ints(&[1]))]), &ow2) && ok(&st(vec![en(0, vec![])]), &ow2));
        assert!(!ok(&st(vec![en(1, vec![f(1.0)])]), &ow2));
        // A scalar value is no aggregate and an aggregate is no scalar.
        assert!(!ok(&i32v(1), &t) && !ok(&i32v(1), &s) && !ok(&Value::Unit, &e));
        assert!(!ok(&tup(vec![]), &Ty::Int(IntKind::I32)) && !ok(&arr(vec![]), &Ty::Bool));
    });
}

#[test]
fn a_row_of_the_table_that_is_an_aggregate_is_read_as_the_type_says_or_the_initializer_is_evaluated() {
    let src = "
struct P { x: F32, y: F32 }
const T: (I32, F32) = (1, 2.0)
const A: [[I32; 2]; 2] = [[1, 2], [3, 4]]
const S: P = P { x: 1.0, y: 2.0 }
const WT: (P, I32) = (P { x: 1.0, y: 2.0 }, 3)
const X: [I32; 2] = [1 + 1, 2]
";
    with_checked(src, true, |a| {
        let view = View::new(a);
        let ty = |name: &str| {
            let (body, init) = view.const_init(def_named(a, name)).expect("a const");
            body.ty(init).expect("a type").clone()
        };
        // The table has a row for each of the first four, and none for `X` (`1 + 1` is not evaluated there).
        let has = |n: &str| view.const_value(def_named(a, n)).is_some();
        assert!([has("T"), has("A"), has("S"), has("WT"), has("X")] == [true, true, true, true, false]);
        // A tuple and an array (nested) are read from the row.
        let read = |c: ConstValue, name: &str| from_const(view, &c, &ty(name));
        let row = |name: &str| view.const_value(def_named(a, name)).expect("a row").clone();
        assert!(read(row("T"), "T").is_ok_and(|v| v.same(&tup(vec![i32v(1), f(2.0)]))));
        let want = arr(vec![arr(ints(&[1, 2])), arr(ints(&[3, 4]))]);
        assert!(read(row("A"), "A").is_ok_and(|v| v.same(&want)));
        // The arity of a tuple and the length of an array are those of the type, else `Unavailable`.
        let short = ConstValue::Tuple(vec![ConstValue::Int(1)]);
        assert!(matches!(read(short, "T"), Err(Fault::Unavailable(_))));
        let long = ConstValue::Array(vec![ConstValue::Int(1); 3]);
        assert!(matches!(read(long, "X"), Err(Fault::Unavailable(_))));
        let bad = ConstValue::Array(vec![ConstValue::Int(1), ConstValue::Bool(true)]);
        assert!(matches!(read(bad, "X"), Err(Fault::Unavailable(_))));
        // A struct (alone, or in a tuple) is not read from the row: the name of the constant still has its value,
        // by the initializer evaluated here.
        assert!(matches!(read(row("S"), "S"), Err(Fault::Unavailable(_))));
        assert!(matches!(read(row("WT"), "WT"), Err(Fault::Unavailable(_))));
        for (name, want) in [
            ("S", st(vec![f(1.0), f(2.0)])),
            ("WT", tup(vec![st(vec![f(1.0), f(2.0)]), i32v(3)])),
            ("X", arr(ints(&[2, 2]))),
        ] {
            let (body, init) = view.const_init(def_named(a, name)).expect("a const");
            let got = Frame::new(body).eval(init);
            assert!(is(&got, &want), "{name}: {got:?}");
        }
    });
    // The name of a constant, in a body, reads the same value as the constant itself.
    let src = "
struct P { x: F32, y: F32 }
const S: P = P { x: 1.0, y: 2.0 }
const T: (I32, F32) = (1, 2.0)
flow f(a: F32 at sample) -> F32 at sample { S.x + S.y + T.1 + a }
";
    assert!(is(&flow(src, "f", vec![("a", f(0.5))]), &f(5.5)));
}

#[test]
fn the_nesting_of_the_aggregates_up_to_the_limit_is_evaluated() {
    // §2.5: 250 levels in a large stack (`with_checked` is one). A tuple of 120 pairs, read back by `.0`.
    let deep = format!("{}x{}", "(".repeat(120), ", 1)".repeat(120));
    let read = format!("{deep}{}", ".0".repeat(120));
    let src = format!("flow f(x: I32 at sample) -> I32 at sample {{ {read} }}");
    assert!(is(&flow(&src, "f", vec![("x", i32v(7))]), &i32v(7)));
    // An array of 120 nested arrays, indexed 120 times.
    let nest = format!("{}x{}", "[".repeat(120), "]".repeat(120));
    let src = format!("flow f(x: I32 at sample) -> I32 at sample {{ {nest}{} }}", "[0]".repeat(120));
    assert!(is(&flow(&src, "f", vec![("x", i32v(7))]), &i32v(7)));
    // 100 `match` one in the other, each takes its first arm.
    let nest = format!("{}x{}", "match true { true => ".repeat(100), ", _ => 0 }".repeat(100));
    let src = format!("flow f(x: I32 at sample) -> I32 at sample {{ {nest} }}");
    assert!(is(&flow(&src, "f", vec![("x", i32v(7))]), &i32v(7)));
}

#[test]
fn the_forms_of_the_later_units_are_still_unavailable_inside_the_aggregates() {
    let src = "
flow call(x: F32 at sample) -> F32 at sample { prev~(x) }
flow inside(x: F32 at sample) -> F32 at sample {
  let t = (x, prev~(x))
  t.0
}
rt fn double(x: F32) -> F32 { x * 2.0 }
flow plain(x: F32 at sample) -> F32 at sample { let t = (double(x), x)
  t.0 }
flow variant(x: F32 at sample) -> F32 at sample {
  match Some(x) { Some(y) => y, None => 0.0 }
}
";
    for name in ["call", "inside", "plain"] {
        let r = flow(src, name, vec![("x", f(1.0))]);
        assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })), "{name}: {r:?}");
    }
    // The constructor of a variant is a call to the table, and is not one of the calls of U5.
    assert!(is(&flow(src, "variant", vec![("x", f(1.5))]), &f(1.5)));
}

#[test]
fn a_body_the_check_rules_out_is_not_evaluated_whatever_the_aggregate() {
    // E0410 (a field missing), E0412 (the elements of a variant), E0401 (a type): the tables are not whole.
    let flows = [
        "struct P { x: I32, y: I32 }\nflow f(a: I32 at sample) -> I32 at sample { let p = P { x: a }\n p.x }",
        "enum Mode { Off, Gain(I32) }\nflow f(a: I32 at sample) -> I32 at sample {\n  match Mode.Gain() { _ => a }\n}",
        "flow f(a: I32 at sample) -> I32 at sample {\n  let t = (a, 1.5)\n  t.0 + t.1\n}",
        "flow f(a: I32 at sample) -> I32 at sample {\n  let xs = [a, a]\n  xs[0] + nothing\n}",
    ];
    for src in flows {
        let r = with_checked(src, false, |a| {
            assert!(!a.diagnostics.is_empty(), "the check rules the source out");
            View::new(a).body(def_named(a, "f")).err()
        });
        assert!(matches!(r, Some(Fault::Unavailable(_))), "{src}: {r:?}");
    }
    // `DefKind` is how the body is found: a flow, so the tables are those of the flow.
    with_checked("flow f(a: I32 at sample) -> I32 at sample { a }", true, |a| {
        assert!(matches!(a.analysis.def(def_named(a, "f")).kind, DefKind::Flow(_)));
    });
}

#[test]
fn a_type_argument_that_is_another_type_argument_is_followed_to_the_one_it_stands_for() {
    // `W[U, T]` in `V[T, U]` swaps the arguments: the field `x: A` of the `W` is the `U` of the `V`, read under the
    // arguments of the `V`, not under those of the `W`. And `Option[Option[T]]` follows the argument twice.
    let src = "
struct W[A, B] { x: A, y: B }
struct V[T, U] { w: W[U, T], o: Option[Option[T]] }
const C: V[I32, F32] = V { w: W { x: 1.5, y: 2 }, o: Some(None) }
";
    with_checked(src, true, |a| {
        let view = View::new(a);
        let (body, init) = view.const_init(def_named(a, "C")).expect("a const");
        let ty = body.ty(init).expect("a type").clone();
        let w = |x: Value, y: Value| st(vec![x, y]);
        let v = |w: Value, o: Value| st(vec![w, o]);
        let none = en(0, vec![]);
        let some = |x: Value| en(1, vec![x]);
        let ok = |x: &Value| x.agrees(&ty, view);
        assert_eq!(ok(&v(w(f(1.5), i32v(2)), some(none.clone()))), Ok(true));
        assert_eq!(ok(&v(w(f(1.5), i32v(2)), some(some(i32v(1))))), Ok(true));
        assert_eq!(ok(&v(w(f(1.5), i32v(2)), none.clone())), Ok(true));
        // The arguments are not swapped back: `x` is an `F32`, `y` an `I32`.
        assert_eq!(ok(&v(w(i32v(2), f(1.5)), none.clone())), Ok(false));
        assert_eq!(ok(&v(w(f(1.5), f(1.5)), none.clone())), Ok(false));
        // The payload of the inner `Option` is the `T` of the `V`, an `I32`, not the `U`.
        assert_eq!(ok(&v(w(f(1.5), i32v(2)), some(some(f(1.0))))), Ok(false));
        assert_eq!(ok(&v(w(f(1.5), i32v(2)), some(i32v(1)))), Ok(false));
    });
}

#[test]
fn a_declaration_the_table_does_not_have_as_a_struct_or_an_enum_is_unavailable_not_a_disagreement() {
    // A struct value against the type of an enum, and an enum value against the type of a struct: the table of the
    // declaration is not the one the value needs (the check stopped), which is `Unavailable`, not "the value is wrong".
    with_checked("struct P { a: I32 }\nenum E { A }", true, |a| {
        let view = View::new(a);
        let (p, e) = (Ty::Named(def_named(a, "P"), vec![]), Ty::Named(def_named(a, "E"), vec![]));
        assert!(matches!(st(ints(&[1])).agrees(&e, view), Err(Fault::Unavailable(_))));
        assert!(matches!(en(0, vec![]).agrees(&p, view), Err(Fault::Unavailable(_))));
        assert_eq!(st(ints(&[1])).agrees(&p, view), Ok(true));
        assert_eq!(en(0, vec![]).agrees(&e, view), Ok(true));
    });
}
