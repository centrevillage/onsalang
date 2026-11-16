//! The tests of the choices (`p | q`) of a pattern with a guard (W7-01 U4 fix): the guard is tried for each way the
//! pattern matches, in the order of Rust's (§7: "Rust と同じ意味のものだけ"; rustc 1.94 gives the values below), and the
//! patterns read the types of the fields and the elements from the type of the value.

use super::expr_tests::{flow, i32v, is, panic_at};
use super::scalar::PanicKind;
use super::value::Value;

const CHOICES: &str = "
struct P { x: I32, y: I32 }
enum Mode { Off, Gain(I32), Pair(I32, I32) }
flow guarded(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  match (a, b) { (x, _) | (_, x) if x == 2 => x * 10, _ => -1 }
}
flow plain(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  match (a, b) { (x, _) | (_, x) => x }
}
flow arms(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  match (a, b) {
    (x, y) if x + y > 100 => 1,
    (x, y) if x == y => 2,
    (x, _) | (_, x) if x > 5 => 3,
    _ => 4,
  }
}
flow nested(p: I32 at sample, q: I32 at sample, r: I32 at sample, s: I32 at sample) -> I32 at sample {
  match ((p, q), (r, s)) {
    ((x, _) | (_, x), (y, _) | (_, y)) if x * 10 + y > 13 => x * 10 + y,
    _ => -1,
  }
}
flow payload(c: I32 at sample, a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let m = if c == 0 { Mode.Pair(a, b) } else { Mode.Gain(a) }
  match m { Mode.Pair(x, _) | Mode.Pair(_, x) if x > 5 => x, _ => -1 }
}
flow fields(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  let p = P { x: a, y: b }
  match p { P { x: 1 | 2, y: n } if n > 5 => n, P { x: x, y: 0 | 1 } => x, _ => 0 }
}
flow panics(a: I32 at sample, b: I32 at sample) -> I32 at sample {
  match (a, b) { (x, _) | (_, x) if 10 / x > 3 => x, _ => -1 }
}
flow after(a: I32 at sample, b: I32 at sample, z: I32 at sample) -> I32 at sample {
  match (a, b) { (x, _) | (_, x) if x == 2 => x, _ => 100 / z }
}
";

fn run(name: &'static str, ins: &[i128]) -> super::expr::Eval {
    let names = ["a", "b", "c", "d"];
    let named =
        |s: &[&'static str]| -> Vec<(&'static str, Value)> { s.iter().zip(ins).map(|(n, v)| (*n, i32v(*v))).collect() };
    match name {
        "nested" => flow(CHOICES, name, named(&["p", "q", "r", "s"])),
        "payload" => flow(CHOICES, name, named(&["c", "a", "b"])),
        "after" => flow(CHOICES, name, named(&["a", "b", "z"])),
        _ => flow(CHOICES, name, named(&names[..ins.len()])),
    }
}

#[test]
fn the_guard_is_tried_for_each_choice_that_matches() {
    // (1, 2): the first choice binds x = 1 (the guard is false), the second binds x = 2 (true): 20, as in Rust.
    for (ins, want) in [([1, 2], 20), ([2, 1], 20), ([1, 1], -1), ([3, 4], -1), ([2, 2], 20)] {
        let r = run("guarded", &ins);
        assert!(is(&r, &i32v(want)), "{ins:?}: {r:?}");
    }
    // Without a guard the first choice that matches binds: (1, 2) is 1, not 2.
    for (ins, want) in [([1, 2], 1), ([5, 6], 5)] {
        let r = run("plain", &ins);
        assert!(is(&r, &i32v(want)), "{ins:?}: {r:?}");
    }
}

#[test]
fn a_guard_that_is_false_for_every_choice_goes_to_the_next_arm() {
    // (1, 9): the arm of `x + y` is false, `x == y` is false, and `x > 5` is true for the second choice: 3 (Rust: 3).
    // (9, 1): the first choice. (1, 1): the arm of `x == y`. (2, 3): every guard is false, the last arm.
    for (ins, want) in [([1, 9], 3), ([9, 1], 3), ([1, 1], 2), ([2, 3], 4), ([60, 60], 1)] {
        let r = run("arms", &ins);
        assert!(is(&r, &i32v(want)), "{ins:?}: {r:?}");
    }
}

#[test]
fn the_choices_one_inside_another_go_in_the_order_the_first_one_is_the_slowest() {
    // ((1, 2), (3, 4)): x is 1 or 2 and y is 3 or 4. The ways are (1, 3), (1, 4), (2, 3), (2, 4), the first choice
    // changing last (rustc 1.94 tries `1 3`, `1 4`): 13 is not above 13, so the way (1, 4) is taken, 14, and not 23.
    for (ins, want) in
        [([1, 2, 3, 4], 14), ([1, 2, 3, 3], 23), ([1, 1, 1, 1], -1), ([2, 1, 3, 3], 23), ([5, 9, 0, 0], 50)]
    {
        let r = run("nested", &ins);
        assert!(is(&r, &i32v(want)), "{ins:?}: {r:?}");
    }
}

#[test]
fn the_choices_in_a_variant_and_in_a_struct_are_tried_the_same_way() {
    for (ins, want) in [([0, 1, 9], 9), ([0, 9, 1], 9), ([0, 1, 1], -1), ([1, 9, 9], -1), ([0, 6, 0], 6)] {
        let r = run("payload", &ins);
        assert!(is(&r, &i32v(want)), "{ins:?}: {r:?}");
    }
    // `P { x: 1 | 2, y: n } if n > 5`: the literal choices that do not match are skipped, the guard reads `n`.
    for (ins, want) in [([2, 9], 9), ([1, 9], 9), ([2, 3], 0), ([3, 9], 0), ([4, 1], 4)] {
        let r = run("fields", &ins);
        assert!(is(&r, &i32v(want)), "{ins:?}: {r:?}");
    }
}

#[test]
fn a_panic_in_a_guard_stops_at_the_choice_it_was_tried_with() {
    // (0, 2): the first choice is x = 0, and `10 / x` panics before the second choice (where it is true) is tried.
    assert_eq!(panic_at(&run("panics", &[0, 2]), CHOICES), (PanicKind::DivZero, "10 / x".to_string()));
    // (2, 0): the first choice is x = 2, the guard is true, and the second choice is never tried: no panic.
    assert!(is(&run("panics", &[2, 0]), &i32v(2)));
    // (20, 0): the first choice is false (10 / 20 is 0), the second is x = 0: the panic of the second.
    assert_eq!(panic_at(&run("panics", &[20, 0]), CHOICES), (PanicKind::DivZero, "10 / x".to_string()));
    // Once an arm is taken the arms after it are not evaluated: `100 / z` with z = 0 is never reached.
    assert!(is(&run("after", &[1, 2, 0]), &i32v(2)));
}

#[test]
fn a_struct_pattern_reads_the_fields_from_the_type_of_the_value() {
    // The struct a pattern names is the struct of the type of the value: a generic struct whose field is a type
    // argument, the struct inside a variant and inside a tuple (the type arguments are followed), and an alias.
    let src = "
struct P { x: I32, y: F32 }
struct W[T] { a: T, b: I32 }
type PA = P
struct W2[T] { a: Option[T] }
struct Id[T] { v: T }
struct Twice[T] { w: Id[T] }
flow h(a: I32 at sample) -> I32 at sample {
  let t = Twice { w: Id { v: P { x: a, y: 1.5 } } }
  let Twice { w: Id { v: P { x: px, _ } } } = t
  px
}
flow g(a: I32 at sample) -> I32 at sample {
  let w = W2 { a: Some(P { x: a, y: 1.5 }) }
  match w { W2 { a: Some(P { x: px, _ }) } => px, W2 { a: None } => 0 }
}
flow f(a: I32 at sample) -> F32 at sample {
  let w = W { a: P { x: a, y: 2.5 }, b: 7 }
  let W { a: P { y: py, _ }, b: wb } = w
  let o = Some((P { x: wb, y: py }, 1))
  let u = match o { Some((PA { x: ox, y: oy }, _)) => if ox == a + 4 { oy } else { 0.0 }, None => 0.0 }
  u
}
";
    assert!(is(&flow(src, "f", vec![("a", i32v(3))]), &Value::F32(2.5)));
    // A parameter of a type that is written in a parameter of another: `a: Option[T]` of `W2[P]`, the `P` is reached
    // through the arguments of the `Option` and then those of the `W2`.
    assert!(is(&flow(src, "g", vec![("a", i32v(4))]), &i32v(4)));
    // A struct whose argument is the argument of the struct around it: the `T` of `Id[T]` in `Twice[T]`.
    assert!(is(&flow(src, "h", vec![("a", i32v(5))]), &i32v(5)));
}
