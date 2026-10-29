//! A drawn sweep of the declared types of `const` items against a model of where the spec places them (§6.6,
//! S-610, S-755, S-773, W4-05 table 5; §4.5 and §5.3 with S-766 and S-771; W4-05 U4b/i2, from `ctypes.py` and
//! `cfuzz.py` of the break side of U4b).
//!
//! Each drawn type (depth 3, a fixed seed) is the type of a `const` of its own line, `= 1`, at the top and as an
//! associated constant of an `impl[T: B]`. The model is the classes of §6.6, the worst part of the type:
//! - Placed statically (Copy): the scalars, `P`, and a type parameter with a bound that is `Copy` or requires it.
//! - Shared, the E0200 of this version: `Str`, `Bytes`, an `Array` (whatever it holds), a type parameter
//!   without such a bound (`?Dup` too, table 5), and the declarations that hold them, those that hold
//!   themselves through an `Array` too (`Tree`, `Rec`, and `Grow[T]`, which holds `Grow[(T, T)]`).
//! - Never placed, the E0407: `Map`, `Set`, `Buf`, Affine, and what holds one, wherever (`Pm[T]` holds
//!   `Pm[Map[U32, U32]]` through an `Array`; `Fo` holds `Tr` through an `Array`, which holds a `Map`). With a
//!   Shared part too, it is the E0407 (S-773).
//! - A type that holds a second-class `Span` has no kind to place (S-766, S-771): its diagnostic is its E0710,
//!   or an E0416 of a type argument before it (the first by its place, §18.1).
//!
//! The E0200 and the E0407 are at the declared type (S-755). It is first in its unit, before an E0416 of a
//! type argument inside it (§18.1), so the drawn types need not be well formed; a type placed statically has
//! neither (the `= 1` may be the E0401 of its value).

mod test_support;

use std::collections::BTreeMap;

use test_support::sweep::{Rng, Texts, check_package, ended_well, package};

/// The classes in their order; `Second`: holds a `Span`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum C {
    Static,
    Later,
    Never,
    Second,
}

const HEAD: &str = "\
pub struct P { x: F32 }
pub struct Sh { s: Str }
pub struct Af { b: Buf[F32] }
pub struct Gen[T] { a: T }
pub struct GenF[T: ?Dup] { a: T }
pub struct GenC[T: Copy] { a: T }
pub struct Two[T, U] { a: T, b: U }
pub enum En[T] { A, B(T) }
pub enum Mix { A(U32), B(Str), C }
pub struct HasMap { m: Option[Map[U32, U32]] }
pub enum Tree { Leaf, Node(Array[Tree]) }
pub struct Rec { kids: Array[Rec] }
pub struct Grow[T] { t: T, a: Array[Grow[(T, T)]] }
pub struct Pm[T] { a: T, b: Array[Pm[Map[U32, U32]]] }
pub struct Fo { ts: Array[Tr] }
pub enum Tr { L, N(Array[Fo]), M(Option[Map[U32, U32]]) }
pub struct Q[T: ?Dup] { a: Option[T] }
type AS = Str
type AB = Buf[F32]
type AT = (Str, U32)
";

const LEAVES: &[(&str, C)] = &[
    ("U32", C::Static),
    ("F32", C::Static),
    ("Bool", C::Static),
    ("()", C::Static),
    ("P", C::Static),
    ("Str", C::Later),
    ("Bytes", C::Later),
    ("Sh", C::Later),
    ("Mix", C::Later),
    ("Tree", C::Later),
    ("Rec", C::Later),
    ("AS", C::Later),
    ("AT", C::Later),
    ("Af", C::Never),
    ("Buf[F32]", C::Never),
    ("Map[U32, U32]", C::Never),
    ("Set[U32]", C::Never),
    ("HasMap", C::Never),
    ("Fo", C::Never),
    ("Tr", C::Never),
    ("AB", C::Never),
];

/// The bounds of the `impl` and the class of its `T`.
const BOUNDS: &[(&str, C)] = &[
    ("Copy", C::Static),
    ("Num", C::Static),
    ("Float", C::Static),
    ("Copy + Show", C::Static),
    ("", C::Later),
    ("Show", C::Later),
    ("Dup", C::Later),
    ("?Dup", C::Later),
    ("Eq", C::Later),
];

/// A type of depth `d` and its class; `t`: the class of `T` where it is in scope.
fn draw(r: &mut Rng, d: usize, t: Option<C>) -> (String, C) {
    if d == 0 || r.chance(30) {
        if let Some(c) = t.filter(|_| r.chance(30)) {
            return ("T".to_string(), c);
        }
        if r.chance(8) {
            return ("Span[F32]".to_string(), C::Second);
        }
        let &(s, c) = r.pick(LEAVES);
        return (s.to_string(), c);
    }
    let one = |r: &mut Rng| draw(r, d - 1, t);
    let (a, ca) = one(r);
    let (b, cb) = one(r);
    // A part with a `Span` makes the whole one with no class (S-771).
    let worst = |floor: C| if ca == C::Second { C::Second } else { ca.max(floor) };
    match r.below(15) {
        0 => (format!("Option[{a}]"), ca),
        1 => (format!("({a}, {b})"), ca.max(cb)),
        2 => (format!("[{a}; 2]"), ca),
        3 => (format!("Result[{a}, {b}]"), ca.max(cb)),
        4 => (format!("Gen[{a}]"), ca),
        5 => (format!("GenF[{a}]"), ca),
        6 => (format!("GenC[{a}]"), ca),
        7 => (format!("Two[{a}, {b}]"), ca.max(cb)),
        8 => (format!("En[{a}]"), ca),
        9 => (format!("Array[{a}]"), worst(C::Later)),
        10 => (format!("Buf[{a}]"), worst(C::Never)),
        11 => (format!("Map[{a}, U32]"), worst(C::Never)),
        12 => (format!("Set[{a}]"), worst(C::Never)),
        13 => (format!("Grow[{a}]"), worst(C::Later)),
        _ => (format!("Pm[{a}]"), worst(C::Never)),
    }
}

#[test]
fn the_type_of_a_const_is_placed_as_the_spec_classes_say() {
    let mut r = Rng::new(0x0610_0405);
    let mut text = HEAD.to_string();
    // The line, the column of the declared type, the type and its class.
    let mut cases = Vec::new();
    for i in 0..450 {
        let (head, t) = match i % 3 {
            2 => {
                let &(b, c) = r.pick(BOUNDS);
                let b = if b.is_empty() { String::new() } else { format!(": {b}") };
                (format!("impl[T{b}] Q[T] {{ const C{i}: "), Some(c))
            }
            _ => (format!("pub const K{i}: "), None),
        };
        let (ty, c) = draw(&mut r, 3, t);
        let close = if t.is_some() { " }" } else { "" };
        text.push_str(&format!("{head}{ty} = 1{close}\n"));
        cases.push((text.lines().count() as u64, head.len() as u64 + 1, ty, c));
    }
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), text);
    let d = package("const_placement_model", "demo", &texts);
    let checked = check_package(d.root());
    assert!(ended_well(&checked), "check did not end as a check does:\n{}", checked.stderr);
    let mut got: BTreeMap<u64, Vec<(u64, String)>> = BTreeMap::new();
    for x in &checked.diags {
        got.entry(x.line).or_default().push((x.col, x.code.clone()));
    }
    let mut bad = Vec::new();
    let mut seen = BTreeMap::new();
    for (line, col, ty, c) in cases {
        *seen.entry(c).or_insert(0) += 1;
        let at = got.get(&line).cloned().unwrap_or_default();
        let codes: Vec<&str> = at.iter().map(|x| x.1.as_str()).collect();
        let ok = match c {
            C::Static => !codes.iter().any(|&x| matches!(x, "E0200" | "E0407" | "E0710")),
            C::Later => at == [(col, "E0200".to_string())],
            C::Never => at == [(col, "E0407".to_string())],
            C::Second => !codes.is_empty() && codes.iter().all(|&x| matches!(x, "E0710" | "E0416")),
        };
        if !ok {
            bad.push(format!("line {line} `{ty}`: {at:?}, the model {c:?} at {col}"));
        }
    }
    // The draw has every class.
    assert!(seen.values().all(|&n| n > 20) && seen.len() == 4, "the classes drawn: {seen:?}");
    assert!(bad.is_empty(), "{} mismatches:\n{}", bad.len(), bad.join("\n"));
}
