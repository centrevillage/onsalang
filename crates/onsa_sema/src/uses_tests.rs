//! Unit tests of the record of the uses (`crate::uses`, R-83, D-15, S-783).

use crate::drop_alloc::Drop;
use crate::tests::{analyze, def, pkg};
use crate::uses::{What, records};

/// Each use of the function `name` in the record of `src`, in its order: its
/// kind, the text at its place, and the number of its drop points.
fn uses_of(src: &str, name: &str) -> Vec<(&'static str, String, usize)> {
    let p = pkg(&[("main", src)]);
    let a = analyze(&p);
    let id = def(&a, name);
    let all = records(&p, &a);
    let r = all.iter().find(|r| r.id == id).unwrap_or_else(|| panic!("no record of {name}"));
    let keys: Vec<_> = r.uses.iter().map(|u| (u.at.start, u.at.end)).collect();
    assert!(keys.is_sorted(), "{name}: {keys:?}");
    let text = |u: &crate::uses::Use| src[u.at.start as usize..u.at.end as usize].to_string();
    (r.uses.iter())
        .map(|u| {
            let (kind, points) = match &u.what {
                What::Call { .. } => ("call", 0),
                What::ValueCall => ("value call", 0),
                What::Interp => ("interp", 0),
                What::Drop { drop, points } => (drop_kind(drop), points.len()),
            };
            (kind, text(u), points)
        })
        .collect()
}

fn drop_kind(d: &Drop) -> &'static str {
    match d {
        Drop::Local(_) => "local",
        Drop::Rest { .. } => "rest",
        Drop::Value { .. } => "waits",
        Drop::IterRest { .. } => "for rest",
        Drop::Temp { .. } => "temp",
        Drop::Overwrite { .. } => "overwrite",
        Drop::Discard { .. } => "discard",
    }
}

const STD: &str = "pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }
pub fn pure(n: U32) -> U32 { n }
pub fn pass(move b: Buf[F32]) -> Buf[F32] uses {Alloc} { b }
pub fn wrap(move b: Buf[F32], n: U32) -> Option[Buf[F32]] uses {Alloc} { Some(b) }
";

fn record_of(body: &str, name: &str) -> Vec<(&'static str, String, usize)> {
    uses_of(&format!("{STD}{body}\n"), name)
}

fn owned(v: &[(&'static str, &str, usize)]) -> Vec<(&'static str, String, usize)> {
    v.iter().map(|&(k, t, n)| (k, t.to_string(), n)).collect()
}

/// The calls (of a function, a method, a function value), the interpolations
/// and the drops, at their places, in the order of the places: every call,
/// whatever it needs; a call before the drop of its value at the same place.
#[test]
fn a_record_has_every_use_by_its_place() {
    let got = record_of(
        "pub fn f(g: fn(U32) -> U32 uses {Alloc}, n: U32) -> U32 { let s: Str = \"{n}\"\n pure(g.(n)) + mk(n).len() }",
        "f",
    );
    let want = [
        ("local", "s", 1),
        ("interp", "\"{n}\"", 0),
        ("call", "pure(g.(n))", 0),
        ("value call", "g.(n)", 0),
        ("call", "mk(n)", 0),
        ("temp", "mk(n)", 1),
        ("call", "mk(n).len()", 0),
    ];
    assert_eq!(got, owned(&want));
}

/// A value is one use with all its drop points (S-783): a local left by a
/// `return` and at the end of the body, the rest of a `for` left by a
/// `break` and at its end, each point tested (`crate::drop_alloc::alloc_drops`).
#[test]
fn a_value_dropped_is_one_use_with_its_points() {
    let got = record_of("pub fn f(move b: Buf[F32], c: Bool) -> U32 { if c { return 0 }\n b.len() }", "f");
    assert_eq!(got, owned(&[("local", "b", 2), ("call", "b.len()", 0)]));
    let got = record_of("pub fn f(move xs: Buf[F32]) { for s in move xs { if s > 0.0 { break } } }", "f");
    assert_eq!(got, owned(&[("for rest", "xs", 2)]));
    // Of an array, its end needs no `Alloc`: the point of the `break` alone.
    let got = record_of("pub fn f(move xs: [Buf[F32]; 2]) { for s in move xs { if s.len() > 0 { break } } }", "f");
    assert_eq!(got, owned(&[("local", "s", 2), ("for rest", "xs", 1), ("call", "s.len()", 0)]));
}

/// The other drops: a place assigned, what binds to no name, what is left
/// where a field is taken out, a value an exit leaves before it is consumed.
#[test]
fn the_drops_are_at_the_values_as_written() {
    let got = record_of("pub fn f(inout b: Buf[F32], move c: Buf[F32]) { b = move c }", "f");
    assert_eq!(got, owned(&[("overwrite", "b", 1)]));
    let got = record_of("pub fn f(move _: Buf[F32]) {}", "f");
    assert_eq!(got, owned(&[("discard", "move _: Buf[F32]", 1)]));
    let got = record_of("pub fn f(move t: (Buf[F32], Str)) -> Buf[F32] { t.0 }", "f");
    assert_eq!(got, owned(&[("rest", "t.0", 1)]));
    let got = record_of(
        "pub fn f(move b: Buf[F32], r: Option[U32]) -> Option[Option[Buf[F32]]] { Some(wrap(pass(move b), r?)) }",
        "f",
    );
    let want = [("call", "wrap(pass(move b), r?)", 0), ("call", "pass(move b)", 0), ("waits", "pass(move b)", 1)];
    assert_eq!(got, owned(&want));
}

/// An `rt` body has its record too (the rt stage reads it, E0901 and the
/// edges of E0903): each call with whether what it calls is `rt` (§10 rule 4).
#[test]
fn an_rt_body_records_whether_its_calls_are_rt() {
    let src = format!("{STD}pub rt fn h(n: U32) -> U32 {{ n }}\npub rt fn k(n: U32) -> U32 {{ h(pure(n)) + h(n) }}\n");
    let p = pkg(&[("main", &src)]);
    let a = analyze(&p);
    let id = def(&a, "k");
    let all = records(&p, &a);
    let r = all.iter().find(|r| r.id == id).expect("a record of the rt function k");
    let got: Vec<_> = r.uses.iter().map(|u| (&src[u.at.start as usize..u.at.end as usize], u.rt)).collect();
    assert_eq!(got, [("h(pure(n))", Some(true)), ("pure(n)", Some(false)), ("h(n)", Some(true))]);
}

/// R-459: of the violations of an `rt` body that start at one place
/// (`p.a().b()`), E0901 reports the first by the key of the record, the
/// inner call, whatever the order of the tables.
#[test]
fn the_e0901_of_one_start_is_the_first_by_the_key() {
    let src = "pub struct P { n: U32 }
impl P {
  pub fn a(self) -> P { P { n: self.n } }
  pub fn b(self) -> U32 { self.n }
}
pub rt fn k(p: P) -> U32 { p.a().b() }
";
    let a = analyze(&pkg(&[("main", src)]));
    let got: Vec<_> = (a.diagnostics.iter())
        .filter(|d| d.code == onsa_diag::Code::E0901)
        .map(|d| (&src[d.span.start as usize..d.span.end as usize], d.message.as_str()))
        .collect();
    assert_eq!(got, [("p.a()", "`rt` function calls `a`, which is not `rt` (§10 rule 4)")]);
}
