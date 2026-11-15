//! Unit tests of the record of the uses (`crate::uses`, R-83, D-15, S-783).

use crate::body::RowFrom;
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
                What::ValueCall { .. } => ("value call", 0),
                What::Interp => ("interp", 0),
                What::Drop { drop, points } => (drop_kind(drop), points.len()),
            };
            (kind, text(u), points)
        })
        .collect()
}

fn drop_kind(d: &Drop) -> &'static str {
    match d {
        Drop::Local(..) => "local",
        Drop::Rest { .. } => "rest",
        Drop::Value { .. } => "waits",
        Drop::IterRest { .. } => "for rest",
        Drop::Temp { .. } => "temp",
        Drop::Overwrite { .. } => "overwrite",
        Drop::Discard { .. } => "discard",
        Drop::Unplaced { .. } => "unplaced",
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
    assert_eq!(
        got,
        [("p.a()", "this calls `a`, which is not `rt`; an `rt` function calls only `rt` ones (§10 rule 4)")]
    );
}

/// §18.1, S-783 C2: of the uses that start at one place, the one that ends
/// first comes first, and a call before the drop of its value: the drop of
/// the value `id(move x)` before the call of `grow` on it. So the E0601 of a
/// function that is not `rt` is at that drop, and in an `rt` function the
/// drop is the E0601 and the call of `grow` the E0901 (W6-03 U2 to U3b, the
/// breaking side's low 1).
#[test]
fn the_uses_of_one_start_are_by_their_end() {
    let hold = "pub struct Hold { buf: Buf[F32], g: F32 }
impl Hold { pub fn grow(self) -> U32 uses {Alloc} { 1 } }
pub fn id(move h: Hold) -> Hold { move h }
pub rt fn rid(move h: Hold) -> Hold { move h }
";
    let src = format!(
        "{hold}pub fn e601(move x: Hold) -> U32 {{ id(move x).grow() }}\npub rt fn e901(move x: Hold) -> U32 {{ rid(move x).grow() }}\n"
    );
    let want = |f: &str| {
        owned(&[
            ("call", &format!("{f}(move x)"), 0),
            ("temp", &format!("{f}(move x)"), 1),
            ("call", &format!("{f}(move x).grow()"), 0),
        ])
    };
    assert_eq!(uses_of(&src, "e601"), want("id"));
    assert_eq!(uses_of(&src, "e901"), want("rid"));
    let a = analyze(&pkg(&[("main", &src)]));
    let mut got: Vec<_> =
        (a.diagnostics.iter()).map(|d| (d.code, &src[d.span.start as usize..d.span.end as usize])).collect();
    got.sort();
    let want = [
        (onsa_diag::Code::E0601, "id(move x)"),
        (onsa_diag::Code::E0601, "rid(move x)"),
        (onsa_diag::Code::E0901, "rid(move x).grow()"),
    ];
    assert_eq!(got, want);
}

/// The scope of each use (§8.1): the innermost anonymous function whose span
/// holds its place, or the body; the call of an anonymous function written
/// where it is called is the body's (W6-03 U5).
#[test]
fn a_use_is_of_the_innermost_scope_that_holds_it() {
    let src = format!(
        "{STD}pub fn ap(g: fn(U32) -> U32, n: U32) -> U32 {{ g.(n) }}
pub fn f(n: U32) -> U32 uses {{Alloc}} {{
  let s = \"{{n}}\"
  ap(fn(y: U32) -> U32 {{ ap(fn(z: U32) -> U32 {{ mk(z).len() }}, pure(y)) }}, n) + (fn(x: U32) -> U32 {{ x }}).(n)
}}
"
    );
    let p = pkg(&[("main", &src)]);
    let a = analyze(&p);
    let id = def(&a, "f");
    let all = records(&p, &a);
    let r = all.iter().find(|r| r.id == id).expect("a record of f");
    let text = |s: onsa_diag::Span| &src[s.start as usize..s.end as usize];
    let ast = &crate::module_of_def(&p, &a, id).expect("its module").parsed.ast;
    let head = |i: u32| r.scopes[i as usize].closure.map(|c| &text(ast.expr(c).span)[..8]);
    let got: Vec<_> = r.uses.iter().map(|u| (text(u.at), head(u.scope))).collect();
    let want = [
        ("s", None),
        ("\"{n}\"", None),
        ("ap(fn(y: U32) -> U32 { ap(fn(z: U32) -> U32 { mk(z).len() }, pure(y)) }, n)", None),
        ("ap(fn(z: U32) -> U32 { mk(z).len() }, pure(y))", Some("fn(y: U3")),
        ("mk(z)", Some("fn(z: U3")),
        ("mk(z)", Some("fn(z: U3")),
        ("mk(z).len()", Some("fn(z: U3")),
        ("pure(y)", Some("fn(y: U3")),
        ("(fn(x: U32) -> U32 { x }).(n)", None),
    ];
    assert_eq!(got, want);
    assert!(r.scopes.iter().skip(1).all(|s| !s.rt && s.row.effects().is_empty()));
}

/// The scope of a use is decided by its place alone (`Closures::around`, the
/// one place, D-15): the value of a drop as written and every point of it
/// are in one scope (W6-03 U5), points in anonymous functions too.
#[test]
fn the_scope_of_a_drop_is_the_one_of_its_points() {
    let bodies = [
        "pub fn f(n: U32) -> U32 uses {Alloc} { ap(fn(move b: Buf[F32]) -> U32 { b.len() }, mk(n)) }",
        "pub fn f(n: U32) -> U32 uses {Alloc} { ap(fn(move _: Buf[F32]) -> U32 { 0 }, mk(n)) }",
        "pub fn f(n: U32) -> U32 uses {Alloc} { ap(fn(move b: Buf[F32]) -> U32 { let c = mk(b.len())\n if c.len() > 2 { return 0 }\n mk(c.len()).len() }, mk(n)) }",
        "pub fn f(n: U32) -> U32 uses {Alloc} { let g = fn(y: U32) -> U32 { let h = fn(move xs: [Buf[F32]; 2]) -> U32 { for s in move xs { if s.len() > 0 { break } }\n 0 }\n h.([mk(y), mk(y)]) }\n g.(n) }",
        "pub fn f(move t: (Buf[F32], Str), n: U32) -> U32 uses {Alloc} { let g = fn(move u: (Buf[F32], Str)) -> U32 { u.0.len() }\n g.(move t) + n }",
        "pub fn f(n: U32) -> Option[U32] uses {Alloc} { let g = fn(r: Option[U32]) -> Option[Option[Buf[F32]]] { Some(wrap(mk(1), r?)) }\n Some(match g.(Some(n))? { Some(b) => b.len(), None => 0 }) }",
    ];
    let mut points = 0;
    for body in bodies {
        let src =
            format!("{STD}pub fn ap(g: fn(move Buf[F32]) -> U32, move b: Buf[F32]) -> U32 {{ g.(move b) }}\n{body}\n");
        let p = pkg(&[("main", &src)]);
        let a = analyze(&p);
        let id = def(&a, "f");
        let all = records(&p, &a);
        let r = all.iter().find(|r| r.id == id).unwrap_or_else(|| panic!("no record of f: {:?}", a.diagnostics));
        let ast = &crate::module_of_def(&p, &a, id).expect("its module").parsed.ast;
        let closures = crate::uses::Closures::of(ast, &a.bodies[&id]);
        let scope_of = |at| closures.around(at).and_then(|i| r.scopes[i + 1].closure);
        points += a.bodies[&id].drops.iter().filter(|d| scope_of(d.at).is_some()).count();
        for u in &r.uses {
            if let What::Drop { points, .. } = &u.what {
                assert!(points.iter().all(|&p| scope_of(p) == r.scopes[u.scope as usize].closure), "{body}");
            }
        }
    }
    assert!(points >= 8, "{points} drop points in anonymous functions");
}

/// The edges of the rt recursion are the calls by name of the body itself
/// (§10 rule 5, S-1057): not those of an anonymous function in it, `rt` or
/// not, and not a function used as a value.
#[test]
fn the_rt_edges_are_the_calls_of_the_body_itself() {
    let src = "pub rt fn ap(g: rt fn(U32) -> U32, n: U32) -> U32 { g.(n) }
pub rt fn h(n: U32) -> U32 { n }
pub rt fn k(n: U32) -> U32 { h(n) + ap(fn(y: U32) -> U32 { h(y) }, n) + ap(h, n) }
";
    let p = pkg(&[("main", src)]);
    let a = analyze(&p);
    let id = def(&a, "k");
    let ast = &crate::module_of_def(&p, &a, id).expect("its module").parsed.ast;
    let got: Vec<_> = (crate::uses::rt_edges(&a, ast, &a.bodies[&id]).into_iter())
        .map(|(at, c)| (&src[at.start as usize..at.end as usize], a.def(c).name.as_str()))
        .collect();
    let want = [("h(n)", "h"), ("ap(fn(y: U32) -> U32 { h(y) }, n)", "ap"), ("ap(h, n)", "ap")];
    assert_eq!(got, want);
}

/// The type parameters that, `Copy`, free a drop from `Alloc` (S-1052,
/// `crate::drop_alloc::copy_would_free`): asked again with them `Copy`, each
/// one it needs (both of `(A, B)`, not the `Copy` one); none where a part
/// needs `Alloc` whatever they are (`(T, Str)`, `(T, Buf[F32])`).
#[test]
fn the_type_parameters_copy_frees_a_drop_of() {
    let src = "pub fn plain[T](move x: T) {}
pub fn dup[T: ?Dup](move x: T) {}
pub fn inside[T](move x: (T, U32)) {}
pub fn option[T](move x: Option[T]) {}
pub fn two[A, B](move x: (A, B)) {}
pub fn one_of_two[A: Copy, B](move x: (A, B)) {}
pub fn pair[T](move x: (T, Str)) {}
pub fn buf[T](move x: (T, Buf[F32])) {}
";
    let p = crate::tests::pkg(&[("main", src)]);
    let a = analyze(&p);
    let all = records(&p, &a);
    let freed = |name: &str| {
        let id = def(&a, name);
        let r = all.iter().find(|r| r.id == id).unwrap_or_else(|| panic!("no record of {name}"));
        let [crate::uses::Use { what: What::Drop { drop, .. }, .. }] = &r.uses[..] else { panic!("{name}: one drop") };
        let generics = crate::body::generics_of(&a, id);
        let names = crate::drop_alloc::copy_would_free(&a, id, drop).into_iter().map(|i| generics[i].name.clone());
        names.collect::<Vec<_>>()
    };
    for (name, want) in [
        ("plain", &["T"][..]),
        ("dup", &["T"]),
        ("inside", &["T"]),
        ("option", &["T"]),
        ("two", &["A", "B"]),
        ("one_of_two", &["B"]),
        ("pair", &[]),
        ("buf", &[]),
    ] {
        assert_eq!(freed(name), want, "{name}");
    }
}

/// Where the row of each anonymous function comes from, as the types stage
/// decided it (`BodyInfo::closure_rows`, S-1041 (2), D-15): written (`uses
/// {}` too), the function type expected (its type, resolved), none expected
/// (an unannotated `let`), and a later branch of a merge (S-1032 (ii-3),
/// S-1061: of an `else if` too, the middle one too), not the first, which
/// has no type before it (none expected). The body's scope has none (W6-03
/// U6b).
#[test]
fn the_scope_of_an_anonymous_function_has_where_its_row_comes_from() {
    let src = format!(
        "{STD}pub fn ap(g: fn(U32) -> U32, n: U32) -> U32 {{ g.(n) }}
pub fn f(a: Bool, b: Bool, n: U32) -> U32 uses {{Alloc}} {{
  let w = fn(y: U32) -> U32 uses {{}} {{ y }}
  let x = fn(y: U32) -> U32 {{ y }}
  let j = if a {{ pure }} else {{ fn(y: U32) -> U32 {{ y }} }}
  let k = if a {{ pure }} else if b {{ pure }} else {{ fn(y: U32) -> U32 {{ y }} }}
  let l = if a {{ fn(y: U32) -> U32 {{ y }} }} else {{ pure }}
  let m = if a {{ fn(y: U32) -> U32 {{ y }} }} else if b {{ pure }} else {{ pure }}
  let o = if a {{ pure }} else if b {{ fn(y: U32) -> U32 {{ y }} }} else {{ pure }}
  ap(fn(y) {{ y }}, n) + w.(n) + x.(n) + j.(n) + k.(n) + l.(n) + m.(n) + o.(n)
}}
"
    );
    let p = pkg(&[("main", &src)]);
    let a = analyze(&p);
    let id = def(&a, "f");
    let all = records(&p, &a);
    let r = all.iter().find(|r| r.id == id).unwrap_or_else(|| panic!("no record of f: {:?}", a.diagnostics));
    let got: Vec<String> = (r.scopes.iter())
        .map(|s| match s.from {
            None => "body".to_string(),
            Some(RowFrom::Expected(t)) => format!("expected {}", a.display_type(t)),
            Some(from) => format!("{from:?}"),
        })
        .collect();
    let want = ["body", "Written", "NoneExpected", "Joining", "Joining", "NoneExpected", "NoneExpected", "Joining"];
    assert_eq!(got, [&want[..], &["expected fn(U32) -> U32"]].concat());
    assert!(r.scopes[0].closure.is_none() && r.scopes[1..].iter().all(|s| s.closure.is_some()));
}

/// The row given to a body with none of its own (W6-03 U7b): `Alloc` and
/// `Random` to a `test` (§8.5), `Alloc` to an initializer (§6.6, S-1055);
/// and each effect a scope lacks is one, at its first use (S-1053): a body
/// with no row that calls `check` and `mk` lacks both, in the order of the
/// record.
#[test]
fn a_body_with_no_row_is_given_one_and_lacks_each_effect() {
    let src = format!(
        "{STD}use std.test.{{check, gen}}
const K: U32 = {{
  check(1, gen.u32(0, 9), fn(x: U32) -> Bool {{ x < 10 }})
  1
}}
pub fn f(n: U32) -> U32 {{
  check(1, gen.u32(0, 9), fn(x: U32) -> Bool {{ x < 10 }})
  mk(n).len() + K
}}
test \"t\" {{ check(1, gen.u32(0, 9), fn(x: U32) -> Bool {{ x < 10 }}) }}
"
    );
    let p = pkg(&[("main", &src)]);
    let a = analyze(&p);
    let all = records(&p, &a);
    let name = |d: crate::DefId| a.def(d).name.clone();
    let row = |r: &crate::uses::Record| r.scopes[0].row.effects().iter().map(|&d| name(d)).collect::<Vec<_>>();
    let of = |pred: &dyn Fn(&crate::def::DefKind) -> bool| {
        all.iter().find(|r| pred(&a.def(r.id).kind)).unwrap_or_else(|| panic!("no record: {:?}", a.diagnostics))
    };
    let (test, konst) =
        (of(&|k| matches!(k, crate::def::DefKind::Test { .. })), of(&|k| matches!(k, crate::def::DefKind::Const(_))));
    assert_eq!((row(test), row(konst)), (vec!["Alloc".to_string(), "Random".into()], vec!["Alloc".to_string()]));
    let text = |u: &crate::uses::Use| src[u.at.start as usize..u.at.end as usize].to_string();
    let lacks = |r: &crate::uses::Record| -> Vec<(String, String)> {
        r.lacking(&a).into_iter().map(|(_, e, u)| (name(e), text(u))).collect()
    };
    let f = all.iter().find(|r| r.id == def(&a, "f")).expect("a record of f");
    let check = "check(1, gen.u32(0, 9), fn(x: U32) -> Bool { x < 10 })";
    assert_eq!(lacks(f), [("Random".to_string(), check.to_string()), ("Alloc".into(), "mk(n)".into())]);
    assert_eq!((lacks(konst), lacks(test)), (vec![("Random".to_string(), check.to_string())], vec![]));
}
