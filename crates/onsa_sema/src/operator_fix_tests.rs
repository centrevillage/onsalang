//! The candidates and the notes of the generic numbers that no case holds:
//! a case writes the promise of a candidate, not the text of a note (§18.1),
//! so the notes are here; with the tables they come from (§6.3).

use onsa_diag::{Code, Diagnostic, FileId};
use onsa_syntax::ast::BinOp;

use crate::def::Bound;
use crate::deferred::OpNeed;
use crate::tests::analyze;
use crate::traits::{implies, member_note, narrowable, narrowed_bound, op_bound};
use crate::{Module, Package};

/// The one diagnostic of `src`, with std.
fn one(src: &str) -> Diagnostic {
    let module = Module::new(vec!["main".into()], FileId(0), src.to_string(), onsa_syntax::parse(FileId(0), src));
    let mut d = analyze(&Package::new("t", vec![module], vec![crate::flow_tests::std_package()])).diagnostics;
    assert_eq!(d.len(), 1, "{src}: {d:?}");
    d.remove(0)
}

fn notes(d: &Diagnostic) -> Vec<String> {
    d.notes.iter().map(|n| n.message.clone()).collect()
}

/// `src` with the only candidate of `d` applied.
fn applied(src: &str, d: &Diagnostic) -> String {
    assert_eq!(d.fixes.len(), 1, "{src}: {d:?}");
    let mut out = src.to_string();
    let mut edits: Vec<_> = d.fixes[0].edits().iter().collect();
    edits.sort_by_key(|e| std::cmp::Reverse(e.span.start));
    for e in edits {
        out.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
    }
    out
}

/// §6.3: the trait of each operator, which has what the operator needs.
#[test]
fn the_trait_narrowed_to_has_the_operator() {
    use BinOp::*;
    let int = [BitAnd, BitOr, BitXor, Shl, Shr, WrapAdd, WrapSub, WrapMul, SatAdd, SatSub, SatMul];
    let table = (int.map(|b| (OpNeed::Binary(b), Bound::Int)).into_iter())
        .chain([Add, Sub, Mul, Div, Rem].map(|b| (OpNeed::Binary(b), Bound::Num)))
        .chain([Eq, Ne].map(|b| (OpNeed::Binary(b), Bound::PartialEq)))
        .chain([Lt, Le, Gt, Ge].map(|b| (OpNeed::Binary(b), Bound::PartialOrd)))
        .chain([(OpNeed::Neg, Bound::Num), (OpNeed::Not, Bound::Int)]);
    for (op, want) in table {
        assert_eq!(narrowed_bound(op), want, "{op:?}");
        assert!(implies(want, op_bound(op)), "{op:?}");
    }
}

/// §6.3: the bounds that cannot be narrowed follow from the table.
#[test]
fn a_list_no_row_holds_is_not_narrowed() {
    assert!(!narrowable(&[Bound::Unsigned], Bound::Num));
    assert!(!narrowable(&[Bound::Float], Bound::Int));
    assert!(narrowable(&[Bound::Int], Bound::Num));
    assert!(narrowable(&[Bound::Num], Bound::Int));
    assert!(narrowable(&[Bound::Show, Bound::Copy], Bound::Num));
    assert!(narrowable(&[], Bound::PartialEq));
    // No row holds `Ordinal`: a type meets it by its derive, with the other derivable traits (§6.4).
    assert!(narrowable(&[Bound::Ordinal], Bound::PartialEq));
    assert!(!narrowable(&[Bound::Ordinal], Bound::Num));
}

#[test]
fn every_bound_the_candidate_contains_goes() {
    let src = "pub fn f[T: PartialOrd + Show + PartialEq](p: T, q: T) -> T {\n  p + q\n}\n";
    assert!(applied(src, &one(src)).starts_with("pub fn f[T: Num + Show](p"));
    let src = "pub fn f[T: Show + ?Dup + PartialEq](p: T, q: T) -> Bool {\n  p < q\n}\n";
    assert!(applied(src, &one(src)).starts_with("pub fn f[T: Show + ?Dup + PartialOrd](p"));
}

/// A check that waits for the type gives what the operator gives (§4.7).
#[test]
fn a_deferred_operator_has_the_same_candidate_and_note() {
    let body = "(p: T) -> T {\n  let o = None\n  match o {\n    Some(v) => -v,\n    None => p,\n  }\n}\n";
    let src = format!("pub fn f[T: AnyNum]{body}");
    let d = one(&src);
    assert_eq!(d.code, Code::E0401);
    assert!(applied(&src, &d).starts_with("pub fn f[T: Num](p"));
    let d = one(&format!("pub fn f[T: Unsigned]{body}"));
    assert_eq!((d.code, d.fixes.len()), (Code::E0401, 0));
    assert!(notes(&d).iter().any(|n| n.contains("`T.ZERO -% x`")), "{d:?}");
}

#[test]
fn the_negation_of_an_unsigned_type_has_its_note() {
    for src in ["pub fn f(u: U32) -> U32 {\n  -u\n}\n", "pub fn f() -> U8 {\n  -5\n}\n"] {
        let d = one(src);
        assert_eq!(d.code, Code::E0401);
        assert!(notes(&d).iter().any(|n| n.contains("`0 -% u`")), "{d:?}");
    }
    let d = one("pub fn f[T: Unsigned](x: T) -> T {\n  -x\n}\n");
    assert!(notes(&d).iter().any(|n| n.contains("`T.ZERO -% x`")), "{d:?}");
    let d = one("pub fn f[T: Int](x: T) -> T {\n  -x\n}\n");
    assert!(notes(&d).iter().all(|n| !n.contains("-%")), "{d:?}");
    let d = one("pub fn f(x: Bool) -> Bool {\n  -x\n}\n");
    assert!(notes(&d).is_empty(), "{d:?}");
}

/// §6.3: `U32` なら `AnyNum`、`Int`、`Unsigned`.
#[test]
fn an_e0416_of_a_number_trait_names_the_ones_the_type_has() {
    let call = |arg: &str, bound: &str| {
        one(&format!("fn g[T: {bound}](x: T) -> T {{\n  x\n}}\n\npub fn f(a: {arg}) -> {arg} {{\n  g(a)\n}}\n"))
    };
    let of = |d: Diagnostic| notes(&d).into_iter().filter(|n| n.contains("number traits")).collect::<Vec<_>>();
    assert_eq!(of(call("U32", "Num")), ["`U32` satisfies the number traits `AnyNum`, `Int` and `Unsigned` (§6.3)"]);
    assert_eq!(of(call("I32", "Float")), ["`I32` satisfies the number traits `AnyNum`, `Num` and `Int` (§6.3)"]);
    assert_eq!(of(call("F64", "Int")), ["`F64` satisfies the number traits `AnyNum`, `Num` and `Float` (§6.3)"]);
    assert!(of(call("Bool", "AnyNum")).is_empty());
    assert!(of(call("(I32, I32)", "AnyNum")).is_empty());
    assert!(of(call("Array[I32]", "PartialOrd")).is_empty());
    // A type argument written in a signature is the same requirement.
    let d = one("pub struct W[T: Float] {\n  v: T,\n}\n\npub fn f(x: W[I32]) -> U32 {\n  0\n}\n");
    assert_eq!(of(d), ["`I32` satisfies the number traits `AnyNum`, `Num` and `Int` (§6.3)"]);
}

#[test]
fn a_member_the_bounds_do_not_give_names_the_traits_that_do() {
    let d = one("pub fn f[T: Num]() -> T {\n  T.ONE\n}\n");
    assert_eq!(d.code, Code::E0302);
    assert_eq!(notes(&d), ["`ONE` is a member of `Float` and `Int`, which the bounds of `T` do not imply (§6.3)"]);
    let d = one("pub fn f[T: Float]() -> U32 {\n  T.BITS\n}\n");
    assert_eq!(notes(&d), ["`BITS` is a member of `Int`, which the bounds of `T` do not imply (§6.3)"]);
    assert_eq!(member_note("T", "ZERO").as_deref().map(|n| n.contains("`AnyNum`")), Some(true));
    assert!(notes(&one("pub fn f[T: Num]() -> T {\n  T.PIE\n}\n")).is_empty());
}

/// `--` is no prefix (§3.1): the form goes in parentheses after a `-`.
#[test]
fn the_form_of_min_is_read_where_it_is_put() {
    let src = "pub fn f(a: F32) -> F32 {\n  a-F32.MIN\n}\n";
    assert_eq!(applied(src, &one(src)), "pub fn f(a: F32) -> F32 {\n  a-(-F32.MAX)\n}\n");
    let src = "pub fn f[T: Float](a: T) -> T {\n  a-T.MIN\n}\n";
    assert_eq!(applied(src, &one(src)), "pub fn f[T: Float](a: T) -> T {\n  a-(-T.MAX)\n}\n");
    let src = "pub fn f(a: F32) -> F32 {\n  a - F32.MIN\n}\n";
    assert_eq!(applied(src, &one(src)), "pub fn f(a: F32) -> F32 {\n  a - -F32.MAX\n}\n");
    let src = "pub fn f() -> U32 {\n  (F32.MIN).to_bits()\n}\n";
    assert_eq!(applied(src, &one(src)), "pub fn f() -> U32 {\n  (-F32.MAX).to_bits()\n}\n");
}

/// A place the form is not read at has no candidate: a callee, a hole and
/// a constant expression of §4.5.
#[test]
fn min_has_no_candidate_where_the_form_is_not_taken() {
    for src in [
        "pub fn f() -> F32 {\n  F32.MIN()\n}\n",
        "pub fn f() -> Str {\n  \"{F32.MIN}\"\n}\n",
        "pub fn f[T: Float]() -> T {\n  T.MIN()\n}\n",
        "pub fn f() -> U32 {\n  let _a = [0; F32.MIN]\n  0\n}\n",
    ] {
        let d = one(src);
        assert_eq!((d.code, d.fixes.len()), (Code::E0302, 0), "{src}");
    }
}
