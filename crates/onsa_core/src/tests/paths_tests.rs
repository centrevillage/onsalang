//! W8-03 U6b: the paths of places (`paths.rs`) and whether two are
//! disjoint, by the rule of the checks (S-796): two roots, or two different
//! fields at the same step, part two places; a prefix and indices, of any
//! value, do not. A local of `LocalKind::Alias` is the place it names.
//! The paths read no type: every node here is a `U32`.

use onsa_diag::{FileId, Span};

use crate::alias::{Table, table};
use crate::ir::*;
use crate::paths::{Path, Step, disjoint};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

/// `xs`, `s` and `b`, values.
const XS: LocalId = LocalId(0);
const S: LocalId = LocalId(1);
const B: LocalId = LocalId(2);
/// `r`, the alias of `xs[1]`, and `q`, of `s.0` (`Alias` statements).
const R: LocalId = LocalId(3);
const Q: LocalId = LocalId(4);

fn x(kind: ExprKind) -> Expr {
    Expr::new(Types::U32, sp(), kind)
}

fn n(v: i128) -> Expr {
    x(ExprKind::Lit(Lit::Int(v)))
}

fn local(l: LocalId) -> Expr {
    x(ExprKind::Local(l))
}

fn field(base: Expr, index: u32) -> Expr {
    x(ExprKind::Field { base: Box::new(base), index })
}

fn index(base: Expr, i: Expr) -> Expr {
    x(ExprKind::Index { base: Box::new(base), index: Box::new(i), bounds: Bounds::Checked })
}

/// The table of a function whose body names `r = xs[1]` and `q = s.0`.
fn aliases() -> Table {
    let of = |name: &str, write| Local { name: name.into(), ty: Types::U32, kind: LocalKind::Alias { write } };
    let locals = vec![
        Local::value("xs", Types::U32),
        Local::value("s", Types::U32),
        Local::value("b", Types::U32),
        of("r", true),
        of("q", false),
    ];
    let row = Place::Index(Box::new(Place::Local(XS)), Box::new(n(1)), sp(), Bounds::Checked);
    let stmts = [StmtKind::Alias(R, row), StmtKind::Alias(Q, Place::Field(Box::new(Place::Local(S)), 0))];
    let f = FnDef {
        name: "g".into(),
        params: Vec::new(),
        ret: Types::UNIT,
        sret: false,
        rt: false,
        locals,
        body: Some(Block { stmts: stmts.into_iter().map(|kind| Stmt { span: sp(), kind }).collect(), value: None }),
        span: sp(),
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    };
    table(&f)
}

/// The path of the place expression `e`, the same as of its place.
fn path(e: &Expr) -> Path {
    let t = aliases();
    let p = Path::of_expr(&t, e).expect("a place");
    assert_eq!(Path::of_place(&t, &e.as_place().expect("a place")), p, "of the expression and of its place");
    p
}

/// Whether `a` and `b` are disjoint, the same both ways.
fn apart(a: &Expr, b: &Expr) -> bool {
    let (a, b) = (path(a), path(b));
    assert_eq!(disjoint(&a, &b), disjoint(&b, &a), "{a:?} {b:?}");
    disjoint(&a, &b)
}

#[test]
fn the_path_of_a_place_is_its_root_and_its_steps_outermost_last() {
    let e = field(index(field(local(S), 2), local(B)), 1);
    assert_eq!(path(&e), Path { root: S, steps: vec![Step::Field(2), Step::Index, Step::Field(1)] });
    assert_eq!(path(&local(B)), Path { root: B, steps: Vec::new() });
}

#[test]
fn an_expression_that_is_no_place_has_no_path() {
    let t = aliases();
    let call = x(ExprKind::Call { fn_: FnId(0), args: Vec::new() });
    for e in [n(1), field(call.clone(), 0), index(call, n(0)), x(ExprKind::SpanOf(Box::new(local(XS))))] {
        assert_eq!(Path::of_expr(&t, &e), None, "{e:?}");
    }
}

#[test]
fn places_of_two_roots_are_disjoint() {
    assert!(apart(&local(S), &local(B)));
    assert!(apart(&field(local(S), 0), &field(local(B), 0)));
    assert!(apart(&index(local(XS), n(0)), &index(local(S), n(0))));
}

#[test]
fn two_fields_of_one_root_are_disjoint_and_one_field_is_not() {
    assert!(apart(&field(local(S), 0), &field(local(S), 1)));
    assert!(apart(&field(field(local(S), 0), 1), &field(field(local(S), 0), 2)), "at the second step");
    assert!(!apart(&field(local(S), 0), &field(local(S), 0)));
    assert!(!apart(&field(field(local(S), 0), 1), &field(field(local(S), 0), 1)));
}

#[test]
fn a_place_and_a_prefix_of_it_overlap() {
    assert!(!apart(&local(S), &field(local(S), 0)));
    assert!(!apart(&field(local(S), 0), &index(field(local(S), 0), n(3))));
    assert!(!apart(&local(XS), &field(index(local(XS), n(0)), 1)));
}

/// S-796: an index is the same as any other, two literals of different
/// values too; two fields past them part the places.
#[test]
fn indices_of_any_value_overlap() {
    assert!(!apart(&index(local(XS), n(0)), &index(local(XS), n(1))), "two literals");
    assert!(!apart(&index(local(XS), local(B)), &index(local(XS), n(1))));
    assert!(!apart(&field(index(local(XS), n(0)), 1), &field(index(local(XS), n(1)), 1)));
    assert!(apart(&field(index(local(XS), n(0)), 1), &field(index(local(XS), n(1)), 2)), "fields past the index");
}

/// `r` names `xs[1]` and `q` names `s.0`: a place through one is the place
/// it names.
#[test]
fn a_place_through_an_alias_is_the_place_it_names() {
    assert_eq!(path(&index(local(R), n(0))), Path { root: XS, steps: vec![Step::Index, Step::Index] });
    assert_eq!(path(&field(local(Q), 3)), Path { root: S, steps: vec![Step::Field(0), Step::Field(3)] });
    assert!(!apart(&index(local(R), n(0)), &index(local(XS), n(0))), "`r[0]` and `xs[0]`");
    assert!(!apart(&local(R), &local(XS)));
    assert!(!apart(&local(Q), &local(S)), "`q` and its root");
    assert!(!apart(&local(Q), &field(local(S), 0)));
    assert!(apart(&local(Q), &field(local(S), 1)), "`q` is `s.0`, apart from `s.1`");
    assert!(apart(&local(R), &local(Q)), "two roots under the aliases");
}
