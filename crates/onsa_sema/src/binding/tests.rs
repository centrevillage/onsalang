//! The table of §5.4 ([`row`]), a row each (R-85 (2)).

use onsa_syntax::ast::Mode;

use super::{Bind, HeadRow, row};
use crate::names::body::BindingKind;

#[test]
fn the_rows_with_no_head() {
    let borrow = Bind::Borrow { no_drop: false };
    for k in [BindingKind::Param, BindingKind::SelfParam, BindingKind::ClosureParam] {
        assert_eq!(row(k(Mode::Borrow), None), borrow);
        assert_eq!(row(k(Mode::Inout), None), Bind::Inout);
        assert_eq!(row(k(Mode::Move), None), Bind::OwnedMut, "R-191");
    }
    assert_eq!(row(BindingKind::FlowInput, None), borrow);
    assert_eq!(row(BindingKind::Var, None), Bind::OwnedMut);
    assert_eq!(row(BindingKind::For { moved: true }, None), Bind::Owned);
    assert_eq!(row(BindingKind::ParVar, None), Bind::Owned);
}

#[test]
fn the_rows_of_a_head() {
    let owned = HeadRow::Owned;
    let static_ = HeadRow::Borrow { sources: Vec::new(), no_drop: true };
    let place = HeadRow::Borrow { sources: Vec::new(), no_drop: false };
    let heads = [BindingKind::Let, BindingKind::FlowLet, BindingKind::MatchBind, BindingKind::For { moved: false }];
    for k in heads {
        assert_eq!(row(k, None), Bind::Owned, "not settled");
        assert_eq!(row(k, Some(&owned)), Bind::Owned);
        assert_eq!(row(k, Some(&static_)), Bind::Borrow { no_drop: true });
        assert_eq!(row(k, Some(&place)), Bind::Borrow { no_drop: false });
    }
    // The head of `for x in move xs` is owned; the kind decides alone.
    assert_eq!(row(BindingKind::For { moved: true }, Some(&place)), Bind::Owned);
}

/// The rows the stage records for the heads of the function `f` of `src`,
/// by the text of each head's value (the one diagnostic of `src` is the
/// E0711 of the owned `if` with a borrowed tail): `owned`, or `borrow` with the texts of
/// its sources and `!` when it needs no drop.
fn heads_of(src: &str) -> Vec<(String, String)> {
    let (a, ast) = analyzed(src);
    // Only the owned tail `x` of a borrowed parameter (S-589: E0711 with no fix).
    let codes: Vec<_> = a.diagnostics.iter().map(|d| (d.code, d.fixes.len())).collect();
    assert_eq!(codes, [(onsa_diag::Code::E0711, 0)], "{:?}", a.diagnostics);
    let text = |s: onsa_diag::Span| src[s.start as usize..s.end as usize].to_string();
    let mut rows: Vec<(u32, String, String)> = bodies(&a)
        .flat_map(|info| info.heads.iter())
        .map(|(head, r)| {
            let value = value_of(&ast, *head);
            let row = match r {
                HeadRow::Owned => "owned".to_string(),
                HeadRow::Borrow { sources, no_drop } => {
                    let s: Vec<String> = sources.iter().map(|&e| text(ast.expr(e).span)).collect();
                    format!("borrow [{}]{}", s.join(", "), if *no_drop { "!" } else { "" })
                }
            };
            let span = ast.expr(value).span;
            (span.start, text(span), row)
        })
        .collect();
    rows.sort();
    rows.into_iter().map(|(_, v, r)| (v, r)).collect()
}

/// The analysis of the one module `src` (with the standard library), and its syntax tree.
fn analyzed(src: &str) -> (crate::Analysis, onsa_syntax::ast::Ast) {
    use onsa_diag::FileId;
    let parsed = onsa_syntax::parse(FileId(0), src);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let modules = vec![crate::Module { segments: vec!["main".into()], file: FileId(0), text: src.into(), parsed }];
    let pkg = crate::Package::new("t", modules, vec![crate::flow_tests::std_package()]);
    (crate::analyze(&pkg), onsa_syntax::parse(FileId(0), src).ast)
}

/// The bodies of the module of [`analyzed`].
fn bodies(a: &crate::Analysis) -> impl Iterator<Item = &crate::body::BodyInfo> {
    a.bodies.iter().filter(|(d, _)| a.def(**d).span.file == onsa_diag::FileId(0)).map(|(_, b)| b)
}

/// The value of a head: the initializer, the iterated value or the scrutinee.
fn value_of(ast: &onsa_syntax::ast::Ast, head: super::Head) -> onsa_syntax::ast::ExprId {
    use onsa_syntax::ast::StmtKind;
    match head {
        super::Head::Let(s) | super::Head::For(s) => match &ast.stmt(s).kind {
            StmtKind::Let { init: v, .. } | StmtKind::For { iter: v, .. } => *v,
            _ => unreachable!(),
        },
        super::Head::Match { scrutinee } => scrutinee,
    }
}

/// The tails of the heads (S-604, S-589), the parts of a view (S-217) and
/// the heads on no place (R-251), §5.4.
#[test]
fn the_rows_of_the_tails_views_and_values() {
    let src = "pub fn mk() -> Buf[F32] uses {Alloc} { Buf.zeroed(2) }\n\
        pub fn f(c: Bool, x: Buf[F32], y: Buf[F32], xs: Span[F32], st: Str) -> U32 uses {Alloc} {\n\
        let _ = if c { x } else { (y) }\n\
        let _ = if c { x } else { mk() }\n\
        let _ = if c { x } else { return 0 }\n\
        let _ = match c { true => \"a\", false => { \"b\" } }\n\
        let _ = if c { st } else { \"a\" }\n\
        let _ = (xs.slice(0, 1))\n\
        let v = mk()\n\
        for _ in v.slice(0, 1) {}\n\
        for _ in [mk(), mk()] {}\n\
        match mk() { _ => {} }\n\
        match ({ v }) { _ => {} }\n\
        0\n\
        }\n";
    let want = [
        ("if c { x } else { (y) }", "borrow [x, y]"),
        ("if c { x } else { mk() }", "owned"),
        ("if c { x } else { return 0 }", "borrow [x]"),
        ("match c { true => \"a\", false => { \"b\" } }", "borrow []!"),
        ("c", "borrow [c]"),
        ("if c { st } else { \"a\" }", "borrow [st]"),
        ("(xs.slice(0, 1))", "borrow [xs]"),
        ("mk()", "owned"),
        ("v.slice(0, 1)", "borrow [v]"),
        ("[mk(), mk()]", "owned"),
        ("mk()", "owned"),
        ("({ v })", "borrow [v]"),
    ];
    let got = heads_of(src);
    let want: Vec<(String, String)> = want.iter().map(|&(v, r)| (v.to_string(), r.to_string())).collect();
    assert_eq!(got, want);
}

/// The marks of the values of the heads of `src` ([`super::LitClass`], §5.4,
/// S-610, S-613, L4, S-780), with the row of the head: `static`, `no drop`,
/// `owned at <first>` or `-` (no mark), then `borrow` (`!` when it needs no
/// drop) or `owned`. `src` has no diagnostic.
fn marks_of(src: &str) -> Vec<(String, String)> {
    let (a, ast) = analyzed(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let text = |e| {
        let s: onsa_diag::Span = ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    let mut rows: Vec<(u32, String, String)> = bodies(&a)
        .flat_map(|info| info.heads.iter().map(move |(h, r)| (info, *h, r)))
        .map(|(info, head, r)| {
            let v = value_of(&ast, head);
            let mark = match info.lits.get(&v) {
                Some(super::LitClass::Static) => "static".to_string(),
                Some(super::LitClass::NoDrop) => "no drop".to_string(),
                Some(super::LitClass::Owned { first }) => format!("owned at {}", text(*first)),
                None => "-".to_string(),
            };
            let row = match r {
                HeadRow::Owned => "owned",
                HeadRow::Borrow { no_drop: true, .. } => "borrow!",
                HeadRow::Borrow { no_drop: false, .. } => "borrow",
            };
            (ast.expr(v).span.start, text(v), format!("{mark}, {row}"))
        })
        .collect();
    rows.sort();
    rows.into_iter().map(|(_, v, r)| (v, r)).collect()
}

/// The marks of the aggregates by their forms (S-610, S-613), of the names
/// that need no drop (L4), of the types that are not Dup (S-780) and of the
/// type parameters by their bounds; the paths of a static value or a literal
/// that needs no drop (S-615), §5.4.
#[test]
fn the_marks_of_the_literals() {
    let src = "pub struct Param { name: Str, value: F32 }\n\
        pub struct Pt { x: F32 }\n\
        pub enum E { A, B(Buf[F32]) }\n\
        pub enum M { Off, On }\n\
        const C: Pt = Pt { x: 1.0 }\n\
        pub fn mk() -> Str { \"a\" }\n\
        pub fn f(v: F32, s: Str, i: U32, move b: Buf[F32]) -> U32 uses {Alloc} {\n\
        let _ = [\"a\", \"bc\"]\n\
        let _ = [(\"a\", 1); 3]\n\
        let _ = (Some(\"a\"), M.On, ())\n\
        let _ = ((\"a\"))\n\
        let _ = (\"a\", 1 + 2)\n\
        let _ = (\"a\", -1)\n\
        let _ = Param { name: \"gain\", value: v }\n\
        let _ = [\"a\", s]\n\
        let nm = \"gain\"\n\
        let p = (nm, v)\n\
        let _ = [(p.0, 1)]\n\
        let o = (s, v)\n\
        let _ = (o, 1)\n\
        let _: Option[Buf[F32]] = None\n\
        let _ = E.A\n\
        let _ = (E.A, 1)\n\
        let _ = Some(move b)\n\
        let _ = [\"a\", \"bc\"][i]\n\
        let _ = (\"gain\", v).0\n\
        let _ = C.x\n\
        let _ = [mk(), \"a\"]\n\
        0\n\
        }\n\
        pub fn g[T: Copy, U, V: ?Dup](t: T, u: U, move w: V) -> U32 {\n\
        let _ = (\"a\", t)\n\
        let _ = (\"a\", u)\n\
        let _ = [move w]\n\
        0\n\
        }\n";
    let want = [
        ("[\"a\", \"bc\"]", "static, borrow!"),
        ("[(\"a\", 1); 3]", "static, borrow!"),
        ("(Some(\"a\"), M.On, ())", "static, borrow!"),
        ("((\"a\"))", "static, borrow!"),
        ("(\"a\", 1 + 2)", "no drop, borrow!"),
        ("(\"a\", -1)", "no drop, borrow!"),
        ("Param { name: \"gain\", value: v }", "no drop, borrow!"),
        ("[\"a\", s]", "owned at s, owned"),
        ("\"gain\"", "static, borrow!"),
        ("(nm, v)", "no drop, borrow!"),
        ("[(p.0, 1)]", "no drop, borrow!"),
        ("(s, v)", "owned at s, owned"),
        ("(o, 1)", "owned at o, owned"),
        ("None", "-, owned"),
        ("E.A", "-, owned"),
        ("(E.A, 1)", "owned at (E.A, 1), owned"),
        ("Some(move b)", "owned at Some(move b), owned"),
        ("[\"a\", \"bc\"][i]", "-, borrow!"),
        ("(\"gain\", v).0", "-, borrow!"),
        ("C.x", "-, borrow!"),
        ("[mk(), \"a\"]", "owned at mk(), owned"),
        ("(\"a\", t)", "no drop, borrow!"),
        ("(\"a\", u)", "owned at u, owned"),
        ("[move w]", "owned at [move w], owned"),
    ];
    let want: Vec<(String, String)> = want.iter().map(|&(v, r)| (v.to_string(), r.to_string())).collect();
    assert_eq!(marks_of(src), want);
}
