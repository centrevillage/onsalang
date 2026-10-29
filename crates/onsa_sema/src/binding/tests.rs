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
    use onsa_diag::FileId;
    let parsed = onsa_syntax::parse(FileId(0), src);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let modules = vec![crate::Module { segments: vec!["main".into()], file: FileId(0), text: src.into(), parsed }];
    let pkg = crate::Package::new("t", modules, vec![crate::flow_tests::std_package()]);
    let a = crate::analyze(&pkg);
    // Only the owned tail `x` of a borrowed parameter (S-589: E0711 with no fix).
    let codes: Vec<_> = a.diagnostics.iter().map(|d| (d.code, d.fixes.len())).collect();
    assert_eq!(codes, [(onsa_diag::Code::E0711, 0)], "{:?}", a.diagnostics);
    let ast = onsa_syntax::parse(FileId(0), src).ast;
    let text = |s: onsa_diag::Span| src[s.start as usize..s.end as usize].to_string();
    let id = a.bodies.keys().copied().find(|&d| a.def(d).name == "f" && a.def(d).span.file == FileId(0)).unwrap();
    let mut rows: Vec<(u32, String, String)> = a.bodies[&id]
        .heads
        .iter()
        .map(|(head, r)| {
            let value = match *head {
                super::Head::Let(s) | super::Head::For(s) => match &ast.stmt(s).kind {
                    onsa_syntax::ast::StmtKind::Let { init: v, .. }
                    | onsa_syntax::ast::StmtKind::For { iter: v, .. } => *v,
                    _ => unreachable!(),
                },
                super::Head::Match { scrutinee } => scrutinee,
            };
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
