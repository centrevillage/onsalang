//! Tests of the tails of a value (`crate::tails`, §5.2, §5.4).

use onsa_diag::FileId;

use crate::ast::ItemKind;
use crate::tails::Tail;

/// The tails of the body of the one function of `src`, by their text.
fn tails_of(src: &str) -> Vec<String> {
    let p = crate::parse(FileId(0), src);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let ItemKind::Fn(f) = &p.ast.item(p.ast.root[0]).kind else { panic!("not a function") };
    let mut out = Vec::new();
    p.ast.tails(f.body.expect("a body"), &mut out);
    let text = |e| {
        let s = p.ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    out.into_iter()
        .map(|t| match t {
            Tail::Value(e) => text(e),
            Tail::Exits => "exits".into(),
            Tail::Unit(e) => format!("() of {}", text(e)),
        })
        .collect()
}

#[test]
fn the_tails_through_branches_blocks_and_parentheses() {
    let src = "fn f(c: Bool, x: I32, y: I32) -> I32 {\n  (if c { (x) } else { match c { true => { y.a }, false => { return 0 } } })\n}\n";
    assert_eq!(tails_of(src), ["x", "y.a", "exits"]);
    let src = "fn f(c: Bool, x: I32) -> I32 {\n  { if c { x } }\n}\n";
    assert_eq!(tails_of(src), ["() of if c { x }"]);
    let src = "fn f(x: I32) -> I32 {\n  { let y = x }\n}\n";
    assert_eq!(tails_of(src), ["() of { let y = x }"]);
    let src = "fn f(x: Buf[F32]) -> Buf[F32] {\n  if true { move x } else { x.slice(0, 1) }\n}\n";
    assert_eq!(tails_of(src), ["move x", "x.slice(0, 1)"]);
}
