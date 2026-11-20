//! The reading of an `if` chain (§11.5): the conditions of its links and its
//! last `else`, the later `if`s with no `~` only.

use onsa_diag::FileId;
use onsa_syntax::ast::ExprKind;

use super::chain;

/// The texts of the conditions and of the last `else` of the chain of the
/// first `if` of the body `body`.
fn read(body: &str) -> (Vec<String>, Option<String>) {
    let src = format!("fn f(a: Bool, b: Bool, c: Bool) -> I32 {{\n  {body}\n}}\n");
    let ast = onsa_syntax::parse(FileId(0), &src).ast;
    let text = |e: onsa_syntax::ast::ExprId| {
        let s = ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    let ifs = (0..ast.exprs.len() as u32).map(onsa_syntax::ast::ExprId);
    let head = ifs.filter(|&e| matches!(ast.expr(e).kind, ExprKind::If { .. })).min_by_key(|&e| ast.expr(e).span.start);
    let c = chain(&ast, head.expect("an `if`"));
    (c.links.iter().map(|l| text(l.cond)).collect(), c.last.map(text))
}

fn texts(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|x| x.to_string()).collect()
}

#[test]
fn a_chain_is_read_to_its_last_else() {
    let (conds, last) = read("if~ a { 1 } else if b { 2 } else if c { 3 } else { 4 }");
    assert_eq!((conds, last.as_deref()), (texts(&["a", "b", "c"]), Some("{ 4 }")));
    let (conds, last) = read("if a { 1 } else if b { 2 } else { 3 }");
    assert_eq!((conds, last.as_deref()), (texts(&["a", "b"]), Some("{ 3 }")));
}

/// An `if` in the block of an `else` is the branch, not a link (§11.5: its
/// condition is evaluated as a part of the branch).
#[test]
fn an_if_in_an_else_block_is_the_branch() {
    let (conds, last) = read("if~ a { 1 } else { if b { 2 } else { 3 } }");
    assert_eq!((conds, last.as_deref()), (texts(&["a"]), Some("{ if b { 2 } else { 3 } }")));
    let (conds, last) = read("if a { 1 }");
    assert_eq!((conds, last), (texts(&["a"]), None));
}
