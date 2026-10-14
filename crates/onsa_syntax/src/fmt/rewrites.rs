//! The rewrites of `onsa fmt` that change the tree (`docs/onsa-tools.md`
//! §3.3): the one closed list, in [`REWRITES`].
//!
//! A rewrite decides on the CST which nodes it rewrites: the nodes it drops
//! code tokens from, which the plan (`fmt/plan.rs`) reads. The comparison of
//! the check before writing and of `diff --ast` (§3.5,
//! [`crate::diff::same_program`]) applies the same rewrite to the AST of both
//! files ([`normalize`]): the AST side does not decide again, it rewrites the
//! AST nodes made from the chosen CST nodes (`Parsed::map`), and a chosen node
//! whose AST is not of the form the CST side saw is an internal error.
//!
//! W3-11 has the one rewrite the formatter did before it printed the CST: the
//! `return` at the end of the body of a function. W3-12 adds the others of
//! §3.3 (`-> ()`, an empty `uses {}`, redundant parentheses, `init`, `move`
//! in the place of the returned value) in the same form; the parentheses, for
//! one, choose a `ParenExpr`, `ParenType` or `ParenPat` node, drop its two
//! brackets and take the AST node of `map.exprs`, `map.types` or `map.pats`
//! out of its parent.

use std::collections::{HashMap, HashSet};

use crate::ast::{Ast, ExprKind, StmtKind};
use crate::cst::{Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::parser::Parsed;
use crate::token::TokenKind;

/// A rewrite of §3.3.
pub(crate) struct Rewrite {
    /// The code tokens it drops from the node (it is called on every node of
    /// the tree): the node it drops tokens from is a node it rewrites.
    pub(crate) cst: fn(&Cst, NodeId, &mut Vec<TokenIdx>),
    /// The same rewrite on the AST, of the nodes the CST side chose.
    pub(crate) ast: fn(&mut Ast, &Parsed, &[NodeId]),
}

/// The closed list of §3.3.
pub(crate) const REWRITES: &[Rewrite] = &[Rewrite { cst: tail_return, ast: tail_return_ast }];

/// Every node of the tree, the root first (without recursion).
pub(crate) fn all_nodes(cst: &Cst) -> Vec<NodeId> {
    let mut nodes = vec![cst.root()];
    let mut i = 0;
    while let Some(&n) = nodes.get(i) {
        nodes.extend(cst.child_nodes(n));
        i += 1;
    }
    nodes
}

/// The AST of `parsed` with every rewrite of the list (§3.5). `parsed` has
/// no diagnostic of the syntax stage (the callers refuse such a file first):
/// one is an internal error here, before a rewrite meets a broken tree.
pub(crate) fn normalize(parsed: &Parsed) -> Ast {
    if let Some(d) = parsed.first_syntax_error() {
        onsa_diag::internal::bug(Some(d.span), "the comparison of fmt and `diff --ast` got a tree with a syntax error");
    }
    let mut ast = parsed.ast.clone();
    let nodes = all_nodes(&parsed.cst);
    let mut dropped = Vec::new();
    for rewrite in REWRITES {
        let mut chosen = Vec::new();
        for &n in &nodes {
            dropped.clear();
            (rewrite.cst)(&parsed.cst, n, &mut dropped);
            if !dropped.is_empty() {
                chosen.push(n);
            }
        }
        (rewrite.ast)(&mut ast, parsed, &chosen);
    }
    ast
}

/// The `return` of a `return e` that is the last statement of the body of a
/// function (spec §6.1): `e` becomes the value of the body. The `return`
/// in a branch of an `if` or a `match` at the end, in the body of a closure
/// and without a value is not dropped yet (the formatter did not drop them
/// before W3-11).
fn tail_return(cst: &Cst, n: NodeId, out: &mut Vec<TokenIdx>) {
    if cst.kind(n) != NodeKind::ReturnStmt || cst.child_nodes(n).next().is_none() {
        return;
    }
    let Some(body) = cst.parent(n).filter(|&b| cst.kind(b) == NodeKind::Block) else { return };
    if cst.parent(body).is_none_or(|f| cst.kind(f) != NodeKind::Fn) || last_node(cst, body) != Some(n) {
        return;
    }
    let keyword = cst.children(n).iter().find_map(|e| match *e {
        Elem::Token(t) if cst.token(t).kind == TokenKind::KwReturn => Some(t),
        _ => None,
    });
    out.extend(keyword);
}

/// The last child node of `n`, looked for from the end (a body of many
/// statements is not walked for each of them).
fn last_node(cst: &Cst, n: NodeId) -> Option<NodeId> {
    cst.children(n).iter().rev().find_map(|e| match *e {
        Elem::Node(c) => Some(c),
        Elem::Token(_) => None,
    })
}

/// [`tail_return`] on the AST: the chosen statement `return e`, the last of
/// its block, becomes the value `e` of the block.
fn tail_return_ast(ast: &mut Ast, parsed: &Parsed, chosen: &[NodeId]) {
    let bug = |n: NodeId, what: &str| -> ! {
        onsa_diag::internal::bug(Some(parsed.cst.span(n)), format!("fmt's rewrite of the last `return`: {what}"))
    };
    let wanted: HashSet<NodeId> = chosen.iter().flat_map(|&n| [Some(n), parsed.cst.parent(n)]).flatten().collect();
    let index_of = |nodes: &[NodeId]| -> HashMap<NodeId, usize> {
        nodes.iter().enumerate().filter(|(_, n)| wanted.contains(n)).map(|(i, &n)| (n, i)).collect()
    };
    let (stmt_of, expr_of) = (index_of(&parsed.map.stmts), index_of(&parsed.map.exprs));
    for &n in chosen {
        let block = parsed.cst.parent(n).and_then(|b| expr_of.get(&b));
        let (Some(&s), Some(&e)) = (stmt_of.get(&n), block) else { bug(n, "no statement in a block") };
        let ExprKind::Block(block) = &mut ast.exprs[e].kind else { bug(n, "no statement in a block") };
        let StmtKind::Return(Some(value)) = ast.stmts[s].kind else { bug(n, "not a `return` with a value") };
        if block.stmts.last().map(|l| l.index()) != Some(s) || block.tail.is_some() {
            bug(n, "not the last statement of its block");
        }
        block.stmts.pop();
        block.tail = Some(value);
    }
}

#[cfg(test)]
mod tests {
    use onsa_diag::FileId;

    /// W3-11/b 1: a body that ends in more than one `return` (the ones before
    /// the last are dead code, which `check` takes) loses the `return` of the
    /// last statement only, on the CST and on the AST alike, so the check
    /// passes and the output is the one fmt wrote before the check.
    #[test]
    fn only_the_last_of_several_returns_is_rewritten() {
        let f = |body: &str| format!("fn f(c: Bool) -> I32 {{\n{body}}}\n");
        let cases = [
            ("  return 1\n  return 2\n", "  return 1\n  2\n"),
            ("  return 1\n  return 2\n  return 3\n", "  return 1\n  return 2\n  3\n"),
            ("  return 1\n  return 2 // c\n", "  return 1\n  2 // c\n"),
            ("  return 1\n  return 2\n  // trailing\n", "  return 1\n  2\n  // trailing\n"),
            ("  if c {\n    return 1\n  }\n  return 2\n  return 3\n", "  if c {\n    return 1\n  }\n  return 2\n  3\n"),
        ];
        let mut all = cases.map(|(a, b)| (f(a), f(b))).to_vec();
        all.push((
            "impl S {\n  fn g(self) -> I32 {\n    return 1\n    return self.v\n  }\n}\n".into(),
            "impl S {\n  fn g(self) -> I32 {\n    return 1\n    self.v\n  }\n}\n".into(),
        ));
        for (src, want) in &all {
            let parsed = crate::parse(FileId(0), src);
            assert!(parsed.diagnostics.is_empty(), "{src}: {:?}", parsed.diagnostics);
            assert_eq!(crate::format(&parsed, src).as_deref(), Ok(want.as_str()), "{src}");
        }
    }
}
