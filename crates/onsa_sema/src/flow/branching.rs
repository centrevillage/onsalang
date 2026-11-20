//! The reading of an `if` chain (§11.3, §11.5, S-1094): the one place that
//! tells the conditions and the branches of `if c1 { a } else if c2 { b }
//! else { e }`, with `~` or without, which the walk of the clocks, the
//! state marking and the lowering of a flow (its stores and `if~`) read
//! (D-15). One loop over the chain, with no recursion: linear in a long
//! `else if` chain.

use onsa_syntax::ast::{Ast, ExprId, ExprKind};

#[cfg(test)]
mod tests;

/// A link of a chain: a condition, its branch, and the `if` of the two.
#[derive(Debug, Clone, Copy)]
pub struct Link {
    pub at: ExprId,
    pub cond: ExprId,
    pub then: ExprId,
}

/// The links of an `if` chain in the order of the text, and its last
/// `else`, if any (an `if~` has one, §11.5).
#[derive(Debug, Clone)]
pub struct Chain {
    pub links: Vec<Link>,
    pub last: Option<ExprId>,
}

/// The chain whose head is the `if` or `if~` `head`: its `else` while that
/// is an `if` with no `~` (one with a `~` is E0020, §2.6, and the branch it
/// is). Of an expression that is no `if`, no link, and it the last.
pub fn chain(ast: &Ast, head: ExprId) -> Chain {
    let (mut links, mut x) = (Vec::new(), Some(head));
    while let Some(at) = x
        && let ExprKind::If { cond, then, else_, tilde } = &ast.expr(at).kind
        && (links.is_empty() || tilde.is_none())
    {
        links.push(Link { at, cond: *cond, then: *then });
        x = *else_;
    }
    Chain { links, last: x }
}
