//! The place of the rewrite of `fmt/rewrites.rs` that a returned value
//! decides: the tail position of spec §6.1 (the `return e`s that go). Each
//! judgement walks up from a node to its parents, through the nesting of
//! §2.5 (at most 256 levels), so the whole choice stays linear in the tree.

use crate::cst::{Cst, Elem, NodeId, NodeKind};

/// The last statement of the block `b`, the attributes the lowering skips
/// skipped too. A `return` without a value is a statement like any other:
/// fmt does not take it off (S-547), so the statement before it is not the
/// last.
fn last_statement(cst: &Cst, b: NodeId) -> Option<NodeId> {
    cst.children(b).iter().rev().find_map(|e| match *e {
        Elem::Node(x) if cst.kind(x) != NodeKind::Attr => Some(x),
        _ => None,
    })
}

/// The last child node of `n`, looked for from the end.
fn last_node(cst: &Cst, n: NodeId) -> Option<NodeId> {
    cst.children(n).iter().rev().find_map(|e| match *e {
        Elem::Node(c) => Some(c),
        Elem::Token(_) => None,
    })
}

/// The parent of the expression `e` out of its parentheses, and the
/// outermost parenthesis (or `e`): a parenthesis does not change where an
/// expression is, whether fmt takes it off or not.
fn climb(cst: &Cst, mut e: NodeId) -> Option<(NodeId, NodeId)> {
    loop {
        let p = cst.parent(e)?;
        if cst.kind(p) != NodeKind::ParenExpr {
            return Some((p, e));
        }
        e = p;
    }
}

/// The `match` of the arm `arm` (in its `MatchArms`).
fn match_of(cst: &Cst, arm: NodeId) -> Option<NodeId> {
    cst.parent(arm).and_then(|arms| cst.parent(arms))
}

/// Whether `child` of the `if` or the arm `p` is a branch (not the
/// condition) or the value of the arm (not the pattern or the guard), and
/// the `if` or the `match` is where `place` says.
fn branch_of(cst: &Cst, p: NodeId, child: NodeId, place: impl Fn(NodeId) -> bool) -> bool {
    match cst.kind(p) {
        NodeKind::IfExpr => cst.child_nodes(p).next() != Some(child) && place(p),
        NodeKind::MatchArm => last_node(cst, p) == Some(child) && match_of(cst, p).is_some_and(place),
        _ => false,
    }
}

/// Whether the block `b` is in the tail position (§6.1): the body of a
/// function (a method, a default body of a trait and a function of a
/// handler too) or of an anonymous function, or a branch of an `if` or an
/// arm of a `match` in the tail position. Not the body of a loop, of a
/// `flow`, of a `test`, nor an `unsafe`, `handle` or block expression.
fn is_tail_block(cst: &Cst, b: NodeId) -> bool {
    let Some(p) = cst.parent(b) else { return false };
    matches!(cst.kind(p), NodeKind::Fn | NodeKind::ClosureExpr) || branch_of(cst, p, b, |e| is_tail_expr(cst, e))
}

/// Whether the expression `e` is in the tail position: the last statement
/// of a block in the tail position or the value of the `return` there, or
/// a branch of such an `if` or `match`.
fn is_tail_expr(cst: &Cst, e: NodeId) -> bool {
    let Some((p, child)) = climb(cst, e) else { return false };
    match cst.kind(p) {
        NodeKind::ExprStmt | NodeKind::ReturnStmt => last_of_tail_block(cst, p),
        _ => branch_of(cst, p, child, |e| is_tail_expr(cst, e)),
    }
}

/// Whether the statement `s` is the last of a block in the tail position.
pub(super) fn last_of_tail_block(cst: &Cst, s: NodeId) -> bool {
    let Some(b) = cst.parent(s).filter(|&b| cst.kind(b) == NodeKind::Block) else { return false };
    last_statement(cst, b) == Some(s) && is_tail_block(cst, b)
}
