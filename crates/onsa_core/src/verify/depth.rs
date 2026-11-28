//! V-22 (R-319): the Core of an item is at most [`CORE_DEPTH_LIMIT`] nodes
//! deep. It is counted with a stack of its own, not by recursion, so a Core
//! of any depth is counted, and before every walk that recurses: the other
//! rules, `rt_cycles`, `fold`, `storage`, `moves`, `dump`, the interpreter
//! and the backends recurse at most that deep.

use onsa_diag::Span;

use super::{Rule, VerifyError};
use crate::ir::{Block, Expr, Module, Place, Stmt};
use crate::walk::{Child, Part, PlaceRole, Role, block_children, expr_children, place_children, stmt_children};

/// The nodes on a path from the root of an item down (a block, a statement,
/// an expression and a place are each one; the body of a function and the
/// initializer of a `const` are 1).
///
/// The limit holds the two conditions of the plan (W8-01, part 1, 7.2):
/// (1) a correct program of the source depth 256 (§2.5) passes, unless the
/// values of its `const`s nest past it (a chain of declarations, the rest of
/// R-319: an internal error); (2) a level of the stages after lowering times
/// the limit fits in [`onsa_diag::stack::STACK_SIZE`]. Measured on
/// aarch64-apple-darwin (2026-11-28, W8-02 U5b, the stack painted under each
/// stage): (1) a level of the source lowers to at most about 5 nodes (a
/// `match~` in an arm of a `match~`: 5 nodes a nest and 8, so 256 levels
/// are about 1280 nodes; the other forms of flows 4 to 5 a level, the rest
/// at most 3); (2) the stage that takes the most, the C backend, takes up
/// to 35 K a node in a debug build (nested calls that take and return a
/// struct by value; the verifier up to 4 K, the others less), so 1400
/// nodes take 49 MB of the 64 MiB.
pub const CORE_DEPTH_LIMIT: u32 = 1400;

#[derive(Clone, Copy)]
enum Node<'a> {
    Block(&'a Block),
    Stmt(&'a Stmt),
    Expr(&'a Expr),
    Place(&'a Place, PlaceRole),
}

/// V-22 for every item of `m`: the first item deeper than the limit, at its
/// first node found past it.
pub(crate) fn module(m: &Module) -> Result<(), VerifyError> {
    items(m, CORE_DEPTH_LIMIT).map(drop)
}

/// The depth of the deepest item of `m`, with no limit (the tests).
#[cfg(test)]
pub(crate) fn deepest(m: &Module) -> u32 {
    items(m, u32::MAX).expect("no item is deeper than no limit")
}

/// The depth of the deepest item of `m`, or the error of the first item
/// deeper than `limit`.
fn items(m: &Module, limit: u32) -> Result<u32, VerifyError> {
    let mut stack = Vec::new();
    let consts = m.consts.iter().map(|c| (&c.name, Node::Expr(&c.init), c.init.span));
    let fns = m.fns.iter().filter_map(|f| Some((&f.name, Node::Block(f.body.as_ref()?), f.span)));
    let mut deepest = 0;
    for (name, root, at) in consts.chain(fns) {
        deepest = deepest.max(depth(root, at, limit, &mut stack).map_err(|at| VerifyError {
            rule: Rule::V22,
            fn_name: name.clone(),
            span: Some(at),
            message: format!("the Core is deeper than {limit} nodes"),
        })?);
    }
    Ok(deepest)
}

/// The depth under `root`, or the position of the first node found deeper
/// than `limit`. A block and a place have the position of their parent.
fn depth<'a>(root: Node<'a>, at: Span, limit: u32, stack: &mut Vec<(Node<'a>, u32, Span)>) -> Result<u32, Span> {
    stack.clear();
    stack.push((root, 1, at));
    let mut deepest = 0;
    while let Some((node, d, at)) = stack.pop() {
        if d > limit {
            return Err(at);
        }
        deepest = deepest.max(d);
        let mut push = |(n, at): (Node<'a>, Span)| stack.push((n, d + 1, at));
        match node {
            Node::Block(b) => block_children(b, Role::Read, &mut |p| match p {
                Part::Stmt(s) => push((Node::Stmt(s), s.span)),
                Part::Value(v, _) => push((Node::Expr(v), v.span)),
            }),
            Node::Stmt(s) => stmt_children(s, &mut |c| push(of(c, at))),
            Node::Expr(e) => expr_children(e, &mut |c| push(of(c, at))),
            Node::Place(p, role) => place_children(p, role, &mut |c| push(of(c, at))),
        }
    }
    Ok(deepest)
}

/// The node of a child, with its position (a block and a place have none: `at`, the parent's).
fn of(c: Child<'_>, at: Span) -> (Node<'_>, Span) {
    match c {
        Child::Expr(e, ..) => (Node::Expr(e), e.span),
        Child::Block(b, ..) => (Node::Block(b), at),
        Child::Place(p, role) => (Node::Place(p, role), at),
    }
}
