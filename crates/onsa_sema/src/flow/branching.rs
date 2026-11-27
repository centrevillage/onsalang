//! The reading of an `if` chain (§11.3, §11.5, S-1094): the one place that
//! tells the conditions and the branches of `if c1 { a } else if c2 { b }
//! else { e }`, with `~` or without, which the walk of the clocks, the
//! state marking and the lowering of a flow (its stores and `if~`) read
//! (D-15). One loop over the chain, with no recursion: linear in a long
//! `else if` chain. And the conditional positions of every expression
//! ([`positions`]).

use onsa_syntax::ast::{Ast, BinOp, ExprId, ExprKind, MatchArm};

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

/// Where a part of an expression is evaluated, of the expression (§11.3,
/// §11.5), which [`positions`] gives: the one judgment of the conditional
/// positions that the walk of the clocks, the state marking and the lowering
/// of a flow read (D-15).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pos {
    /// Whenever the expression is: an operand, a branch of `if~` / `match~`
    /// (S-1094), the body of a `par~`.
    Always,
    /// Whenever the expression is, and it chooses the positions after it:
    /// the first condition of a chain, the scrutinee, the left of `&&` / `||`.
    Cond,
    /// A later condition of a chain or a guard: evaluated until one is taken
    /// only (S-1094, S-394), and it chooses the positions after it.
    Choose,
    /// A branch of `if` / `match`, on the samples that take it only; `head`
    /// the `if` that starts its chain or the `match`, which a `~` makes
    /// evaluate every branch.
    Branch { head: ExprId },
    /// The right of `&&` / `||`, evaluated when the left does not decide only.
    Right,
    /// A later `if` of a chain with no `~`: the `else` of the link before
    /// it, a node in its branch that holds the rest of the chain, which
    /// follows. A walk of the nodes walks it as a branch and stops.
    Link,
}

/// The parts of `e` with their positions ([`Pos`]), in the order of the
/// text; of an `if`, of its chain ([`chain`]), read a link at a time, so a
/// walk that stops at a [`Pos::Link`] is not linear in the chain.
pub fn positions(ast: &Ast, e: ExprId) -> Positions<'_> {
    let mut ps = Positions {
        ast,
        near: [(e, Pos::Always); 3],
        at: 0,
        len: 0,
        arms: [].iter(),
        body: Pos::Always,
        always: Vec::new().into_iter(),
        link: None,
        head: e,
        branch: Pos::Always,
    };
    match &ast.expr(e).kind {
        ExprKind::If { tilde, .. } => {
            ps.branch = if tilde.is_some() { Pos::Always } else { Pos::Branch { head: e } };
            ps.link = Some(e);
        }
        ExprKind::Match { scrutinee, arms, tilde } => {
            ps.body = if tilde.is_some() { Pos::Always } else { Pos::Branch { head: e } };
            ps.push((*scrutinee, Pos::Cond));
            ps.arms = arms.iter();
        }
        ExprKind::Binary { op, lhs, rhs, .. } => {
            let (l, r) = match op {
                BinOp::And | BinOp::Or => (Pos::Cond, Pos::Right),
                _ => (Pos::Always, Pos::Always),
            };
            ps.push((*lhs, l));
            ps.push((*rhs, r));
        }
        ExprKind::Lit(_)
        | ExprKind::Path(_)
        | ExprKind::Hole
        | ExprKind::Error
        | ExprKind::Paren(_)
        | ExprKind::Tuple(_)
        | ExprKind::Array(_)
        | ExprKind::Repeat { .. }
        | ExprKind::Struct { .. }
        | ExprKind::Block(_)
        | ExprKind::Closure { .. }
        | ExprKind::Handle { .. }
        | ExprKind::Unsafe(_)
        | ExprKind::Par { .. }
        | ExprKind::Cast { .. }
        | ExprKind::At { .. }
        | ExprKind::Feedback(_)
        | ExprKind::Unary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Field { .. }
        | ExprKind::TypeArgs { .. }
        | ExprKind::TupleIndex { .. }
        | ExprKind::Index { .. }
        | ExprKind::Try(_)
        | ExprKind::Move(_)
        | ExprKind::Range(_) => ps.always = ast.sub_exprs(e).into_iter(),
    }
    ps
}

/// The iterator of [`positions`], which makes no list but of the parts of
/// the kinds with no conditional position ([`Ast::sub_exprs`]).
#[derive(Debug, Clone)]
pub struct Positions<'a> {
    ast: &'a Ast,
    /// The parts read next, of a link of a chain, of a binary operator, or
    /// the scrutinee and then the guard and the body of an arm: those from
    /// `at` to `len`.
    near: [(ExprId, Pos); 3],
    at: usize,
    len: usize,
    /// Of a `match`, the arms not read yet and the position of a body; of a
    /// kind with no conditional position, its parts, all `Always`.
    arms: std::slice::Iter<'a, MatchArm>,
    body: Pos,
    always: std::vec::IntoIter<ExprId>,
    /// Of a chain whose `head` it is, the link to read next, and the
    /// position of its branches.
    link: Option<ExprId>,
    head: ExprId,
    branch: Pos,
}

impl Positions<'_> {
    /// The positions in a walk of the nodes: to a [`Pos::Link`], whose node
    /// holds the rest of the chain.
    pub fn of_node(self) -> impl Iterator<Item = (ExprId, Pos)> {
        let mut link = false;
        self.take_while(move |&(_, p)| !std::mem::replace(&mut link, p == Pos::Link))
    }

    fn push(&mut self, p: (ExprId, Pos)) {
        self.near[self.len] = p;
        self.len += 1;
    }
}

impl Iterator for Positions<'_> {
    type Item = (ExprId, Pos);

    fn next(&mut self) -> Option<(ExprId, Pos)> {
        if self.at < self.len {
            self.at += 1;
            return Some(self.near[self.at - 1]);
        }
        (self.at, self.len) = (0, 0);
        if let Some(a) = self.arms.next() {
            a.guard.into_iter().for_each(|g| self.push((g, Pos::Choose)));
            self.push((a.body, self.body));
            return self.next();
        }
        if let Some(x) = self.always.next() {
            return Some((x, Pos::Always));
        }
        let at = self.link.take()?;
        let ExprKind::If { cond, then, else_, .. } = &self.ast.expr(at).kind else { return None };
        self.push((*cond, if at == self.head { Pos::Cond } else { Pos::Choose }));
        self.push((*then, self.branch));
        match *else_ {
            Some(x) if matches!(self.ast.expr(x).kind, ExprKind::If { tilde: None, .. }) => {
                if self.branch != Pos::Always {
                    self.push((x, Pos::Link));
                }
                self.link = Some(x);
            }
            x => x.into_iter().for_each(|x| self.push((x, self.branch))),
        }
        self.next()
    }
}
