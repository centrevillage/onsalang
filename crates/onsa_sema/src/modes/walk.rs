//! The walk of the expressions (W4-07 memo 2.1, 2.2): each gives its
//! sub-expressions their positions. U1 has the reads of the locals and the
//! move of a whole local marked `move`; U2 decides every position.

use onsa_syntax::ast::{ExprId, ExprKind, Lit, Mode, StrSeg};

use super::check::Walker;
use super::flow::Run;
use crate::Kind;
use crate::body::LocalId;
use crate::names::body::PathRes;

/// Where a value stands (§5.2, §5.3): what the walk checks at it. Passed down
/// to the tails of a block, an `if` and a `match` (§5.2) and through
/// parentheses.
#[allow(dead_code)] // U2 reads every position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Pos {
    /// An operand, a condition, a guard, an index, a statement's value.
    Read,
    /// A borrowed or `inout` argument, a receiver, an index base, a borrowed head.
    Arg(Mode),
    /// The argument of a `move` parameter, a `move self` receiver (S-609).
    MoveArg,
    /// The value of a `let`, `for` or `match` head whose row is a borrow (§5.4).
    Bind,
    /// An owned head, `var`, an assignment's value, an element of a literal.
    Consume,
    /// `return e` and the tail of a function or anonymous function.
    Return,
    /// An argument of a call on a value of the error type (§18.1): no check.
    Unknown,
}

impl Walker<'_> {
    /// Walk `e` at `pos` (in source order).
    pub(super) fn expr(&mut self, r: &mut Run, e: ExprId, pos: Pos) {
        #[cfg(test)]
        {
            self.m.visits += 1;
        }
        if self.control(r, e, pos) {
            return;
        }
        let ast = self.ast;
        match &ast.expr(e).kind {
            ExprKind::Path(_) => {
                if let Some(PathRes::Local(b)) = self.names.paths.get(&e) {
                    self.used(r, LocalId(b.0), ast.expr(e).span);
                }
            }
            ExprKind::Lit(Lit::Str(s)) => {
                for (i, seg) in s.segments.iter().enumerate() {
                    let hole = self.names.interp.get(&(e, i as u32)).and_then(|v| v.last());
                    if let (StrSeg::Interp(p), Some((_, PathRes::Local(b)))) = (seg, hole) {
                        self.used(r, LocalId(b.0), p.span);
                    }
                }
            }
            ExprKind::Paren(x) | ExprKind::TypeArgs { base: x, .. } => self.expr(r, *x, pos),
            ExprKind::Move(x) if matches!(pos, Pos::Consume | Pos::Return) => self.consume(r, *x, true),
            ExprKind::Tuple(xs) | ExprKind::Array(xs) => xs.iter().for_each(|&x| self.expr(r, x, Pos::Consume)),
            ExprKind::Struct { fields, .. } => fields.iter().for_each(|&(_, x)| self.expr(r, x, Pos::Consume)),
            ExprKind::Repeat { elem, len } => {
                self.expr(r, *elem, Pos::Consume);
                self.expr(r, *len, Pos::Read);
            }
            ExprKind::Call { callee, args, .. } => {
                self.expr(r, *callee, Pos::Read);
                self.lazily(r, e, |w, r| {
                    for arg in args {
                        match arg.mode {
                            Mode::Move => w.consume(r, arg.expr, true),
                            m => w.expr(r, arg.expr, Pos::Arg(m)),
                        }
                    }
                });
            }
            _ => ast.sub_exprs(e).into_iter().for_each(|x| self.expr(r, x, Pos::Read)),
        }
    }

    /// The value `e` at a consuming position, marked `move` or not. U1: a
    /// whole owned Affine local marked `move` is moved (§5.2); U2 decides
    /// the rest (E0711, E0703, E0710, the paths, R-117).
    pub(super) fn consume(&mut self, r: &mut Run, e: ExprId, marked: bool) {
        let x = self.ast.without_parens(e);
        let Some(l) = self.whole_local(x).filter(|_| marked) else { return self.expr(r, x, Pos::Read) };
        let at = self.ast.expr(x).span;
        if self.used(r, l, at) && self.owns(l) && self.kind(l) == Some(Kind::Affine) {
            self.move_local(r, l, at);
        }
    }

    /// The local `e` names as a whole (through parentheses).
    pub(super) fn whole_local(&self, e: ExprId) -> Option<LocalId> {
        let x = self.ast.without_parens(e);
        match (&self.ast.expr(x).kind, self.names.paths.get(&x)) {
            (ExprKind::Path(_), Some(PathRes::Local(b))) => Some(LocalId(b.0)),
            _ => None,
        }
    }
}
