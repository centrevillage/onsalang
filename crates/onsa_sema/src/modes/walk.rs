//! The walk of the expressions (W4-07 memo 2.1): each gives its
//! sub-expressions their positions, and a place at a consuming position goes
//! to [`Walker::consume`]. A call gives its receiver and arguments the
//! positions of the parameters of its callee (`calls.rs`).

use onsa_syntax::ast::{ExprId, ExprKind, Lit, Mode, StrSeg};

use super::check::Walker;
use super::flow::Run;
use super::place::place_of;
use crate::body::LocalId;
use crate::names::body::PathRes;
use crate::ty::TyId;

/// Where a value stands (§5.2, §5.3): what the walk checks at it. Passed down
/// to the tails of a block, an `if` and a `match` (§5.2) and through
/// parentheses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Pos {
    /// An operand, a condition, a guard, an index, a statement's value.
    Read,
    /// A borrowed or `inout` argument, a receiver, an index base, a borrowed head.
    Arg(Mode),
    /// The argument of a `move` parameter (S-609).
    MoveArg,
    /// The value of a `let`, `for` or `match` head whose row is a borrow (§5.4).
    Bind,
    /// An owned head, `var`, an assignment's value, an element of a literal.
    Consume,
    /// `return e` and the tail of a function or anonymous function.
    Return,
    /// A consuming position with no mark written: the operand of `?`, a
    /// `move self` receiver (S-786, §5.2, §9.1).
    Extract,
    /// An argument of a call on a value of the error type (§18.1): no check.
    Unknown,
}

impl Pos {
    /// A value at it is consumed (§5.2): moved, copied or an error.
    pub(super) fn consumes(self) -> bool {
        matches!(self, Pos::Consume | Pos::MoveArg | Pos::Return | Pos::Extract)
    }
}

impl Walker<'_> {
    /// Walk `e` at `pos` (in source order).
    pub(super) fn expr(&mut self, r: &mut Run, e: ExprId, pos: Pos) {
        #[cfg(test)]
        {
            self.m.visits += 1;
        }
        let ast = self.ast;
        // A place goes whole to `consume` (a candidate outside parentheses).
        if pos.consumes() && place_of(ast, self.names, e).is_some() {
            return self.consume(r, e, pos, None);
        }
        if self.control(r, e, pos) || self.out_of_place(r, e, pos) {
            return;
        }
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
            ExprKind::Tuple(xs) | ExprKind::Array(xs) => xs.iter().for_each(|&x| self.expr(r, x, Pos::Consume)),
            ExprKind::Struct { fields, .. } => fields.iter().for_each(|&(_, x)| self.expr(r, x, Pos::Consume)),
            ExprKind::Try(x) => self.expr(r, *x, Pos::Extract),
            ExprKind::Repeat { elem, len } => {
                self.expr(r, *elem, Pos::Consume);
                self.expr(r, *len, Pos::Read);
            }
            ExprKind::Index { base, index } => {
                self.expr(r, *base, Pos::Arg(Mode::Borrow));
                self.expr(r, *index, Pos::Read);
            }
            ExprKind::Call { callee, args, kind } => self.call(r, e, *callee, args, *kind),
            _ => ast.sub_exprs(e).into_iter().for_each(|x| self.expr(r, x, Pos::Read)),
        }
    }

    /// The argument `e` of the mode `m` (not `move`) of a parameter of the
    /// type `param`, if read: a literal of a second-class type at a borrowed
    /// one passes its elements on as arguments (memo 2.1, §5.3:
    /// `planes([a, b])`, `swap.Out { l: a, r: b }`; the type of an array
    /// literal is that of its elements). `inout [a, b]` is W4-08's.
    pub(super) fn argument(&mut self, r: &mut Run, e: ExprId, m: Mode, param: Option<TyId>) {
        let x = self.ast.without_parens(e);
        let literal =
            matches!(self.ast.expr(x).kind, ExprKind::Array(_) | ExprKind::Tuple(_) | ExprKind::Struct { .. });
        if m == Mode::Borrow && literal && param.and_then(|t| self.class_of(t)).is_some() {
            return self.ast.sub_exprs(x).into_iter().for_each(|y| self.expr(r, y, Pos::Arg(m)));
        }
        self.expr(r, e, Pos::Arg(m))
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
