//! The walk of the expressions (W4-07 memo 2.1): each gives its
//! sub-expressions their positions, and a place at a consuming position goes
//! to [`Walker::consume`]. A call gives its receiver and arguments the
//! positions of the parameters of its callee (`calls.rs`).

use onsa_syntax::ast::{ExprId, ExprKind, Lit, Mode, PatId, StrSeg};

use super::check::Walker;
use super::flow::Run;
use super::place::{Place, hole_place, pattern_places, place_of};
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
        // A use of a place is of its path, at the whole of it (S-803).
        if let Some(place) = self.path(r, e) {
            self.used(r, &place, ast.expr(e).span, None);
            return;
        }
        match &ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => {
                for (i, seg) in s.segments.iter().enumerate() {
                    let StrSeg::Interp(p) = seg else { continue };
                    if let Some(place) = hole_place(self.names, e, i as u32, p) {
                        self.used(r, &place, p.span, None);
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

    /// The place `e` is, the indexes in it walked first, the inner first
    /// (§3.5: an element is read after its index is evaluated, S-803).
    fn path(&mut self, r: &mut Run, e: ExprId) -> Option<Place> {
        let place = place_of(self.ast, self.names, e)?;
        let (mut indexes, mut x) = (Vec::new(), self.ast.without_parens(e));
        loop {
            x = match &self.ast.expr(x).kind {
                ExprKind::Field { base, .. } | ExprKind::TupleIndex { base, .. } => *base,
                ExprKind::Index { base, index } => {
                    indexes.push(*index);
                    *base
                }
                _ => break,
            };
            x = self.ast.without_parens(x);
        }
        indexes.into_iter().rev().for_each(|i| self.expr(r, i, Pos::Read));
        Some(place)
    }

    /// The value `e` of a head at `pos` with the patterns `pats` (of each
    /// arm of a `match`): a place of a binding of the index at a borrow row
    /// is used by the paths the patterns read (S-803's D1, D2, S-804: the
    /// elements bound, the ones compared, a variant's position whole, not
    /// `_`), at `e`, each noted at the first element that reads it.
    pub(super) fn head(&mut self, r: &mut Run, e: ExprId, pos: Pos, pats: &[PatId]) {
        let place = place_of(self.ast, self.names, e).filter(|p| pos != Pos::Consume && self.deps.indexed(p.root));
        let Some(place) = place else { return self.expr(r, e, pos) };
        let at = self.ast.expr(e).span;
        self.path(r, e);
        self.read_captured(place.root, at);
        let mut reads = Vec::new();
        for &p in pats {
            pattern_places(self.ast, self.info, p, &mut place.proj.clone(), &mut |_, proj, q| {
                reads.push((proj.to_vec(), q))
            });
        }
        for (proj, q) in reads {
            let by = self.ast.pat(q).span;
            if !self.used(r, &Place { root: place.root, proj }, at, Some(by)) {
                return;
            }
        }
    }

    /// The borrowed argument `e` of a parameter of the type `param`, if
    /// read: a literal of a second-class type passes its elements on as
    /// arguments (memo 2.1, §5.3: `planes([a, b])`, `swap.Out { l: a, r: b }`;
    /// the type of an array literal is that of its elements). An `inout` one
    /// is a write (`write.rs`; `inout [a, b]` is W4-08's).
    pub(super) fn argument(&mut self, r: &mut Run, e: ExprId, param: Option<TyId>) {
        let x = self.ast.without_parens(e);
        let literal =
            matches!(self.ast.expr(x).kind, ExprKind::Array(_) | ExprKind::Tuple(_) | ExprKind::Struct { .. });
        let at =
            if literal && param.and_then(|t| self.class_of(t)).is_some() { self.ast.sub_exprs(x) } else { vec![e] };
        at.into_iter().for_each(|y| self.expr(r, y, Pos::Arg(Mode::Borrow)));
    }
}
