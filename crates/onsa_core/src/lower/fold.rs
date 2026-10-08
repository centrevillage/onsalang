//! The normalization after lowering (S-288): the comparisons whose result the
//! types or the identity of the operands decide become constants, a `for`
//! over a range that the types make empty is dropped, and an assignment of a
//! place to itself is dropped.
//!
//! The source is valid and its meaning is plain (§3.4): an integer, `Bool` or
//! `Char` compared with itself; a value compared with a constant outside or
//! at the edge of the values it can have (`x >= 0` of an unsigned `x`,
//! `x <= I8.MAX`, `(x as I32) < 256` of a `U8`); `for i in lo..0` over an
//! unsigned `i`; `y = y`. A C compiler warns about the same text
//! (`-Wtautological-compare`, `-Wtype-limits`, `-Wself-assign`), and §13.4
//! promises C without a warning for every source that checks. The fold is
//! done once here, so every backend reads the same Core (plan D-15); it does
//! not change a value, so the interpreter's results do not change.
//!
//! - The operands of a folded comparison, and the bounds of a dropped `for`,
//!   are still evaluated, in order, as expression statements (of a block
//!   whose value is the constant): their effects stay.
//! - Only operands that Core knows to be the same binding fold as a
//!   self-comparison: the same local, or the same fields of it. An element
//!   (`a[i]`) never does: its index has a check.
//! - The values a value can have are those of its type, or of the type a
//!   widening `as` converted it from (§3.3: the conversion keeps the value).
//!   A constant is a literal, a `const` whose value is one, or the length of
//!   an array (its type has it).
//! - A float never folds: a NaN changes the result of a comparison with
//!   itself, and the edges of a float type are not a C warning.
//! - An assignment of a place to itself becomes the place as an expression
//!   statement.

use crate::ir::*;
use crate::prim::Prim;

/// Fold every function body of `m`.
pub fn fold_module(m: &mut Module) {
    let consts = &m.consts;
    let f = Folder { consts };
    for def in &mut m.fns {
        if let Some(b) = &mut def.body {
            f.block(b);
        }
    }
}

struct Folder<'m> {
    consts: &'m [ConstDef],
}

impl Folder<'_> {
    fn block(&self, b: &mut Block) {
        let stmts = std::mem::take(&mut b.stmts);
        for mut s in stmts {
            self.stmt(&mut s);
            match s.kind {
                // It never runs: its bounds stay as statements.
                StmtKind::ForRange(_, from, to, _) if self.never_runs(&to) => b.stmts.extend(self.effects([from, to])),
                kind => b.stmts.push(Stmt { span: s.span, kind }),
            }
        }
        if let Some(v) = &mut b.value {
            self.expr(v);
        }
    }

    /// A `for` whose upper bound `hi` is at or below the smallest value of
    /// the loop variable's type never runs.
    fn never_runs(&self, hi: &Expr) -> bool {
        matches!((self.constant(hi), limits(&hi.ty)), (Some(k), Some((lo, _))) if k <= lo)
    }

    /// The expressions as statements, in order, but those without an effect
    /// or a read (a literal, a `const`).
    fn effects(&self, xs: impl IntoIterator<Item = Expr>) -> Vec<Stmt> {
        xs.into_iter()
            .filter(|x| !matches!(x.kind, ExprKind::Lit(_) | ExprKind::Const(_)))
            .map(|x| Stmt { span: x.span, kind: StmtKind::Expr(x) })
            .collect()
    }

    fn stmt(&self, s: &mut Stmt) {
        match &mut s.kind {
            StmtKind::Let(_, e) | StmtKind::Expr(e) => self.expr(e),
            StmtKind::Assign(p, e) => {
                self.place(p);
                self.expr(e);
                if e.as_place().is_some_and(|q| same_path(p, &q)) {
                    let e = std::mem::replace(e, Expr::new(Ty::Unit, s.span, ExprKind::Lit(Lit::Unit)));
                    s.kind = StmtKind::Expr(e);
                }
            }
            StmtKind::If(c, a, b) => {
                self.expr(c);
                self.block(a);
                self.block(b);
            }
            StmtKind::While(c, b) => {
                self.expr(c);
                self.block(b);
            }
            StmtKind::ForRange(_, lo, hi, b) => {
                self.expr(lo);
                self.expr(hi);
                self.block(b);
            }
            StmtKind::Return(Some(e)) => self.expr(e),
            StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue => {}
        }
    }

    fn place(&self, p: &mut Place) {
        match p {
            Place::Local(_) => {}
            Place::Field(b, _) => self.place(b),
            Place::Index(b, i, _) => {
                self.place(b);
                self.expr(i);
            }
        }
    }

    fn expr(&self, e: &mut Expr) {
        match &mut e.kind {
            ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::Const(_) | ExprKind::Zeroed | ExprKind::Panic(_) => {}
            ExprKind::Unary(_, x) | ExprKind::Cast(x) | ExprKind::SpanOf(x) | ExprKind::Tag(x) => self.expr(x),
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::Cmp { lhs, rhs, .. } | ExprKind::Logic { lhs, rhs, .. } => {
                self.expr(lhs);
                self.expr(rhs);
            }
            ExprKind::Call { args, .. } | ExprKind::Prim { args, .. } => {
                for a in args {
                    self.expr(&mut a.expr);
                }
            }
            ExprKind::Field { base, .. } | ExprKind::Payload { base, .. } => self.expr(base),
            ExprKind::Index { base, index } => {
                self.expr(base);
                self.expr(index);
            }
            ExprKind::Struct { fields: xs, .. }
            | ExprKind::Variant { fields: xs, .. }
            | ExprKind::Array(xs)
            | ExprKind::Tuple(xs) => {
                for x in xs {
                    self.expr(x);
                }
            }
            ExprKind::Repeat { elem, .. } => self.expr(elem),
            ExprKind::IfExpr { cond, then, else_ } => {
                self.expr(cond);
                self.block(then);
                self.block(else_);
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                self.expr(scrutinee);
                for (_, b) in arms {
                    self.block(b);
                }
                if let Some(b) = default {
                    self.block(b);
                }
            }
            ExprKind::Block(b) => self.block(b),
        }
        if let ExprKind::Cmp { op, lhs, rhs } = &e.kind
            && let Some(value) = self.decided(*op, lhs, rhs)
        {
            let ExprKind::Cmp { lhs, rhs, .. } = std::mem::replace(&mut e.kind, ExprKind::Lit(Lit::Unit)) else {
                unreachable!("matched above")
            };
            let operands = if same_binding(&lhs, &rhs) { vec![*lhs] } else { vec![*lhs, *rhs] };
            let stmts = self.effects(operands);
            let lit = Expr::new(Ty::Bool, e.span, ExprKind::Lit(Lit::Bool(value)));
            e.kind =
                if stmts.is_empty() { lit.kind } else { ExprKind::Block(Block { stmts, value: Some(Box::new(lit)) }) };
        }
    }

    /// The result of `lhs op rhs` when the types or the identity of the
    /// operands decide it; `None` otherwise.
    fn decided(&self, op: CmpOp, lhs: &Expr, rhs: &Expr) -> Option<bool> {
        limits(&lhs.ty)?;
        if same_binding(lhs, rhs) {
            return Some(matches!(op, CmpOp::Eq | CmpOp::Le | CmpOp::Ge));
        }
        // Written as `x op k`, the constant on the right.
        let (op, x, k) = match (self.constant(lhs), self.constant(rhs)) {
            (None, Some(k)) => (op, lhs, k),
            (Some(k), None) => (mirror(op), rhs, k),
            _ => return None,
        };
        let (lo, hi) = values(x)?;
        match op {
            CmpOp::Lt if hi < k => Some(true),
            CmpOp::Lt if lo >= k => Some(false),
            CmpOp::Le if hi <= k => Some(true),
            CmpOp::Le if lo > k => Some(false),
            CmpOp::Gt if lo > k => Some(true),
            CmpOp::Gt if hi <= k => Some(false),
            CmpOp::Ge if lo >= k => Some(true),
            CmpOp::Ge if hi < k => Some(false),
            CmpOp::Eq if k < lo || k > hi => Some(false),
            CmpOp::Ne if k < lo || k > hi => Some(true),
            _ => None,
        }
    }

    /// The value of a constant of an exact type: a literal, a `const` whose
    /// value is one, a widening `as` of one, or the length of an array place.
    fn constant(&self, e: &Expr) -> Option<i128> {
        self.constant_at(e, 0)
    }

    fn constant_at(&self, e: &Expr, depth: usize) -> Option<i128> {
        // A `const` refers to another at most this deep here (the checks of
        // the cycles are the analysis'; this only bounds the walk).
        if depth > 64 {
            return None;
        }
        match &e.kind {
            ExprKind::Lit(Lit::Int(v)) => Some(*v),
            ExprKind::Lit(Lit::Bool(b)) => Some(i128::from(*b)),
            ExprKind::Lit(Lit::Char(c)) => Some(i128::from(u32::from(*c))),
            ExprKind::Const(c) => self.constant_at(&self.consts.get(c.0 as usize)?.init, depth + 1),
            ExprKind::Cast(x) if limits(&x.ty).is_some() => self.constant_at(x, depth + 1),
            ExprKind::Prim { prim: Prim::Len, args } => match (&args.first()?.expr.ty, args[0].expr.as_place()) {
                (Ty::Array(_, n), Some(p)) if without_element(&p) => Some(i128::from(*n)),
                _ => None,
            },
            _ => None,
        }
    }
}

/// `k op x` as `x op' k`.
fn mirror(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Lt => CmpOp::Gt,
        CmpOp::Gt => CmpOp::Lt,
        CmpOp::Le => CmpOp::Ge,
        CmpOp::Ge => CmpOp::Le,
        CmpOp::Eq => CmpOp::Eq,
        CmpOp::Ne => CmpOp::Ne,
    }
}

/// The values an exact type has (§3.1, §4.1); `None` for a float and the
/// other types. A `Char` is a scalar value of Unicode, at most U+10FFFF.
fn limits(ty: &Ty) -> Option<(i128, i128)> {
    match ty {
        Ty::Int(k) => Some(k.range()),
        Ty::Bool => Some((0, 1)),
        Ty::Char => Some((0, 0x10FFFF)),
        _ => None,
    }
}

/// The values `x` can have: those of the type it was widened from by `as`
/// (§3.3), or of its own type.
fn values(x: &Expr) -> Option<(i128, i128)> {
    match &x.kind {
        ExprKind::Cast(inner) if limits(&inner.ty).is_some() => values(inner),
        _ => limits(&x.ty),
    }
}

/// The two operands are the same binding: the same local, or the same fields
/// of it (never an element: its index is checked).
fn same_binding(a: &Expr, b: &Expr) -> bool {
    match (a.as_place(), b.as_place()) {
        (Some(p), Some(q)) => same_path(&p, &q),
        _ => false,
    }
}

/// A local or fields of it: a place that reads no element (no index check).
fn without_element(p: &Place) -> bool {
    match p {
        Place::Local(_) => true,
        Place::Field(b, _) => without_element(b),
        Place::Index(..) => false,
    }
}

/// The same local, or the same fields of it; never a place with an element.
fn same_path(p: &Place, q: &Place) -> bool {
    match (p, q) {
        (Place::Local(a), Place::Local(b)) => a == b,
        (Place::Field(a, i), Place::Field(b, j)) => i == j && same_path(a, b),
        _ => false,
    }
}

#[cfg(test)]
mod tests;
