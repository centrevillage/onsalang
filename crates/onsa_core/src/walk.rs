//! Generic traversal of Core bodies: every expression, depth first, in
//! evaluation order (used by reachability, the move bookkeeping and tools).

use crate::ir::{Block, Expr, ExprKind, FnDef, Place, Stmt, StmtKind};

pub fn walk_block(b: &Block, f: &mut dyn FnMut(&Expr)) {
    for s in &b.stmts {
        walk_stmt(s, f);
    }
    if let Some(v) = &b.value {
        walk_expr(v, f);
    }
}

pub fn walk_stmt(s: &Stmt, f: &mut dyn FnMut(&Expr)) {
    match &s.kind {
        StmtKind::Let(_, e) | StmtKind::Expr(e) => walk_expr(e, f),
        StmtKind::Assign(p, e) => {
            walk_place(p, f);
            walk_expr(e, f);
        }
        StmtKind::If(c, a, b) => {
            walk_expr(c, f);
            walk_block(a, f);
            walk_block(b, f);
        }
        StmtKind::While(c, b) => {
            walk_expr(c, f);
            walk_block(b, f);
        }
        StmtKind::ForRange(_, lo, hi, b) => {
            walk_expr(lo, f);
            walk_expr(hi, f);
            walk_block(b, f);
        }
        StmtKind::Break | StmtKind::Continue => {}
        StmtKind::Return(e) => {
            if let Some(e) = e {
                walk_expr(e, f);
            }
        }
    }
}

pub fn walk_place(p: &Place, f: &mut dyn FnMut(&Expr)) {
    match p {
        Place::Local(_) => {}
        Place::Field(b, _) => walk_place(b, f),
        Place::Index(b, i, _) => {
            walk_place(b, f);
            walk_expr(i, f);
        }
    }
}

pub fn walk_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    for_each_child(e, &mut |c| match c {
        Child::Expr(x) => walk_expr(x, f),
        Child::Block(b) => walk_block(b, f),
    });
}

/// A direct part of an expression ([`for_each_child`]).
pub enum Child<'e> {
    Expr(&'e Expr),
    Block(&'e Block),
}

/// The direct parts of `e`, one level, in evaluation order: the one list of
/// the children of each kind of expression (D-15), which [`walk_expr`] and
/// the move bookkeeping (without the blocks) read.
pub fn for_each_child<'e>(e: &'e Expr, f: &mut dyn FnMut(Child<'e>)) {
    let mut exprs = |xs: &mut dyn Iterator<Item = &'e Expr>| xs.for_each(|x| f(Child::Expr(x)));
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::Const(_) | ExprKind::Zeroed | ExprKind::Panic { .. } => {}
        ExprKind::Unary(_, x) | ExprKind::Cast(x) | ExprKind::SpanOf(x) | ExprKind::Tag(x) => f(Child::Expr(x)),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::Cmp { lhs, rhs, .. } | ExprKind::Logic { lhs, rhs, .. } => {
            exprs(&mut [&**lhs, &**rhs].into_iter())
        }
        ExprKind::Call { args, .. } | ExprKind::Prim { args, .. } => exprs(&mut args.iter().map(|a| &a.expr)),
        ExprKind::Field { base, .. } | ExprKind::Payload { base, .. } => f(Child::Expr(base)),
        ExprKind::Index { base, index } => exprs(&mut [&**base, &**index].into_iter()),
        ExprKind::Struct { fields: xs, .. } | ExprKind::Variant { fields: xs, .. } => exprs(&mut xs.iter()),
        ExprKind::Array(xs) | ExprKind::Tuple(xs) => exprs(&mut xs.iter()),
        ExprKind::Repeat { elem, .. } => f(Child::Expr(elem)),
        ExprKind::IfExpr { cond, then, else_ } => {
            f(Child::Expr(cond));
            f(Child::Block(then));
            f(Child::Block(else_));
        }
        ExprKind::Switch { scrutinee, arms, default } => {
            f(Child::Expr(scrutinee));
            arms.iter().map(|(_, b)| b).chain(default).for_each(|b| f(Child::Block(b)));
        }
        ExprKind::Block(b) => f(Child::Block(b)),
    }
}

/// Whether a function body contains a `Return` statement anywhere: each
/// node once (R-439), the index of an assigned place too.
pub fn has_return(def: &FnDef) -> bool {
    fn block(b: &Block) -> bool {
        b.stmts.iter().any(stmt) || b.value.as_ref().is_some_and(|v| expr(v))
    }
    fn stmt(s: &Stmt) -> bool {
        match &s.kind {
            StmtKind::Return(_) => true,
            StmtKind::Let(_, e) | StmtKind::Expr(e) => expr(e),
            StmtKind::Assign(p, e) => place(p) || expr(e),
            StmtKind::If(c, a, b) => expr(c) || block(a) || block(b),
            StmtKind::While(c, b) => expr(c) || block(b),
            StmtKind::ForRange(_, lo, hi, b) => expr(lo) || expr(hi) || block(b),
            StmtKind::Break | StmtKind::Continue => false,
        }
    }
    fn place(p: &Place) -> bool {
        match p {
            Place::Local(_) => false,
            Place::Field(b, _) => place(b),
            Place::Index(b, i, _) => place(b) || expr(i),
        }
    }
    fn expr(e: &Expr) -> bool {
        let mut found = false;
        for_each_child(e, &mut |c| {
            found = found
                || match c {
                    Child::Expr(x) => expr(x),
                    Child::Block(b) => block(b),
                }
        });
        found
    }
    def.body.as_ref().is_some_and(block)
}
