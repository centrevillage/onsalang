//! Generic traversal of Core bodies: every expression, depth first, in
//! evaluation order (used by reachability, the move bookkeeping and tools).

use crate::ir::{Block, Expr, ExprKind, Place, Stmt, StmtKind};

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
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::Const(_) | ExprKind::Zeroed | ExprKind::Panic(_) => {}
        ExprKind::Unary(_, x) | ExprKind::Cast(x) | ExprKind::SpanOf(x) | ExprKind::Tag(x) => walk_expr(x, f),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::Cmp { lhs, rhs, .. } | ExprKind::Logic { lhs, rhs, .. } => {
            walk_expr(lhs, f);
            walk_expr(rhs, f);
        }
        ExprKind::Call { args, .. } | ExprKind::Prim { args, .. } => {
            for a in args {
                walk_expr(&a.expr, f);
            }
        }
        ExprKind::Field { base, .. } | ExprKind::Payload { base, .. } => walk_expr(base, f),
        ExprKind::Index { base, index } => {
            walk_expr(base, f);
            walk_expr(index, f);
        }
        ExprKind::Struct { fields, .. } | ExprKind::Variant { fields, .. } => {
            for x in fields {
                walk_expr(x, f);
            }
        }
        ExprKind::Array(xs) | ExprKind::Tuple(xs) => {
            for x in xs {
                walk_expr(x, f);
            }
        }
        ExprKind::Repeat { elem, .. } => walk_expr(elem, f),
        ExprKind::IfExpr { cond, then, else_ } => {
            walk_expr(cond, f);
            walk_block(then, f);
            walk_block(else_, f);
        }
        ExprKind::Switch { scrutinee, arms, default } => {
            walk_expr(scrutinee, f);
            for (_, b) in arms {
                walk_block(b, f);
            }
            if let Some(b) = default {
                walk_block(b, f);
            }
        }
        ExprKind::Block(b) => walk_block(b, f),
    }
}
