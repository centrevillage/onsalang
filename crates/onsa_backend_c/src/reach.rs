//! Reachability: the functions, constants and types the exports need.

use std::collections::BTreeSet;

use onsa_core::{Block, ConstId, Expr, ExprKind, FnDef, FnId, Module, Place, Stmt, StmtKind};

#[derive(Debug, Default)]
pub struct Reach {
    pub fns: BTreeSet<FnId>,
    pub consts: BTreeSet<ConstId>,
}

pub fn reach(m: &Module, roots: &[FnId]) -> Reach {
    let mut r = Reach::default();
    let mut stack: Vec<FnId> = roots.to_vec();
    while let Some(f) = stack.pop() {
        if !r.fns.insert(f) {
            continue;
        }
        let def = m.fn_(f);
        if let Some(b) = &def.body {
            walk_block(b, &mut |e| match &e.kind {
                ExprKind::Call { fn_, .. } => stack.push(*fn_),
                ExprKind::Const(c) => {
                    if r.consts.insert(*c) {
                        walk_expr(&m.const_(*c).init, &mut |e2| {
                            if let ExprKind::Const(c2) = &e2.kind {
                                r.consts.insert(*c2);
                            }
                        });
                    }
                }
                _ => {}
            });
        }
    }
    r
}

/// Every expression of a block, depth first, in evaluation order.
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

/// Whether a function body contains a `Return` statement anywhere.
pub fn has_return(def: &FnDef) -> bool {
    fn block(b: &Block) -> bool {
        b.stmts.iter().any(stmt) || b.value.as_ref().is_some_and(|v| expr(v))
    }
    fn stmt(s: &Stmt) -> bool {
        match &s.kind {
            StmtKind::Return(_) => true,
            StmtKind::Let(_, e) | StmtKind::Expr(e) => expr(e),
            StmtKind::Assign(_, e) => expr(e),
            StmtKind::If(c, a, b) => expr(c) || block(a) || block(b),
            StmtKind::While(c, b) => expr(c) || block(b),
            StmtKind::ForRange(_, lo, hi, b) => expr(lo) || expr(hi) || block(b),
            StmtKind::Break | StmtKind::Continue => false,
        }
    }
    fn expr(e: &Expr) -> bool {
        let mut found = false;
        walk_expr(e, &mut |x| {
            if let ExprKind::IfExpr { then, else_, .. } = &x.kind {
                found |= then.stmts.iter().any(stmt) || else_.stmts.iter().any(stmt);
            }
            if let ExprKind::Switch { arms, default, .. } = &x.kind {
                found |= arms.iter().any(|(_, b)| b.stmts.iter().any(stmt))
                    || default.as_ref().is_some_and(|b| b.stmts.iter().any(stmt));
            }
            if let ExprKind::Block(b) = &x.kind {
                found |= b.stmts.iter().any(stmt);
            }
        });
        found
    }
    def.body.as_ref().is_some_and(block)
}
