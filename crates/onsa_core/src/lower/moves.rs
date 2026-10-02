//! Copies of aggregate values (spec §12.7, T4-9): the places where a struct,
//! array, tuple or enum value is moved by copying bytes rather than built in
//! place. `onsa audit --memory` (M9) lists the ones above a threshold.
//!
//! What counts (§12.7):
//! - `let y = x` / `p = x` where `x` is an existing place (`Copy`);
//! - `if` / `switch` arms that yield existing places — two locals of which one
//!   is returned cannot both be built in the result slot (`Branch`);
//! - a payload taken out of an enum (`Option` / `Result`, `?`, `match`)
//!   (`Payload`);
//! - an aggregate passed as a `move` argument: the callee owns a copy
//!   (`MoveArg`).
//!
//! What does not count: calls, literals, `Zeroed`, `Repeat`, blocks whose
//! value is a local declared inside them (they are built in the destination,
//! §12.7 "集成体を返す式はその置き場所に直接構築される"), and the tail local of an
//! `sret` function (NRVO).

use crate::ir::{Block, Expr, ExprKind, FnDef, LocalId, Mode, Module, MoveKind, MoveSite, Stmt, StmtKind};
use crate::layout::size_align;

pub fn collect(m: &Module) -> Vec<MoveSite> {
    let mut out = Vec::new();
    for f in &m.fns {
        let Some(body) = &f.body else { continue };
        let mut cx = Cx { m, f, out: &mut out };
        cx.block(body, true);
    }
    out
}

struct Cx<'a> {
    m: &'a Module,
    f: &'a FnDef,
    out: &'a mut Vec<MoveSite>,
}

impl Cx<'_> {
    fn record(&mut self, e: &Expr, kind: MoveKind) {
        if !e.ty.is_aggregate() {
            return;
        }
        let bytes = size_align(self.m, &e.ty).0;
        self.out.push(MoveSite { fn_name: self.f.name.clone(), span: e.span, ty: e.ty.clone(), bytes, kind });
    }

    /// An expression whose value is stored somewhere (`let`, assignment,
    /// a literal element, a return value). `nrvo` marks the sret tail.
    fn stored(&mut self, e: &Expr, nrvo: Option<LocalId>) {
        match &e.kind {
            ExprKind::Local(l) if nrvo == Some(*l) => {}
            ExprKind::Local(_) | ExprKind::Field { .. } | ExprKind::Index { .. } => self.record(e, MoveKind::Copy),
            ExprKind::Payload { .. } => self.record(e, MoveKind::Payload),
            ExprKind::IfExpr { then, else_, .. } => {
                let branches = [then, else_];
                if branches.iter().any(|b| yields_place(b)) {
                    self.record(e, MoveKind::Branch);
                }
                for b in branches {
                    self.branch_block(b);
                }
            }
            ExprKind::Switch { arms, default, .. } => {
                let blocks: Vec<&Block> = arms.iter().map(|(_, b)| b).chain(default.iter()).collect();
                if blocks.iter().any(|b| yields_place(b)) {
                    self.record(e, MoveKind::Branch);
                }
                for b in blocks {
                    self.branch_block(b);
                }
            }
            ExprKind::Block(b) => self.block_value(b),
            _ => {}
        }
        // Nested stores inside the expression (literal elements, arguments).
        if !matches!(&e.kind, ExprKind::IfExpr { .. } | ExprKind::Switch { .. } | ExprKind::Block(_)) {
            self.inner(e);
        }
    }

    /// One arm of a branch: a place as its value was counted once on the
    /// branch itself; anything else is a store of its own.
    fn branch_block(&mut self, b: &Block) {
        for s in &b.stmts {
            self.stmt(s);
        }
        if let Some(v) = &b.value {
            match &v.kind {
                ExprKind::Local(_) | ExprKind::Field { .. } | ExprKind::Index { .. } | ExprKind::Payload { .. } => {
                    self.inner(v)
                }
                _ => self.stored(v, None),
            }
        }
    }

    /// A block in value position: its value is stored by the enclosing store.
    fn block_value(&mut self, b: &Block) {
        for s in &b.stmts {
            self.stmt(s);
        }
        if let Some(v) = &b.value {
            match &v.kind {
                // A local declared in this block is built in the destination.
                ExprKind::Local(l) if declares(b, *l) => self.inner(v),
                _ => self.stored(v, None),
            }
        }
    }

    /// Stores that happen inside an expression: literal elements and
    /// `move` arguments. Statements inside nested blocks are visited too.
    fn inner(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Struct { fields, .. } | ExprKind::Variant { fields, .. } => {
                for x in fields {
                    self.stored(x, None);
                }
            }
            ExprKind::Array(xs) | ExprKind::Tuple(xs) => {
                for x in xs {
                    self.stored(x, None);
                }
            }
            ExprKind::Repeat { elem, .. } => self.stored(elem, None),
            ExprKind::Call { args, .. } | ExprKind::Prim { args, .. } => {
                for a in args {
                    if a.mode == Mode::Move && a.expr.ty.is_aggregate() {
                        match &a.expr.kind {
                            ExprKind::Local(_) | ExprKind::Field { .. } | ExprKind::Index { .. } => {
                                self.record(&a.expr, MoveKind::MoveArg)
                            }
                            _ => {}
                        }
                    }
                    self.inner(&a.expr);
                }
            }
            // A branch or block in argument / operand position materializes a
            // temporary: treated as a store.
            ExprKind::IfExpr { .. } | ExprKind::Switch { .. } | ExprKind::Block(_) => self.stored(e, None),
            _ => {
                // Other expressions: look for nested blocks' statements and stores.
                let mut subs: Vec<&Expr> = Vec::new();
                collect_children(e, &mut subs);
                for x in subs {
                    self.inner(x);
                }
            }
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let(_, e) | StmtKind::Assign(_, e) => self.stored(e, None),
            StmtKind::Expr(e) => self.inner(e),
            StmtKind::If(c, a, b) => {
                self.inner(c);
                self.block(a, false);
                self.block(b, false);
            }
            StmtKind::While(c, b) => {
                self.inner(c);
                self.block(b, false);
            }
            StmtKind::ForRange(_, lo, hi, b) => {
                self.inner(lo);
                self.inner(hi);
                self.block(b, false);
            }
            StmtKind::Break | StmtKind::Continue => {}
            StmtKind::Return(Some(e)) => self.stored(e, None),
            StmtKind::Return(None) => {}
        }
    }

    fn block(&mut self, b: &Block, top: bool) {
        for s in &b.stmts {
            self.stmt(s);
        }
        if let Some(v) = &b.value {
            let nrvo = if top && self.f.sret {
                match &v.kind {
                    ExprKind::Local(l) if declares(b, *l) => Some(*l),
                    _ => None,
                }
            } else {
                None
            };
            if top {
                self.stored(v, nrvo);
            } else {
                self.block_value(b);
            }
        }
    }
}

fn declares(b: &Block, l: LocalId) -> bool {
    b.stmts.iter().any(|s| matches!(&s.kind, StmtKind::Let(x, _) if *x == l))
}

/// The block's value is an existing place (not something built in place).
fn yields_place(b: &Block) -> bool {
    match &b.value {
        Some(v) => match &v.kind {
            ExprKind::Local(l) => !declares(b, *l),
            ExprKind::Field { .. } | ExprKind::Index { .. } | ExprKind::Payload { .. } => true,
            _ => false,
        },
        None => false,
    }
}

/// Direct child expressions (one level).
fn collect_children<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::Const(_) | ExprKind::Zeroed | ExprKind::Panic(_) => {}
        ExprKind::Unary(_, x) | ExprKind::Cast(x) | ExprKind::SpanOf(x) | ExprKind::Tag(x) => out.push(x),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::Cmp { lhs, rhs, .. } | ExprKind::Logic { lhs, rhs, .. } => {
            out.push(lhs);
            out.push(rhs);
        }
        ExprKind::Call { args, .. } | ExprKind::Prim { args, .. } => out.extend(args.iter().map(|a| &a.expr)),
        ExprKind::Field { base, .. } | ExprKind::Payload { base, .. } => out.push(base),
        ExprKind::Index { base, index } => {
            out.push(base);
            out.push(index);
        }
        ExprKind::Struct { fields, .. } | ExprKind::Variant { fields, .. } => out.extend(fields.iter()),
        ExprKind::Array(xs) | ExprKind::Tuple(xs) => out.extend(xs.iter()),
        ExprKind::Repeat { elem, .. } => out.push(elem),
        ExprKind::IfExpr { cond, .. } => out.push(cond),
        ExprKind::Switch { scrutinee, .. } => out.push(scrutinee),
        ExprKind::Block(_) => {}
    }
}
