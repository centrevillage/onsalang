//! The height of the storage of a local (§5.2, R-481, R-484, S-1118 (2)).
//!
//! The scopes are the blocks a backend opens: an arm of an `IfExpr` or a
//! `Switch`, the block of an `If`, a `While` or a `ForRange`. A block
//! expression does not end the life of the locals it declares (a Core
//! promise: `span_of` places `{ let __arr = …; span(__arr) }` at an
//! argument). The C backend opens two more, the right operand of `&&`/`||`
//! and the condition of a `while`; their value is a `Bool` and holds no view.

use std::collections::BTreeSet;

use crate::ir::*;
use crate::walk::{Child, for_each_child};

/// The locals of `f` a view out of a scope reads, stored at the function's
/// level, ascending: a value leaves a scope as the value of an arm, or
/// assigned to a place whose root the scope does not declare (a root with no
/// `let`, a parameter or `__result`, is at the function's level). Of the
/// locals the value views ([`Storage::roots`]), the ones the scope declares,
/// at any depth. Linear in the body, times the depth of the scopes.
pub(crate) fn hoisted(m: &Module, f: &FnDef) -> Vec<LocalId> {
    let Some(body) = &f.body else { return Vec::new() };
    let n = f.locals.len();
    let mut s = Storage {
        m,
        f,
        defs: vec![Vec::new(); n],
        memo: vec![None; n],
        depth: 0,
        declared: vec![0; n],
        exits: Vec::new(),
    };
    s.block(body, false);
    let mut out = BTreeSet::new();
    for (v, inside) in std::mem::take(&mut s.exits) {
        let mut roots = BTreeSet::new();
        s.roots(v, &mut roots);
        out.extend(roots.into_iter().filter(|r| s.declared[r.0 as usize] >= inside));
    }
    out.into_iter().collect()
}

struct Storage<'a> {
    m: &'a Module,
    f: &'a FnDef,
    /// The values each local is given (its `let`, an assignment to it or a part of it).
    defs: Vec<Vec<&'a Expr>>,
    memo: Vec<Option<BTreeSet<LocalId>>>,
    depth: u32,
    /// The depth of the scope of each local's `let` (0: the function's level).
    declared: Vec<u32>,
    /// A value leaving a scope, and the least depth of a local inside it.
    exits: Vec<(&'a Expr, u32)>,
}

// The walk keeps its own list of the parts of a statement: `walk.rs` has no
// list of them that marks where a block of a scope opens and closes.
impl<'a> Storage<'a> {
    fn block(&mut self, b: &'a Block, scope: bool) {
        self.depth += u32::from(scope);
        b.stmts.iter().for_each(|s| self.stmt(s));
        if let Some(v) = &b.value {
            self.expr(v);
            if scope {
                self.exits.push((v, self.depth));
            }
        }
        self.depth -= u32::from(scope);
    }

    fn stmt(&mut self, s: &'a Stmt) {
        match &s.kind {
            StmtKind::Let(l, e) => {
                self.expr(e);
                self.declared[l.0 as usize] = self.depth;
                self.defs[l.0 as usize].push(e);
            }
            StmtKind::Assign(p, e) => {
                self.place(p);
                self.expr(e);
                let root = p.root().0 as usize;
                self.defs[root].push(e);
                self.exits.push((e, self.declared[root] + 1));
            }
            StmtKind::Expr(e) | StmtKind::Return(Some(e)) => self.expr(e),
            StmtKind::If(c, a, b) => {
                self.expr(c);
                self.block(a, true);
                self.block(b, true);
            }
            StmtKind::While(c, b) => {
                self.expr(c);
                self.block(b, true);
            }
            StmtKind::ForRange(_, lo, hi, b) => {
                self.expr(lo);
                self.expr(hi);
                self.block(b, true);
            }
            StmtKind::Break | StmtKind::Continue | StmtKind::Return(None) => {}
        }
    }

    fn place(&mut self, p: &'a Place) {
        match p {
            Place::Local(_) => {}
            Place::Field(b, _) => self.place(b),
            Place::Index(b, i, ..) => {
                self.place(b);
                self.expr(i);
            }
        }
    }

    fn expr(&mut self, e: &'a Expr) {
        let arms = matches!(e.kind, ExprKind::IfExpr { .. } | ExprKind::Switch { .. });
        for_each_child(e, &mut |c| match c {
            Child::Expr(x) => self.expr(x),
            Child::Block(b) => self.block(b, arms),
        });
    }

    /// The locals whose storage the value of `e` may view: none when its type
    /// holds no view; of `span(p)`, the root `r` of `p` and the roots of `r`
    /// (`s[0]` of a `Span` local `s` views what `s` views); of a local, the
    /// roots of the values it is given; of an `if`, a `match` or a block, the
    /// roots of their values; of anything else, of its parts.
    fn roots(&mut self, e: &'a Expr, out: &mut BTreeSet<LocalId>) {
        if !self.views(e.ty) {
            return;
        }
        match &e.kind {
            ExprKind::SpanOf(p) => {
                if let Some(r) = p.as_place().map(|p| p.root()) {
                    out.insert(r);
                    self.local(r, out);
                }
            }
            ExprKind::Local(l) => self.local(*l, out),
            _ => {
                let values_only = matches!(e.kind, ExprKind::IfExpr { .. } | ExprKind::Switch { .. });
                for_each_child(e, &mut |c| match c {
                    Child::Expr(x) if !values_only => self.roots(x, out),
                    Child::Expr(_) => {}
                    Child::Block(b) => b.value.iter().for_each(|v| self.roots(v, out)),
                });
            }
        }
    }

    /// The roots of the values of local `l`, once; none while they are being
    /// found. A local that holds a view is given one value, by its `let`
    /// (§5.3): the chain has no cycle, and no partial result is kept.
    fn local(&mut self, l: LocalId, out: &mut BTreeSet<LocalId>) {
        let (i, f) = (l.0 as usize, self.f);
        if !self.views(f.locals[i].ty) {
            return;
        }
        if let Some(set) = &self.memo[i] {
            return out.extend(set.iter().copied());
        }
        self.memo[i] = Some(BTreeSet::new());
        let mut set = BTreeSet::new();
        for v in self.defs[i].clone() {
            self.roots(v, &mut set);
        }
        out.extend(set.iter().copied());
        self.memo[i] = Some(set);
    }

    /// Whether a value of `t` holds a view ([`crate::layout::TyFacts::views`]).
    fn views(&self, t: CTy) -> bool {
        self.m.facts(t).views
    }
}

#[cfg(test)]
mod tests;
