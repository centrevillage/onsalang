//! The places the locals of `LocalKind::Alias` name (`StmtKind::Alias`):
//! a use of one is a use of its place, so where roots and projections are
//! compared it is replaced by that place first ([`resolve`]). The lowering,
//! the normalization and the verifier read the one table of a function
//! ([`table`], D-15).

use std::collections::HashMap;

use crate::ir::{FnDef, LocalId, LocalKind, Place, Stmt, StmtKind};
use crate::walk::{Child, Eval, Part, Role, Scope, block_children, expr_children, place_children, stmt_children};

/// By local of `LocalKind::Alias`: the place its `Alias` statement names,
/// itself resolved, so the root of each is no alias.
#[derive(Debug, Default)]
pub struct Table(HashMap<LocalId, Place>);

/// The table of `f`, of its `Alias` statements in the order of the walk
/// (one defines an alias before its uses, V-04): a function with no local
/// of `LocalKind::Alias` is not walked.
pub fn table(f: &FnDef) -> Table {
    fn child(t: &mut Table, c: Child<'_>) {
        match c {
            Child::Expr(x, ..) => expr_children(x, &mut |c| child(t, c)),
            Child::Block(b, ..) => block_children(b, Role::Read, &mut |p| match p {
                Part::Stmt(s) => stmt(t, s),
                Part::Value(v, _) => expr_children(v, &mut |c| child(t, c)),
            }),
            Child::Place(p, role) => place_children(p, role, &mut |c| child(t, c)),
        }
    }
    fn stmt(t: &mut Table, s: &Stmt) {
        stmt_children(s, &mut |c| child(t, c));
        if let StmtKind::Alias(l, p) = &s.kind {
            let p = resolve(t, p);
            t.0.insert(*l, p);
        }
    }
    let mut t = Table::default();
    let any = f.locals.iter().any(|l| l.kind != LocalKind::Value);
    if let Some(b) = f.body.as_ref().filter(|_| any) {
        child(&mut t, Child::Block(b, Scope::Opens, Eval::Always));
    }
    t
}

/// `p` with its root replaced by the place it names, when it is an alias
/// of `t` (`r[0]` of `Alias(r, g[i])` is `g[i][0]`).
pub fn resolve(t: &Table, p: &Place) -> Place {
    match p {
        Place::Local(l) => t.0.get(l).cloned().unwrap_or(Place::Local(*l)),
        Place::Field(b, i) => Place::Field(Box::new(resolve(t, b)), *i),
        Place::Index(b, i, at, bounds) => Place::Index(Box::new(resolve(t, b)), i.clone(), *at, *bounds),
    }
}
