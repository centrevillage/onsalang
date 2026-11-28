//! The children of the nodes of Core, listed in one place with their roles
//! (W8-02, D-15), and the traversals on that list: every expression, depth
//! first, in evaluation order (used by reachability, the move bookkeeping,
//! the storage of the locals and tools).
//!
//! A list gives one level: the direct parts of a statement, an expression or
//! a place, in evaluation order (§3.5: an assignment evaluates its value and
//! then its place). A reader handles [`Child::Block`] in one place, where a
//! scope opens and closes ([`Scope`]); the matches on `StmtKind`, `ExprKind`
//! and `Place` have no `_` arm, so a new form is a compile error in the list.
//!
//! Each list has a shared version ([`Child`], [`Part`]) and a `&mut` one
//! ([`ChildMut`], [`PartMut`]) for the passes that rewrite Core in place;
//! one text makes both (`lists!`), so they cannot differ.

use crate::ir::{Block, Expr, ExprKind, FnDef, Mode, Place, Stmt, StmtKind};
use crate::prim::Prim;

/// A direct part of a node, with how it is evaluated.
#[derive(Debug, Clone, Copy)]
pub enum Child<'a> {
    Expr(&'a Expr, Eval, Role),
    /// A block: its statements, then its value ([`block_children`]).
    Block(&'a Block, Scope, Eval),
    Place(&'a Place, PlaceRole),
}

/// A [`Child`] that its reader may change.
#[derive(Debug)]
pub enum ChildMut<'a> {
    Expr(&'a mut Expr, Eval, Role),
    Block(&'a mut Block, Scope, Eval),
    Place(&'a mut Place, PlaceRole),
}

/// How often a child is evaluated when its parent is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Eval {
    Always,
    /// Once or not at all: the right operand of `&&`/`||`, an arm.
    Conditional,
    /// Zero or more times: the condition and the body of a `while`, the body
    /// of a `for`.
    Loop,
    /// Not by the backends: the values a panic shows (`Panic.shown`).
    Observed,
}

/// Whether a block is a scope: its locals live to its end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    /// A block a backend opens: an arm of an `IfExpr` or a `Switch`, the
    /// block of an `If`, a `While` or a `ForRange`.
    Opens,
    /// A block expression: it ends neither the life nor the name of the
    /// locals it declares (a Core promise: `span_of` places
    /// `{ let __arr = …; span(__arr) }` at an argument).
    Inline,
}

/// What is done with the value of an expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    Read,
    /// Taken by a `move` argument.
    Consume,
    /// Stored where it goes: the value of a `let`, an assignment, a
    /// `return`, an element of a literal.
    Dest,
    /// An `inout` argument: the places it writes are [`written_places`].
    Inout,
}

/// What is done with a place.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlaceRole {
    Write,
    /// Named by an `Alias` statement: its indices are read there, and it is
    /// used later through the alias.
    Alias,
}

/// A part of a block ([`block_children`]).
#[derive(Debug, Clone, Copy)]
pub enum Part<'a> {
    Stmt(&'a Stmt),
    /// The value, evaluated always once the statements are, with its role.
    Value(&'a Expr, Role),
}

/// A [`Part`] that its reader may change.
#[derive(Debug)]
pub enum PartMut<'a> {
    Stmt(&'a mut Stmt),
    Value(&'a mut Expr, Role),
}

/// The four lists, written once: given the child and the part types, the
/// method that iterates a vector, the names of the four functions and,
/// for the `&mut` version, `mut` (D-15: the two versions give the same
/// children, in the same order, with the same `Eval`, `Scope` and `Role`).
macro_rules! lists {
    ($child:ident, $part:ident, $iter:ident, $stmt:ident, $place:ident, $expr:ident, $block:ident $(, $m:tt)?) => {
        /// The direct parts of `s`, in evaluation order.
        pub fn $stmt<'a>(s: &'a $($m)? Stmt, f: &mut dyn FnMut($child<'a>)) {
            use Eval::{Always, Conditional, Loop};
            let read = |e| $child::Expr(e, Always, Role::Read);
            match &$($m)? s.kind {
                StmtKind::Let(_, e) | StmtKind::Return(Some(e)) => f($child::Expr(e, Always, Role::Dest)),
                StmtKind::Assign(p, e) => {
                    f($child::Expr(e, Always, Role::Dest));
                    f($child::Place(p, PlaceRole::Write));
                }
                StmtKind::Alias(_, p) => f($child::Place(p, PlaceRole::Alias)),
                StmtKind::Expr(e) => f(read(e)),
                StmtKind::If(c, a, b) => {
                    f(read(c));
                    f($child::Block(a, Scope::Opens, Conditional));
                    f($child::Block(b, Scope::Opens, Conditional));
                }
                StmtKind::While(c, b) => {
                    f($child::Expr(c, Loop, Role::Read));
                    f($child::Block(b, Scope::Opens, Loop));
                }
                StmtKind::ForRange { lo, hi, body: b, .. } => {
                    f(read(lo));
                    f(read(hi));
                    f($child::Block(b, Scope::Opens, Loop));
                }
                StmtKind::Break | StmtKind::Continue | StmtKind::Return(None) => {}
            }
        }

        /// The direct parts of place `p` used as `role`: its base is used the
        /// same way, and an index is read.
        pub fn $place<'a>(p: &'a $($m)? Place, role: PlaceRole, f: &mut dyn FnMut($child<'a>)) {
            match p {
                Place::Local(_) => {}
                Place::Field(b, _) => f($child::Place(b, role)),
                Place::Index(b, i, ..) => {
                    f($child::Place(b, role));
                    f($child::Expr(i, Eval::Always, Role::Read));
                }
            }
        }

        /// The direct parts of `e`, in evaluation order. An expression has no
        /// [`Child::Place`].
        pub fn $expr<'a>(e: &'a $($m)? Expr, f: &mut dyn FnMut($child<'a>)) {
            use Eval::{Always, Conditional};
            let mut each = |xs: &mut dyn Iterator<Item = &'a $($m)? Expr>, role| {
                xs.for_each(|x| f($child::Expr(x, Always, role)))
            };
            let pair = |a: &'a $($m)? Expr, b: &'a $($m)? Expr| [a, b].into_iter();
            match &$($m)? e.kind {
                ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::Const(_) | ExprKind::Zeroed => {}
                ExprKind::Unary(_, x)
                | ExprKind::Cast(x)
                | ExprKind::SpanOf(x)
                | ExprKind::Tag(x)
                | ExprKind::Field { base: x, .. }
                | ExprKind::Payload { base: x, .. } => f($child::Expr(x, Always, Role::Read)),
                ExprKind::Binary { lhs, rhs, .. } | ExprKind::Cmp { lhs, rhs, .. } => {
                    each(&mut pair(lhs, rhs), Role::Read)
                }
                ExprKind::Index { base, index, .. } => each(&mut pair(base, index), Role::Read),
                ExprKind::Logic { lhs, rhs, .. } => {
                    f($child::Expr(lhs, Always, Role::Read));
                    f($child::Expr(rhs, Conditional, Role::Read));
                }
                ExprKind::Call { args, .. } | ExprKind::Prim { args, .. } => args.$iter().for_each(|a| {
                    let role = match a.mode {
                        Mode::Borrow => Role::Read,
                        Mode::Inout => Role::Inout,
                        Mode::Move => Role::Consume,
                    };
                    f($child::Expr(&$($m)? a.expr, Always, role))
                }),
                ExprKind::Struct { fields, .. } => each(&mut fields.$iter().map(|(_, x)| x), Role::Dest),
                ExprKind::Variant { fields: xs, .. } | ExprKind::Array(xs) | ExprKind::Tuple(xs) => {
                    each(&mut xs.$iter(), Role::Dest)
                }
                ExprKind::Repeat { elem, .. } => f($child::Expr(elem, Always, Role::Dest)),
                ExprKind::IfExpr { cond, then, else_ } => {
                    f($child::Expr(cond, Always, Role::Read));
                    f($child::Block(then, Scope::Opens, Conditional));
                    f($child::Block(else_, Scope::Opens, Conditional));
                }
                ExprKind::Switch { scrutinee, arms, default } => {
                    f($child::Expr(scrutinee, Always, Role::Read));
                    let blocks = arms.$iter().map(|(_, b)| b).chain(default);
                    blocks.for_each(|b| f($child::Block(b, Scope::Opens, Conditional)));
                }
                ExprKind::Block(b) => f($child::Block(b, Scope::Inline, Always)),
                ExprKind::Panic { shown, .. } => {
                    shown.$iter().for_each(|x| f($child::Expr(x, Eval::Observed, Role::Read)))
                }
            }
        }

        /// The parts of block `b`, in order: each statement, then the value.
        /// The value goes where the value of the block goes, so it has `role`,
        /// the role of the expression the block is a part of (of a function's
        /// body, `Dest`); a reader that reads no role gives `Read`.
        pub fn $block<'a>(b: &'a $($m)? Block, role: Role, f: &mut dyn FnMut($part<'a>)) {
            b.stmts.$iter().for_each(|s| f($part::Stmt(s)));
            if let Some(v) = &$($m)? b.value {
                f($part::Value(v, role));
            }
        }
    };
}

lists!(Child, Part, iter, stmt_children, place_children, expr_children, block_children);
lists!(ChildMut, PartMut, iter_mut, stmt_children_mut, place_children_mut, expr_children_mut, block_children_mut, mut);

/// The places an `inout` argument `e` writes, given to `f`, each an
/// expression that is a place ([`Expr::as_place`]); whether `e` is of the
/// forms that write places: a place, a span over a place, a slice of one (a
/// partial view, R-31), or (planar channels, §5.3) an array literal of those,
/// and a literal of a generated `Out` of those (§11.6); of a block, its
/// value (`{ alias r = g[next(inout i)]; [span(r[0]), span(r[1])] }`), of
/// no root a `Let` of the block declares (a write to it would be lost).
pub fn written_places<'a>(e: &'a Expr, f: &mut dyn FnMut(&'a Expr)) -> bool {
    match &e.kind {
        ExprKind::SpanOf(inner) => inner.as_place().map(|_| f(inner)).is_some(),
        ExprKind::Prim { prim: Prim::Slice, args } => args.first().is_some_and(|a| written_places(&a.expr, f)),
        ExprKind::Array(items) => items.iter().fold(true, |all, x| written_places(x, f) && all),
        ExprKind::Struct { fields, .. } => fields.iter().fold(true, |all, (_, x)| written_places(x, f) && all),
        ExprKind::Block(b) => b.value.as_ref().is_some_and(|v| {
            let mut outside = true;
            let lets = |l| b.stmts.iter().any(|s| matches!(s.kind, StmtKind::Let(k, _) if k == l));
            written_places(v, &mut |p| {
                outside &= !p.place_root().is_some_and(lets);
                f(p)
            }) && outside
        }),
        _ => e.as_place().map(|_| f(e)).is_some(),
    }
}

pub fn walk_block(b: &Block, f: &mut dyn FnMut(&Expr)) {
    block_children(b, Role::Read, &mut |p| match p {
        Part::Stmt(s) => walk_stmt(s, f),
        Part::Value(v, _) => walk_expr(v, f),
    });
}

pub fn walk_stmt(s: &Stmt, f: &mut dyn FnMut(&Expr)) {
    stmt_children(s, &mut |c| walk_child(c, f));
}

pub fn walk_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    expr_children(e, &mut |c| walk_child(c, f));
}

fn walk_child(c: Child<'_>, f: &mut dyn FnMut(&Expr)) {
    match c {
        Child::Expr(x, ..) => walk_expr(x, f),
        Child::Block(b, ..) => walk_block(b, f),
        Child::Place(p, role) => place_children(p, role, &mut |c| walk_child(c, f)),
    }
}

/// Whether a function body contains a `Return` statement anywhere: each
/// node once (R-439), the index of an assigned place too.
pub fn has_return(def: &FnDef) -> bool {
    fn block(b: &Block) -> bool {
        let mut found = false;
        block_children(b, Role::Read, &mut |p| {
            found = found
                || match p {
                    Part::Stmt(s) => stmt(s),
                    Part::Value(v, _) => expr(v),
                }
        });
        found
    }
    fn stmt(s: &Stmt) -> bool {
        let mut found = matches!(s.kind, StmtKind::Return(_));
        stmt_children(s, &mut |c| found = found || child(c));
        found
    }
    fn expr(e: &Expr) -> bool {
        let mut found = false;
        expr_children(e, &mut |c| found = found || child(c));
        found
    }
    /// Past the first `Return` found, no child is looked into.
    fn child(c: Child<'_>) -> bool {
        match c {
            Child::Expr(x, ..) => expr(x),
            Child::Block(b, ..) => block(b),
            Child::Place(p, role) => {
                let mut found = false;
                place_children(p, role, &mut |c| found = found || child(c));
                found
            }
        }
    }
    def.body.as_ref().is_some_and(block)
}
