//! The states of the bindings (spec §5.4, R-85, S-80): one stage after the
//! types and before the modes settles, once for each body, whether each
//! binding is owned, owned and mutable, a borrow or `inout`, from the closed
//! table of §5.4 ([`row`]) and the rows of the heads whose bindings take the
//! row of their value (`let`, `for`, the arms of a `match`). The later stages
//! read the record ([`crate::body::LocalInfo::state`], [`BodyInfo::heads`],
//! [`BodyInfo::lits`]) and decide none of it again (D-15). It reports no
//! diagnostic, so it is not a stage of §18.1.
//!
//! The walk goes in source order: a head is settled after its value is
//! walked, so the state of the binding at the root of a place it reads is
//! settled before (§5.1: a `let` sees only the bindings before it). It goes
//! into anonymous functions and `par` bodies, whose bindings are of the same
//! body. A flow body is not settled (the modes, `rt` and effects stages do
//! not read it), nor is a body they skip (one that is not complete or whose
//! unit failed before the modes, §18.1): its heads' bindings stay owned.

use std::collections::HashMap;

use onsa_diag::Stage;
use onsa_syntax::ast::{Ast, ExprId, ExprKind, Mode, StmtId, StmtKind};
use onsa_syntax::tails::Tail;

use crate::body::{BodyInfo, LocalId, Target};
use crate::names::body::{BindingKind, BodyNames, Origin, PathRes};
use crate::ty::{BuiltinTy, Ty};
use crate::{Analysis, DefId, Package, module_of_def};

mod literal;
#[cfg(test)]
mod tests;

/// The state of a binding (§5.4, R-85 (1)): one of four, so that a borrow
/// that can be written cannot be made.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bind {
    Owned,
    /// Owned and written to: a `var`, a `move` parameter and `move self`
    /// (§5.1: only a `let` and a borrowed parameter are read-only, R-191).
    OwnedMut,
    /// A borrow, a root or derived (a derived borrow is a root too, §5.4).
    /// `no_drop`: a binding that needs no drop (from a static value or a
    /// literal that needs no drop, or derived from one, S-613 L4).
    Borrow {
        no_drop: bool,
    },
    Inout,
}

/// A head whose bindings take the row of its value (§5.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Head {
    Let(StmtId),
    For(StmtId),
    Match { scrutinee: ExprId },
}

/// The row of a head (§5.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeadRow {
    Owned,
    /// `sources`: the places of the value the bindings derive from (S-604:
    /// the invalidation of §7 and E0715 apply to each); a static value adds
    /// none. `no_drop` as of [`Bind::Borrow`].
    Borrow {
        sources: Vec<ExprId>,
        no_drop: bool,
    },
}

/// What a literal is (§5.4): a static value (S-610), one that needs no drop
/// (S-613), or owned with its first element that made it so.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LitClass {
    Static,
    NoDrop,
    Owned { first: ExprId },
}

/// The state of a binding of kind `kind`, from the table of §5.4, with the
/// row of its head for the kinds that have one (`None`: its head is not
/// settled, and it is owned). No `_`: a new kind of binding needs a row here.
pub(crate) fn row(kind: BindingKind, head: Option<&HeadRow>) -> Bind {
    let of_head = match head {
        Some(HeadRow::Borrow { no_drop, .. }) => Bind::Borrow { no_drop: *no_drop },
        Some(HeadRow::Owned) | None => Bind::Owned,
    };
    match kind {
        BindingKind::Param(m) | BindingKind::SelfParam(m) | BindingKind::ClosureParam(m) => match m {
            Mode::Borrow => Bind::Borrow { no_drop: false },
            Mode::Inout => Bind::Inout,
            Mode::Move => Bind::OwnedMut,
        },
        BindingKind::FlowInput => Bind::Borrow { no_drop: false },
        BindingKind::Let | BindingKind::FlowLet | BindingKind::MatchBind | BindingKind::For { moved: false } => of_head,
        BindingKind::For { moved: true } | BindingKind::ParVar => Bind::Owned,
        BindingKind::Var => Bind::OwnedMut,
    }
}

/// Settle the bindings of every body the modes stage reads.
pub(crate) fn settle_all(pkg: &Package, a: &mut Analysis) {
    let ids: Vec<DefId> = a.bodies.keys().copied().collect();
    for id in ids {
        if !a.body_checked(id, Stage::Modes) {
            continue;
        }
        let (Some(module), Some(root)) = (module_of_def(pkg, a, id), crate::body::root_of(a, id)) else {
            continue;
        };
        let _scope = onsa_diag::internal::item_scope(a.def(id).span);
        let Some(mut info) = a.bodies.remove(&id) else { continue };
        if let Some(names) = a.names.get(&id) {
            Settle::new(a, &module.parsed.ast, names, &mut info).expr(root);
        }
        a.bodies.insert(id, info);
    }
}

struct Settle<'a> {
    a: &'a Analysis,
    ast: &'a Ast,
    names: &'a BodyNames,
    info: &'a mut BodyInfo,
    /// The bindings of each head, from their origins.
    bound: HashMap<Head, Vec<LocalId>>,
}

impl<'a> Settle<'a> {
    fn new(a: &'a Analysis, ast: &'a Ast, names: &'a BodyNames, info: &'a mut BodyInfo) -> Self {
        let mut bound: HashMap<Head, Vec<LocalId>> = HashMap::new();
        for (i, b) in names.bindings.iter().enumerate() {
            let head = match b.origin {
                Origin::Let(s) if b.kind == BindingKind::Let => Head::Let(s),
                Origin::For(s) => Head::For(s),
                Origin::Arm { scrutinee, .. } => Head::Match { scrutinee },
                _ => continue,
            };
            bound.entry(head).or_default().push(LocalId(i as u32));
        }
        Settle { a, ast, names, info, bound }
    }

    fn expr(&mut self, e: ExprId) {
        let ast = self.ast;
        match &ast.expr(e).kind {
            ExprKind::Block(b) => {
                for &s in &b.stmts {
                    self.stmt(s);
                }
                if let Some(t) = b.tail {
                    self.expr(t);
                }
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                self.expr(*scrutinee);
                let row = self.head(*scrutinee, true);
                self.settle(Head::Match { scrutinee: *scrutinee }, row);
                for arm in arms {
                    if let Some(g) = arm.guard {
                        self.expr(g);
                    }
                    self.expr(arm.body);
                }
            }
            _ => {
                if let Some(class) = literal::leaf(self.a, ast, self.info, e) {
                    self.info.lits.insert(e, class);
                }
                for x in ast.sub_exprs(e) {
                    self.expr(x);
                }
            }
        }
    }

    fn stmt(&mut self, s: StmtId) {
        let ast = self.ast;
        match &ast.stmt(s).kind {
            StmtKind::Let { init, .. } => {
                self.expr(*init);
                let row = self.head(*init, false);
                self.settle(Head::Let(s), row);
            }
            StmtKind::For { moved, iter, body, .. } => {
                self.expr(*iter);
                let row = if *moved { HeadRow::Owned } else { self.head(*iter, true) };
                self.settle(Head::For(s), row);
                self.expr(*body);
            }
            StmtKind::Var { init: x, .. } | StmtKind::Return(Some(x)) | StmtKind::Assert(x) | StmtKind::Expr(x) => {
                self.expr(*x)
            }
            StmtKind::Assign { target, value } => {
                self.expr(*target);
                self.expr(*value);
            }
            StmtKind::While { cond, body } => {
                self.expr(*cond);
                self.expr(*body);
            }
            StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue => {}
        }
    }

    /// The row of a head on the value `e` (§5.4, S-604, S-589): a borrow
    /// when every tail that does not exit is one ([`Settle::borrowed`]),
    /// derived from the places of all; else owned, and owned when every tail
    /// exits (the E0503 of §7 does not ask the row). `any_place`: the head of
    /// a `for` or a `match`, which borrows any place; a `let` borrows a place
    /// only from a borrow (S-41).
    fn head(&self, e: ExprId, any_place: bool) -> HeadRow {
        let mut tails = Vec::new();
        self.ast.tails(e, &mut tails);
        let (mut sources, mut no_drop, mut borrows) = (Vec::new(), true, false);
        for tail in tails {
            match tail {
                Tail::Exits => {}
                Tail::Unit(_) => return HeadRow::Owned,
                Tail::Value(v) => {
                    let Some((place, nd)) = self.borrowed(v, any_place) else { return HeadRow::Owned };
                    sources.extend(place);
                    no_drop &= nd;
                    borrows = true;
                }
            }
        }
        if borrows { HeadRow::Borrow { sources, no_drop } } else { HeadRow::Owned }
    }

    /// Whether a tail `e` (without parentheses) is borrowed (§5.4), with the
    /// place it derives from (none for a static value) and whether it needs
    /// no drop: a place whose root is a borrow, or any place (`any_place`);
    /// a partial view of such a place (S-217: `xs.slice(a, b)`, known by the
    /// `Span` its builtin method gives, not by its name, Q-14); a static value.
    fn borrowed(&self, e: ExprId, any_place: bool) -> Option<(Option<ExprId>, bool)> {
        if let ExprKind::Call { callee, .. } = &self.ast.expr(e).kind
            && let ExprKind::Field { base, .. } = &self.ast.expr(*callee).kind
            && let Some(Target::BuiltinMethod { .. }) = self.info.targets.get(&e)
            && let Some(&t) = self.info.expr_types.get(&e)
            && let Ty::Builtin(BuiltinTy::Span, _) = self.a.types.get(t)
        {
            return self.borrowed(self.ast.without_parens(*base), any_place);
        }
        if let Some(root) = self.ast.place_root_node(e)
            && let Some(PathRes::Local(b)) = self.names.paths.get(&root)
        {
            return match self.info.locals[b.0 as usize].state {
                Bind::Borrow { no_drop } => Some((Some(e), no_drop)),
                _ if any_place => Some((Some(e), false)),
                _ => None,
            };
        }
        match self.info.lits.get(&e) {
            Some(LitClass::Static | LitClass::NoDrop) => Some((None, true)),
            _ => None,
        }
    }

    /// Give the bindings of `head` the state of `row` and record it.
    fn settle(&mut self, head: Head, head_row: HeadRow) {
        for &id in self.bound.get(&head).into_iter().flatten() {
            let kind = self.names.bindings[id.0 as usize].kind;
            self.info.locals[id.0 as usize].set_state(row(kind, Some(&head_row)));
        }
        self.info.heads.insert(head, head_row);
    }
}
