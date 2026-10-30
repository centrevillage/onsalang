//! The statements and the control (W4-07 memo 1.3, 3): blocks, branches
//! (joined), loops (their head from a summary made once), the exits and the
//! declarations of the bindings.

use std::mem::replace;

use onsa_diag::internal::bug;
use onsa_syntax::ast::{BinOp, ExprId, ExprKind, Mode, PatId, PatKind, StmtId, StmtKind};

use super::check::Walker;
use super::state::{Delta, LoopSum};
use super::walk::Pos;
use super::write::How;
use crate::binding::{Head, HeadRow};
use crate::body::{LocalId, Target};

/// A walk's state, the `break` and `continue` states of the innermost loop
/// it is in, and the bindings declared in the blocks it is in (innermost
/// last), which leave the table at the end of their block (memo 1.3).
pub(super) struct Run {
    pub(super) cur: Delta,
    exits: (Delta, Delta),
    declared: Vec<LocalId>,
}

impl Run {
    pub(super) fn new() -> Self {
        Run { cur: Delta::start(), exits: (Delta::bottom(), Delta::bottom()), declared: Vec::new() }
    }

    fn declare(&mut self, l: LocalId) {
        self.cur.revive(l);
        self.declared.push(l);
    }
}

impl Walker<'_> {
    /// Walk `e` if it is a form of the control or one that passes `pos` on
    /// to its tails or operand (§5.2: a block, an `if`, a `match`,
    /// parentheses, `TypeArgs`, `move`; the one list of those); `false` for
    /// any other.
    pub(super) fn control(&mut self, r: &mut Run, e: ExprId, pos: Pos) -> bool {
        let ast = self.ast;
        match &ast.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::TypeArgs { base: x, .. } => self.expr(r, *x, pos),
            ExprKind::Move(x) => self.marked(r, e, *x, pos),
            ExprKind::Block(b) => {
                let outer = r.declared.len();
                b.stmts.iter().for_each(|&s| self.stmt(r, s));
                if let Some(t) = b.tail {
                    self.expr(r, t, pos);
                }
                for l in r.declared.split_off(outer) {
                    r.cur.forget(l);
                }
            }
            ExprKind::If { cond, then, else_, .. } => {
                self.expr(r, *cond, Pos::Read);
                let before = r.cur.clone();
                self.expr(r, *then, pos);
                let then = replace(&mut r.cur, before);
                if let Some(x) = else_ {
                    self.expr(r, *x, pos);
                }
                r.cur.join(&then);
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                let head = self.head_pos(Head::Match { scrutinee: *scrutinee }, Pos::Arg(Mode::Borrow));
                if head != Pos::Consume {
                    self.view_of_inout(*scrutinee, arms.iter().map(|a| a.pat));
                }
                self.expr(r, *scrutinee, head);
                // The state an arm is tried at: no arm before matched, or
                // one matched and its guard was false.
                let (mut tried, mut out) = (r.cur.clone(), Delta::bottom());
                for arm in arms {
                    r.cur = tried.clone();
                    self.declare(r, arm.pat);
                    if let Some(g) = arm.guard {
                        self.expr(r, g, Pos::Read);
                        tried.join(&r.cur);
                    }
                    self.expr(r, arm.body, pos);
                    out.join(&r.cur);
                }
                r.cur = out;
            }
            ExprKind::Binary { op: BinOp::And | BinOp::Or, lhs, rhs, .. } => {
                self.expr(r, *lhs, Pos::Read);
                self.lazily(r, e, |w, r| w.expr(r, *rhs, Pos::Read));
            }
            // A new frame (`capture.rs`); it changes no state outside.
            ExprKind::Closure { body, .. } => {
                if !self.out_of_place(r, e, pos) {
                    self.closure(r, e, *body);
                }
            }
            _ => return false,
        }
        true
    }

    /// Walk what `f` walks on the paths through it and the paths that skip
    /// it, joined: the right of `&&` and `||` (`e` the operator), and the
    /// arguments of a builtin method that evaluates them on some paths
    /// (`e` the call, [`Target::BuiltinMethod`]).
    pub(super) fn lazily(&mut self, r: &mut Run, e: ExprId, f: impl FnOnce(&mut Self, &mut Run)) {
        let lazy = match (&self.ast.expr(e).kind, self.info.targets.get(&e)) {
            (ExprKind::Binary { .. }, _) => true,
            (_, Some(Target::BuiltinMethod { lazy_args, .. })) => *lazy_args,
            _ => false,
        };
        let skip = lazy.then(|| r.cur.clone());
        f(self, r);
        if let Some(s) = skip {
            r.cur.join(&s);
        }
    }

    fn stmt(&mut self, r: &mut Run, s: StmtId) {
        let ast = self.ast;
        match &ast.stmt(s).kind {
            StmtKind::Let { pat, init, .. } => {
                let pos = self.head_pos(Head::Let(s), Pos::Bind);
                self.expr(r, *init, pos);
                self.declare(r, *pat);
            }
            StmtKind::Var { init, .. } => {
                self.expr(r, *init, Pos::Consume);
                let Some(&l) = self.vars.get(&s) else { bug(Some(ast.stmt(s).span), "a `var` with no local") };
                r.declare(l);
            }
            // The value, then the target (§3.5).
            StmtKind::Assign { target, value } => {
                self.expr(r, *value, Pos::Consume);
                self.write_place(r, *target, How::Assign);
            }
            StmtKind::For { pat, moved, iter, body } => {
                match moved {
                    true => self.consume(r, *iter, Pos::Consume, Some(ast.expr(*iter).span.start)),
                    false => {
                        let head = self.head_pos(Head::For(s), Pos::Arg(Mode::Borrow));
                        if head != Pos::Consume {
                            self.view_of_inout(*iter, [*pat]);
                        }
                        self.expr(r, *iter, head)
                    }
                }
                self.run_loop(r, s, (None, Some(*pat), *body));
            }
            StmtKind::While { cond, body } => self.run_loop(r, s, (Some(*cond), None, *body)),
            StmtKind::Break => r.exits.0.join(&replace(&mut r.cur, Delta::bottom())),
            StmtKind::Continue => r.exits.1.join(&replace(&mut r.cur, Delta::bottom())),
            StmtKind::Return(x) => {
                if let Some(x) = x {
                    self.expr(r, *x, Pos::Return);
                }
                r.cur = Delta::bottom();
            }
            StmtKind::Assert(x) | StmtKind::Expr(x) => self.expr(r, *x, Pos::Read),
        }
    }

    /// The position of the value of a head: `borrow` if its row is a borrow,
    /// else (owned, or not settled) consumed (§5.4).
    fn head_pos(&self, head: Head, borrow: Pos) -> Pos {
        match self.info.heads.get(&head) {
            Some(HeadRow::Borrow { .. }) => borrow,
            _ => Pos::Consume,
        }
    }

    /// The loop `s` from the state before its head (memo 1.3, 3). The walk
    /// that reports goes in once from the head `x ⊔ G`; the other applies
    /// the summary, made once for each loop by a walk that does not go into
    /// the loops inside (their summaries are made first and kept).
    fn run_loop(&mut self, r: &mut Run, s: StmtId, parts: Loop) {
        let sum = match self.m.loops.get(&s) {
            Some(sum) => sum.clone(),
            None => {
                let reports = replace(&mut self.reports, false);
                let (exit, back) = self.iterate(&mut Run::new(), parts);
                self.reports = reports;
                let sum = LoopSum { exit: LoopSum::head(&back).then(&exit), back };
                self.m.loops.insert(s, sum.clone());
                sum
            }
        };
        if self.reports {
            r.cur = r.cur.then(&LoopSum::head(&sum.back));
            r.cur = self.iterate(r, parts).0;
        } else {
            r.cur = r.cur.then(&sum.exit);
        }
    }

    /// One iteration of a loop from its head in `r`: the exit (at the end of
    /// the condition of a `while`, at the head of a `for`, or at a `break`)
    /// and the back edge (at the end of the body or a `continue`). A `for`
    /// declares its pattern at each iteration (R-29).
    fn iterate(&mut self, r: &mut Run, (cond, pat, body): Loop) -> (Delta, Delta) {
        let outer = replace(&mut r.exits, (Delta::bottom(), Delta::bottom()));
        if let Some(c) = cond {
            self.expr(r, c, Pos::Read);
        }
        let mut exit = r.cur.clone();
        if let Some(p) = pat {
            self.declare(r, p);
        }
        self.expr(r, body, Pos::Read);
        let (brk, cont) = replace(&mut r.exits, outer);
        exit.join(&brk);
        let mut back = replace(&mut r.cur, Delta::bottom());
        back.join(&cont);
        (exit, back)
    }

    /// Declare the bindings of the pattern `p`: live (memo 1.3).
    fn declare(&mut self, r: &mut Run, p: PatId) {
        self.each_local(p, &mut |l| r.declare(l));
    }

    /// Each local the pattern `p` binds.
    pub(super) fn each_local(&self, p: PatId, f: &mut dyn FnMut(LocalId)) {
        let ast = self.ast;
        match &ast.pat(p).kind {
            PatKind::Bind(_) => {
                let Some(&l) = self.info.pat_locals.get(&p) else {
                    bug(Some(ast.pat(p).span), "a binding with no local")
                };
                f(l);
            }
            PatKind::TupleStruct { elems: ps, .. } | PatKind::Tuple(ps) | PatKind::Or(ps) => {
                ps.iter().for_each(|&q| self.each_local(q, f))
            }
            PatKind::Struct { fields, .. } => fields.iter().for_each(|&(_, q)| self.each_local(q, f)),
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
        }
    }
}

/// The parts of a loop: the condition of a `while`, the pattern of a `for`,
/// the body.
type Loop = (Option<ExprId>, Option<PatId>, ExprId);
