//! The statements and the control (§5.2: a move counts along the flow of
//! the control): blocks, branches (joined), loops (their head from a
//! summary made once, `state.rs`), the exits and the declarations of the
//! bindings.

use std::mem::replace;

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{BinOp, ExprId, ExprKind, Mode, PatId, PatKind, StmtId, StmtKind};

use super::check::Walker;
use super::state::{LoopSum, Paths, Trail};
use super::walk::Pos;
use super::write::How;
use crate::Kind;
use crate::binding::{Head, HeadRow};
use crate::body::{DropPoint, Dropped, LocalId, LocalKind};
use crate::names::body::Origin;

/// A walk's state, the innermost loop it is in, and the bindings declared
/// in the blocks it is in (innermost last), which leave the table at the
/// end of their block (no name reads them after it: the table stays small).
pub(super) struct Run {
    pub(super) cur: Trail,
    exits: Exits,
    declared: Vec<LocalId>,
}

/// The paths from the head of a loop (at the mark `at`) to its exit (`brk`:
/// the end of the condition, the `break`s) and to its back edge (`cont`:
/// the end of the body, the `continue`s).
struct Exits {
    brk: Paths,
    cont: Paths,
    at: usize,
}

impl Run {
    pub(super) fn new() -> Self {
        let exits = Exits { brk: Paths::none(), cont: Paths::none(), at: 0 };
        Run { cur: Trail::new(), exits, declared: Vec::new() }
    }

    fn declare(&mut self, l: LocalId) {
        self.cur.declare(l);
        self.declared.push(l);
    }

    /// The bindings declared after the first `outer` leave the table: their
    /// block or arm ended.
    fn forget(&mut self, outer: usize) {
        for l in self.declared.split_off(outer) {
            self.cur.change(l, |d| d.forget(l));
        }
    }

    /// A `break` (`back`: a `continue`): the bindings declared in the loop
    /// leave (no drop point until U3), then the state joins the loop's exit
    /// (or its back edge).
    fn leave(&mut self, back: bool) {
        let paths = if back { &mut self.exits.cont } else { &mut self.exits.brk };
        self.cur.join_into(self.exits.at, paths, true);
        self.cur.stop();
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
                self.ends(r, &r.declared[outer..], ast.expr(e).span);
                r.forget(outer);
            }
            ExprKind::If { cond, then, else_, .. } => {
                self.expr(r, *cond, Pos::Read);
                let (m, mut paths) = (r.cur.mark(), Paths::none());
                self.expr(r, *then, pos);
                r.cur.join_into(m, &mut paths, false);
                r.cur.back_to(m);
                if let Some(x) = else_ {
                    self.expr(r, *x, pos);
                }
                r.cur.join_into(m, &mut paths, false);
                r.cur.settle(m, &paths);
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                let subject = Head::Match { scrutinee: *scrutinee };
                let head = self.head_pos(subject, Pos::Bind);
                if head != Pos::Own {
                    self.view_of_inout(*scrutinee, arms.iter().map(|a| a.pat));
                }
                self.head(r, *scrutinee, head, &arms.iter().map(|a| a.pat).collect::<Vec<_>>());
                // The paths an arm is tried at, from the head: no arm before
                // matched, or one matched and its guard was false.
                let (m, mut tried, mut out) = (r.cur.mark(), Paths::none(), Paths::none());
                r.cur.join_into(m, &mut tried, false);
                // A guard changes no place of a borrowed head, and consumes
                // no binding of its arm of an owned one (§7: E0715, `frozen.rs`).
                let mut held = self.frame(subject);
                for arm in arms {
                    r.cur.reset(m, &tried);
                    let outer = r.declared.len();
                    self.declare(r, arm.pat);
                    if let Some(g) = arm.guard {
                        let mut arm_held = (head == Pos::Own).then(|| self.arm_frame(subject, arm.pat));
                        let frame = if arm_held.is_some() { &mut arm_held } else { &mut held };
                        self.holding(frame, |w| w.expr(r, g, Pos::Read));
                        // False: back to the head, the arm's bindings out with no drop (S-1039).
                        r.cur.join_into(m, &mut tried, true);
                    }
                    self.expr(r, arm.body, pos);
                    self.ends(r, &r.declared[outer..], ast.expr(arm.body).span);
                    r.forget(outer);
                    r.cur.join_into(m, &mut out, false);
                }
                r.cur.settle(m, &out);
            }
            ExprKind::Binary { op: BinOp::And | BinOp::Or, lhs, rhs, .. } => {
                self.expr(r, *lhs, Pos::Read);
                // The paths through the right and the paths that skip it, joined.
                let (m, mut paths) = (r.cur.mark(), Paths::none());
                r.cur.join_into(m, &mut paths, false);
                self.expr(r, *rhs, Pos::Read);
                r.cur.join_into(m, &mut paths, false);
                r.cur.settle(m, &paths);
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

    fn stmt(&mut self, r: &mut Run, s: StmtId) {
        let ast = self.ast;
        match &ast.stmt(s).kind {
            StmtKind::Let { pat, init, .. } => {
                let pos = self.head_pos(Head::Let(s), Pos::Bind);
                self.head(r, *init, pos, &[*pat]);
                self.declare(r, *pat);
            }
            StmtKind::Var { init, .. } => {
                self.expr(r, *init, Pos::Own);
                let Some(&l) = self.origins.get(&Origin::Var(s)) else {
                    bug(Some(ast.stmt(s).span), "a `var` with no local")
                };
                r.declare(l);
            }
            // The value, then the target (§3.5).
            StmtKind::Assign { target, value } => {
                self.expr(r, *value, Pos::Value);
                self.write_place(r, *target, How::Assign);
            }
            StmtKind::For { pat, moved, iter, body } => {
                match moved {
                    // S-362: a range has no value to consume (§7).
                    Some(m) if matches!(ast.expr(*iter).kind, ExprKind::Range(_)) => {
                        let message = "a range has no value to consume: `move` is not written on it (§7)";
                        let d = Diagnostic::new(Stage::Modes, Code::E0703, ast.expr(*iter).span, message);
                        self.report(d.with_fix(self.unmark(m.file, m.start, "move")));
                        self.expr(r, *iter, Pos::Read);
                    }
                    Some(m) => self.consume(r, *iter, Pos::Own, Some(m.start)),
                    None => {
                        let head = self.head_pos(Head::For(s), Pos::Arg(Mode::Borrow));
                        if head != Pos::Own {
                            self.view_of_inout(*iter, [*pat]);
                        }
                        self.expr(r, *iter, head)
                    }
                }
                let mut held = self.frame(Head::For(s));
                self.holding(&mut held, |w| w.run_loop(r, s, (None, Some(*pat), *body)));
            }
            StmtKind::While { cond, body } => {
                self.run_loop(r, s, (Some(*cond), None, *body));
                if self.info.diverging.forever(s) {
                    r.cur.stop();
                }
            }
            StmtKind::Break => r.leave(false),
            StmtKind::Continue => r.leave(true),
            StmtKind::Return(x) => {
                if let Some(x) = x {
                    self.expr(r, *x, Pos::Return);
                }
                r.cur.stop();
            }
            StmtKind::Assert(x) | StmtKind::Expr(x) => self.expr(r, *x, Pos::Read),
        }
    }

    /// The position of the value of a head: `borrow` if its row is a borrow,
    /// else (owned, or not settled) consumed (§5.4).
    fn head_pos(&self, head: Head, borrow: Pos) -> Pos {
        match self.info.heads.get(&head) {
            Some(HeadRow::Borrow { .. }) => borrow,
            _ => Pos::Own,
        }
    }

    /// The loop `s` from the state before its head ([`LoopSum`]). The walk
    /// that reports goes in once from the head `x; head(back)`; the other applies
    /// the summary, made once for each loop by a walk that does not go into
    /// the loops inside (their summaries are made first and kept).
    fn run_loop(&mut self, r: &mut Run, s: StmtId, parts: Loop) {
        let sum = match self.m.loops.get(&s) {
            Some(sum) => sum.clone(),
            None => {
                let reports = replace(&mut self.reports, false);
                let mut run = Run::new();
                let back = self.iterate(&mut run, parts);
                self.reports = reports;
                let exit = run.cur.state().clone();
                run.cur.reset(0, &back);
                let back = run.cur.state().clone();
                let sum = LoopSum { exit: LoopSum::head(&back).then(&exit), back };
                self.m.loops.insert(s, sum.clone());
                sum
            }
        };
        if self.reports {
            r.cur.then(&LoopSum::head(&sum.back));
            self.iterate(r, parts);
        } else {
            r.cur.then(&sum.exit);
        }
    }

    /// One iteration of a loop from its head in `r`, which it leaves at the
    /// exit (the end of the condition of a `while`, the head of a `for`, a
    /// `break`); the paths from the head to the back edge (the end of the
    /// body, a `continue`). A `for` declares its pattern at each iteration
    /// (R-29), whose bindings end with it (R-32: their drop points).
    fn iterate(&mut self, r: &mut Run, (cond, pat, body): Loop) -> Paths {
        let exits = Exits { brk: Paths::none(), cont: Paths::none(), at: r.cur.mark() };
        let outer = replace(&mut r.exits, exits);
        if let Some(c) = cond {
            self.expr(r, c, Pos::Read);
        }
        r.cur.join_into(r.exits.at, &mut r.exits.brk, false);
        let scope = r.declared.len();
        if let Some(p) = pat {
            self.declare(r, p);
        }
        self.expr(r, body, Pos::Read);
        self.ends(r, &r.declared[scope..], self.ast.expr(body).span);
        r.forget(scope);
        let Exits { brk, mut cont, at } = replace(&mut r.exits, outer);
        r.cur.join_into(at, &mut cont, false);
        r.cur.settle(at, &brk);
        cont
    }

    /// The drop points at the end of `scope`, of the locals `ls` it ends
    /// (R-32, §12.2): each owned one that may be live there, not Copy; none
    /// where no path reaches (S-873).
    pub(super) fn ends(&mut self, r: &Run, ls: &[LocalId], scope: Span) {
        let info = self.info;
        for &l in ls {
            let local = &info.locals[l.0 as usize];
            if !local.state.owned() {
                continue;
            }
            if let Some(sure) = r.cur.state().lives(l)
                && self.kind_of(local.ty) != Some(Kind::Copy)
            {
                self.drop_point(r, Span::empty(scope.file, scope.end), Dropped::End(l), sure);
            }
        }
    }

    /// The end of the body `root` walked in `r`: the drop points of the
    /// parameters.
    pub(super) fn body_end(&mut self, r: &Run, root: ExprId) {
        let info = self.info;
        let params = (0..info.locals.len() as u32).map(LocalId);
        let params: Vec<_> = params
            .filter(|l| matches!(info.locals[l.0 as usize].kind, LocalKind::Param(_) | LocalKind::SelfParam(_)))
            .collect();
        self.ends(r, &params, self.ast.expr(root).span);
    }

    /// A drop point met by the walk that reports, where a path reaches.
    pub(super) fn drop_point(&mut self, r: &Run, at: Span, what: Dropped, sure: bool) {
        if self.reports && r.cur.state().reaches() {
            let closure = self.closure_in();
            self.m.drops.push(DropPoint { at, what, closure, sure });
        }
    }

    /// Declare the bindings of the pattern `p`: live.
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
