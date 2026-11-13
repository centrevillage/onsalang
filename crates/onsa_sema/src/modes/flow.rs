//! The statements and the control (§5.2: a move counts along the flow of
//! the control): blocks, branches (joined), loops (their head from a
//! summary made once, `state.rs`), the exits and the declarations of the
//! bindings.

use std::mem::replace;

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{BinOp, ExprId, ExprKind, Mode, PatId, PatKind, StmtId, StmtKind};

use super::check::Walker;
use super::consume::Movable;
use super::place::place_of;
use super::state::{LoopSum, Paths, Releases, Trail};
use super::walk::Pos;
use super::write::How;
use crate::Kind;
use crate::binding::LitClass;
use crate::binding::{Head, HeadRow};
use crate::body::{DropPoint, Dropped, LocalId, LocalKind};
use crate::names::body::Origin;
use crate::tails::literal_true;

/// A walk's state, the innermost loop it is in, and the items of the
/// scopes it is in (innermost last): the bindings declared in its blocks,
/// which leave the table at the end of their block (no name reads them
/// after it: the table stays small), the parameters under them.
pub(super) struct Run {
    pub(super) cur: Trail,
    exits: Exits,
    declared: Vec<Item>,
}

/// What a scope or an exit leaves (R-32, §12.2): a binding; a value
/// evaluated at a consuming position that waits for the operands after it
/// (A-1); the rest of the iterated value of an owned `for` (S-1037).
#[derive(Clone, Copy)]
enum Item {
    Local(LocalId),
    Value(ExprId),
    IterRest(ExprId),
}

/// The paths from the head of a loop (at the mark `at`) to its exit (`brk`:
/// the end of the condition, the `break`s) and to its back edge (`cont`:
/// the end of the body, the `continue`s); the first item a `break` and a
/// `continue` leave (`from`: the rest of an owned `for` is the `break`'s only).
struct Exits {
    brk: Paths,
    cont: Paths,
    at: usize,
    from: (usize, usize),
}

impl Run {
    pub(super) fn new() -> Self {
        Run::with(Vec::new())
    }

    /// The walk of a body from its start, its parameters `params` in its
    /// outermost scope (which a `return` and a `?` leave).
    pub(super) fn with(params: Vec<LocalId>) -> Self {
        let exits = Exits { brk: Paths::none(), cont: Paths::none(), at: 0, from: (0, 0) };
        Run { cur: Trail::new(), exits, declared: params.into_iter().map(Item::Local).collect() }
    }

    fn declare(&mut self, l: LocalId) {
        self.cur.declare(l);
        self.declared.push(Item::Local(l));
    }

    /// The items after the first `outer` leave: their block, arm or
    /// consumption ended, and the bindings the table.
    pub(super) fn forget(&mut self, outer: usize) {
        for item in self.declared.split_off(outer) {
            if let Item::Local(l) = item {
                self.cur.change(l, |d| d.forget(l));
            }
        }
    }

    /// The number of the items: where the values that wait for a consumer start.
    pub(super) fn items(&self) -> usize {
        self.declared.len()
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
                self.ends(r, outer, ast.expr(e).span);
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
                    self.ends(r, outer, ast.expr(arm.body).span);
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
            // The value, then the target (§3.5), which it waits for (A-1).
            StmtKind::Assign { target, value } => {
                let base = r.items();
                self.expr(r, *value, Pos::Value);
                self.waits(r, *value, Pos::Value);
                self.write_place(r, *target, How::Assign);
                r.forget(base);
            }
            StmtKind::For { pat, moved, iter, body } => {
                let range = matches!(ast.expr(*iter).kind, ExprKind::Range(_));
                let head = self.head_pos(Head::For(s), Pos::Arg(Mode::Borrow));
                match moved {
                    // S-362: a range has no value to consume (§7).
                    Some(m) if range => {
                        let message = "a range has no value to consume: `move` is not written on it (§7)";
                        let d = Diagnostic::new(Stage::Modes, Code::E0703, ast.expr(*iter).span, message);
                        self.report(d.with_fix(self.unmark(m.file, m.start, "move")));
                        self.expr(r, *iter, Pos::Read);
                    }
                    Some(m) => self.consume(r, *iter, Pos::Own, Some(m.start)),
                    None => {
                        if head != Pos::Own {
                            self.view_of_inout(*iter, [*pat]);
                        }
                        self.expr(r, *iter, head)
                    }
                }
                // The value an owned `for` iterates (S-1037), not Copy.
                let ty = self.info.expr_types.get(iter).copied().filter(|_| head == Pos::Own && !range);
                let rest = ty.is_some_and(|t| self.kind_of(t) != Some(Kind::Copy)).then_some(*iter);
                let mut held = self.frame(Head::For(s));
                self.holding(&mut held, |w| w.run_loop(r, s, (None, Some(*pat), rest, *body)));
            }
            // A `while true` with no `break` is left by no path (S-1042: `iterate`).
            StmtKind::While { cond, body } => self.run_loop(r, s, (Some(*cond), None, None, *body)),
            StmtKind::Break => self.leave(r, false, ast.stmt(s).span),
            StmtKind::Continue => self.leave(r, true, ast.stmt(s).span),
            StmtKind::Return(x) => {
                if let Some(x) = x {
                    self.expr(r, *x, Pos::Return);
                }
                self.drops(r, 0, ast.stmt(s).span, true);
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
                let (back, leaves) = (run.cur.state().clone(), run.exits.brk.reaches() || run.exits.cont.reaches());
                let sum = LoopSum { exit: LoopSum::head(&back).then(&exit), back, leaves };
                self.m.loops.insert(s, sum.clone());
                sum
            }
        };
        // One whose condition leaves the loop around is walked, its paths to that loop's exits too.
        if self.reports || sum.leaves {
            r.cur.then(&LoopSum::head(&sum.back));
            self.iterate(r, parts);
        } else {
            r.cur.then(&sum.exit);
        }
    }

    /// One iteration of a loop from its head in `r`, which it leaves at the
    /// exit (the end of the condition of a `while` but the literal `true`,
    /// S-1042; the head of a `for`; a `break`); the paths from the head to
    /// the back edge (the end of the body, a `continue`). A `for` declares
    /// its pattern at each iteration (R-29), whose bindings end with it
    /// (R-32: their drop points); an owned one, the rest of the value it
    /// iterates `rest` in the scope a `break` leaves (S-1037).
    fn iterate(&mut self, r: &mut Run, (cond, pat, rest, body): Loop) -> Paths {
        let from = r.declared.len();
        r.declared.extend(rest.map(Item::IterRest));
        let (scope, at) = (r.declared.len(), r.cur.mark());
        // Out of the body: a `break` or a `continue` in it is the outer loop's (§7).
        if let Some(c) = cond {
            self.expr(r, c, Pos::Read);
        }
        let exits = Exits { brk: Paths::none(), cont: Paths::none(), at, from: (from, scope) };
        let outer = replace(&mut r.exits, exits);
        // The end of an owned `for` drops the container of its value (S-1037).
        if let Some(x) = rest {
            self.drops(r, from, self.ast.expr(x).span, false);
        }
        if !cond.is_some_and(|c| literal_true(self.ast, c)) {
            r.cur.join_into(r.exits.at, &mut r.exits.brk, false);
        }
        if let Some(p) = pat {
            self.declare(r, p);
        }
        self.expr(r, body, Pos::Read);
        self.ends(r, scope, self.ast.expr(body).span);
        r.forget(from);
        let Exits { brk, mut cont, at, .. } = replace(&mut r.exits, outer);
        r.cur.join_into(at, &mut cont, false);
        r.cur.settle(at, &brk);
        cont
    }

    /// A `break` (`back`: a `continue`) at `at`: the drop points of what it
    /// leaves, then the bindings declared in the loop leave the table with
    /// no other (`Trail::join_into`), and the state joins the loop's exit (or
    /// its back edge).
    fn leave(&mut self, r: &mut Run, back: bool, at: Span) {
        self.drops(r, if back { r.exits.from.1 } else { r.exits.from.0 }, at, true);
        let paths = if back { &mut r.exits.cont } else { &mut r.exits.brk };
        r.cur.join_into(r.exits.at, paths, true);
        r.cur.stop();
    }

    /// The drop points at the end of `scope`, of the items after the first
    /// `outer`: its bindings.
    pub(super) fn ends(&mut self, r: &Run, outer: usize, scope: Span) {
        self.drops(r, outer, Span::empty(scope.file, scope.end), false);
    }

    /// The drop points of the items after the first `from`, which the end
    /// of their scope or an exit at `at` (`exit`: a `return`, a `?`, a
    /// `break`, a `continue`) leaves (R-32, §12.2): each owned binding that
    /// may hold its value there, not Copy (surely if live on every path; of
    /// one released on every path, unless each release moves, S-1030); a
    /// value that waits (A-1), surely: it is made on every path to the
    /// exit; the rest of an owned `for` (S-1037), at its end (`iterate`)
    /// or left early; none where no path reaches (S-873). The one place
    /// that decides them.
    pub(super) fn drops(&mut self, r: &Run, from: usize, at: Span, exit: bool) {
        for i in from..r.declared.len() {
            let (what, sure, unless) = match r.declared[i] {
                Item::Local(l) => {
                    let local = &self.info.locals[l.0 as usize];
                    let lives = r.cur.state().lives(l).filter(|_| local.state.owned());
                    let Some((sure, unless)) = lives.filter(|_| self.kind_of(local.ty) != Some(Kind::Copy)) else {
                        continue;
                    };
                    (if exit { Dropped::Exit(l) } else { Dropped::End(l) }, sure, unless)
                }
                Item::Value(e) => (Dropped::Value(e), true, None),
                Item::IterRest(e) => (Dropped::IterRest { iter: e, early: exit }, true, None),
            };
            self.drop_point(r, at, what, (sure, unless));
        }
    }

    /// The operand `e`, walked at `pos` (of a call, a receiver, a literal or
    /// an assignment, whose consumer runs after the operands after it): its
    /// value waits there for them (A-1), until the consumer runs
    /// (`Run::forget`), if `pos` consumes and it is owned: an Affine place
    /// moved, a Dup value not Copy (released or copied, §5.2) that is no
    /// literal or static value with no drop (S-610, S-613), an Affine new
    /// value. The one place that decides it.
    pub(super) fn waits(&mut self, r: &mut Run, e: ExprId, pos: Pos) {
        let mut x = self.ast.without_parens(e);
        while let ExprKind::Move(y) = &self.ast.expr(x).kind {
            x = self.ast.without_parens(*y);
        }
        let Some(&ty) = self.info.expr_types.get(&x).filter(|_| pos.consumes()) else { return };
        let owned = match (self.kind_of(ty), place_of(self.ast, self.names, x)) {
            (Some(Kind::Shared), _) => !matches!(self.info.lits.get(&x), Some(LitClass::Static | LitClass::NoDrop)),
            (_, Some(p)) => self.movable(&p, ty) == Some(Movable::Owned),
            (kind, None) => kind == Some(Kind::Affine),
        };
        if owned {
            r.declared.push(Item::Value(x));
        }
    }

    /// The parameters of the body: its outermost scope ([`Run::with`]).
    pub(super) fn params(&self) -> Vec<LocalId> {
        let info = self.info;
        let params = (0..info.locals.len() as u32).map(LocalId);
        params
            .filter(|l| matches!(info.locals[l.0 as usize].kind, LocalKind::Param(_) | LocalKind::SelfParam(_)))
            .collect()
    }

    /// The end of the body `root` walked in `r`: the drop points of the
    /// parameters.
    pub(super) fn body_end(&mut self, r: &Run, root: ExprId) {
        self.ends(r, 0, self.ast.expr(root).span);
    }

    /// A drop point met by the walk that reports, where a path reaches;
    /// `unless`: the releases it is one only if one of them copies.
    pub(super) fn drop_point(&mut self, r: &Run, at: Span, what: Dropped, (sure, unless): (bool, Option<&Releases>)) {
        if self.reports && r.cur.state().reaches() {
            let closure = self.closure_in();
            if let Some(xs) = unless {
                self.m.unless.push((self.m.drops.len(), xs.iter().copied().collect()));
            }
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

/// The parts of a loop: the condition of a `while`, the pattern of a `for`
/// and the value an owned one iterates, the body.
type Loop = (Option<ExprId>, Option<PatId>, Option<ExprId>, ExprId);
