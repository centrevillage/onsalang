//! The walk of the clocks of a flow body (§11.3, W7-02 U2b): one walk of the
//! expressions with the rules of the clocks in one place (D-15), run in a
//! mode ([`Mode`]) per stage.
//!
//! - Stage 1 solves the `let`s: `Deps` finds the `let`s each reads, apart
//!   from the places whose clock is not of their operands (the arguments of
//!   a user's flow, the operand of `at`, the `d` and the `init` of a delay,
//!   §11.3 "読み方"), [`loops::components`] orders their loops, and `Solve`
//!   walks each component once, a loop with its own `let`s as ⊥, which gets
//!   the [`loop_clock`] of the join of its `let`s (§11.3, S-567 P3).
//! - Stage 2 (`Check`) walks the `let`s in their order and the output, with
//!   `^y` the value of stage 1, and records every clock. The checks of the
//!   flow rules go at its places in W7-02 U2b-2.
//!
//! Each expression is walked at most three times; the components are linear
//! in the reads (Tarjan), so the walk is linear in the body, with no bound of
//! rounds. Until U2b-2 the rate pass makes the tables, and a debug build
//! compares the walk with it ([`cross_check`]).

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::{Ast, MatchArm};

use super::loops;
use super::*;
use crate::clock::{self, ClockFrame, Ratio, delay_out, loop_clock, rebase};
use crate::names::body::BodyNames;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// Stage 1: the `let`s an expression reads, not through a cut place.
    Deps,
    /// Stage 1: the clock, a `let` of the loop being solved read as ⊥.
    Solve,
    /// Stage 2: the clock of every expression and local, recorded; ⊥ is a
    /// constant here.
    Check,
}

/// The clocks of a flow body the walk found.
#[derive(Debug, Clone)]
pub(super) struct Walked {
    /// Stage 1: the clock of each `let`, in the order of the text.
    pub(super) lets: Vec<Clock>,
    /// Stage 2: the clock of each `let`.
    pub(super) checked: Vec<Clock>,
    /// Stage 2: the clocks of the expressions and the locals.
    pub(super) info: ClockInfo,
}

pub(super) struct Walk<'a> {
    a: &'a Analysis,
    ast: &'a Ast,
    body: &'a BodyInfo,
    cx: &'a FlowCx,
    names: &'a BodyNames,
    calls: HashMap<ExprId, usize>,
    sample_rate: HashSet<ExprId>,
    mode: Mode,
    /// Stage 1: the clock of each `let`, ⊥ until its component is solved.
    lets: Vec<Option<Clock>>,
    /// The `let`s of the loop being solved, read as ⊥.
    solving: Vec<bool>,
    /// The `let`s in a loop, and whether the `let` walked now is one.
    looped: Vec<bool>,
    in_loop: bool,
    /// `Deps`: the `let`s read.
    deps: Vec<usize>,
    /// The clocks of the bindings of a `match` arm and of a `par~` index.
    scoped: HashMap<LocalId, Option<Clock>>,
    checked: Vec<Option<Clock>>,
    out: ClockInfo,
}

/// Runs the two stages over the body of the flow `id`.
pub(super) fn walk(a: &Analysis, ast: &Ast, id: DefId, body: &BodyInfo, cx: &FlowCx) -> Walked {
    let span = a.def(id).as_flow().map(|f| ast.expr(f.body).span);
    let (Some(names), Some(decl)) = (a.names.get(&id), a.def(id).as_flow()) else {
        onsa_diag::internal::bug(span, "the walk of the clocks of a flow with no record of its names")
    };
    if decl.inputs.len() != cx.inputs.len() {
        onsa_diag::internal::bug(span, "the inputs of the flow and of its body differ");
    }
    let n = cx.pending.len();
    let mut w = Walk {
        a,
        ast,
        body,
        cx,
        names,
        calls: cx.calls.iter().enumerate().map(|(i, c)| (c.expr, i)).collect(),
        sample_rate: cx.sample_rate_calls.iter().copied().collect(),
        mode: Mode::Deps,
        lets: vec![None; n],
        solving: vec![false; n],
        looped: vec![false; n],
        in_loop: false,
        deps: Vec::new(),
        scoped: HashMap::default(),
        checked: vec![None; n],
        out: ClockInfo::default(),
    };
    for ((l, _), input) in cx.inputs.iter().zip(&decl.inputs) {
        w.out.locals.insert(*l, input.api_clock());
    }
    w.solve();
    w.check();
    let solved = |c: Option<Clock>| c.unwrap_or_else(|| onsa_diag::internal::bug(span, "a `let` left unsolved"));
    Walked {
        lets: w.lets.into_iter().map(solved).collect(),
        checked: w.checked.into_iter().map(solved).collect(),
        info: w.out,
    }
}

impl Walk<'_> {
    /// Stage 1: the reads of each `let`, then its component.
    fn solve(&mut self) {
        let mut deps = Vec::with_capacity(self.cx.pending.len());
        for p in &self.cx.pending {
            self.expr(p.init);
            let mut d = std::mem::take(&mut self.deps);
            d.sort_unstable();
            d.dedup();
            deps.push(d);
        }
        self.mode = Mode::Solve;
        for scc in loops::components(&deps) {
            for &k in &scc.lets {
                (self.looped[k], self.solving[k]) = (scc.looped, scc.looped);
            }
            self.in_loop = scc.looped;
            let ops: Vec<Option<Clock>> = scc.lets.iter().map(|&k| self.expr(self.cx.pending[k].init)).collect();
            let first = self.cx.pending[scc.lets[0]].init;
            let c = if scc.looped { loop_clock(self.join(first, &ops)) } else { ops[0].unwrap_or(Clock::Const) };
            for &k in &scc.lets {
                (self.lets[k], self.solving[k]) = (Some(c), false);
            }
        }
    }

    /// Stage 2: the `let`s in their order, then the output.
    fn check(&mut self) {
        self.mode = Mode::Check;
        for (k, p) in self.cx.pending.iter().enumerate() {
            self.in_loop = self.looped[k];
            let c = self.expr(p.init).unwrap_or(Clock::Const);
            self.checked[k] = Some(c);
            for &l in &p.locals {
                self.out.locals.insert(l, c);
            }
        }
        if let Some(out) = self.cx.output {
            self.in_loop = false;
            self.expr(out);
        }
    }

    fn span(&self, e: ExprId) -> Option<Span> {
        Some(self.ast.expr(e).span)
    }

    /// The clock of `e` (⊥ is `None`), recorded at `Check`.
    fn expr(&mut self, e: ExprId) -> Option<Clock> {
        let c = self.rule(e);
        if self.mode != Mode::Check {
            return c;
        }
        let c = c.unwrap_or(Clock::Const);
        self.out.exprs.insert(e, c);
        Some(c)
    }

    /// A place whose clock is not its operand's: walked at `Check` only.
    fn cut(&mut self, e: ExprId) {
        if self.mode == Mode::Check {
            self.expr(e);
        }
    }

    /// The join of the clocks of operands of `e` (a constant of none). A
    /// clash is no error of W7-02, whose ticks are all the `sample` of the
    /// body: W7-09 reports it (E0815).
    fn join(&self, e: ExprId, ops: &[Option<Clock>]) -> Option<Clock> {
        if ops.is_empty() {
            return Some(Clock::Const);
        }
        clock::join(ops).unwrap_or_else(|c| {
            let msg = format!("the clocks of the operands {:?} and {:?} clash, which W7-09 reports", c.first, c.second);
            onsa_diag::internal::bug(self.span(e), msg)
        })
    }

    fn join_of(&mut self, e: ExprId, es: impl IntoIterator<Item = ExprId>) -> Option<Clock> {
        let ops: Vec<Option<Clock>> = es.into_iter().map(|x| self.expr(x)).collect();
        self.join(e, &ops)
    }

    /// The rule of the clock of each form of expression (§11.3).
    fn rule(&mut self, e: ExprId) -> Option<Clock> {
        let ast = self.ast;
        match &ast.expr(e).kind {
            ExprKind::Lit(_)
            | ExprKind::Hole
            | ExprKind::Error
            | ExprKind::Range(_)
            | ExprKind::Closure { .. }
            | ExprKind::Handle { .. } => Some(Clock::Const),
            ExprKind::Path(_) | ExprKind::Feedback(_) => self.name(e),
            ExprKind::Field { base, .. } if !self.body.targets.contains_key(&e) => self.expr(*base),
            ExprKind::Field { .. } => self.name(e),
            ExprKind::Paren(x)
            | ExprKind::Cast { expr: x, .. }
            | ExprKind::Unary { expr: x, .. }
            | ExprKind::Move(x)
            | ExprKind::Try(x)
            | ExprKind::Unsafe(x)
            | ExprKind::TupleIndex { base: x, .. }
            | ExprKind::TypeArgs { base: x, .. }
            | ExprKind::Repeat { elem: x, .. } => self.expr(*x),
            ExprKind::At { expr, .. } => {
                self.cut(*expr);
                let Some(k) = self.names.clocks.get(&e) else {
                    onsa_diag::internal::bug(self.span(e), "an `at` whose clock the names stage did not record")
                };
                Some(k.clock())
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) => self.join_of(e, es.iter().copied()),
            ExprKind::Struct { fields, .. } => self.join_of(e, fields.iter().map(|(_, x)| *x)),
            ExprKind::Block(b) => match b.tail {
                Some(t) => self.expr(t),
                None => Some(Clock::Const),
            },
            // E0200 of W7-06 in the rate pass: the walk stops at them.
            ExprKind::If { tilde: Some(_), .. } | ExprKind::Match { tilde: Some(_), .. } => Some(Clock::Error),
            ExprKind::If { cond, then, else_, .. } => self.join_of(e, [*cond, *then].into_iter().chain(*else_)),
            ExprKind::Match { scrutinee, arms, .. } => self.match_arms(e, *scrutinee, arms),
            ExprKind::Binary { lhs: x, rhs: y, .. } | ExprKind::Index { base: x, index: y } => {
                self.join_of(e, [*x, *y])
            }
            ExprKind::Par { body, .. } => {
                let Some(&(var, ..)) = self.cx.pars.get(&e) else {
                    onsa_diag::internal::bug(self.span(e), "a `par~` the check did not record")
                };
                self.bind_local(var, Some(Clock::Init));
                let b = self.expr(*body);
                self.join(e, &[b, Some(Clock::Init)])
            }
            ExprKind::Call { callee, args, .. } => self.call(e, *callee, args),
        }
    }

    /// A name or a `^y` (§11.3): the clock of its local, else a constant.
    fn name(&mut self, e: ExprId) -> Option<Clock> {
        match self.body.targets.get(&e) {
            Some(Target::Local(id)) => self.local(e, *id),
            Some(Target::Fn { .. } | Target::Method { .. } | Target::Value) => {
                onsa_diag::internal::bug(self.span(e), "a function as a value in a flow body, E0806 of the names stage")
            }
            Some(Target::Const { .. } | Target::ConstParam(_) | Target::Variant { .. } | Target::Panic) | None => {
                Some(Clock::Const)
            }
        }
    }

    fn local(&mut self, e: ExprId, id: LocalId) -> Option<Clock> {
        if let Some(&k) = self.cx.let_of_local.get(&id) {
            let feedback = matches!(self.ast.expr(e).kind, ExprKind::Feedback(_));
            return match self.mode {
                Mode::Deps => {
                    self.deps.push(k);
                    None
                }
                Mode::Solve if self.solving[k] => None,
                Mode::Check if !feedback => self.checked[k].or(self.lets[k]),
                Mode::Solve | Mode::Check => self.lets[k],
            };
        }
        if let Some(&c) = self.scoped.get(&id) {
            return c;
        }
        match self.out.locals.get(&id) {
            Some(&c) => Some(c),
            None => onsa_diag::internal::bug(self.span(e), format!("the local {id:?} has no clock")),
        }
    }

    fn bind_local(&mut self, l: LocalId, c: Option<Clock>) {
        self.scoped.insert(l, c);
        if self.mode == Mode::Check {
            self.out.locals.insert(l, c.unwrap_or(Clock::Const));
        }
    }

    /// `match` (§11.3): the scrutinee, the guards and the bodies; the
    /// bindings of a pattern have the clock of the scrutinee.
    fn match_arms(&mut self, e: ExprId, scrutinee: ExprId, arms: &[MatchArm]) -> Option<Clock> {
        let s = self.expr(scrutinee);
        let mut ops = vec![s];
        for arm in arms {
            self.bind_pat(arm.pat, s);
            ops.extend(arm.guard.map(|g| self.expr(g)));
            ops.push(self.expr(arm.body));
        }
        self.join(e, &ops)
    }

    fn bind_pat(&mut self, p: PatId, c: Option<Clock>) {
        let ast = self.ast;
        match &ast.pat(p).kind {
            PatKind::Bind(_) => match self.body.pat_locals.get(&p) {
                Some(&l) => self.bind_local(l, c),
                None if self.body.pat_consts.contains_key(&p) || self.body.pat_ctors.contains_key(&p) => {}
                None => onsa_diag::internal::bug(Some(ast.pat(p).span), "a binding with no local"),
            },
            PatKind::TupleStruct { elems: ps, .. } | PatKind::Tuple(ps) | PatKind::Or(ps) => {
                ps.iter().for_each(|&q| self.bind_pat(q, c));
            }
            PatKind::Struct { fields, .. } => fields.iter().for_each(|&(_, q)| self.bind_pat(q, c)),
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
        }
    }

    /// A call (§11.3, §11.4, §11.5).
    fn call(&mut self, e: ExprId, callee: ExprId, args: &[Arg]) -> Option<Clock> {
        if let Some(&i) = self.calls.get(&e) {
            let call = &self.cx.calls[i];
            return match call.kind {
                NodeKind::Instance(d) => {
                    args.iter().for_each(|x| self.cut(x.expr));
                    let Some(f) = self.a.def(d).as_flow() else {
                        onsa_diag::internal::bug(self.span(e), "an instance of no flow")
                    };
                    Some(rebase(f.out_clock, ClockFrame { ratio: Ratio(0) }))
                }
                NodeKind::Delay(..) => {
                    let Some(&first) = call.args.first() else {
                        onsa_diag::internal::bug(self.span(e), "a delay with no argument")
                    };
                    let c = self.expr(first);
                    args.iter().filter(|x| x.expr != first).for_each(|x| self.cut(x.expr));
                    delay_out(c, self.in_loop)
                }
            };
        }
        if self.sample_rate.contains(&e) {
            return Some(Clock::Init);
        }
        let target = self.body.targets.get(&e);
        let receiver = crate::names::body::receiver(self.ast, callee)
            .filter(|b| self.body.expr_types.contains_key(b) && !matches!(target, Some(Target::Fn { .. })));
        let ops: Vec<Option<Clock>> =
            receiver.into_iter().chain(args.iter().map(|x| x.expr)).map(|x| self.expr(x)).collect();
        let r = self.join(e, &ops);
        match target {
            Some(Target::Variant { .. } | Target::Panic) => r,
            Some(Target::Value) => onsa_diag::internal::bug(self.span(e), "a call of a function value in a flow body"),
            // Provisional (W9-03 takes it off, §11.3 "定数のクロックの式"): a
            // call of constants alone is at `init` until they are evaluated.
            _ => self.join(e, &[r, Some(Clock::Init)]),
        }
    }
}

impl Walked {
    /// After stage 2 with no error: each `let` has the clock of stage 1,
    /// past one in error.
    pub(super) fn post_check(&self, cx: &FlowCx) {
        let lets = self.lets.iter().zip(&self.checked).zip(&cx.pending);
        for ((&l, &c), p) in lets.filter(|((l, _), _)| **l != Clock::Error) {
            if l != c {
                onsa_diag::internal::bug(Some(p.span), format!("the `let` is {l:?} in stage 1 and {c:?} in stage 2"));
            }
        }
    }
}

#[cfg(test)]
thread_local! {
    /// The walks of the flows a test checked, and whether each was compared.
    pub(crate) static WALKED: std::cell::RefCell<Vec<(DefId, Walked, bool)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// A debug build: the walk against the tables of the rate pass (W7-02
/// U2b-1), when the rate pass gave no diagnostic and no input is in error.
/// The clocks the walk has in error are not compared (a call of a flow whose
/// output is in error). A difference is an internal error at its place.
pub(super) fn cross_check(a: &Analysis, ast: &Ast, id: DefId, body: &BodyInfo, cx: &FlowCx, info: &FlowInfo) {
    let walked = walk(a, ast, id, body, cx);
    let inputs_ok = a.def(id).as_flow().is_some_and(|f| f.inputs.iter().all(|i| i.clock != Clock::Error));
    let compared = info.complete && inputs_ok;
    if compared {
        walked.post_check(cx);
        compare(ast, body, info, &walked);
    }
    #[cfg(test)]
    WALKED.with(|w| w.borrow_mut().push((id, walked, compared)));
}

fn compare(ast: &Ast, body: &BodyInfo, info: &FlowInfo, walked: &Walked) {
    let new = &walked.info;
    let mut exprs: Vec<_> = info.clocks.exprs.iter().collect();
    exprs.sort_by_key(|(e, _)| e.0);
    for (&e, &old) in exprs {
        let x = ast.expr(e);
        let kind = format!("{:?}", x.kind);
        let kind = kind.split(|c: char| !c.is_alphanumeric()).next().unwrap_or("");
        match new.exprs.get(&e) {
            None => onsa_diag::internal::bug(
                Some(x.span),
                format!("the walk of the clocks has no clock of the {kind} expression, {old:?} in the rate pass"),
            ),
            Some(&c) if c != old && c != Clock::Error => onsa_diag::internal::bug(
                Some(x.span),
                format!("the {kind} expression is {old:?} in the rate pass and {c:?} in the walk of the clocks"),
            ),
            Some(_) => {}
        }
    }
    let mut locals: Vec<_> = info.clocks.locals.iter().collect();
    locals.sort_by_key(|(l, _)| l.0);
    for (&l, &old) in locals {
        let span = body.locals.get(l.0 as usize).map(|x| x.span);
        match new.locals.get(&l) {
            Some(&c) if c == old || c == Clock::Error => {}
            c => onsa_diag::internal::bug(
                span,
                format!("the local {l:?} is {old:?} in the rate pass and {c:?} in the walk of the clocks"),
            ),
        }
    }
    if info.lets.len() != walked.lets.len() {
        onsa_diag::internal::bug(None, "the rate pass and the walk of the clocks have other `let`s");
    }
    for (old, &c) in info.lets.iter().zip(&walked.lets) {
        if c != old.clock && c != Clock::Error {
            let msg = format!("the `let` is {:?} in the rate pass and {c:?} in the walk of the clocks", old.clock);
            onsa_diag::internal::bug(Some(old.span), msg);
        }
    }
}

#[cfg(test)]
mod tests;
