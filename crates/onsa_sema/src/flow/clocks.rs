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
//!   `^y` the value of stage 1, records every clock, checks the flow rules
//!   ([`checks`]) all through, keeping the first diagnostic in the order of
//!   the file (§18.1), and records the nodes and their owners
//!   ([`NodeBuilder`]).
//!
//! Each expression is walked at most three times; the components are linear
//! in the reads (Tarjan), so the walk is linear in the body, with no bound of
//! rounds. [`finish_flow`] makes the tables of the flow from the walk and the
//! state marking (`reads`), and the plan of the nodes (`plan`) of a walk with
//! no diagnostic.

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::{Ast, BinOp, MatchArm};

use super::loops;
use super::nodes::{NodeBuilder, Recorded};
use super::plan::Owner;
use super::*;
use crate::clock::{self, ClockFrame, Ratio, delay_out, loop_clock, rebase};
use crate::names::body::BodyNames;

mod checks;

/// After type checking: the walk of the clocks, the state marking and the
/// tables of the flow `id` (§11.2–§11.5). The diagnostic is the first in
/// the order of the file of the walk and of the marking, else a call of an
/// `inout self` method (the modes stage comes after the flow checks, §18.1);
/// with one, the tables are partial.
pub(crate) fn finish_flow(a: &mut Analysis, module: &Module, id: DefId, body: BodyInfo, fcx: FlowCx) {
    let _flow = onsa_diag::timing::phase(onsa_diag::timing::Phase::Flow);
    let mut info = FlowInfo {
        inputs: fcx.inputs.clone(),
        sample_rate_calls: fcx.sample_rate_calls.clone(),
        output: fcx.output,
        complete: false,
        ..Default::default()
    };
    if !body.complete {
        info.body = body;
        a.flows.insert(id, info);
        return;
    }
    let error = a.types.error();
    let (ast, text) = (&module.parsed.ast, module.text.as_str());
    let mut w = walk(a, ast, text, id, &body, &fcx, error);
    if w.diag.is_none() {
        w.post_check(&fcx);
    }
    let ty = |p: &PendingLet| body.expr_types.get(&p.init).copied().unwrap_or(error);
    let lets = fcx.pending.iter().zip(&w.checked);
    let lets = lets.map(|(p, &clock)| FlowLet {
        pat: p.pat,
        locals: p.locals.clone(),
        name: p.name.clone(),
        ty: ty(p),
        clock,
        init: p.init,
        span: p.span,
        state: false,
    });
    info.lets = lets.collect();
    let m = super::reads::mark_all(ast, text, &body, &fcx, &w, &info.lets);
    (info.read_at, info.sample_rate_at) = (m.read_at, m.sample_rate_at);
    info.complete = w.diag.is_none() && m.diag.is_none() && w.inout_call.is_none();
    #[cfg(test)]
    WALKED.with(|x| x.borrow_mut().push((id, w.clone(), info.complete)));
    info.clocks = std::mem::take(&mut w.info);
    info.body = body;
    let state: Vec<bool> = info.lets.iter().map(|l| l.locals.iter().any(|&v| info.stored(Kept::Local(v)))).collect();
    info.lets.iter_mut().zip(state).for_each(|(l, s)| l.state = s);
    if info.complete {
        let recorded = std::mem::take(&mut w.recorded);
        super::plan::build(&mut info, recorded, &w);
    }
    let mut diag = w.diag;
    if let Some(d) = m.diag {
        keep_first(&mut diag, d);
    }
    let diag = diag.or(w.inout_call);
    if let Some(d) = diag {
        a.diagnostics.push(d);
    }
    a.flows.insert(id, info);
}

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

/// The clocks of a flow body the walk found, its first diagnostic and the
/// record of its nodes.
#[derive(Debug, Clone)]
pub(super) struct Walked {
    /// Stage 1: the clock of each `let`, in the order of the text.
    pub(super) lets: Vec<Clock>,
    /// Stage 2: the clock of each `let`.
    pub(super) checked: Vec<Clock>,
    /// Stage 2: the clocks of the expressions and the locals.
    pub(super) info: ClockInfo,
    /// Stage 2: the clocks of the delays and the instance calls in the order
    /// of the text (each before its arguments'), flat: the nodes of a `par~`
    /// body too, and not the `par~` itself. Read in the walk and the marking
    /// only, which run with a diagnostic too; the plan has the clocks of its
    /// nodes.
    pub(super) nodes: Vec<NodeClock>,
    /// A delay or an instance call → its index in `nodes`.
    pub(super) node_of: HashMap<ExprId, usize>,
    /// Stage 2: the first diagnostic in the order of the file.
    pub(super) diag: Option<Diagnostic>,
    /// Stage 2: the first call of an `inout self` method (E0713, §5.2),
    /// reported when the flow checks find no error.
    pub(super) inout_call: Option<Diagnostic>,
    /// Stage 2: the calls of a function that is not `rt` with values at
    /// `init` (§11.5), which the marking reads (E0200 at a later stage).
    pub(super) non_rt: HashSet<ExprId>,
    /// Stage 2: the nodes and their owners, for the plan.
    pub(super) recorded: Vec<Recorded>,
}

pub(super) struct Walk<'a> {
    a: &'a Analysis,
    ast: &'a Ast,
    /// The text of the module, for the `found` of a diagnostic.
    text: &'a str,
    /// The error type, of an expression with no type.
    error: TyId,
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
    node_clocks: Vec<NodeClock>,
    node_of: HashMap<ExprId, usize>,
    /// Nonzero inside a branch of `if` and `match`, a guard and the right
    /// side of `&&` / `||` (K-08, `StatefulInBranch`).
    branch: u32,
    diag: Option<Diagnostic>,
    inout_call: Option<Diagnostic>,
    non_rt: HashSet<ExprId>,
    recorder: NodeBuilder,
}

/// Runs the two stages over the body of the flow `id` of the module of
/// `ast` and `text`; `error` is the error type.
pub(super) fn walk(
    a: &Analysis,
    ast: &Ast,
    text: &str,
    id: DefId,
    body: &BodyInfo,
    cx: &FlowCx,
    error: TyId,
) -> Walked {
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
        text,
        error,
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
        node_clocks: Vec::new(),
        node_of: HashMap::default(),
        branch: 0,
        diag: None,
        inout_call: None,
        non_rt: HashSet::default(),
        recorder: NodeBuilder::new(&cx.pending),
    };
    for (l, input) in cx.inputs.iter().zip(&decl.inputs) {
        w.out.locals.insert(*l, input.api_clock());
    }
    w.solve();
    w.check();
    let solved = |c: Option<Clock>| c.unwrap_or_else(|| onsa_diag::internal::bug(span, "a `let` left unsolved"));
    Walked {
        lets: w.lets.into_iter().map(solved).collect(),
        checked: w.checked.into_iter().map(solved).collect(),
        info: w.out,
        diag: w.diag,
        inout_call: w.inout_call,
        non_rt: w.non_rt,
        nodes: w.node_clocks,
        node_of: w.node_of,
        recorded: w.recorder.finish(),
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

    /// Stage 2: the `let`s in their order, each checked after its
    /// initializer, then the output.
    fn check(&mut self) {
        self.mode = Mode::Check;
        let cx = self.cx;
        for (k, p) in cx.pending.iter().enumerate() {
            self.recorder.owner(Owner::Let(k as u32));
            self.in_loop = self.looped[k];
            let c = self.expr(p.init).unwrap_or(Clock::Const);
            self.checked[k] = Some(c);
            for &l in &p.locals {
                self.out.locals.insert(l, c);
            }
            self.check_let(p);
        }
        if let Some(out) = self.cx.output {
            self.recorder.owner(Owner::Output);
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

    /// A place whose clock is not its operand's: walked at `Check` only,
    /// which gives its clock to check.
    fn cut(&mut self, e: ExprId) -> Option<Clock> {
        if self.mode == Mode::Check { self.expr(e) } else { None }
    }

    /// `f` walking a branch (K-08).
    fn in_branch<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.branch += 1;
        let r = f(self);
        self.branch -= 1;
        r
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
                let c = self.cut(*expr);
                let Some(k) = self.names.clocks.get(&e) else {
                    onsa_diag::internal::bug(self.span(e), "an `at` whose clock the names stage did not record")
                };
                self.check_at(e, *expr, c, k.clock());
                Some(k.clock())
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) => self.join_of(e, es.iter().copied()),
            ExprKind::Struct { fields, .. } => self.join_of(e, fields.iter().map(|(_, x)| *x)),
            ExprKind::Block(b) => match b.tail {
                Some(t) => self.expr(t),
                None => Some(Clock::Const),
            },
            // E0200 of W7-06: the walk stops at them.
            ExprKind::If { tilde: Some(t), .. } => self.tilde(*t, "if~"),
            ExprKind::Match { tilde: Some(t), .. } => self.tilde(*t, "match~"),
            ExprKind::If { cond, then, else_, .. } => {
                let mut ops = vec![self.expr(*cond)];
                self.in_branch(|w| ops.extend([Some(*then), *else_].into_iter().flatten().map(|x| w.expr(x))));
                self.join(e, &ops)
            }
            ExprKind::Match { scrutinee, arms, .. } => self.match_arms(e, *scrutinee, arms),
            ExprKind::Binary { op, lhs, rhs, .. } => {
                let l = self.expr(*lhs);
                let r = match op {
                    BinOp::And | BinOp::Or => self.in_branch(|w| w.expr(*rhs)),
                    _ => self.expr(*rhs),
                };
                self.join(e, &[l, r])
            }
            ExprKind::Index { base, index } => self.join_of(e, [*base, *index]),
            ExprKind::Par { body, .. } => self.par(e, *body),
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

    /// `match` (§11.3): the scrutinee, the guards and the bodies, these two
    /// in a branch; the bindings of a pattern have the clock of the
    /// scrutinee.
    fn match_arms(&mut self, e: ExprId, scrutinee: ExprId, arms: &[MatchArm]) -> Option<Clock> {
        let s = self.expr(scrutinee);
        let mut ops = vec![s];
        for arm in arms {
            self.bind_pat(arm.pat, s);
            self.in_branch(|w| {
                ops.extend(arm.guard.map(|g| w.expr(g)));
                ops.push(w.expr(arm.body));
            });
        }
        self.join(e, &ops)
    }

    /// `par~` (§11.5): its index at `init`, its body, and its node.
    fn par(&mut self, e: ExprId, body: ExprId) -> Option<Clock> {
        let Some(&(var, from, to)) = self.cx.pars.get(&e) else {
            onsa_diag::internal::bug(self.span(e), "a `par~` the check did not record")
        };
        if !self.stateful_here(e) {
            return Some(Clock::Error);
        }
        self.bind_local(var, Some(Clock::Init));
        let (check, span) = (self.mode == Mode::Check, self.ast.expr(e).span);
        if check {
            self.recorder.enter_par(e, span, var, from, to, body);
        }
        let b = self.expr(body);
        if check {
            self.recorder.leave_par(e, span);
        }
        self.join(e, &[b, Some(Clock::Init)])
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
            let cx = self.cx;
            return self.node(e, &cx.calls[i]);
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
        if let Some(Target::Fn { def, .. } | Target::Method { def, .. }) = target
            && !self.check_fn_call(e, *def, receiver.is_some(), &ops, r)
        {
            return Some(Clock::Error);
        }
        match target {
            Some(Target::Variant { .. } | Target::Panic) => r,
            Some(Target::Value) => onsa_diag::internal::bug(self.span(e), "a call of a function value in a flow body"),
            // Provisional (W9-03 takes it off, §11.3 "定数のクロックの式"): a
            // call of constants alone is at `init` until they are evaluated.
            _ => self.join(e, &[r, Some(Clock::Init)]),
        }
    }

    /// A delay or an instance call `call` at `e` (§11.4, §11.5): its clock,
    /// its checks, and at `Check` its node and the clocks its arguments are
    /// read at, in the order of the text (its slot before its arguments').
    fn node(&mut self, e: ExprId, call: &NodeCall) -> Option<Clock> {
        if !self.stateful_here(e) {
            return Some(Clock::Error);
        }
        let slot = (self.mode == Mode::Check).then(|| {
            self.node_of.insert(e, self.node_clocks.len());
            self.node_clocks.push(NodeClock { clock: Clock::Error, args: Vec::new() });
            self.node_clocks.len() - 1
        });
        let (clock, args) = match call.kind {
            NodeKind::Instance(d) => self.instance(e, d, call),
            NodeKind::Delay(delay, _) => self.delay(e, delay, call),
        };
        if let Some(k) = slot {
            let span = self.ast.expr(e).span;
            if let Err(d) = self.recorder.node(self.a, self.body, e, call, span) {
                let found = self.src(span);
                self.report(d.with_found(found));
            }
            self.node_clocks[k] = NodeClock { clock: clock.unwrap_or(Clock::Const), args };
        }
        clock
    }

    /// `g~(args)` (§11.5): each argument read at the clock of its input in
    /// the frame of the call, and the output of `g` in it.
    fn instance(&mut self, e: ExprId, g: DefId, call: &NodeCall) -> (Option<Clock>, Vec<ArgRead>) {
        let Some(f) = self.a.def(g).as_flow() else { onsa_diag::internal::bug(self.span(e), "an instance of no flow") };
        if f.inputs.len() != call.args.len() {
            onsa_diag::internal::bug(self.span(e), "an instance with other arguments than its inputs");
        }
        let frame = ClockFrame { ratio: Ratio(0) };
        let mut reads = Vec::new();
        for (&x, input) in call.args.iter().zip(&f.inputs) {
            let at = rebase(input.api_clock(), frame);
            if let Some(c) = self.cut(x) {
                self.check_arg(x, c, at, input, g);
                reads.push(ArgRead { expr: x, at, lookback: false });
            }
        }
        (Some(rebase(f.out_clock, frame)), reads)
    }

    /// A delay (§11.4): its first argument, the `d` of `vdelay~` and its
    /// `init`, not its length, and the element type of `vdelay~`. With the
    /// E0813 of its first argument, it is in error (§18.1).
    fn delay(&mut self, e: ExprId, delay: Delay, call: &NodeCall) -> (Option<Clock>, Vec<ArgRead>) {
        let Some(&first) = call.args.first() else {
            onsa_diag::internal::bug(self.span(e), "a delay with no argument")
        };
        let c = self.expr(first);
        let held = c.filter(|_| self.checking()).is_none_or(|c| self.check_first(delay, first, c));
        if delay == Delay::Variable && self.checking() {
            self.check_float(e);
        }
        let d = call.d();
        if let Some(d) = d {
            self.cut(d);
        }
        if let Some(i) = call.init_expr
            && let Some(c) = self.cut(i)
        {
            self.check_init(delay, i, c);
        }
        let out = if held { delay_out(c, self.in_loop) } else { Some(Clock::Error) };
        let at = out.unwrap_or(Clock::Const);
        let reads = [Some(first), d].into_iter().flatten().map(|x| ArgRead { expr: x, at, lookback: x == first });
        let init = call.init_expr.map(|i| ArgRead { expr: i, at: Clock::Init, lookback: false });
        (out, reads.chain(init).collect())
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
    /// The walks of the flows a test checked, and whether each flow had no
    /// diagnostic.
    pub(crate) static WALKED: std::cell::RefCell<Vec<(DefId, Walked, bool)>> = const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(test)]
mod tests;
