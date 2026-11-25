//! The walk of the clocks of a flow body (§11.3, W7-02 U2b): one walk of the
//! expressions with the rules of the clocks in one place (D-15), run in a
//! mode ([`Mode`]) per stage.
//!
//! - Stage 1 solves the `let`s: `Deps` finds the `let`s each reads, apart
//!   from the places whose clock is not of their operands (the arguments of
//!   a user's flow, the operand of `at`, the `d` and the `init` of a delay,
//!   §11.3 "読み方"), [`loops::components`] orders their loops, and `Solve`
//!   walks each component once, a loop with its own `let`s as ⊥, which gets
//!   the [`loop_clock`] of the join of its `let`s (§11.3, S-567 P3). The
//!   checks that give a clock in error decide it in every mode and report at
//!   `Check` only (R-496), so a `^y` of a `let` in error is in error; of
//!   operands that read a ⊥ they decide nothing in stage 1 ([`Walk::bottoms`]).
//! - Stage 2 (`Check`) walks the `let`s in their order and the output, with
//!   `^y` the value of stage 1, records every clock, checks the flow rules
//!   ([`checks`]) all through, keeping the first diagnostic in the order of
//!   the file (§18.1), and records the nodes and their owners
//!   ([`NodeBuilder`]), and gives each value of `sample_tick()` the clock of
//!   the place that uses it ([`Walk::settle`]).
//!
//! Each expression is walked at most three times; the components are linear
//! in the reads (Tarjan), so the walk is linear in the body, with no bound of
//! rounds. [`finish_flow`] makes the tables of the flow from the walk and the
//! state marking (`reads`), and the plan of the nodes (`plan`) of a walk with
//! no diagnostic.

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::{Ast, BinOp, MatchArm};

use super::lift::{self, Stmt};
use super::loops;
use super::nodes::{NodeBuilder, Recorded};
use super::plan::bounds::Ports;
use super::plan::{Edge, Owner};
use super::*;
use crate::body::LocalKind;
use crate::clock::{self, ClockFrame, EventSrc, Ratio, delay_out, grounded, loop_clock, rebase, rooted};
use crate::names::body::BodyNames;

mod checks;
mod mix;
mod stages;
mod to_sample;

use checks::Branching;

/// After type checking: the walk of the clocks, the state marking and the
/// tables of the flow `id` (§11.2–§11.5). The diagnostic is the first in
/// the order of the file of the walk, of the marking and of the error the
/// check of the types held ([`FlowCx::held`]), else a call of an `inout
/// self` method (the modes stage comes after the flow checks, §18.1); with
/// one, the tables are partial. A body the check of the types did not end
/// has the held error only when that check reported none (a type error
/// comes first, §18.1; it stopped with no diagnostic at a name held as an
/// error).
pub(crate) fn finish_flow(
    a: &mut Analysis,
    flat: &[&Package],
    module: &Module,
    id: DefId,
    body: BodyInfo,
    mut fcx: FlowCx,
) {
    let _flow = onsa_diag::timing::phase(onsa_diag::timing::Phase::Flow);
    let mut info = FlowInfo {
        inputs: fcx.inputs.clone(),
        sample_rate_calls: fcx.sample_rate_calls.clone(),
        sample_tick_calls: fcx.sample_tick_calls.clone(),
        modifiers: fcx.node_exprs().into_iter().filter_map(|(e, r)| Some((e, r?))).collect(),
        output: fcx.output,
        derived_port: a.def(id).as_flow().and_then(|f| f.derived_port(a.def(id).name_span)),
        event_form: first_event(a, id, &fcx),
        complete: false,
        ..Default::default()
    };
    super::check::hold_vdelay_max(a, module, &body, &mut fcx);
    if !body.complete {
        if a.diagnostics.len() == fcx.diags_before
            && let Some(d) = fcx.held
        {
            a.diagnostics.push(d);
        }
        info.body = body;
        a.flows.insert(id, info);
        return;
    }
    let error = a.types.error();
    let (ast, text) = (&module.parsed.ast, module.text.as_str());
    let mut w = walk(a, flat, (ast, text), id, &body, &fcx, error);
    if w.diag.is_none() {
        w.post_check(&fcx, ast);
    }
    let ty = |p: &PendingLet| body.expr_types.get(&p.init).copied().unwrap_or(error);
    let lets = fcx.pending.iter().zip(&w.checked);
    let lets = lets.zip(&w.stages).map(|((p, &clock), &stage)| FlowLet {
        pat: p.pat,
        locals: p.locals.clone(),
        name: p.name.clone(),
        ty: ty(p),
        clock,
        stage,
        init: p.init,
        span: p.span,
        state: false,
    });
    info.lets = lets.collect();
    let out = w.output;
    let mut m = super::reads::mark_all((a, id), (ast, text), &body, &fcx, &w, &info.lets, out);
    (info.read_at, info.bound_at, info.sample_rate_at) = (m.read_at, m.bound_at, m.sample_rate_at);
    (info.eval_at, info.time_at, info.work, info.late) = (m.eval_at, m.time_at, m.work, m.late);
    info.complete = w.diag.is_none() && m.diag.is_none() && w.inout_call.is_none() && fcx.held.is_none() && !fcx.unread;
    #[cfg(test)]
    WALKED.with(|x| x.borrow_mut().push((id, w.clone(), info.complete)));
    info.clocks = std::mem::take(&mut w.info);
    info.body = body;
    let state: Vec<bool> = info.lets.iter().map(|l| l.locals.iter().any(|&v| info.stored(Kept::Local(v)))).collect();
    info.lets.iter_mut().zip(state).for_each(|(l, s)| l.state = s);
    if info.complete {
        let recorded = std::mem::take(&mut w.recorded);
        info.edges = std::mem::take(&mut w.edges);
        (info.tilde_matches, info.store_bindings) = (std::mem::take(&mut w.tilde), std::mem::take(&mut w.store));
        let out = match out {
            Clock::Tick(k) => ClockStage::Tick(k),
            Clock::Event(s) => ClockStage::Event(s),
            _ => ClockStage::SAMPLE,
        };
        info.out_stage = Some(info.run_stage(out));
        super::plan::build(&mut info, recorded, &w, ast, std::mem::take(&mut m.hoisted));
        (info.checks, info.const_conds) = (std::mem::take(&mut m.checks), std::mem::take(&mut m.const_conds));
        let unused = super::reads::unused(a, id, ast, &info, &fcx);
        a.diagnostics.extend(unused);
    }
    let diag = Diagnostic::first_in_file([w.diag, m.diag, fcx.held].into_iter().flatten());
    let diag = diag.or(w.inout_call);
    if let Some(d) = diag {
        a.diagnostics.push(d);
    }
    a.flows.insert(id, info);
}

/// The word `event` a flow has an event clock by: the first of the heading of
/// the flow `id`, else of that of a flow with an event output it calls; none
/// of a flow with no event clock.
fn first_event(a: &Analysis, id: DefId, cx: &FlowCx) -> Option<Span> {
    let callee = |c: &NodeCall| match c.kind {
        NodeKind::Instance(g) => a.def(g).as_flow().filter(|f| f.gives_events())?.event_port(),
        NodeKind::Delay(..) => None,
    };
    a.def(id).as_flow()?.event_port().or_else(|| cx.calls.iter().find_map(callee))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// Stage 1: the `let`s an expression reads, not through a cut place.
    /// Not the edges of the plan (all the reads, of stage 2): the relation
    /// of the clocks, needed before they are known.
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
    /// Stage 2: the clock the body writes the output at
    /// ([`crate::def::FlowDef::body_out_clock`]).
    pub(super) output: Clock,
    /// The stage of each `let` ([`FlowLet::stage`]).
    pub(super) stages: Vec<Clock>,
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
    /// `init` (§11.5), each with whether a value is not a constant, which
    /// the marking reads (E0815 or E0200 at a later stage).
    pub(super) non_rt: HashMap<ExprId, bool>,
    /// Stage 2: the nodes and their owners, for the plan.
    pub(super) recorded: Vec<Recorded>,
    /// Stage 2: the edges of the plan ([`FlowInfo::edges`]).
    pub(super) edges: Vec<Edge>,
    /// Stage 2: [`FlowInfo::tilde_matches`] and [`FlowInfo::store_bindings`].
    pub(super) tilde: BTreeMap<ExprId, TildeMatch>,
    pub(super) store: HashSet<LocalId>,
}

/// A place that is not evaluated on every sample (§11.5), around a part of
/// the walk; the innermost decides the error of a thing with state in it
/// (S-1188).
// SPEC-GAP(S-1188): the innermost place, of a right of `&&` / `||` and a
// branch one in the other (provisional).
#[derive(Debug, Clone, Copy)]
enum Site {
    /// A branch of `if` / `match` (E0811); `head` the `if` that starts its
    /// chain or the `match`, which the `~` makes evaluate every branch.
    Branch { head: ExprId },
    /// A guard of a `match` or a condition of a chain after the first, which
    /// chooses (E0811, S-1094, S-394: no `~` makes it evaluated every sample).
    Choose,
    /// The right of `&&` / `||` (E0806).
    Right,
}

pub(super) struct Walk<'a> {
    a: &'a Analysis,
    /// The packages, for the body of a called flow ([`to_sample`]).
    flat: &'a [&'a Package],
    /// The flow.
    def: DefId,
    ast: &'a Ast,
    /// The text of the module, for the `found` of a diagnostic.
    text: &'a str,
    /// The error type, of an expression with no type.
    error: TyId,
    body: &'a BodyInfo,
    cx: &'a FlowCx,
    names: &'a BodyNames,
    calls: HashMap<ExprId, usize>,
    /// The calls of `sample_rate()`, at `init`, and of `sample_tick()`, of
    /// the clock of the place that reads them (S-567 K6), as the check of
    /// the types found them.
    time: HashMap<ExprId, Clock>,
    mode: Mode,
    /// Stage 1: the clock of each `let`, ⊥ until its component is solved:
    /// in `Solve`, a `let` of the loop being solved (the reads not through a
    /// cut place are of its component or an earlier one).
    lets: Vec<Option<Clock>>,
    /// `Solve`: a ⊥ was read ([`Self::bottoms`]).
    bottom: bool,
    /// `Deps`: the `let`s read.
    deps: Vec<usize>,
    /// The clocks of the bindings of a `match` arm and of a `par~` index.
    scoped: HashMap<LocalId, Option<Clock>>,
    checked: Vec<Option<Clock>>,
    out: ClockInfo,
    node_clocks: Vec<NodeClock>,
    node_of: HashMap<ExprId, usize>,
    /// The places around the expression walked that are not evaluated on
    /// every sample, the innermost last.
    sites: Vec<Site>,
    /// At `Check`: the statement walked.
    stmt: Option<Stmt>,
    /// The frame of the instance whose argument is walked now (§11.9), of
    /// the clock a delay there keeps its state at.
    frame: ClockFrame,
    diag: Option<Diagnostic>,
    inout_call: Option<Diagnostic>,
    non_rt: HashMap<ExprId, bool>,
    recorder: NodeBuilder,
    /// A type → whether it is Dup and whether its drop needs `Alloc`
    /// ([`Walk::fault`]).
    dup_drops: HashMap<TyId, (bool, bool)>,
    /// At `Check`: the `match~`s, and the bindings of the arms read in the
    /// first argument of a delay, the depth of which is `first`.
    tilde: BTreeMap<ExprId, TildeMatch>,
    store: HashSet<LocalId>,
    first: u32,
    /// Stage 1: the first clash of the `let` walked ([`Walk::join`]).
    clash: Option<Clashed>,
    /// The clash of a loop by the `let` it is reported at (S-1198).
    loop_clash: Vec<Option<Clashed>>,
    /// Stage 1: the loops of `let`s, each in the order of its `let`s ([`mix`]).
    loops: Vec<Vec<usize>>,
    /// The stages of the `let`s checked, in their order ([`stages::of_params`]).
    let_stages: Vec<Clock>,
    /// [`Walked::output`].
    output: Clock,
}

/// An operand of a join: its expression (none of the `init` that the index
/// of a `par~` and a call of constants add) and its clock.
type Op = (Option<ExprId>, Option<Clock>);

/// Two operands whose clocks do not meet (E0815, M-7), each with its
/// expression and its clock, the one the join held first.
pub(super) type Clashed = [(Option<ExprId>, Clock); 2];

/// The frame whose tick the candidate that lifts the node `call` names
/// ([`Walk::lift`]): of an instance, `frame`; of a delay, none (it counts
/// the ticks of its first argument, not walked yet, S-1189).
fn lift_frame(call: &NodeCall, frame: ClockFrame) -> Option<ClockFrame> {
    matches!(call.kind, NodeKind::Instance(_)).then_some(frame)
}

/// Runs the two stages over the body of the flow `id` of the module of
/// `ast` and `text`, of the packages `flat`; `error` is the error type.
pub(super) fn walk(
    a: &Analysis,
    flat: &[&Package],
    (ast, text): (&Ast, &str),
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
        flat,
        def: id,
        ast,
        text,
        error,
        body,
        cx,
        names,
        calls: cx.calls.iter().enumerate().map(|(i, c)| (c.expr, i)).collect(),
        time: cx
            .sample_rate_calls
            .iter()
            .map(|&e| (e, Clock::Init))
            .chain(cx.sample_tick_calls.iter().map(|&e| (e, Clock::Ambient)))
            .collect(),
        mode: Mode::Deps,
        lets: vec![None; n],
        bottom: false,
        deps: Vec::new(),
        scoped: HashMap::default(),
        checked: vec![None; n],
        out: ClockInfo::default(),
        node_clocks: Vec::new(),
        node_of: HashMap::default(),
        sites: Vec::new(),
        stmt: None,
        frame: ClockFrame::BODY,
        diag: None,
        inout_call: None,
        non_rt: HashMap::default(),
        recorder: NodeBuilder::new(&cx.pending, ast, body, names),
        dup_drops: HashMap::default(),
        tilde: BTreeMap::new(),
        store: HashSet::default(),
        first: 0,
        clash: None,
        loop_clash: vec![None; n],
        loops: Vec::new(),
        let_stages: Vec::new(),
        output: Clock::SAMPLE,
    };
    for (l, input) in cx.inputs.iter().zip(&decl.inputs) {
        w.out.locals.insert(*l, input.body_clock());
    }
    w.solve();
    // S-1139 (a): of the clocks of stage 1, before the nodes are named.
    for (p, c) in cx.pending.iter().zip(&w.lets) {
        if c.is_some_and(Clock::of_ratio) {
            w.recorder.apart(super::plan::names::value_call(ast, names, p.init));
        }
    }
    w.check();
    mix::check(&mut w);
    let stages;
    (w.out.stages, w.out.local_stages, stages) = stages::of_walk(&w);
    let solved = |c: Option<Clock>| c.unwrap_or_else(|| onsa_diag::internal::bug(span, "a `let` left unsolved"));
    let (recorded, edges) = w.recorder.finish();
    Walked {
        lets: w.lets.into_iter().map(solved).collect(),
        checked: w.checked.into_iter().map(solved).collect(),
        output: w.output,
        stages,
        info: w.out,
        diag: w.diag,
        inout_call: w.inout_call,
        non_rt: w.non_rt,
        nodes: w.node_clocks,
        node_of: w.node_of,
        recorded,
        edges,
        tilde: w.tilde,
        store: w.store,
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
            // The first clash in a loop, in the order of its `let`s, then of
            // their clocks: of the `let` the second operand enters (S-1198).
            let mut clashed = None;
            let mut ops: Vec<Op> = Vec::with_capacity(scc.lets.len());
            for &k in &scc.lets {
                self.clash = None;
                let init = self.cx.pending[k].init;
                ops.push((Some(init), self.expr(init)));
                clashed = clashed.or(self.clash.map(|x| (k, x)));
            }
            let first = self.cx.pending[scc.lets[0]].init;
            self.clash = None;
            let c = if scc.looped { loop_clock(self.join(first, &ops)) } else { ops[0].1.unwrap_or(Clock::Const) };
            let c = grounded(c);
            let second = |x: &Clashed| scc.lets.iter().copied().find(|&k| Some(self.cx.pending[k].init) == x[1].0);
            clashed = clashed.or(self.clash.and_then(|x| Some((second(&x)?, x))));
            if let Some((k, x)) = clashed.filter(|_| scc.looped) {
                self.loop_clash[k] = Some(x);
            }
            for &k in &scc.lets {
                self.lets[k] = Some(c);
            }
            if scc.looped {
                self.loops.push(scc.lets);
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
            self.stmt = Some(Stmt { root: p.init, start: p.span.start });
            let c = grounded(self.expr(p.init).unwrap_or(Clock::Const));
            self.settle(p.init, c);
            self.checked[k] = Some(c);
            for &l in &p.locals {
                self.out.locals.insert(l, c);
            }
            if let Some(x) = self.loop_clash[k] {
                self.report_clash(p.init, x, true);
            }
            self.check_let(p);
        }
        if let Some(out) = self.cx.output {
            self.recorder.owner(Owner::Output);
            self.stmt = Some(Stmt { root: out, start: self.ast.expr(out).span.start });
            if let (Some(c), Some(f)) = (self.expr(out), self.a.def(self.def).as_flow()) {
                let at = f.body_out_clock(c);
                self.output = at;
                let c = rooted(c, at);
                self.settle(out, c);
                self.check_out(out, c, at);
            }
        }
    }

    /// At `Check`, `e`, used at the clock `at`, and its parts: each recorded
    /// at the clock of `sample_tick()` takes the clock of the place that
    /// uses it ([`rooted`], §11.4), a part that of its expression, an
    /// argument of a node the clock it is read at, so no table keeps that
    /// clock (the stages, the plan, `onsa graph`). Of a body that calls no
    /// `sample_tick()`, nothing; else linear in the body.
    fn settle(&mut self, e: ExprId, at: Clock) {
        if self.cx.sample_tick_calls.is_empty() {
            return;
        }
        let at = match self.out.exprs.get_mut(&e) {
            Some(c) => {
                *c = rooted(*c, at);
                *c
            }
            None => at,
        };
        match self.node_of.get(&e) {
            Some(&k) => (0..self.node_clocks[k].args.len()).for_each(|i| {
                let ArgRead { expr, at, .. } = self.node_clocks[k].args[i];
                self.settle(expr, at);
            }),
            None => self.ast.sub_exprs(e).into_iter().for_each(|x| self.settle(x, at)),
        }
    }

    /// `f` and whether it read a ⊥ (in `Solve`, a `let` of the loop being
    /// solved): of a check of its clock, decided when the loop is (§11.3,
    /// R-496: the E0813 and the E0815 of a function not `rt`, which so give
    /// no clock in error to the loop that reads them at `Check`).
    fn bottoms<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> (T, bool) {
        let outer = std::mem::replace(&mut self.bottom, false);
        let r = f(self);
        let read = self.bottom;
        self.bottom |= outer;
        (r, read)
    }

    fn span(&self, e: ExprId) -> Option<Span> {
        Some(self.ast.expr(e).span)
    }

    /// The clock of `e` (⊥ is `None`), recorded at `Check`: in error with a
    /// fault of its value that the rule of its clock rests on (E0805, not
    /// E0810: S-1133, [`Walk::fault`]).
    fn expr(&mut self, e: ExprId) -> Option<Clock> {
        let c = self.rule(e);
        let c = match self.fault(e) {
            Some(f) => {
                if self.checking() {
                    self.report_fault(e, f);
                }
                if matches!(f, checks::Fault::Alloc(_)) { Some(Clock::Error) } else { c }
            }
            None => c,
        };
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

    /// `f` walking in the place `site` (§11.5).
    fn at<T>(&mut self, site: Site, f: impl FnOnce(&mut Self) -> T) -> T {
        self.sites.push(site);
        let r = f(self);
        self.sites.pop();
        r
    }

    /// The candidate that lifts the thing with state `e` of the kind `kind`
    /// in the frame `frame` (none of a delay: its tick is not named) into a
    /// `let` before its statement ([`lift::lift`]).
    fn lift(&self, e: ExprId, kind: &str, frame: Option<ClockFrame>) -> Option<Fix> {
        let body = lift::Body { a: self.a, def: self.def, ast: self.ast, text: self.text, names: self.names };
        let per = frame.map(|f| checks::per_tick(f.tick(), self.ast.expr(e).span));
        lift::lift(&body, e, kind, self.stmt?, per.as_deref())
    }

    /// The join of the clocks of the operands `ops` of `e` (a constant of
    /// none). A clash (M-7) is in error (S-1133): at `Check` the E0815 at `e`
    /// ([`Self::report_clash`]); in stage 1 the first of the `let` walked is
    /// kept for its loop ([`Self::solve`]).
    fn join(&mut self, e: ExprId, ops: &[Op]) -> Option<Clock> {
        if ops.is_empty() {
            return Some(Clock::Const);
        }
        let x = match clock::join_by(ops, |o| o.1) {
            Ok(c) => return c,
            Err(x) => [x.first, x.second].map(|(i, c)| (ops[i].0, c)),
        };
        if self.checking() {
            self.report_clash(e, x, false);
        } else {
            self.clash.get_or_insert(x);
        }
        Some(Clock::Error)
    }

    fn join_of(&mut self, e: ExprId, es: impl IntoIterator<Item = ExprId>) -> Option<Clock> {
        let ops: Vec<Op> = es.into_iter().map(|x| (Some(x), self.expr(x))).collect();
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
            | ExprKind::Move(x)
            | ExprKind::Try(x)
            | ExprKind::Unsafe(x)
            | ExprKind::TupleIndex { base: x, .. }
            | ExprKind::TypeArgs { base: x, .. }
            | ExprKind::Repeat { elem: x, .. } => self.expr(*x),
            // SPEC-GAP(S-1083): an operation of a value of the `sample * N`
            // of the caller is E0815 (provisional (1)), as of the operands of
            // a join.
            ExprKind::Cast { expr: x, .. } | ExprKind::Unary { expr: x, .. } => match self.expr(*x) {
                Some(c) => self.join(e, &[(Some(*x), Some(c)), (None, Some(Clock::Const))]),
                None => None,
            },
            ExprKind::At { expr, .. } => {
                let c = self.cut(*expr);
                let Some(&k) = self.cx.at_clocks.get(&e) else {
                    onsa_diag::internal::bug(self.span(e), "an `at` whose clock the check did not record")
                };
                self.check_at(e, c, k);
                Some(k)
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) => self.join_of(e, es.iter().copied()),
            ExprKind::Struct { fields, .. } => self.join_of(e, fields.iter().map(|(_, x)| *x)),
            ExprKind::Block(b) => match b.tail {
                Some(t) => self.expr(t),
                None => Some(Clock::Const),
            },
            ExprKind::If { tilde, .. } => self.if_chain(e, *tilde),
            ExprKind::Match { scrutinee, arms, tilde } => self.match_arms(e, *scrutinee, arms, *tilde),
            ExprKind::Binary { op, lhs, rhs, .. } => {
                let l = self.expr(*lhs);
                let r = match op {
                    BinOp::And | BinOp::Or => self.at(Site::Right, |w| w.expr(*rhs)),
                    _ => self.expr(*rhs),
                };
                self.join(e, &[(Some(*lhs), l), (Some(*rhs), r)])
            }
            ExprKind::Index { base, index } => self.join_of(e, [*base, *index]),
            ExprKind::Par { tilde, body, .. } => self.par(e, *tilde, *body),
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
        if self.mode == Mode::Check {
            self.recorder.read(id, self.ast.expr(e).span);
            if self.first > 0 && self.body.locals[id.0 as usize].kind == LocalKind::MatchBind {
                self.store.insert(id);
            }
        }
        if let Some(&k) = self.cx.let_of_local.get(&id) {
            let feedback = matches!(self.ast.expr(e).kind, ExprKind::Feedback(_));
            return match self.mode {
                Mode::Deps => {
                    self.deps.push(k);
                    None
                }
                Mode::Check if !feedback => self.checked[k].or(self.lets[k]),
                Mode::Solve | Mode::Check => {
                    self.bottom |= self.lets[k].is_none();
                    self.lets[k]
                }
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

    /// The `if` chain `e` (§11.3, §11.5), `tilde` the `~` of its head, in
    /// the order of the text: its first condition, evaluated every sample;
    /// the later ones, which choose (S-1094, S-394); its branches, of a chain
    /// with no `~` the places of the `if` at its head, of an `if~` evaluated
    /// every sample, which holds state in one ([`Self::check_tilde`]). The
    /// later `if`s of the chain have the clocks of their links, joined from
    /// the last. One loop over the chain.
    fn if_chain(&mut self, e: ExprId, tilde: Option<Span>) -> Option<Clock> {
        let chain = super::branching::chain(self.ast, e);
        if let (Some(t), Some(first)) = (tilde.filter(|_| self.checking()), chain.links.first()) {
            self.check_tilde(t, Branching::If, chain.links.iter().map(|l| l.then).chain(chain.last), first.cond);
        }
        let branch = |w: &mut Self, x| match tilde {
            None => w.at(Site::Branch { head: e }, |w| w.expr(x)),
            Some(_) => w.expr(x),
        };
        let mut ops: Vec<Op> = Vec::with_capacity(2 * chain.links.len() + 1);
        for (k, l) in chain.links.iter().enumerate() {
            let c = if k == 0 { self.expr(l.cond) } else { self.at(Site::Choose, |w| w.expr(l.cond)) };
            ops.push((Some(l.cond), c));
            ops.push((Some(l.then), branch(self, l.then)));
        }
        let last = chain.last.map(|x| (Some(x), branch(self, x)));
        let (mut c, mut rest) = (last.and_then(|o| o.1), chain.last);
        let later = if self.checking() { chain.links.len() } else { 1 };
        for (k, l) in chain.links.iter().enumerate().take(later).skip(1).rev() {
            c = self.join(l.at, &[(rest, c), ops[2 * k], ops[2 * k + 1]]);
            rest = Some(l.at);
            self.out.exprs.insert(l.at, c.unwrap_or(Clock::Const));
        }
        ops.extend(last);
        let arms: Vec<Op> = ops.iter().skip(1).step_by(2).copied().chain(last).collect();
        self.join_arms(e, tilde.is_some(), &arms, &ops)
    }

    /// The join of the operands `ops` of the branching `e` (`tilde`: an `if~`
    /// or a `match~`), whose branches are `arms`.
    // SPEC-GAP(S-1239): the branches of an `if~` or a `match~` at the clocks of
    // two events are E0815 (§11.11) also where a condition or the scrutinee
    // is at a tick, the largest operand of §11.3 (provisional).
    fn join_arms(&mut self, e: ExprId, tilde: bool, arms: &[Op], ops: &[Op]) -> Option<Clock> {
        let event = |(_, c): (usize, Clock)| matches!(c, Clock::Event(_));
        let apart = || clock::join_by(arms, |o| o.1).is_err_and(|x| event(x.first) && event(x.second));
        self.join(e, if tilde && apart() { arms } else { ops })
    }

    /// `match` / `match~` (§11.3, §11.5), `tilde` its `~`: the scrutinee, the
    /// guards, which choose (S-1094, S-394), and the bodies, of a `match` the
    /// places of its head, of a `match~` evaluated every sample, which holds
    /// state in one ([`Self::check_tilde`]). The bindings of a pattern have
    /// the clock of the scrutinee in the guard; in the body of a `match~`, the
    /// join of it and the guards of the arms to this one (S-1131), the
    /// default of their type on a sample that does not take it (E0816).
    /// At `Check`, the record of a `match~`.
    fn match_arms(&mut self, e: ExprId, scrutinee: ExprId, arms: &[MatchArm], tilde: Option<Span>) -> Option<Clock> {
        let record = tilde.is_some() && self.checking();
        if let Some(t) = tilde.filter(|_| self.checking()) {
            self.check_tilde(t, Branching::Match, arms.iter().map(|a| a.body), scrutinee);
        }
        let s = self.expr(scrutinee);
        let (mut ops, mut chosen, mut bound) = (vec![(Some(scrutinee), s)], s, Vec::new());
        let mut bodies: Vec<Op> = Vec::with_capacity(arms.len());
        for arm in arms {
            self.bind_pat(arm.pat, s);
            if let Some(g) = arm.guard {
                let c = self.at(Site::Choose, |w| w.expr(g));
                chosen = self.join(e, &[(Some(scrutinee), chosen), (Some(g), c)]);
                ops.push((Some(g), c));
            }
            let body = match tilde {
                None => self.at(Site::Branch { head: e }, |w| w.expr(arm.body)),
                Some(_) => {
                    self.bind_pat(arm.pat, chosen);
                    bound.push(self.check_arm_bindings(arm.pat));
                    self.expr(arm.body)
                }
            };
            ops.push((Some(arm.body), body));
            bodies.push((Some(arm.body), body));
        }
        if record {
            self.tilde.insert(e, TildeMatch { arms: bound, pars: self.recorder.pars() });
        }
        self.join_arms(e, tilde.is_some(), &bodies, &ops)
    }

    /// `par` / `par~` (§11.5), `tilde` its `~`: the `~` its body asks for
    /// ([`Self::par_mark`]), its index at `init`, its body, and its node; one
    /// whose body holds state is a thing with state, in no branch.
    fn par(&mut self, e: ExprId, tilde: Option<Span>, body: ExprId) -> Option<Clock> {
        let Some(&(var, from, count, end)) = self.cx.pars.get(&e) else {
            onsa_diag::internal::bug(self.span(e), "a `par~` the check did not record")
        };
        let (check, span) = (self.checking(), self.ast.expr(e).span);
        let holds = super::nodes::holds_state(self.ast, body);
        if check {
            self.par_mark(e, tilde, holds);
        }
        if holds && !self.stateful_here(e, crate::flow_names::PAR, Some(ClockFrame::BODY)) {
            return Some(Clock::Error);
        }
        self.bind_local(var, Some(Clock::Init));
        if check {
            self.recorder.enter_par(e, span, var, (from, count, end), (body, holds));
        }
        let b = self.expr(body);
        if check {
            self.recorder.leave_par(e, span);
            self.check_par(e);
        }
        // S-1096: the event of a call in the body is of a clock of its own in each replica.
        if let Some(Clock::Event(src)) = b
            && let Some(call) = self.event_call(src).filter(|&x| self.ast.expr(body).span.contains(x.start))
        {
            if check {
                self.report_par_event(e, call);
            }
            return Some(Clock::Error);
        }
        self.join(e, &[(Some(body), b), (None, Some(Clock::Init))])
    }

    fn bind_pat(&mut self, p: PatId, c: Option<Clock>) {
        let ast = self.ast;
        crate::pat::each_bind(ast, p, true, &mut |q, _| match self.body.pat_locals.get(&q) {
            Some(&l) => self.bind_local(l, c),
            None if self.body.pat_consts.contains_key(&q) || self.body.pat_ctors.contains_key(&q) => {}
            None => onsa_diag::internal::bug(Some(ast.pat(q).span), "a binding with no local"),
        });
    }

    /// A call (§11.3, §11.4, §11.5).
    fn call(&mut self, e: ExprId, callee: ExprId, args: &[Arg]) -> Option<Clock> {
        if let Some(&i) = self.calls.get(&e) {
            let cx = self.cx;
            return self.node(e, &cx.calls[i]);
        }
        if let Some(&c) = self.time.get(&e) {
            return Some(c);
        }
        if let Some(m) = self.names.modifier(e) {
            return self.modifier(e, m.receiver, m.head, args);
        }
        let target = self.body.targets.get(&e);
        let receiver = crate::names::body::receiver(self.ast, callee)
            .filter(|b| self.body.expr_types.contains_key(b) && !matches!(target, Some(Target::Fn { .. })));
        let parts = receiver.into_iter().chain(args.iter().map(|x| x.expr));
        let (ops, partial) = self.bottoms(|w| parts.map(|x| (Some(x), w.expr(x))).collect::<Vec<Op>>());
        let r = self.join(e, &ops);
        if let Some(Target::Fn { def, .. } | Target::Method { def, .. }) = target
            && (self.signature_failed(*def) || !self.check_fn_call(e, *def, receiver.is_some(), (&ops, partial), r))
        {
            return Some(Clock::Error);
        }
        match target {
            Some(Target::Variant { .. } | Target::Panic) => r,
            Some(Target::Value) => onsa_diag::internal::bug(self.span(e), "a call of a function value in a flow body"),
            // Provisional (W9-03 takes it off, §11.3 "定数のクロックの式"): a
            // call of constants alone is at `init` until they are evaluated.
            _ => self.join(e, &[(None, r), (None, Some(Clock::Init))]),
        }
    }

    /// The modifier `e` of the receiver `receiver` of the chain of the head
    /// `head` (§11.9, §11.10): the value of the chain, the output of its
    /// head ([`Walk::instance`]). The chain is the thing with state, of the
    /// kind of its head (S-392). A head with no node (S-59) is walked as a
    /// call, and the chain is in error, as one with no frame ([`Self::frame_of`])
    /// (§18.1; its head runs in its frame). The condition of a `.when~` and a
    /// `.reset_if~` is read by the ports of the head ([`Self::guard_cond`]):
    /// of an instance its declared ones, of a built-in delay its output at
    /// the clock of its first argument (§11.10), none of one in error, whose
    /// condition is read with no rule as the N of `.down~` and `.up~` is; one of
    /// an event is [`Self::event_delay_modifier`].
    fn modifier(&mut self, e: ExprId, receiver: ExprId, head: ExprId, args: &[Arg]) -> Option<Clock> {
        let call = self.calls.get(&head).map(|&i| &self.cx.calls[i]);
        let frame = self.frame_of(head);
        if let Some(call) = call
            && !self.stateful_here(
                e,
                super::plan::names::kind(self.a, &call.kind),
                lift_frame(call, frame.unwrap_or(ClockFrame::BODY)),
            )
        {
            return Some(Clock::Error);
        }
        let c = self.expr(receiver);
        let ports = match (call.map(|c| &c.kind), frame, c) {
            (Some(&NodeKind::Instance(g)), Some(_), _) => self.a.def(g).as_flow().map(Ports::of),
            (Some(NodeKind::Delay(..)), Some(_), Some(k @ Clock::Tick(_))) => Some(Ports::delay(k)),
            _ => None,
        };
        match ports.and_then(|p| self.guard_cond(e, head, p)) {
            Some(false) => return Some(Clock::Error),
            Some(true) => {}
            None => {
                args.iter().for_each(|x| _ = self.cut(x.expr));
                if matches!((call.map(|c| &c.kind), c), (Some(NodeKind::Delay(..)), Some(Clock::Event(_)))) {
                    self.event_delay_modifier(e, head);
                }
            }
        }
        if call.is_some() && frame.is_some() { c } else { Some(Clock::Error) }
    }

    /// The condition of the `.when~` or the `.reset_if~` `e` of the chain of
    /// the head `head` of the ports `ports` (§11.10, S-1209), of its clock W
    /// ([`super::plan::bounds::bounds`]) moved out of the ratios outside it
    /// (`w`, a `sample * N` read at the `sample` of the body, §11.4). Of
    /// `.when~` read at W; of `.reset_if~` read at the tick R it resets at,
    /// that of the clock of its condition (an `at` too), of a parameter kind
    /// (or `sample_tick()`) W ([`Self::reset_tick`]). By its head's node
    /// ([`ArgRead`]) in the stage of the caller that reads it
    /// ([`super::plan::bounds::run_at`]): hoisted and kept as the other
    /// arguments are, a value of a slower tick held. A condition faster than
    /// W, and of `.when~` an `at` in it to another clock than W (not in an
    /// argument of a flow, read at its port), are E0815. An event in the
    /// condition of `.when~` is read at W (its last value), in that of
    /// `.reset_if~` at its own clock (§11.11; its plan is W7-17's): whether it is opened, its condition walked; none of
    /// `.down~` and `.up~`, whose argument the caller walks.
    fn guard_cond(&mut self, e: ExprId, head: ExprId, ports: Ports) -> Option<bool> {
        let chain = self.cx.chains.get(&head)?;
        let i = chain.mods.iter().position(|m| m.call == e)?;
        let (_, guards, resets) = super::plan::bounds::bounds(chain.mods.iter().map(|m| &m.plan), ports);
        let cond = chain.mods[i].plan.cond?;
        let outside = chain.mods[i + 1..].iter().filter_map(|m| m.plan.ratio).map(|r| r.0).sum::<i32>();
        let (own, reset) = match resets.iter().find(|x| x.at == i as u32) {
            Some(r) => (r.w, true),
            None => (guards.iter().find(|x| x.at == i as u32)?.w, false),
        };
        let w = Ratio(own.0.saturating_add(outside));
        let c = self.cut(cond);
        // §11.10: the condition of `.reset_if~` resets at the tick of its clock, `at` too.
        let apart = !reset && self.at_apart(cond, Clock::Tick(w));
        let faster = matches!(c, Some(Clock::Tick(k)) if k > w);
        if (apart || faster) && self.checking() {
            self.cond_e0815(chain, i, (own, w), apart);
            return Some(false);
        }
        if !self.checking() {
            return Some(true);
        }
        if let Some(at @ Clock::Event(_)) = c.filter(|_| reset) {
            if let Some(&k) = self.node_of.get(&head) {
                self.node_clocks[k].args.push(ArgRead { expr: cond, at, stage: None });
            }
            return Some(true);
        }
        let mods = || chain.mods.iter().map(|m| &m.plan);
        let (at, from, r) = match reset {
            false => (Clock::Tick(Ratio(w.0.min(0))), ClockStage::Tick(own), None),
            true => {
                let r = match c {
                    Some(Clock::Tick(k)) => k,
                    _ => Ratio(w.0.min(0)),
                };
                let rp = Ratio(r.0.saturating_sub(outside));
                if !self.reset_tick(chain, i, &guards, rp) {
                    return Some(false);
                }
                (Clock::Tick(r), ClockStage::Tick(rp), Some(rp))
            }
        };
        // Its port in its frame, of a periodic value (§11.10, R3: `sample_tick()` alone of
        // W): read at the stage of the ring that gathers it, else at its own. Not of a value
        // of the parameter kinds `at` a tick (§11.3: the `at` makes no state).
        // SPEC-GAP(S-1227): a condition mixing a signal and a value of the parameter
        // kinds (`c && b`) is of the signal's clock: the whole of it is gathered (provisional).
        let port = match c {
            Some(Clock::Tick(k)) if !stages::of_params(self, cond) => Some(k),
            Some(Clock::Ambient) => Some(Ratio(w.0.min(0))),
            _ => None,
        };
        let port = port.map(|k| Ratio(k.0.saturating_sub(outside)));
        if let Some(&k) = self.node_of.get(&head) {
            let ring = port.and_then(|p| super::plan::bounds::cond_ring(mods(), i as u32, p));
            let (j, from) = ring.unwrap_or((i as u32, from));
            let stage = super::plan::bounds::run_at(mods(), &guards, j, from);
            // §11.4, S-1230: `sample_tick()` alone is as with the `at` of W (its root, `settle`): where
            // an outer guard moved W to a faster stage, a field of the grid of W, as a head's argument.
            let stage = (at.stage() != Some(stage)).then_some(stage);
            self.node_clocks[k].args.push(ArgRead { expr: cond, at, stage });
            self.node_clocks[k].resets.extend(r.map(|r| (i as u32, r)));
            self.node_clocks[k].ports.extend(port.map(|p| (i as u32, p)));
        }
        Some(true)
    }

    /// Whether the tick `rp` the `.reset_if~` at `i` of `chain` resets at,
    /// in its frame, is a tick of a counter of one `U32` word
    /// ([`Ratio::made_n`]) in each frame from its own out to the caller's
    /// ([`super::plan::bounds::run_at`]); else the E0200 of S-1225.
    // SPEC-GAP(S-1225): a tick slower than `sample / 2^31` in a frame of the
    // chain (of an `.up~` outside it) is an E0200 (provisional), whether or
    // not a `.when~` outside it drives it.
    fn reset_tick(&mut self, chain: &ModifierChain, i: usize, guards: &[PlanGuard], rp: Ratio) -> bool {
        let mods = || chain.mods.iter().map(|m| &m.plan);
        let frames = (i..chain.mods.len())
            .map(|j| super::plan::bounds::run_at(mods().take(j + 1), guards, i as u32, ClockStage::Tick(rp)));
        let past = frames.filter_map(|s| match s {
            ClockStage::Tick(k) if k.made_n().is_none() => Some(k),
            ClockStage::Init | ClockStage::Block | ClockStage::Event(_) | ClockStage::Tick(_) => None,
        });
        let Some(k) = past.min() else { return true };
        let name = chain.mods[i].plan.name;
        let d = Feature::ResetTicksPastU32.diagnostic(Stage::Flow, name, &[&k.0.unsigned_abs().to_string()]);
        self.report(d.with_found(self.src(name)));
        false
    }

    /// The E0815 of the condition of the modifier `i` of `chain` (§11.10),
    /// whose W is `own` in its frame and `w` in the caller's: an `at` in it
    /// to another clock than W (`apart`, of `.when~`), else a clock faster
    /// than W.
    fn cond_e0815(&mut self, chain: &ModifierChain, i: usize, (own, w): (Ratio, Ratio), apart: bool) {
        let (m, receiver) = (chain.mods[i].plan, self.ast.expr(chain.mods[i].receiver).span);
        let (n, span) = (m.modifier.name(), m.cond.map_or(m.name, |c| self.ast.expr(c).span));
        let wc = Clock::Tick(w).shown(m.name);
        let (w_is, reads) = match m.modifier {
            crate::flow_names::Modifier::ResetIf => ("its clock W, the fastest it resets at", "resets at most at"),
            _ => ("the clock it is read at", "reads its condition at"),
        };
        let msg = match apart {
            true => format!(
                "the condition of `.when~` reads a value `at` another clock than `{wc}`, the clock it is read at; `when~` reads a slower value with no `at` (§11.10)"
            ),
            false => format!("the condition of `.{n}~` is at a clock faster than `{wc}`, {w_is} (§11.10)"),
        };
        let of = if own.slower_than_body() { "the output of its receiver" } else { "the place of the modifier" };
        let mut d = Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(self.src(span));
        d = d.with_note(receiver, format!("`.{n}~` {reads} `{wc}`, the clock of {of}"));
        if !apart {
            d = d.with_rule(format!("a value is made slower by a flow of the writer: `.{n}~(dws~(c))`"));
        }
        self.report(d);
    }

    /// Whether the condition `cond` has an `at` to another clock than `w` in
    /// it (§11.10, E0815): in its parts, not in an argument of a flow (read
    /// at its port) nor in the condition of a modifier in it (its own).
    fn at_apart(&self, cond: ExprId, w: Clock) -> bool {
        let mut todo = vec![cond];
        while let Some(x) = todo.pop() {
            if let Some(&k) = self.cx.at_clocks.get(&x)
                && k != Clock::Error
                && k != w
            {
                return true;
            }
            match (self.calls.get(&x).map(|&i| &self.cx.calls[i].kind), self.names.modifier(x)) {
                (Some(NodeKind::Instance(_)), _) => {}
                (_, Some(m)) => todo.push(m.receiver),
                _ => todo.extend(self.ast.sub_exprs(x)),
            }
        }
        false
    }

    /// A delay or an instance call `call` at `e` (§11.4, §11.5): its clock,
    /// its checks, and at `Check` its node and the clocks its arguments are
    /// read at, in the order of the text (its slot and its node before its
    /// arguments', §11.6; the error of its node after theirs, §18.1).
    fn node(&mut self, e: ExprId, call: &NodeCall) -> Option<Clock> {
        if !self.stateful_here(e, super::plan::names::kind(self.a, &call.kind), lift_frame(call, ClockFrame::BODY)) {
            return Some(Clock::Error);
        }
        let span = self.ast.expr(e).span;
        let slot = (self.mode == Mode::Check).then(|| {
            self.node_of.insert(e, self.node_clocks.len());
            self.node_clocks.push(NodeClock {
                clock: Clock::Error,
                args: Vec::new(),
                resets: Vec::new(),
                ports: Vec::new(),
            });
            let chain = self.cx.chains.get(&e);
            (self.node_clocks.len() - 1, self.recorder.node((self.a, self.body), e, call, chain, span))
        });
        // Its node is the innermost reader of its arguments (none of an E0816).
        let own = slot.as_ref().is_some_and(|(_, recorded)| recorded.is_ok());
        let (clock, args) = match call.kind {
            NodeKind::Instance(d) => self.instance(e, d, call),
            NodeKind::Delay(delay, _) => self.delay(delay, call, own),
        };
        if let Some((k, recorded)) = slot {
            if recorded.is_ok() {
                self.recorder.leave_node();
            }
            // SPEC-GAP(S-1155): of a value type neither Copy nor `Default`,
            // the E0810 is the one (provisional): not the E0816 of an omitted `init`.
            let not_copy = matches!(call.kind, NodeKind::Delay(..)) && self.check_delay_value(e);
            if let Err(d) = recorded
                && !not_copy
            {
                let found = self.src(span);
                self.report(d.with_found(found));
            }
            if let NodeKind::Delay(delay, _) = call.kind
                && !not_copy
                && let Some(d) = self.held_default(e, &format!("{}~", delay.name()))
            {
                self.report(d);
            }
            self.node_clocks[k] =
                NodeClock { clock: clock.unwrap_or(Clock::Const), args, resets: Vec::new(), ports: Vec::new() };
        }
        clock
    }

    /// `g~(args)` (§11.5): each argument read at the clock of its input in
    /// the frame of the call (of an event input, at the event clock of the
    /// argument, §11.11), and the output of `g` in it (an event output, at
    /// the event clock of the call). The head of a
    /// chain runs in the frame of the sum of its ratios (§11.9), which a
    /// chain with an N in error has not: its arguments and its output are
    /// then in error (§18.1).
    fn instance(&mut self, e: ExprId, g: DefId, call: &NodeCall) -> (Option<Clock>, Vec<ArgRead>) {
        let Some(f) = self.a.def(g).as_flow() else { onsa_diag::internal::bug(self.span(e), "an instance of no flow") };
        if f.inputs.len() != call.args.len() {
            onsa_diag::internal::bug(self.span(e), "an instance with other arguments than its inputs");
        }
        let frame = self.frame_of(e);
        let rebased = |c: Clock| frame.map_or(Clock::Error, |frame| rebase(c, frame));
        let mut reads = Vec::new();
        let outer = std::mem::replace(&mut self.frame, frame.unwrap_or(ClockFrame::BODY));
        for (&x, input) in call.args.iter().zip(&f.inputs) {
            if let Some(c) = self.cut(x) {
                let at = match input.caller_clock() {
                    Clock::Event(_) => self.bound_event(x, c, input, g),
                    at => rebased(at),
                };
                self.check_arg(x, c, at, input, g);
                reads.push(ArgRead { expr: x, at, stage: None });
            }
        }
        self.frame = outer;
        // A chain with an N in error has no boundary (§18.1).
        if self.checking() && frame.is_some() {
            self.check_gather_deal(e, g, &call.args);
            self.head_stages(e, f, &mut reads);
        }
        let out = match self.calls.get(&e) {
            _ if !f.gives_events() => rebased(f.out_clock),
            Some(&i) if frame.is_some() => Clock::Event(EventSrc::call(self.cx.inputs.len(), i)),
            _ => Clock::Error,
        };
        (Some(out), reads)
    }

    /// The place of the call whose output the source `src` is of; none of an
    /// input.
    fn event_call(&self, src: EventSrc) -> Option<Span> {
        let i = src.place(self.cx.inputs.len()).ok()?;
        Some(self.ast.expr(self.cx.calls.get(i)?.expr).span)
    }

    /// The stages the arguments `reads` of the head `e` of a chain, an
    /// instance of `f`, are read at where its `.when~`s move them
    /// ([`super::plan::bounds::head_stage`]).
    fn head_stages(&self, e: ExprId, f: &crate::def::FlowDef, reads: &mut [ArgRead]) {
        let Some(chain) = self.cx.chains.get(&e) else { return };
        let mods = || chain.mods.iter().map(|m| &m.plan);
        let (_, guards, _) = super::plan::bounds::bounds(mods(), Ports::of(f));
        if guards.is_empty() {
            return;
        }
        for r in reads {
            if let Some(s) = r.at.stage() {
                let moved = super::plan::bounds::head_stage(mods(), &guards, s);
                r.stage = (moved != s).then_some(moved);
            }
        }
    }

    /// The frame an instance call `e` runs in: of the sum of the ratios of
    /// the chain it heads (§11.9), none when an N of it is in error.
    fn frame_of(&self, e: ExprId) -> Option<ClockFrame> {
        self.cx.chains.get(&e).map_or(Some(Ratio(0)), |c| c.ratio).map(|ratio| ClockFrame { ratio })
    }

    /// A delay (§11.4): its first argument, the `d` of `vdelay~` and its
    /// `init`, not its length. With the E0813 of its first argument, it is in
    /// error (§18.1). `own`: its node was recorded, and reads its arguments.
    fn delay(&mut self, delay: Delay, call: &NodeCall, own: bool) -> (Option<Clock>, Vec<ArgRead>) {
        let (first, d, init) = call.delay_parts();
        // Read a tick later (§11.4): the one place of the judgement (RF-8
        // (C)), marked on its own node only, not on a reader around it.
        if own {
            self.recorder.lookback(true);
        }
        self.first += 1;
        let (c, partial) = self.bottoms(|w| w.expr(first));
        self.first -= 1;
        if own {
            self.recorder.lookback(false);
        }
        let failed = Self::first_fails(c, partial);
        if let Some(c) = failed.filter(|_| self.checking()) {
            self.report_first(delay, first, c);
        }
        let out = if failed.is_none() { delay_out(c, partial) } else { Some(Clock::Error) };
        let at = out.unwrap_or(Clock::Const);
        if let Some(d) = d
            && let Some(c) = self.cut(d)
        {
            self.check_d(d, c, at);
        }
        if let Some(i) = init
            && let Some(c) = self.cut(i)
        {
            self.check_init(delay, i, c);
        }
        let reads = [Some(first), d].into_iter().flatten().map(|x| ArgRead { expr: x, at, stage: None });
        let init = init.map(|i| ArgRead { expr: i, at: Clock::Init, stage: None });
        (out, reads.chain(init).collect())
    }
}

impl Walked {
    /// After stage 2 with no error: each `let` has the clock of stage 1,
    /// past one in error, and no expression the clock of `sample_tick()`
    /// ([`Walk::settle`]).
    pub(super) fn post_check(&self, cx: &FlowCx, ast: &Ast) {
        let lets = self.lets.iter().zip(&self.checked).zip(&cx.pending);
        for ((&l, &c), p) in lets {
            if l != Clock::Error && l != c {
                onsa_diag::internal::bug(Some(p.span), format!("the `let` is {l:?} in stage 1 and {c:?} in stage 2"));
            }
        }
        if let Some(&e) = self.info.exprs.iter().find_map(|(e, &c)| (c == Clock::Ambient).then_some(e)) {
            onsa_diag::internal::bug(Some(ast.expr(e).span), "an expression left at the clock of `sample_tick()`");
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
