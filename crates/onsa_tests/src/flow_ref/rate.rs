//! The rates (§11.9, §11.4): the chain of `.down~(N)` and `.up~(N)` that ends in a call of an instance (its head and the sum of the ratios of the
//! chain, S-566, S-567), the ratio of a derived clock `(sample / N)`, the ticks slower than `sample` a flow has stages for (S-578, S-1079, S-1088),
//! and the time an instance of a chain runs in (`sample_rate()` and `sample_tick()` are 1/N and N times, §11.4). A ratio is the exponent `r` of
//! the `2^r` of the clock over the `sample` of the body: `.down~(4)` is `-2`.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use onsa_diag::Span;
use onsa_sema::flow_names::FlowBuiltin;
use onsa_sema::{LocalId, Target};
use onsa_syntax::ast::{CallKind, ClockRatio, ExprId, ExprKind, RatioOp};

use super::call::parts;
use super::expr::{Frame, LIMITS, LOW_STACK, Stop};
use super::flow::{Clock, Ctx, Inst, Known, Plans, Step, clock_of, join};
use super::hoist::{feedback, stage_of};
use super::scalar::Fault;
use super::sema_view::{Body, Called, Stage, View, output_stage};
use super::state::SAVED;
use super::value::Value;
use onsa_sema::def::FlowDef;

/// A chain of modifiers: the call of the instance it starts at (`lp~(x)` of `lp~(x).down~(2).up~(4)`) and the sum of its ratios.
pub(super) struct Chain {
    pub head: ExprId,
    pub ratio: i32,
}

/// The exponent of the N of a modifier or of a derived clock: a power of two that is 2 or more (E0808 stops the others in the checker).
fn exponent(body: &Body, n: ExprId) -> Result<i32, Fault> {
    match Frame::new(*body).eval(n).map_err(|stop| stop.fault)? {
        Value::Int(_, n, _) if n >= 2 && n.count_ones() == 1 => Ok(n.trailing_zeros() as i32),
        _ => Err(Fault::Unavailable("an N that is not a power of 2 of 2 or more")),
    }
}

/// The ratio of a derived clock written `at (sample / N)` or `(sample * N)`: `-log2 N` or `log2 N`.
pub(super) fn derived(body: &Body, r: &ClockRatio) -> Result<i32, Fault> {
    match r.op {
        RatioOp::Div => exponent(body, r.n).map(|k| -k),
        RatioOp::Mul => exponent(body, r.n),
    }
}

/// The ratio of the tick the output of a flow is declared at, as a caller reads it (§11.9): 0 for `sample`.
pub(super) fn out_ratio(decl: &FlowDef) -> Result<i32, Fault> {
    match output_stage(decl)? {
        Stage::Tick(m) => Ok(m),
        _ => Err(Fault::Unavailable("an output that is not at a tick")),
    }
}

/// How the argument of an input declared at the ratio `k` reaches an instance that runs at the ratio `r` of its chain (§11.9: a port is read in the frame of the call, `k + r`).
/// An input of `sample * 2^k` that a `.down~` chain runs gathers, from the 2^-r frames of its caller before the tick, their `2^(k + r)` values each (`per`: one for `sample`,
/// an array of them for `sample * 2^(k + r)`), in the order of time; one that no chain runs (`k + r > 0`) takes the array of `sample * N` the argument is; an input of `sample` of
/// `.up~(N)` takes one element of such an array at each run. Another form has no value in the spec.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Feed {
    Plain,
    Gather { frames: usize, per: usize },
    Each,
}

pub(super) fn feed(k: i32, r: i32) -> Result<Feed, Fault> {
    match (k, r) {
        (_, 0) | (..=0, ..0) => Ok(Feed::Plain),
        (1.., ..0) if k + r >= 0 => Ok(Feed::Gather { frames: n_of(r) as usize, per: n_of(k + r) as usize }),
        (0, 1..) => Ok(Feed::Each),
        (..0, 1..) if k + r <= 0 => Ok(Feed::Plain),
        _ => Err(Fault::Unavailable("an input of sample * N that the chain does not read at the sample of its caller")),
    }
}

/// What a call at the chain ratio `r` makes of an output declared at `m` (§11.9): the value itself (`sample * N` of no chain is the array the body made, and the output of a tick
/// of a `.down~` chain is the one the last tick made), the array that a `.up~(N)` chain makes of the N outputs of its runs, or the one that a `.down~` chain deals out, `per` elements
/// at a time, to the 2^-r frames after the tick (`Dealt`: the output of 2^m is a value of `sample * 2^(m + r)` in the frame of the call).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Out {
    Plain,
    All,
    Dealt { r: i32, per: usize },
}

pub(super) fn out_of(m: i32, r: i32) -> Result<Out, Fault> {
    match (m, r) {
        (1.., ..0) if m + r >= 0 => Ok(Out::Dealt { r, per: n_of(m + r) as usize }),
        (_, 0) | (..=0, ..0) => Ok(Out::Plain),
        (0, 1..) => Ok(Out::All),
        _ => Err(Fault::Unavailable("an output that the chain does not read at the sample of its caller")),
    }
}

/// The chain that the call `e` ends, if it is a modifier: `.down~(N)` and `.up~(N)` add `-log2 N` and `log2 N` (§11.9); `when~` and `reset_if~` are
/// W7-10's.
pub(super) fn chain_of(body: &Body, e: ExprId) -> Result<Option<Chain>, Fault> {
    let (mut at, mut ratio, mut seen) = (e, 0, false);
    while let Some((m, receiver)) = body.modifier(at) {
        let ExprKind::Call { args, .. } = &body.ast.expr(at).kind else { break };
        let n = args.first().ok_or(Fault::Internal("a modifier with no argument"))?.expr;
        ratio += match m.ratio_op() {
            Some(RatioOp::Div) => -exponent(body, n)?,
            Some(RatioOp::Mul) => exponent(body, n)?,
            None => return Err(Fault::Unavailable("a modifier of W7-10 (`when~`, `reset_if~`)")),
        };
        (at, seen) = (receiver, true);
    }
    Ok(seen.then_some(Chain { head: at, ratio }))
}

/// The arguments of the call `e`.
pub(super) fn args_of(body: &Body, e: ExprId) -> Vec<ExprId> {
    match &body.ast.expr(e).kind {
        ExprKind::Call { args, .. } => args.iter().map(|a| a.expr).collect(),
        _ => Vec::new(),
    }
}

/// The N of the ratio `2^r` of a clock, `.down~(N)` or `.up~(N)` or `sample / N` (`r` is the sign of the direction and `log2 N` of the size): the one place of the
/// division of the time that every rate reads. A ratio over 40 is not told apart from 40 (the counter is 2^64 at most).
pub(super) fn n_of(ratio: i32) -> u64 {
    1u64 << ratio.unsigned_abs().min(40)
}

/// Does an instance of the rate `ratio` run at the time of its caller (a call with no modifier, or a chain whose ratios cancel)? S-1088: its ticks slower than
/// `sample` are then in the stages of its caller, at the same position; one of another rate has a time of its own, and its ticks are its own.
pub(super) fn at_callers_time(ratio: i32) -> bool {
    ratio == 0
}

/// How many frames the time `ctx` is after the last tick of `sample / N` (the ratio `r` < 0): the counter modulo N, 0 on the tick (§11.9).
pub(super) fn phase(ctx: Ctx, r: i32) -> u64 {
    ctx.total() % n_of(r)
}

/// Is the time `ctx` on a tick of `sample / N` (the ratio `r` < 0): when the counter is a multiple of N, the first frame included (§11.9).
pub(super) fn on_tick(ctx: Ctx, r: i32) -> bool {
    phase(ctx, r) == 0
}

/// The ratio `2^m` of the clock a call of a flow reads at (the output's `m` and the chain's `r`, §11.9); `None` for what is not a call of a flow.
pub(super) fn call_ratio(body: &Body, e: ExprId) -> Result<Option<i32>, Fault> {
    let (head, r) = match chain_of(body, e)? {
        Some(chain) => (chain.head, chain.ratio),
        None => (e, 0),
    };
    if !matches!(body.ast.expr(head).kind, ExprKind::Call { kind: CallKind::Flow, .. }) {
        return Ok(None);
    }
    match body.called(head)? {
        Called::Flow(def) => Ok(Some(out_ratio(body.view.flow(def)?)? + r)),
        Called::Builtin(_) => Ok(None),
    }
}

/// The frames an instance of the rate `ratio` of the chain runs for a frame of its caller: one for `.down~(N)` (when the caller's tick is a multiple of N) and
/// none of the chain (ratio 0), N for `.up~(N)` (§11.9).
pub(super) fn frames(ratio: i32) -> u32 {
    if ratio > 0 { u32::try_from(n_of(ratio)).unwrap_or(0) } else { 1 }
}

/// The time the j-th frame of an instance of the rate `ratio` runs in, for the time `ctx` of its caller (§11.4): at 1/N of the rate and of the counter for
/// `.down~(N)` (its caller's counter is a multiple of N, so the instance's is the total of the caller / N, the digits over the `U32` kept), at N times the rate
/// and the counter `total * N + j` for `.up~(N)`.
pub(super) fn time_of(ctx: Ctx, ratio: i32, j: u32) -> Ctx {
    let n = n_of(ratio);
    match ratio {
        0 => ctx,
        ..0 => Ctx::at(ctx.sample_rate / n as f32, ctx.total() / n),
        _ => Ctx::at(ctx.sample_rate * n as f32, ctx.total().wrapping_mul(n).wrapping_add(u64::from(j))),
    }
}

/// The ticks slower than `sample` that the stages of a body are of, in the order they run: the larger N (the slower tick) first (§11.9, S-1079): those of the parts of each step that
/// a tick makes (the ticks of a delay, of an `at (sample / N)`, of a chain), and those of the instances the body calls at its own time (a call with
/// no modifier, or a chain of ratio 0: S-1088 puts their ticks in the stage of the caller). The ticks of an instance that a chain runs at another rate
/// are its own (its frame has them).
pub(super) fn slow_ticks(view: View, body: &Body, steps: &[Step], plans: &Plans) -> Result<Rc<[i32]>, Stop> {
    let mut all = BTreeSet::new();
    for s in steps {
        visit(view, body, &s.known, s.init, s.init, plans, &mut all)?;
    }
    let mut ticks: Vec<i32> = all.into_iter().collect();
    ticks.sort_by_key(|r| std::cmp::Reverse(n_of(*r)));
    Ok(ticks.into())
}

/// The sets of steps that read each other (§11.3: "互いに頼る `let` は一つのクロックを持ち、外から入る被演算子の刻みのクロックから決まる") whose clock is a tick slower than `sample`, with that clock:
/// a loop of one `let` (`let s = prev~(^s) + lf`) or of a ring of them (`let a = prev~(^b)`, `let b = a + lf`) ticks with the clock of what enters it from outside, so its delays count that tick. A loop
/// that a tick enters only under an `at` to `sample` (`let u = (lf at sample) + prev~(^u)`) ticks with `sample`. A clock of what enters that the evaluator has not is `Unavailable`: it is not `sample`.
pub(super) fn slow_rings(body: &Body, steps: &[Step]) -> Result<Vec<(Vec<usize>, Clock)>, Stop> {
    let mut found = Vec::new();
    for ring in loops(body, steps) {
        let at = body.ast.expr(steps[ring[0]].init).span;
        let inside: Vec<LocalId> = ring.iter().flat_map(|i| step_locals(body, &steps[*i])).collect();
        let mut clock = Clock::Const;
        for i in &ring {
            let c = entering(body, &steps[*i].known, steps[*i].init, steps[*i].init, &inside)
                .map_err(|fault| Stop { fault, at })?;
            clock = join(clock, c).ok_or(Stop { fault: Fault::Internal("clocks that do not join"), at })?;
        }
        if slower(clock) {
            found.push((ring, clock.rooted()));
        }
    }
    Ok(found)
}

/// The locals a step binds.
fn step_locals(body: &Body, s: &Step) -> Vec<LocalId> {
    s.pat.and_then(|p| body.pat_locals(p).ok()).unwrap_or_default()
}

/// The sets of steps that read each other, a `^name` among the reads (§11.3: "互いに頼る `let`", a `let` that reads itself included): each step with a way back to itself,
/// with the steps it shares that way with.
fn loops(body: &Body, steps: &[Step]) -> Vec<Vec<usize>> {
    if !steps.iter().any(|s| feedback(body, s.init)) {
        return Vec::new();
    }
    let owner: HashMap<LocalId, usize> =
        steps.iter().enumerate().flat_map(|(i, s)| step_locals(body, s).into_iter().map(move |l| (l, i))).collect();
    fn reads(body: &Body, owner: &HashMap<LocalId, usize>, e: ExprId, out: &mut Vec<usize>) {
        if let (true, Ok(Target::Local(l))) = (body.names(e), body.target(e)) {
            out.extend(owner.get(l));
        }
        body.ast.sub_exprs(e).into_iter().for_each(|x| reads(body, owner, x, out));
    }
    let edges: Vec<Vec<usize>> = steps
        .iter()
        .map(|s| {
            let mut v = Vec::new();
            reads(body, &owner, s.init, &mut v);
            v
        })
        .collect();
    let reach = |from: usize| {
        let (mut seen, mut todo) = (vec![false; steps.len()], edges[from].clone());
        while let Some(i) = todo.pop() {
            if !std::mem::replace(&mut seen[i], true) {
                todo.extend(&edges[i]);
            }
        }
        seen
    };
    let reaches: Vec<Vec<bool>> = (0..steps.len()).map(reach).collect();
    let mut done = vec![false; steps.len()];
    let mut out = Vec::new();
    for i in (0..steps.len()).filter(|i| reaches[*i][*i]) {
        if !std::mem::replace(&mut done[i], true) {
            let ring: Vec<usize> = (i..steps.len()).filter(|j| reaches[i][*j] && reaches[*j][i]).collect();
            ring.iter().for_each(|j| done[*j] = true);
            out.push(ring);
        }
    }
    out
}

/// Is `c` a tick slower than `sample`?
fn slower(c: Clock) -> bool {
    matches!(c.rooted(), Clock::Tick(r) if r < 0)
}

/// A clock the evaluator has not (`Unavailable`) is no clock here, as for the ticks of a part: the plan does not stop at what it does not read.
fn lenient(clock: Result<Clock, Fault>, at: Span) -> Result<Clock, Stop> {
    match clock {
        Err(Fault::Unavailable(_)) => Ok(Clock::Const),
        other => other.map_err(|fault| Stop { fault, at }),
    }
}

/// The clock a loop (an expression that reads a `^name`, or a name of the `inside` of its ring) ticks with (§11.3): that of what enters it from outside, by the rules of an
/// expression with no loop. The reads of the loop enter nothing, and a delay of one (`prev~(^s)`) has the clock of its first argument, so it enters what that has besides.
fn entering(body: &Body, known: &Known, root: ExprId, e: ExprId, inside: &[LocalId]) -> Result<Clock, Fault> {
    if !feedback(body, e) && !reads_inside(body, e, inside) {
        return clock_of(body, known, root, e);
    }
    match &body.ast.expr(e).kind {
        ExprKind::Feedback(_) => Ok(Clock::Const),
        ExprKind::At { .. } => clock_of(body, known, root, e),
        ExprKind::Call { kind: CallKind::Flow, args, .. } => match body.called(e)? {
            Called::Builtin(FlowBuiltin::Delay(_)) => entering(
                body,
                known,
                root,
                args.get(SAVED).ok_or(Fault::Internal("a delay with no argument"))?.expr,
                inside,
            ),
            _ => clock_of(body, known, root, e),
        },
        _ => body.ast.sub_exprs(e).into_iter().try_fold(Clock::Const, |c, x| {
            join(c, entering(body, known, root, x, inside)?).ok_or(Fault::Internal("clocks that do not join"))
        }),
    }
}

/// Does `e` read a name of the `inside` of a ring?
fn reads_inside(body: &Body, e: ExprId, inside: &[LocalId]) -> bool {
    matches!(body.target(e), Ok(Target::Local(l)) if body.names(e) && inside.contains(l))
        || body.ast.sub_exprs(e).into_iter().any(|x| reads_inside(body, x, inside))
}

/// The slower ticks of `e` and of its parts into `out`.
fn visit(
    view: View,
    body: &Body,
    known: &Known,
    root: ExprId,
    e: ExprId,
    plans: &Plans,
    out: &mut BTreeSet<i32>,
) -> Result<(), Stop> {
    let at = body.ast.expr(e).span;
    let here = |fault| Stop { fault, at };
    if onsa_diag::stack::remaining().is_some_and(|left| left < LIMITS.reserve) {
        return Err(here(LOW_STACK));
    }
    // The clock `at` gives a part of `block` (`p at (sample / 4)`) is a tick too (a loop it enters ticks with it, `slow_rings`).
    let read = lenient(clock_of(body, known, root, e), at)?;
    let clocks = [stage_of(body, known, root, e).map_err(here)?, read];
    out.extend(clocks.into_iter().filter_map(|c| match c.rooted() {
        Clock::Tick(r) if r < 0 => Some(r),
        _ => None,
    }));
    let chain = chain_of(body, e).map_err(here)?;
    let own = at_callers_time(chain.as_ref().map_or(0, |c| c.ratio)).then_some(chain.as_ref().map_or(e, |c| c.head));
    if let Some(Ok(Called::Flow(def))) = own.map(|call| body.called(call)) {
        out.extend(Inst::planned(view, def, plans)?.slow.iter());
    }
    let inside = match &chain {
        Some(c) => args_of(body, c.head),
        None => parts(body, e),
    };
    inside.into_iter().try_for_each(|x| visit(view, body, known, root, x, plans, out))
}
