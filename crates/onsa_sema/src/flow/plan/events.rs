//! The event clocks of the body of a flow (§11.11): the sources it has
//! ([`sources`]) and what a delay reads of them where it is written
//! ([`saved`]), of the body alone; and, of the walk of the table
//! ([`super::entries`]), the work of an instance at the events its inputs
//! are bound to ([`entries`]), which stage ticks each ([`table`]) and the
//! most events a run gives out ([`most`]). Each expression of a flow with an
//! event once and each source once, by the log of their number; the stages
//! that tick one another end at a tick or an input, as a loop of them is the
//! one form not run ([`rooted`]).

use onsa_syntax::ast::Ast;

use super::*;
use crate::body::LocalKind;

/// What the source of an event clock is (§11.11): the input of its index, or
/// the node of the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EventFrom {
    Input(u32),
    Call(NodeId),
}

/// A source of an event clock of a flow and its stage (§11.11), which is a
/// function of its own.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EventPlan {
    pub src: EventSrc,
    pub from: EventFrom,
    /// Of a call, the stage of this flow whose function runs the stage of
    /// the callee that gives the events out ([`Out::Event`]) and, for each,
    /// this one after it; none of an input, which the caller ticks, and of a
    /// call of a callee with no table.
    pub parent: Option<ClockStage>,
    /// The events the flow gives out are made in it, so its function gives
    /// them to the one that ticks it ([`FlowInfo::gives`]).
    pub gives: bool,
}

/// The sources of the event clocks of `info`, in the order of their numbers,
/// whatever the table of a callee: of each input at `event`, and of each call
/// of an event output.
pub(super) fn sources(info: &FlowInfo) -> Vec<EventPlan> {
    let plan = |src, from| EventPlan { src, from, parent: None, gives: false };
    let input = |(i, &l): (u32, &LocalId)| match info.own_stage(l) {
        Some(ClockStage::Event(src)) => Some(plan(src, EventFrom::Input(i))),
        _ => None,
    };
    // The clock of a delay is an event of another source.
    let call = |(i, n): (u32, &PlanNode)| match (&n.kind, n.clock) {
        (PlanKind::Instance { .. }, Clock::Event(src)) => Some(plan(src, EventFrom::Call(NodeId(i)))),
        _ => None,
    };
    let inputs = (0u32..).zip(&info.inputs).filter_map(input);
    let mut plans: Vec<EventPlan> = inputs.chain((0u32..).zip(&info.nodes).filter_map(call)).collect();
    plans.sort_by_key(|p| p.src);
    plans
}

/// What `of` reads of events (§11.3, S-1240, S-1249): the rest of what a
/// delay at a tick stores, or a `part` of a tick of [`FlowInfo::late`]: each
/// name of one and each part computed at one, but for a `^name` and those that
/// read one themselves ([`FlowInfo::back`]), in the order of the text. Its
/// value is that of its place, though what is made of it is made at the end
/// of the stage. Not in what is of another place: another hoisted part, a
/// call, the condition of a modifier, and of another delay but the `d` of a
/// `vdelay~`.
pub(super) fn saved(info: &FlowInfo, ast: &Ast, of: ExprId, part: bool) -> Vec<ExprId> {
    let (mut saved, mut todo) = (Vec::new(), vec![of]);
    while let Some(e) = todo.pop() {
        let read = match (info.hoist_of(e).filter(|_| !part || e != of), info.body.targets.get(&e)) {
            (Some(h), _) => Some(info.hoist(h).stage),
            (None, _) if matches!(ast.expr(e).kind, ExprKind::Feedback(_)) => None,
            // A binding of an arm has the value of its place.
            (None, Some(&Target::Local(l))) if info.body.locals[l.0 as usize].kind != LocalKind::MatchBind => {
                info.own_stage(l)
            }
            _ => None,
        };
        if matches!(read, Some(ClockStage::Event(_))) && !info.back.contains(&e) {
            saved.push(e);
        }
        match (info.modifiers.get(&e), info.node_of.get(&e).map(|&id| &info.node(id).kind)) {
            _ if read.is_some() => {}
            (Some(&receiver), _) => todo.push(receiver),
            (None, Some(&PlanKind::Vdelay { d, .. })) => todo.push(d),
            (None, Some(PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Instance { .. })) => {}
            (None, Some(PlanKind::Par { .. }) | None) => todo.extend(ast.sub_exprs(e).into_iter().rev()),
        }
    }
    saved
}

/// Where the output of `g` is made, and where the run of that stage puts it:
/// the events it gives out ([`FlowInfo::emit`]), else its value.
pub(super) fn out(g: &FlowInfo) -> Option<(ClockStage, Out)> {
    let value = g.out_stage.map(|s| (s, Out::Value));
    g.emit.map(|s| (s, Out::Event)).or(value)
}

/// Adds to the `entries` of the node `n` ([`super::steps`]) its work at the
/// events (§11.11), an entry of a source in the order of their numbers: of an
/// instance of `g`, the tick of each input bound to it, in the order they are
/// declared (S-1236), and before them the reset of each `.reset_if~` with a
/// condition of it, the outer first (§11.10). One entry of a stage. Through
/// no boundary and no guard of the chain: none gathers, deals or stops them.
pub(super) fn entries(n: &PlanNode, g: Option<&FlowInfo>, entries: &mut Vec<Entry>) {
    let mut at: BTreeMap<EventSrc, Vec<Op>> = BTreeMap::new();
    for (g, p) in g.into_iter().flat_map(|g| g.events.iter().map(move |p| (g, p))) {
        // An argument in error has the diagnostic of a callee.
        if let EventFrom::Input(i) = p.from
            && let Some(Clock::Event(src)) = n.args.get(i as usize).map(|r| r.at)
        {
            let body = ClockStage::Event(p.src);
            let out = out(g).filter(|o| o.0 == body).map_or(Out::None, |o| o.1);
            at.entry(src).or_default().push(Op::Run { body, out });
        }
    }
    for (k, m) in (0u32..).zip(&n.chain) {
        if let Some(ClockStage::Event(src)) = m.reset {
            at.entry(src).or_default().insert(0, Op::Reset { at: k });
        }
    }
    for (src, mut ops) in at {
        let caller = ClockStage::Event(src);
        match entries.iter_mut().find(|e| e.caller == caller) {
            // The read of a delay at it.
            Some(e) => {
                ops.append(&mut e.ops);
                e.ops = ops;
            }
            None => entries.push(Entry { caller, read: false, ops }),
        }
    }
}

/// The most runs of the head of `n` that give out events in the ops `ops`
/// (§11.9): of the stage y of the part under an `.up~(N)`, at N >> |y| of the
/// runs j, a multiple of 2^|y| each ([`Op::Each`]: j = 0 alone of one slower
/// than the `sample` of its caller); of a stopped part, as if it ran.
fn most(n: &PlanNode, ops: &[Op]) -> u32 {
    let runs = |op: &Op| match op {
        Op::Run { out: Out::Event, .. } => 1,
        Op::When { ops, .. } => most(n, ops),
        Op::Each { once: true, groups, .. } => groups.iter().map(|g| most(n, &g.1)).sum(),
        Op::Each { bound, groups, .. } => {
            let up = n.bounds.get(*bound as usize).map_or(0, |b| b.ratio.0.unsigned_abs());
            let of = |y: ClockStage| match y {
                ClockStage::Tick(k) => up.saturating_sub(k.0.unsigned_abs()),
                ClockStage::Init | ClockStage::Block | ClockStage::Event(_) => 0,
            };
            let runs =
                |(y, ops): &(_, Vec<Op>)| most(n, ops).saturating_mul(1u32.checked_shl(of(*y)).unwrap_or(u32::MAX));
            groups.iter().map(runs).fold(0, u32::saturating_add)
        }
        _ => 0,
    };
    ops.iter().map(runs).fold(0, u32::saturating_add)
}

/// The events of a flow with what the table gives of them ([`table`]).
pub(super) struct Ticked {
    pub events: Vec<EventPlan>,
    /// [`FlowInfo::emit`].
    pub emit: Option<ClockStage>,
    /// [`FlowInfo::burst`].
    pub burst: u32,
}

/// The events of `info` with the stage that ticks each, of the tables of its
/// nodes, and the stage of it that gives out those of its output (`gives`:
/// it is at `event`) with the most of them one run of it gives (the [`most`]
/// runs of the call it runs, of the `burst` of its callee); the time a stage
/// takes is of the one that ticks it too (`time`). Of a flow with a source that
/// nothing outside it ticks, its place.
pub(super) fn table(
    info: &FlowInfo,
    gives: bool,
    tables: &[Option<(Vec<Entry>, Read)>],
    burst_of: impl Fn(DefId) -> u32,
    time: &mut BTreeMap<ClockStage, Words>,
) -> Result<Ticked, Span> {
    let mut plans = info.events.clone();
    let of = |id: NodeId| tables.get(id.0 as usize).and_then(Option::as_ref);
    for p in &mut plans {
        if let EventFrom::Call(id) = p.from {
            // In the runs of an `.up~` and under a guard too.
            let emits = |e: &&Entry| most(info.node(id), &e.ops) > 0;
            p.parent = of(id).and_then(|t| t.0.iter().find(emits)).map(|e| e.caller);
        }
    }
    for k in rooted(info, &plans)?.into_iter().rev() {
        if let (Some(parent), Some(&w)) = (plans[k].parent, time.get(&ClockStage::Event(plans[k].src))) {
            let at = time.entry(parent).or_insert(w);
            *at = (*at).max(w);
        }
    }
    let (mut emit, mut burst) = (info.out_stage.filter(|_| gives), 1);
    while let Some(k) = find(&plans, emit) {
        plans[k].gives = true;
        let EventFrom::Call(id) = plans[k].from else { break };
        emit = plans[k].parent;
        let (n, entries) = (info.node(id), of(id).map_or(&[][..], |t| &t.0));
        let ops = entries.iter().find(|e| Some(e.caller) == emit).map_or(&[][..], |e| &e.ops);
        let inner = if let PlanKind::Instance { callee, .. } = n.kind { burst_of(callee) } else { 1 };
        // Of the first of them, which a tick runs (the others an event, once): 2^24 at
        // most of a flow with no E0808 (S-1089).
        burst = most(n, ops).saturating_mul(inner);
    }
    Ok(Ticked { events: plans, emit, burst })
}

/// The resets of the delay `id` of `info`, by their place in its chain, that
/// an event may tick between the place it is written at and its store (§11.3,
/// S-1250; [`PlanNode::late`]): the event, or one whose stage ticks it, is
/// given out in the function of the stage of the delay, by a call after it.
/// Of any other the delay has been stored, or is not yet read: the functions
/// of the stages are in one another by the events given out alone, and an
/// event of an input comes of the caller between them (S-1251).
pub(super) fn late(info: &FlowInfo, plans: &[EventPlan], ast: &Ast, id: NodeId) -> Vec<u32> {
    let n = info.node(id);
    let Some(own) = info.node_stage(id).filter(|_| n.kind.delay().is_some()) else { return Vec::new() };
    // What is made in the order of the text: a chain after its head and its conditions (§11.3).
    let end = |id: NodeId| {
        let n = info.node(id);
        let conds = n.chain.iter().filter_map(|m| Some(ast.expr(m.cond?).span.end));
        conds.fold(n.span.end, u32::max)
    };
    let after = |p: &EventPlan| matches!(p.from, EventFrom::Call(c) if p.parent == Some(own) && end(c) > end(id));
    let ticks = |s: Option<ClockStage>| std::iter::successors(find(plans, s), |&k| find(plans, plans[k].parent));
    let late = |m: &PlanModifier| ticks(m.reset).any(|k| after(&plans[k]));
    (0..).zip(&n.chain).filter(|(_, m)| late(m)).map(|(at, _)| at).collect()
}

/// The source of `plans` whose stage is `s`, by its place in them.
pub(super) fn find(plans: &[EventPlan], s: Option<ClockStage>) -> Option<usize> {
    let Some(ClockStage::Event(src)) = s else { return None };
    plans.binary_search_by_key(&src, |p| p.src).ok()
}

/// The places of `plans`, each after the one that ticks it; or, of sources
/// that tick one another, the first call in the text of one of them.
// SPEC-GAP(S-1237): a source that its own output alone ticks is E0200, on the
// way to the output or not (provisional).
fn rooted(info: &FlowInfo, plans: &[EventPlan]) -> Result<Vec<usize>, Span> {
    let (mut seen, mut order, mut loops) = (vec![false; plans.len()], Vec::new(), Vec::new());
    for k in 0..plans.len() {
        let (mut path, mut next) = (Vec::new(), Some(k));
        while let Some(j) = next.filter(|&j| !std::mem::replace(&mut seen[j], true)) {
            path.push(j);
            next = find(plans, plans[j].parent);
        }
        // Back to one of this path, or on to one walked before.
        let back = next.and_then(|j| path.iter().position(|&p| p == j));
        loops.extend(back.into_iter().flat_map(|p| &path[p..]).filter_map(|&j| match plans[j].from {
            EventFrom::Call(id) => Some(info.node(id).span),
            EventFrom::Input(_) => None,
        }));
        order.extend(path.into_iter().rev());
    }
    loops.into_iter().min_by_key(|s| (s.start, s.end)).map_or(Ok(order), Err)
}

#[cfg(test)]
mod tests;
