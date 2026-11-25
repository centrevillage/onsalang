//! The event clocks of the body of a flow (§11.11): the sources it has
//! ([`sources`]), the forms of them this version does not run ([`form`],
//! [`table`]) and what a delay reads of them where it is written
//! ([`saved`]), of the body alone; and, of the walk of the table
//! ([`super::entries`]), the work of an instance at the events its inputs
//! are bound to ([`entries`]) and which stage ticks each ([`table`]). Each
//! expression of a flow with an event once and each source once, by the log
//! of their number; the stages that tick one another end at a tick or an
//! input, as a loop of them is a form not run ([`rooted`]).

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

/// The first form of `info`, in the order of the text, of those with events
/// this version does not run (W7-17), of the body: a chain of a call of a
/// flow with an event port, of a delay at an event or with a condition at
/// one; and in a `par~` (and a `par`, whose fields are of each replica as
/// well), an `if~` or a `match~`, its conditions, scrutinee and guards too,
/// a call of a flow with an event port, a delay at an event or a computed
/// part of one, but not a name. Not those of a callee, which stop it.
pub(super) fn form(a: &Analysis, info: &FlowInfo, ast: &Ast) -> Option<Span> {
    if info.events.is_empty() {
        return None;
    }
    let event = |e: &ExprId| matches!(info.clocks.exprs.get(e), Some(Clock::Event(_)));
    let ticks = |n: &PlanNode| match n.kind {
        PlanKind::Instance { callee, .. } => a.def(callee).as_flow().is_some_and(|f| f.event_port().is_some()),
        _ => n.kind.delay().is_some() && matches!(n.clock, Clock::Event(_)),
    };
    let mut found: Vec<Span> = Vec::new();
    let mut todo: Vec<(ExprId, bool)> =
        info.lets.iter().map(|l| l.init).chain(info.output).map(|e| (e, false)).collect();
    while let Some((e, inside)) = todo.pop() {
        if let Some(n) = info.node_of.get(&e).map(|&id| info.node(id)) {
            found.extend((ticks(n) && (inside || !n.chain.is_empty())).then_some(n.span));
            found.extend(n.chain.iter().filter(|m| m.cond.as_ref().is_some_and(event)).map(|m| m.name));
        }
        let part = info.hoist_of(e).map(|h| info.hoist(h)).filter(|h| matches!(h.stage, ClockStage::Event(_)));
        found.extend(part.filter(|_| inside).map(|h| h.span));
        let inside = inside
            || matches!(
                ast.expr(e).kind,
                ExprKind::Par { .. } | ExprKind::If { tilde: Some(_), .. } | ExprKind::Match { tilde: Some(_), .. }
            );
        todo.extend(ast.sub_exprs(e).into_iter().map(|x| (x, inside)));
    }
    first(found)
}

fn first(spans: Vec<Span>) -> Option<Span> {
    spans.into_iter().min_by_key(|s| (s.start, s.end))
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

/// The work of the instance `n` of `g` at the events its inputs are bound to
/// (§11.11), an entry of a source in the order of their numbers: the tick of
/// each input bound to it, in the order they are declared (S-1236). Not
/// through the boundaries of a chain ([`form`]).
pub(super) fn entries(n: &PlanNode, g: &FlowInfo) -> Vec<Entry> {
    let mut at: BTreeMap<EventSrc, Vec<Op>> = BTreeMap::new();
    for p in &g.events {
        // An argument in error has the diagnostic of a callee.
        if let EventFrom::Input(i) = p.from
            && let Some(Clock::Event(src)) = n.args.get(i as usize).map(|r| r.at)
        {
            let body = ClockStage::Event(p.src);
            let out = out(g).filter(|o| o.0 == body).map_or(Out::None, |o| o.1);
            at.entry(src).or_default().push(Op::Run { body, out });
        }
    }
    at.into_iter().map(|(src, ops)| Entry { caller: ClockStage::Event(src), read: false, ops }).collect()
}

/// The events of `info` with the stage that ticks each, of the tables of its
/// nodes, and the stage of it that gives out those of its output (`gives`:
/// it is at `event`); the time a stage takes is of the one that ticks it too
/// (`time`). Of a flow with a source that nothing outside it ticks, its place.
pub(super) fn table(
    info: &FlowInfo,
    gives: bool,
    tables: &[Option<(Vec<Entry>, Read)>],
    time: &mut BTreeMap<ClockStage, Words>,
) -> Result<(Vec<EventPlan>, Option<ClockStage>), Span> {
    let mut plans = info.events.clone();
    let emits = |e: &&Entry| e.ops.iter().any(|op| matches!(op, Op::Run { out: Out::Event, .. }));
    for p in &mut plans {
        if let EventFrom::Call(id) = p.from {
            let table = tables.get(id.0 as usize).and_then(Option::as_ref);
            p.parent = table.and_then(|t| t.0.iter().find(emits)).map(|e| e.caller);
        }
    }
    for k in rooted(info, &plans)?.into_iter().rev() {
        if let (Some(parent), Some(&w)) = (plans[k].parent, time.get(&ClockStage::Event(plans[k].src))) {
            let at = time.entry(parent).or_insert(w);
            *at = (*at).max(w);
        }
    }
    let mut emit = info.out_stage.filter(|_| gives);
    while let Some(k) = find(&plans, emit) {
        plans[k].gives = true;
        match plans[k].from {
            EventFrom::Input(_) => break,
            EventFrom::Call(_) => emit = plans[k].parent,
        }
    }
    Ok((plans, emit))
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
    first(loops).map_or(Ok(order), Err)
}

#[cfg(test)]
mod tests;
