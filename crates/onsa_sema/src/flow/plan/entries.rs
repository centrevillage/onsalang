//! The table of the entries of the stages (§11.9, S-1088): of each flow,
//! the work of each instance in its own stages ([`PlanNode::entries`],
//! [`steps`]), its stages with those
//! ([`FlowInfo::stages`]), the words of the time each of its stages takes
//! ([`FlowInfo::time`]), then the fields of its state, which these
//! decide. The same walk checks the N of `.down~` and `.up~` on the paths
//! through flows (S-1089) and the clocks they compose (S-1216), E0808 of
//! the flow stage, and the loops of calls nothing outside them ticks
//! (S-1237), E0815.
//!
//! One walk after the bodies of all the flows are checked, the callees
//! before their callers: depth first with a stack of its own (a body never
//! runs out the stack of `check`), each flow open while its callees are
//! walked and done after. A callee open (a loop of calls, which the names
//! stage reports, E0817), not done or with no table (in error) gives its
//! caller nothing: no run and no count. Each flow and each node once:
//! O(flows + nodes + runs), a run per stage of the callee (32 at most).

use std::collections::{BTreeMap, BTreeSet};

use onsa_diag::{Code, Diagnostic, Stage};

use super::*;
use crate::Package;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mark {
    Open,
    Done,
}

/// The most of the exponents of the N on a path from the body of a flow
/// (S-1089) and the first step of that path with an N, the flow and its
/// node (none of a path with no N); none when it is not counted: of no
/// table, past 2^24 in it, or through a callee not counted.
type Most = Option<(u32, Option<(DefId, NodeId)>)>;

/// The place of an E0808 of a path (S-1089), the exponent of its N and the
/// node of its first step.
type Past = (Span, u32, NodeId);

/// A clock past `U32` a chain composes ([`unmade`]): its node, its modifier,
/// its exponent and what it is of.
type Unmade = (NodeId, Span, Ratio, Over);

/// The walk of the table of every flow of `a` (the module docs), in the
/// order of their [`DefId`]s, so that the diagnostics come in one order.
pub(crate) fn walk(pkg: &Package, a: &mut Analysis) {
    let mut roots: Vec<DefId> = a.flows.keys().copied().collect();
    roots.sort();
    let mut marks: HashMap<DefId, Mark> = HashMap::default();
    let mut most: HashMap<DefId, Most> = HashMap::default();
    for root in roots {
        if marks.contains_key(&root) {
            continue;
        }
        marks.insert(root, Mark::Open);
        // Each flow open with the next of its nodes to look at.
        let mut stack = vec![(root, 0usize)];
        while let Some(top) = stack.last_mut() {
            let f = top.0;
            let Some(n) = a.flows.get(&f).and_then(|info| info.nodes.get(top.1)) else {
                stack.pop();
                let m = close(pkg, a, f, &marks, &most);
                most.insert(f, m);
                marks.insert(f, Mark::Done);
                continue;
            };
            top.1 += 1;
            if let PlanKind::Instance { callee, .. } = n.kind
                && a.flows.contains_key(&callee)
                && !marks.contains_key(&callee)
            {
                marks.insert(callee, Mark::Open);
                stack.push((callee, 0));
            }
        }
    }
}

/// Closes the flow `f`, whose callees are done (but those in a loop of
/// calls): writes the entries of its instances, its stages, the time they
/// take and its fields, reports the first of its nodes past 2^24 on a path
/// through flows (by the place of the modifier, §18.1), else each chain that
/// composes a clock past `U32`, and gives its count.
fn close(pkg: &Package, a: &mut Analysis, f: DefId, marks: &HashMap<DefId, Mark>, most: &HashMap<DefId, Most>) -> Most {
    let info = a.flows.get(&f)?;
    let mut time = own_time(info);
    // A flow in error, whose entries nothing reads.
    if !info.planned() {
        if let Some(info) = a.flows.get_mut(&f) {
            info.time = time;
        }
        return None;
    }
    let table = |g: DefId| a.flows.get(&g).filter(|t| marks.get(&g) == Some(&Mark::Done) && t.planned());
    let mut tables = Vec::with_capacity(info.nodes.len());
    let mut stages: BTreeSet<ClockStage> = info.stages.iter().copied().collect();
    let (mut count, mut counted) = ((0, None), true);
    let mut past_at: Option<Past> = None;
    let mut unmade_at = Vec::new();
    for (i, n) in info.nodes.iter().enumerate() {
        let id = NodeId(i as u32);
        let PlanKind::Instance { callee, .. } = n.kind else {
            // A delay with a chain runs at its one stage (§11.10), a stage of this flow.
            let stage = n.clock.stage().filter(|_| n.kind.delay().is_some() && !n.chain.is_empty());
            let mut table = stage.map(|s| steps::table(n, &[s], Some((s, Out::Value))));
            table.iter_mut().for_each(|t| events::entries(n, None, &mut t.0));
            tables.push(table);
            continue;
        };
        let Some(g) = table(callee) else {
            tables.push(None);
            // SPEC-GAP(S-1212): a callee in error leaves the whole flow not
            // counted (its other paths too), so the flows that run it say
            // nothing until the error is mended.
            counted = false;
            continue;
        };
        let heads: Vec<ClockStage> = g.stages.iter().copied().chain([ClockStage::SAMPLE]).collect();
        let (mut entries, read) = steps::table(n, &heads, events::out(g));
        events::entries(n, Some(g), &mut entries);
        unmade_at.extend(unmade(n, g).map(|(at, k, over)| (id, at, k, over)));
        callee_time(&mut time, info, n, g, &entries);
        tables.push(Some((entries, read)));
        let Some((inner, via)) = most.get(&callee).copied().flatten() else {
            counted = false;
            continue;
        };
        let total = inner.saturating_add(n.size);
        if total <= MOST_N_EXP {
            if total > count.0 {
                // A step of no N goes on to the first one with an N in the callee.
                count = (total, if n.size > 0 { Some((f, id)) } else { via });
            }
            continue;
        }
        counted = false;
        // `inner` is 2^24 or less, so the N past it are of this chain.
        let at = past(&n.chain, inner).map_or(n.span, |m| m.name);
        if past_at.is_none_or(|(first, ..)| (at.start, at.end) < (first.start, first.end)) {
            past_at = Some((at, total, id));
        }
    }
    // The E0808 of the path first, one of the flow, as before S-1216.
    let found: Vec<Diagnostic> = match past_at {
        Some(p) => vec![past_path(pkg, a, f, p, most)],
        None => unmade_at.into_iter().map(|u| past_u32(pkg, a, f, u)).collect(),
    };
    let gives = a.def(f).as_flow().is_some_and(FlowDef::gives_events);
    let burst_of = |g| a.flows.get(&g).map_or(1, |g| g.burst);
    let ast = || match crate::module_of_def(pkg, a, f) {
        Some(m) => &m.parsed.ast,
        None => onsa_diag::internal::bug(None, "a flow of no module"),
    };
    let ticked = match events::table(info, gives, &tables, burst_of, &mut time) {
        Ok(ticked) => ticked,
        // Before `late` and the walk of `emit`, which go up the parents of no loop.
        Err(ring) => {
            let (d, time) = (unticked(a, info, ast(), &ring), own_time(info));
            a.diagnostics.extend(found.into_iter().chain([d]));
            a.flows.entry(f).and_modify(|info| (info.unticked, info.time) = (true, time));
            return None;
        }
    };
    let ast = (!ticked.events.is_empty()).then(ast);
    let late = |id| ast.map_or(Vec::new(), |ast| events::late(info, &ticked.events, ast, NodeId(id)));
    let late: Vec<Vec<u32>> = (0..info.nodes.len() as u32).map(late).collect();
    let callers = tables.iter().flatten().flat_map(|t| &t.0).map(|e| e.caller);
    stages.extend(callers.filter(|s| s.slow_tick()));
    let Some(flow) = a.flows.get_mut(&f) else { onsa_diag::internal::bug(None, "a flow closed out of the table") };
    let set = |n: &mut PlanNode, (e, read)| (n.entries, n.read) = (e, read);
    flow.nodes.iter_mut().zip(tables).for_each(|(n, t)| t.into_iter().for_each(|t| set(n, t)));
    flow.nodes.iter_mut().zip(late).for_each(|(n, late)| n.late = late);
    (flow.stages, flow.time) = (stages.into_iter().collect(), time);
    (flow.events, flow.emit, flow.burst) = (ticked.events, ticked.emit, ticked.burst);
    node_work(flow);
    fields::build(flow);
    a.diagnostics.extend(found);
    counted.then_some(count)
}

/// The E0815 of the loop `ring` of calls of `info` that nothing outside it
/// ticks (§11.11, S-1237; [`events::table`]), at the argument of its first
/// call that ticks its output: a note at that of each other call, and one at
/// the input of the first callee that gives its events out.
fn unticked(a: &Analysis, info: &FlowInfo, ast: &onsa_syntax::ast::Ast, ring: &[NodeId]) -> Diagnostic {
    // The input whose events the callee gives out is the source of it that gives.
    let arg = |id: NodeId| {
        let n = info.node(id);
        let PlanKind::Instance { callee, .. } = n.kind else { onsa_diag::internal::bug(Some(n.span), "no call") };
        let i = a.flows.get(&callee).and_then(|g| {
            g.events.iter().find_map(|p| match p.from {
                EventFrom::Input(i) if p.gives => Some(i as usize),
                _ => None,
            })
        });
        let found = i.and_then(|i| Some((n.args.get(i)?, a.def(callee).as_flow()?.inputs.get(i)?)));
        let Some((arg, input)) = found else {
            onsa_diag::internal::bug(Some(n.span), "a call in a loop of events not at an input")
        };
        (ast.expr(arg.expr).span, callee, input)
    };
    let (at, callee, input) = arg(ring[0]);
    let msg = if ring.len() == 1 {
        "nothing outside the call ticks this argument: it is at the events of the output of the call it is given to, so the call never gives an event (§11.11)"
    } else {
        "nothing outside the loop ticks this argument: it is at the events of a loop of calls that only their own outputs tick, so none of them gives an event (§11.11)"
    };
    // Each call of the loop is ticked by the next.
    let mut others: Vec<_> = (1..ring.len()).map(|k| (arg(ring[k]).0, arg(ring[(k + 1) % ring.len()]).1)).collect();
    others.sort_by_key(|(s, _)| (s.start, s.end));
    let mut d = Diagnostic::new(Stage::Flow, Code::E0815, at, msg);
    for (at, by) in others {
        d = d.with_note(at, format!("this argument is at the events of `{}~`, in the loop", a.def(by).name));
    }
    let (name, of) = (&a.def(callee).name, &input.name);
    d.with_note(input.span, format!("the output of `{name}` gives its events at those of its input `{of}`"))
}

/// Adds the work of the nodes of `flow` to [`FlowInfo::work`]: of each
/// instance its stages (`init`, `block`, its entries), of a delay `init`, at
/// the `let` or the output that holds it, which a function of another stage
/// walks (that of its own stage evaluates it).
fn node_work(flow: &mut FlowInfo) {
    let own: Vec<_> = flow.lets.iter().map(|l| l.stage.stage()).chain([flow.out_stage]).collect();
    let own: Vec<_> = own.into_iter().map(|s| s.map(|s| flow.run_stage(s))).collect();
    for (n, k) in flow.nodes.iter().zip(flow.outer()) {
        let made: &[ClockStage] = match n.kind {
            PlanKind::Instance { .. } => &[ClockStage::Init, ClockStage::Block],
            PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. } => &[ClockStage::Init],
            PlanKind::Par { .. } => &[],
        };
        let stages = made.iter().copied().chain(n.entries.iter().map(|e| e.caller));
        flow.work.extend(stages.filter(|&s| own[k] != Some(s)).map(|s| (k as u32, s)));
    }
}

/// What a chain composes past `U32` ([`unmade`]): of an input of the callee
/// by its index, of its output, or of a stage of it by its ratio.
enum Over {
    Input(usize),
    Output,
    Stage(Ratio),
}

/// The first clock past `U32` ([`Ratio::made_n`]) the chain of the instance
/// `n` of the callee `g` composes (§11.9, S-1216), inner first, with its
/// modifier: of a port of the part a boundary wraps, or a stage of `g` (not
/// one past it, told in `g`), moved to that boundary ([`PlanBound::outside`]).
fn unmade(n: &PlanNode, g: &FlowInfo) -> Option<(Span, Ratio, Over)> {
    let past = |k: Ratio| k.made_n().is_none();
    let slow = |s: &ClockStage| match *s {
        ClockStage::Tick(k) if k.slower_than_body() && !past(k) => Some((k, k)),
        ClockStage::Init | ClockStage::Block | ClockStage::Event(_) | ClockStage::Tick(_) => None,
    };
    let mut stages: Vec<(Ratio, Ratio)> = g.stages.iter().filter_map(slow).collect();
    for b in &n.bounds {
        stages.iter_mut().for_each(|s| s.1 = b.outside(s.1));
        let ins = (0..).zip(&b.ins).filter_map(|(i, k)| Some((b.outside((*k)?), Over::Input(i))));
        let mut over = ins
            .chain(b.out.map(|k| (b.outside(k), Over::Output)))
            .chain(stages.iter().map(|s| (s.1, Over::Stage(s.0))));
        if let Some((k, over)) = over.find(|p| past(p.0)) {
            let Some(m) = n.chain.get(b.at as usize) else {
                onsa_diag::internal::bug(Some(n.span), "a boundary of no modifier of its chain")
            };
            return Some((m.name, k, over));
        }
    }
    None
}

/// The E0808 of the clock `k` past `U32` the chain of the node `id` of `f`
/// composes at its modifier `at` ([`unmade`]): the notes of the path
/// ([`down_path`]) down to the flow that declares the N, and one of the
/// clock it declares.
fn past_u32(pkg: &Package, a: &Analysis, f: DefId, (id, at, k, mut over): Unmade) -> Diagnostic {
    let op = if k.faster_than_body() { "*" } else { "/" };
    let msg =
        format!("this chain makes the clock `sample {op} 2^{}`, past `U32`: an N is 2^31 at most (§11.9)", k.0.abs());
    let (d, callee) = down_path(a, e0808(pkg, a, f, at, msg), (f, id), |g| match over {
        Over::Stage(s) => {
            let (id, o) = source(&a.flows[&g], s)?;
            over = o;
            Some((g, id))
        }
        _ => None,
    });
    let def = a.def(callee);
    let Some(g) = def.as_flow() else { return d };
    let (span, what, c) = match over {
        Over::Input(i) => {
            (g.inputs[i].span, format!("the input `{}` of", g.inputs[i].name), g.inputs[i].caller_clock())
        }
        Over::Output => (def.name_span, "the output of".into(), g.out_clock),
        Over::Stage(s) => (def.name_span, "a stage of".into(), Clock::Tick(s)),
    };
    d.with_note(span, format!("{what} `{}` is at `{}`", def.name, c.shown(span)))
}

/// The instance of `g` whose chain moves a stage of its callee slower than its
/// `sample` to the stage of `g` of the ratio `s` ([`Entry::runs`]), with it
/// (not a delay, whose run is of its own stage).
fn source(g: &FlowInfo, s: Ratio) -> Option<(NodeId, Over)> {
    let run = |(body, at)| match body {
        ClockStage::Tick(k) if at == ClockStage::Tick(s) && k.slower_than_body() => Some(Over::Stage(k)),
        ClockStage::Init | ClockStage::Block | ClockStage::Event(_) | ClockStage::Tick(_) => None,
    };
    let instances = (0u32..).zip(&g.nodes).filter(|(_, n)| matches!(n.kind, PlanKind::Instance { .. }));
    instances.into_iter().find_map(|(i, n)| Some((NodeId(i), Entry::runs(&n.entries).into_iter().find_map(run)?)))
}

/// The time of the stages of `info` that read `sample_tick()` (§11.4,
/// S-1217): `t` at the [`FlowInfo::run_stage`] of each stage the marking
/// evaluates one at ([`FlowInfo::time_at`]), a slower one of its
/// [`FlowInfo::stages`], which have the stages it evaluates at.
fn own_time(info: &FlowInfo) -> BTreeMap<ClockStage, Words> {
    info.time_at.iter().map(|&s| (info.run_stage(s), Words::One)).collect()
}

/// The time the runs of the entries `entries` of the instance `n` of the
/// callee `g` take in `info`, into `time` (§11.4, S-1217): of each run of
/// a stage of `g` that takes it ([`Entry::runs`]), at its
/// [`FlowInfo::run_stage`] here, its words, two under a `.down~`, which
/// divides the count before it is cut to `U32` (§12.4).
fn callee_time(time: &mut BTreeMap<ClockStage, Words>, info: &FlowInfo, n: &PlanNode, g: &FlowInfo, entries: &[Entry]) {
    let down = n.chain.iter().any(|m| m.ratio.is_some_and(Ratio::slower_than_body));
    for (body, caller) in Entry::runs(entries) {
        let words = match g.time.get(&body) {
            None => continue,
            Some(_) if down => Words::Two,
            Some(&w) => w,
        };
        let at = time.entry(info.run_stage(caller)).or_insert(words);
        *at = (*at).max(words);
    }
}

/// The E0808 of the N past 2^24 (`total` the exponent) on the path from
/// the body of `f` through its node `id`, at the modifier `at` of its chain
/// (§11.9, S-1089), with a note at each step of the path with a chain of N
/// (25 at most, each of an N of 2 or more): the node and the N of its chain.
fn past_path(pkg: &Package, a: &Analysis, f: DefId, (at, total, id): Past, most: &HashMap<DefId, Most>) -> Diagnostic {
    let msg = format!(
        "the N of the `.down~` and `.up~` on the path from the body of `{}` multiply to 2^{total}, past 2^24 (§11.9)",
        a.def(f).name
    );
    let next = |callee| most.get(&callee).copied().flatten().and_then(|(_, via)| via);
    down_path(a, e0808(pkg, a, f, at, msg), (f, id), next).0
}

/// The E0808 of `f` at `at` with the message `msg`.
fn e0808(pkg: &Package, a: &Analysis, f: DefId, at: Span, msg: String) -> Diagnostic {
    let found = crate::module_of_def(pkg, a, f).map(|m| at.text_in(&m.text).to_string()).unwrap_or_default();
    Diagnostic::new(Stage::Flow, Code::E0808, at, msg).with_found(found)
}

/// `d` with the notes of the path of an E0808 (S-1089, S-1216) down from a
/// node (callees closed first): of each step of a chain of N, its callee and
/// chain; `next` gives a callee's next step. Returns the last step's callee.
fn down_path(
    a: &Analysis,
    mut d: Diagnostic,
    (mut caller, mut id): (DefId, NodeId),
    mut next: impl FnMut(DefId) -> Option<(DefId, NodeId)>,
) -> (Diagnostic, DefId) {
    loop {
        let n = a.flows[&caller].node(id);
        let PlanKind::Instance { callee, .. } = n.kind else {
            onsa_diag::internal::bug(Some(n.span), "a step of the path of an E0808 that is no instance")
        };
        if !n.bounds.is_empty() {
            let (name, called) = (&a.def(caller).name, &a.def(callee).name);
            d = d.with_note(n.span, format!("on the path: in `{name}`, `{called}` runs under `{}`", shown(&n.chain)));
        }
        let Some(step) = next(callee) else { return (d, callee) };
        (caller, id) = step;
    }
}
