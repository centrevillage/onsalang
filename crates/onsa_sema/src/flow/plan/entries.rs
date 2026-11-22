//! The table of the entries of the stages (§11.9, S-1088): of each flow,
//! the stages of the bodies of its callees each instance runs and in which
//! of its own stages ([`PlanNode::runs`]), its stages with those
//! ([`FlowInfo::stages`]), whether it reads the time
//! ([`FlowInfo::reads_time`]), then the fields of its state, which these
//! decide. The same walk checks the N of `.down~` and `.up~` on the paths
//! through flows (S-1089, E0808 of the flow stage).
//!
//! One walk after the bodies of all the flows are checked, the callees
//! before their callers: depth first with a stack of its own (a body never
//! runs out the stack of `check`), each flow open while its callees are
//! walked and done after. A callee open (a loop of calls, which the names
//! stage reports, E0817), not done or with no table (in error) gives its
//! caller nothing: no run and no count. Each flow and each node once:
//! O(flows + nodes + runs), a run per stage of the callee (32 at most).

use std::collections::BTreeSet;

use onsa_diag::{Code, Diagnostic, Stage};

use super::*;
use crate::Package;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mark {
    Open,
    Done,
}

/// The most of the exponents of the N on a path from the body of a flow
/// (S-1089) and the node of the first step of that path (none of a path
/// with no instance); none when it is not counted: of no table, past 2^24
/// in it, or through a callee not counted.
type Most = Option<(u32, Option<NodeId>)>;

/// The place of an E0808 of a path (S-1089), the exponent of its N and the
/// node of its first step.
type Past = (Span, u32, NodeId);

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
/// calls): writes its runs, its stages, whether it reads the time and its
/// fields, reports the first of its nodes past 2^24 on a path through
/// flows (by the place of the modifier, §18.1), and gives its count.
fn close(pkg: &Package, a: &mut Analysis, f: DefId, marks: &HashMap<DefId, Mark>, most: &HashMap<DefId, Most>) -> Most {
    let info = a.flows.get(&f)?;
    let own_time = !info.sample_tick_calls.is_empty();
    if !info.complete {
        a.flows.get_mut(&f).into_iter().for_each(|info| info.reads_time = own_time);
        return None;
    }
    let table = |g: DefId| a.flows.get(&g).filter(|t| marks.get(&g) == Some(&Mark::Done) && t.complete);
    let mut runs = Vec::with_capacity(info.nodes.len());
    let mut stages: BTreeSet<ClockStage> = info.stages.iter().copied().collect();
    let mut reads_time = own_time;
    let (mut count, mut counted) = ((0, None), true);
    let mut past_at: Option<Past> = None;
    for (i, n) in info.nodes.iter().enumerate() {
        let id = NodeId(i as u32);
        let PlanKind::Instance { callee, .. } = n.kind else {
            runs.push(None);
            continue;
        };
        let Some(g) = table(callee) else {
            runs.push(None);
            // SPEC-GAP(S-1212): a callee in error leaves the whole flow not
            // counted (its other paths too), so the flows that run it say
            // nothing until the error is mended.
            counted = false;
            continue;
        };
        let (r, bounds, outer) = node_runs(n, g);
        stages.extend(outer.into_iter().filter(|s| s.tick_slower_than(ClockStage::SAMPLE)));
        runs.push(Some((r, bounds)));
        reads_time |= g.reads_time;
        let Some((inner, _)) = most.get(&callee).copied().flatten() else {
            counted = false;
            continue;
        };
        let total = inner.saturating_add(n.size);
        if total <= MOST_N_EXP {
            if total > count.0 {
                count = (total, Some(id));
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
    let Some(flow) = a.flows.get_mut(&f) else { onsa_diag::internal::bug(None, "a flow closed out of the table") };
    flow.nodes.iter_mut().zip(runs).for_each(|(n, r)| r.into_iter().for_each(|r| (n.runs, n.bounds) = r));
    (flow.stages, flow.reads_time) = (stages.into_iter().collect(), reads_time);
    fields::build(flow);
    if let Some(p) = past_at {
        a.diagnostics.push(past_path(pkg, a, f, p, most));
    }
    counted.then_some(count)
}

/// The runs of the instance `n` of the callee whose table is `g` (§11.9,
/// S-1088, S-1207), its boundaries with their stages, and the stages of
/// this flow it has: each stage x of the body of `g` (its slow stages,
/// then `sample`) is moved out of each boundary of `n`, inner first
/// ([`bounds::step`]), and the one of the stage that makes the output of
/// the outermost part is read (`g.out_stage` with no boundary). Each
/// boundary maps the stages of the caller of the part it wraps, and has
/// those, the stages of its rings and its tick if it deals. O(boundaries ×
/// stages), 56 stages at most (S-1089).
fn node_runs(n: &PlanNode, g: &FlowInfo) -> (Vec<Run>, Vec<PlanBound>, BTreeSet<ClockStage>) {
    let mut heads: Vec<_> = g.stages.iter().copied().chain([ClockStage::SAMPLE]).map(|x| (x, x)).collect();
    let mut stages: BTreeSet<ClockStage> = heads.iter().map(|h| h.1).collect();
    let (mut made, mut bounds) = (g.out_stage, n.bounds.clone());
    for b in &mut bounds {
        let Some(r) = n.chain.get(b.at as usize).and_then(|m| m.ratio) else {
            onsa_diag::internal::bug(Some(n.span), "a boundary of no modifier with a ratio")
        };
        b.maps = stages.iter().map(|&y| (y, bounds::step(y, r))).collect();
        let tick = b.deals.then_some(ClockStage::Tick(r));
        stages = b.maps.iter().map(|m| m.1).chain(b.gathers.iter().map(|g| g.1)).chain(tick).collect();
        made = if b.deals { tick } else { made.map(|m| bounds::step(m, r)) };
        (b.stages, b.made) = (stages.iter().copied().collect(), made);
        heads.iter_mut().for_each(|h| h.1 = bounds::step(h.1, r));
    }
    let runs = heads.into_iter().map(|(body, caller)| Run { body, caller, at_read: Some(caller) == made }).collect();
    (runs, bounds, stages)
}

/// The E0808 of the N past 2^24 (`total` the exponent) on the path from
/// the body of `f` through its node `id`, at the modifier `at` of its chain
/// (§11.9, S-1089), with a note at each step of the path with a chain of N
/// (24 at most): the node and the N of its chain.
fn past_path(pkg: &Package, a: &Analysis, f: DefId, (at, total, id): Past, most: &HashMap<DefId, Most>) -> Diagnostic {
    let name = |d: DefId| a.def(d).name.as_str();
    let msg = format!(
        "the N of the `.down~` and `.up~` on the path from the body of `{}` multiply to 2^{total}, past 2^24 (§11.9)",
        name(f)
    );
    let found = crate::module_of_def(pkg, a, f).map(|m| at.text_in(&m.text).to_string()).unwrap_or_default();
    let mut d = Diagnostic::new(Stage::Flow, Code::E0808, at, msg).with_found(found);
    // Each flow once: a path of the counts goes to callees done before.
    let mut step = Some((f, id));
    while let Some((caller, id)) = step {
        let n = a.flows[&caller].node(id);
        let PlanKind::Instance { callee, .. } = n.kind else { break };
        if n.size > 0 {
            let note =
                format!("on the path: in `{}`, `{}` runs under `{}`", name(caller), name(callee), shown(&n.chain));
            d = d.with_note(n.span, note);
        }
        step = most.get(&callee).copied().flatten().and_then(|(_, via)| via).map(|v| (callee, v));
    }
    d
}
