//! The table of the entries of the stages (§11.9, S-1088): of each flow,
//! the work of each instance in its own stages ([`PlanNode::entries`],
//! [`steps`]), its stages with those
//! ([`FlowInfo::stages`]), the words of the time each of its stages takes
//! ([`FlowInfo::time`]), then the fields of its state, which these
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
/// calls): writes the entries of its instances, its stages, the time they
/// take and its fields, reports the first of its nodes past 2^24 on a path
/// through flows (by the place of the modifier, §18.1), and gives its count.
fn close(pkg: &Package, a: &mut Analysis, f: DefId, marks: &HashMap<DefId, Mark>, most: &HashMap<DefId, Most>) -> Most {
    let info = a.flows.get(&f)?;
    let mut time = own_time(info);
    if !info.complete {
        if let Some(info) = a.flows.get_mut(&f) {
            info.time = time;
        }
        return None;
    }
    let table = |g: DefId| a.flows.get(&g).filter(|t| marks.get(&g) == Some(&Mark::Done) && t.complete);
    let mut tables = Vec::with_capacity(info.nodes.len());
    let mut stages: BTreeSet<ClockStage> = info.stages.iter().copied().collect();
    let (mut count, mut counted) = ((0, None), true);
    let mut past_at: Option<Past> = None;
    let mut unmade_at = Vec::new();
    for (i, n) in info.nodes.iter().enumerate() {
        let id = NodeId(i as u32);
        let PlanKind::Instance { callee, .. } = n.kind else {
            tables.push(None);
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
        let (entries, read) = steps::table(n, g);
        unmade_at.extend(unmade(n, g, &entries));
        stages.extend(entries.iter().map(|e| e.caller).filter(|s| s.tick_slower_than(ClockStage::SAMPLE)));
        callee_time(&mut time, info, n, g, &entries);
        tables.push(Some((entries, read)));
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
    let set = |n: &mut PlanNode, (e, read)| (n.entries, n.read) = (e, read);
    flow.nodes.iter_mut().zip(tables).for_each(|(n, t)| t.into_iter().for_each(|t| set(n, t)));
    (flow.stages, flow.time) = (stages.into_iter().collect(), time);
    fields::build(flow);
    // The E0808 of the flow first: the E0200 of a clock past the Core is of no limit decided.
    if let Some(p) = past_at {
        a.diagnostics.push(past_path(pkg, a, f, p, most));
    } else if !unmade_at.is_empty() {
        let text = crate::module_of_def(pkg, a, f).map(|m| m.text.clone()).unwrap_or_default();
        for at in unmade_at {
            let d = onsa_diag::unsupported::Feature::ComposedClocks.diagnostic(Stage::Flow, at, &[]);
            a.diagnostics.push(d.with_found(at.text_in(&text).to_string()));
        }
    }
    counted.then_some(count)
}

/// Where the chain of the instance `n` of the callee `g` makes a clock the
/// Core does not ([`Ratio::made_n`]), of its entries `entries`: the
/// modifier of the first boundary out of which a port of the part it wraps
/// faster than `sample` is past it (an array of a `.down~` outside or the
/// value is of it), else the call, of a stage of the caller past it that
/// `g` has not (that of its own chains, told there). A port or a stage
/// slower than `sample` inside the chain is of no counter: the runs of an
/// `.up~` at a slower stage are one ([`Op::Each`]).
// SPEC-GAP(S-1216): no limit of a composed clock is decided (`sample * N`,
// `sample / N` past `U32`); one the Core does not make is E0200.
fn unmade(n: &PlanNode, g: &FlowInfo, entries: &[Entry]) -> Option<Span> {
    let made = |k: Ratio| !k.faster_than_body() || k.made_n().is_some();
    let port = n.bounds.iter().find(|b| !b.ins.iter().flatten().chain(&b.out).all(|&k| made(b.outside(k))));
    if let Some(b) = port {
        return Some(n.chain.get(b.at as usize).map_or(n.span, |m| m.name));
    }
    let past = |s: &ClockStage| matches!(*s, ClockStage::Tick(k) if k.made_n().is_none());
    (entries.iter().any(|e| past(&e.caller)) && !g.stages.iter().any(past)).then_some(n.span)
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
