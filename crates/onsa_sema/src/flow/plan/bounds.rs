//! The boundaries of a chain of modifiers (§11.9, §11.10, S-1207, S-1214):
//! each `.down~(N)` and `.up~(N)` runs the whole part on its left as one
//! part, so the ports of that part are those of the head moved by the
//! ratios inside it, and it gathers and deals at them by the rule of one
//! `.down~` (§11.9). The one place of the judgement (D-15): the check of
//! E0816 and the plan ([`PlanNode::bounds`]) read it.

use super::*;
use crate::def::FlowDef;
use crate::flow_names::Modifier;

/// The exponent of a declared clock (`sample * 2^k`); none of a parameter
/// kind and of a clock in error.
fn exponent(c: Clock) -> Option<Ratio> {
    match c {
        Clock::Tick(k) => Some(k),
        _ => None,
    }
}

/// The stage `s` of the caller of a part, moved out of a boundary of the
/// ratio `r` (§11.9): `Tick(min(s + r, 0))`, a stage faster than the
/// `sample` of its own caller being of that `sample` (an `.up~` runs it
/// there 2^r times); `init` and `block` as they are. The one rule of it.
pub(in crate::flow) fn step(s: ClockStage, r: Ratio) -> ClockStage {
    match s {
        ClockStage::Tick(k) => ClockStage::Tick(Ratio(k.0.saturating_add(r.0).min(0))),
        s => s,
    }
}

/// The stage of the caller of a chain that runs the stage `s` of the frame
/// of its modifier `from` (of the part it wraps): moved out of each
/// modifier outside it, of a boundary by [`step`], of a guard to its W when
/// slower (§11.10: its stages slower than W run at W, the arm of the table,
/// `steps::when`). Of the condition of a guard, the stage that reads it.
pub(in crate::flow) fn run_at<'a>(
    chain: impl IntoIterator<Item = &'a PlanModifier>,
    guards: &[PlanGuard],
    from: u32,
    s: ClockStage,
) -> ClockStage {
    let outside = (0u32..).zip(chain).skip(from as usize + 1);
    outside.fold(s, |s, (at, m)| match m.ratio {
        Some(r) => step(s, r),
        None => guards.iter().find(|g| g.at == at).map_or(s, |g| s.max(ClockStage::Tick(g.w))),
    })
}

/// The stage of the caller of a chain that reads the condition of its guard
/// `g` (§11.10, S-1209): its W, moved out by [`run_at`]. The one place of it
/// (D-15): the walk of the clocks reads the condition there, and an input of
/// the head no faster than it ([`head_stage`]).
pub(in crate::flow) fn cond_stage<'a>(
    chain: impl IntoIterator<Item = &'a PlanModifier>,
    guards: &[PlanGuard],
    g: &PlanGuard,
) -> ClockStage {
    run_at(chain, guards, g.at, ClockStage::Tick(g.w))
}

/// The stage of the caller that reads an input of the head of a chain read
/// at the stage `s` of its port (§11.10, S-1209: a part a `.when~` stops
/// reads it at the tick of the part, its stages slower than W being run at
/// W): `s` past the stage of each guard that reads its condition, a tick
/// the steps then run at ([`run_at`] being monotone in its stage, the
/// greatest of them is that of the steps of the input). `init` and `block`
/// as they are (of the caller).
pub(in crate::flow) fn head_stage<'a>(
    chain: impl IntoIterator<Item = &'a PlanModifier> + Clone,
    guards: &[PlanGuard],
    s: ClockStage,
) -> ClockStage {
    let conds = guards.iter().map(|g| cond_stage(chain.clone(), guards, g));
    match s {
        ClockStage::Tick(_) => conds.fold(s, ClockStage::max),
        s => s,
    }
}

/// The boundaries of the chain `chain` of an instance of `f`, inner first
/// ([`PlanBound`]): of each modifier with a ratio (not `.when~` and
/// `.reset_if~`), the ports of the part it wraps, the inputs it gathers
/// with the stage of the ring, and whether it deals; no stage, which the
/// walk of the table adds. With them its guards ([`PlanGuard`]): of each
/// `.when~`, the clock W it reads its condition at (§11.10, S-1209), that
/// of the output of the part it wraps where it is slower than the `sample`
/// of its frame, else that `sample`. O(modifiers × inputs).
pub(in crate::flow) fn bounds<'a>(
    chain: impl IntoIterator<Item = &'a PlanModifier>,
    f: &FlowDef,
) -> (Vec<PlanBound>, Vec<PlanGuard>) {
    let mut ins: Vec<Option<Ratio>> = f.inputs.iter().map(|i| exponent(i.caller_clock())).collect();
    let mut out = exponent(f.out_clock);
    let (mut list, mut guards) = (Vec::new(), Vec::new());
    for (at, m) in (0u32..).zip(chain) {
        let Some(r) = m.ratio else {
            // `.reset_if~` is the E0200 of W7-10 U2, which makes no plan.
            if let (Modifier::When, Some(cond)) = (m.modifier, m.cond) {
                let w = out.filter(|k| k.slower_than_body()).unwrap_or(Ratio(0));
                guards.push(PlanGuard { at, cond, w, out });
            }
            continue;
        };
        let fast = |k: Option<Ratio>| k.filter(|k| r.slower_than_body() && k.faster_than_body());
        let gathers = (0u32..).zip(&ins).filter_map(|(i, &k)| fast(k).map(|k| (i, step(ClockStage::Tick(k), r))));
        let gathers = gathers.collect();
        let bound = PlanBound { at, ratio: r, ins: ins.clone(), out, gathers, deals: fast(out).is_some() };
        ins.iter_mut().for_each(|k| *k = k.map(|k| bound.outside(k)));
        out = out.map(|k| bound.outside(k));
        list.push(bound);
    }
    (list, guards)
}
