//! What each stage of a flow reads (§11.3, §11.4, S-05): the questions the
//! lowering asks of the plan for the function of a stage, so that it does
//! not judge them itself (R-91 (1)).

use super::*;

impl FlowInfo {
    /// The stage of the local `l` (of an input its `body_clock`, of a `let`
    /// its stage, S-1196); `None` of a constant or a local the walk gave no
    /// clock ([`ClockInfo::own_stage`]).
    pub fn own_stage(&self, l: LocalId) -> Option<ClockStage> {
        self.clocks.own_stage(l)
    }

    /// Whether the field `of` is written at a tick and read at a faster
    /// stage, so that it starts at `T.default()` at `init` and `reset` sets
    /// it back (§11.3, S-1186, R-92): a field hoisted to a tick, that of a
    /// `let` or an input of a tick read at a faster stage, and the rings and
    /// the arrays of a chain (§11.9: at the phase 0). The Core
    /// writes it so at `init` and `reset` (W7-16); W8-07 and W7-10 read it.
    pub fn starts_default(&self, of: FieldOf) -> bool {
        let read_faster = |l: LocalId| {
            let reads = self.read_at.get(&l).into_iter().flatten();
            self.own_stage(l).is_some_and(|own| reads.into_iter().any(|&s| own.tick_slower_than(s)))
        };
        self.field_at(of).is_some()
            && match of {
                FieldOf::Hoist(h) => matches!(self.hoist(h).stage, ClockStage::Tick(_)),
                FieldOf::Input(l) | FieldOf::Let(l) => read_faster(l),
                // The rings a chain gathers in and the arrays it deals from (§11.9, phase 0).
                FieldOf::Node(_, Part::Gather { .. } | Part::Deal(_)) => true,
                _ => false,
            }
    }

    /// The field of the state that keeps the local `l` (an input or a local
    /// of a `let`), if there is one.
    pub fn kept_field(&self, l: LocalId) -> Option<FieldOf> {
        [FieldOf::Input(l), FieldOf::Let(l)].into_iter().find(|&of| self.field_at(of).is_some())
    }

    /// Whether the stage `stage` reads `v` from the state (S-05): the state
    /// keeps it and its own stage is another (that of `sample_rate()` is
    /// `init`).
    pub fn from_state(&self, v: Kept, stage: ClockStage) -> bool {
        match v {
            Kept::Local(l) => {
                self.kept_field(l).is_some() && self.own_stage(l).map(|s| self.run_stage(s)) != Some(stage)
            }
            Kept::SampleRate => self.stored(Kept::SampleRate) && stage != ClockStage::Init,
        }
    }

    /// Every stage some local is read at ([`FlowInfo::read_at`]), once or more.
    pub fn read_stages(&self) -> impl Iterator<Item = ClockStage> + '_ {
        self.read_at.values().flatten().copied()
    }

    /// The stage whose function evaluates what is of the stage `s`
    /// (§11.9, R-91 (1)): a tick faster than the `sample` of the body (the
    /// `sample * N` of the caller) is of the function of that `sample`,
    /// another stage of its own. The one place of it: the Core asks it of
    /// every stage it lowers and judges none itself.
    pub fn run_stage(&self, s: ClockStage) -> ClockStage {
        match s {
            ClockStage::Tick(k) if k.faster_than_body() => ClockStage::SAMPLE,
            s => s,
        }
    }

    /// Whether the flow counts the time (§11.4, §11.9): it has a stage
    /// slower than its `sample` ([`FlowInfo::stages`], those of its callees
    /// too) or reads the time ([`FlowInfo::reads_time`]). Its state has the
    /// counter of the phase (`_tick`).
    pub fn counts_time(&self) -> bool {
        !self.stages.is_empty() || self.reads_time
    }

    /// The stage of the function a node is read in ([`FlowInfo::run_stage`]
    /// of its clock): a delay's stores there too, an instance's value is
    /// read there; none of a `par~`, whose replicas run where its body is
    /// read. The one place of it (D-15).
    pub fn node_stage(&self, id: NodeId) -> Option<ClockStage> {
        let n = self.node(id);
        match n.kind {
            PlanKind::Par { .. } => None,
            _ => n.clock.stage().map(|s| self.run_stage(s)),
        }
    }

    /// The first place of the plan (by its place) the Core does not lower
    /// until a later unit of W7-16, which stops at it (E0200, R-91 (1)): a
    /// node with a chain the Core does not lower yet
    /// ([`PlanNode::lowered_chain`]), and an instance that gathers or deals
    /// a burst in this flow (its clock, or that of an argument it reads, at
    /// `sample * N`, §11.9). The one gate of them (D-15).
    pub fn multirate_at(&self) -> Option<Span> {
        let stops = |n: &&PlanNode| match &n.kind {
            PlanKind::Instance { .. } => n.clock.burst() || n.args.iter().any(|a| a.at.burst()),
            _ => false,
        } || !n.lowered_chain();
        self.nodes.iter().filter(stops).map(|n| n.span).min_by_key(|s| (s.start, s.end))
    }

    /// The `let`s of the stage `stage`, in their order (§11.4).
    pub fn lets_at(&self, stage: ClockStage) -> impl Iterator<Item = &FlowLet> {
        self.lets.iter().filter(move |l| l.stage.stage() == Some(stage))
    }

    /// The `let`s of a constant a local of which is read at the stage
    /// `stage`, in their order: the function of the stage defines them
    /// (§11.3, [`FlowInfo::read_at`]).
    pub fn consts_at(&self, stage: ClockStage) -> impl Iterator<Item = &FlowLet> {
        let read =
            move |v: &LocalId| self.read_at.get(v).is_some_and(|r| r.iter().any(|&s| self.run_stage(s) == stage));
        self.lets.iter().filter(move |l| l.stage == Clock::Const && l.locals.iter().any(read))
    }
}

impl PlanNode {
    /// Whether the Core lowers the chain of the node (§11.9, S-1207): none,
    /// or one of an instance whose modifiers are all `.down~(N)`, whose
    /// boundaries but the innermost gather and deal nothing (U6b of W7-16),
    /// of a callee that reads no time (`timed`: U6a3 of W7-16 lifts it,
    /// S-1217); a burst it gathers or deals in its caller stops the gate on
    /// its own. The one test of it (D-15): the gate
    /// ([`FlowInfo::multirate_at`]) and the Core, which runs a stage of a
    /// callee of no other chain, read it.
    pub fn lowered_chain(&self) -> bool {
        let downs = || self.chain.iter().all(|m| m.ratio.is_some_and(Ratio::slower_than_body));
        let plain = || self.bounds.iter().skip(1).all(|b| b.gathers.is_empty() && !b.deals);
        self.chain.is_empty() || matches!(self.kind, PlanKind::Instance { .. }) && !self.timed && downs() && plain()
    }

    /// Whether its chain deals the output of its head (§11.9): its value is
    /// read from the array, not where a stage of the head runs. The runs
    /// ([`Run::at_read`]) and the Core read it.
    pub fn deals(&self) -> bool {
        self.dealt_at().is_some()
    }

    /// The boundary whose array the stage of the head that makes its output
    /// writes and the caller reads (§11.9), of a chain that deals: the
    /// innermost that deals, the one the gate passes
    /// ([`PlanNode::lowered_chain`]). The one test of it (D-15).
    pub fn dealt_at(&self) -> Option<u32> {
        self.bounds.iter().position(|b| b.deals).and_then(|b| u32::try_from(b).ok())
    }

    /// The stage of this flow the stage `s` of the frame around the
    /// boundary `b` is (§11.9): `s` moved out of each boundary outside it
    /// by its `maps`, as the walk of the table made them; the stage of the
    /// function that writes a ring of `b` (of [`PlanBound::gathers`]). None
    /// of a stage no `maps` has (of a callee with no table).
    pub fn outer_stage(&self, b: usize, s: ClockStage) -> Option<ClockStage> {
        let moved = |s: ClockStage, o: &PlanBound| o.maps.iter().find(|m| m.0 == s).map(|m| m.1);
        self.bounds.get(b + 1..)?.iter().try_fold(s, moved)
    }
}

/// The ticks of the body of `info` slower than its `sample`, slowest
/// first ([`FlowInfo::stages`]): of its inputs, `let`s, nodes and hoisted
/// fields, and of its output.
pub(super) fn slow_stages(info: &FlowInfo) -> Vec<ClockStage> {
    // S-1213: an output at `sample / N` is made at its own tick, so a
    // value of a parameter kind it reads is the one of that tick until the next.
    let inputs = info.inputs.iter().filter_map(|&l| info.own_stage(l)).chain(info.out_stage);
    let lets = info.lets.iter().filter_map(|l| l.stage.stage());
    let nodes = info.nodes.iter().filter_map(|n| n.clock.stage());
    let all = inputs.chain(lets).chain(nodes).chain(info.hoists.iter().map(|h| h.stage));
    let slow: BTreeSet<ClockStage> = all.filter(|s| s.tick_slower_than(ClockStage::SAMPLE)).collect();
    slow.into_iter().collect()
}

#[cfg(test)]
mod tests;
