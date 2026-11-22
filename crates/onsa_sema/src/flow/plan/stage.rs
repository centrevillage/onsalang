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
    /// it back (§11.3, S-1186, R-92): a field hoisted to a tick, and that of
    /// a `let` or an input of a tick read at a faster stage. The Core
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

    /// Whether the flow counts the time (§11.4, §11.9): it has a tick
    /// slower than its `sample` ([`FlowInfo::stages`]) or reads
    /// `sample_tick()`. Its state has the counter of the phase (`_tick`).
    pub fn counts_time(&self) -> bool {
        !self.stages.is_empty() || !self.sample_tick_calls.is_empty()
    }

    /// The first place of the plan (by its place) the Core does not lower
    /// until a later unit of W7-16, which stops at it (E0200, R-91 (1)): a
    /// port of a derived clock (§11.9); a node with a chain of modifiers
    /// (`.down~(2).up~(2)` of the ratio one too); a call of a conversion
    /// flow (an instance of a ratio, or that reads an argument at one); and
    /// an instance of a flow of `flows` that counts the time
    /// ([`FlowInfo::counts_time`]), whose ticks and time no caller gives
    /// yet. The one gate of them (D-15).
    pub fn multirate_at(&self, flows: &HashMap<DefId, FlowInfo>) -> Option<Span> {
        let reads = |n: &PlanNode| n.args.iter().any(|a| a.at.of_ratio());
        let times = |callee: &DefId| flows.get(callee).is_some_and(FlowInfo::counts_time);
        let stops = |n: &&PlanNode| match &n.kind {
            PlanKind::Instance { callee, .. } => n.clock.of_ratio() || reads(n) || times(callee),
            _ => false,
        } || !n.chain.is_empty();
        let all = self.derived_port.into_iter().chain(self.nodes.iter().filter(stops).map(|n| n.span));
        all.min_by_key(|s| (s.start, s.end))
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

/// The ticks of the body of `info` slower than its `sample`, slowest
/// first ([`FlowInfo::stages`]): of its inputs, `let`s, nodes and hoisted
/// fields.
pub(super) fn slow_stages(info: &FlowInfo) -> Vec<ClockStage> {
    let inputs = info.inputs.iter().filter_map(|&l| info.own_stage(l));
    let lets = info.lets.iter().filter_map(|l| l.stage.stage());
    let nodes = info.nodes.iter().filter_map(|n| n.clock.stage());
    let all = inputs.chain(lets).chain(nodes).chain(info.hoists.iter().map(|h| h.stage));
    let slow: BTreeSet<ClockStage> = all.filter(|s| s.tick_slower_than(ClockStage::SAMPLE)).collect();
    slow.into_iter().collect()
}

#[cfg(test)]
mod tests;
