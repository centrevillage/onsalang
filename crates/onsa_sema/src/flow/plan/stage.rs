//! What each stage of a flow reads (§11.3, §11.4, S-05): the questions the
//! lowering asks of the plan for the function of a stage, so that it does
//! not judge them itself (R-91 (1)).

use super::*;

impl FlowInfo {
    /// The stage of the local `l` (of an input its `api_clock`, of a `let`
    /// its stage, S-1196); `None` of a constant or a local the walk gave no
    /// clock ([`ClockInfo::own_stage`]).
    pub fn own_stage(&self, l: LocalId) -> Option<ClockStage> {
        self.clocks.own_stage(l)
    }

    /// Whether the field `of` is written at a tick and read at a faster
    /// stage, so that it starts at `T.default()` at `init` and `reset` sets
    /// it back (§11.3, S-1186, R-92): a field hoisted to a tick, and that of
    /// a `let` or an input of a tick read at a faster stage. W8-07 and
    /// W7-10 read it.
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
            Kept::Local(l) => self.kept_field(l).is_some() && self.own_stage(l) != Some(stage),
            Kept::SampleRate => self.stored(Kept::SampleRate) && stage != ClockStage::Init,
        }
    }

    /// Every stage some local is read at ([`FlowInfo::read_at`]), once or more.
    pub fn read_stages(&self) -> impl Iterator<Item = ClockStage> + '_ {
        self.read_at.values().flatten().copied()
    }

    /// The first `let` or node (by its place) whose stage is a periodic
    /// tick of a ratio (`sample / N`, §11.3), or a node with a chain of
    /// modifiers, whose ratio may be one (§11.9): the Core lowers no stage
    /// of them until W7-16, which stops at it (E0200, R-91 (1)).
    pub fn multirate_at(&self) -> Option<Span> {
        let lets = self.lets.iter().filter(|l| l.stage.of_ratio()).map(|l| l.span);
        let nodes = self.nodes.iter().filter(|n| n.clock.of_ratio() || !n.chain.is_empty()).map(|n| n.span);
        lets.chain(nodes).min_by_key(|s| (s.start, s.end))
    }

    /// The `let`s of the stage `stage`, in their order (§11.4).
    pub fn lets_at(&self, stage: ClockStage) -> impl Iterator<Item = &FlowLet> {
        self.lets.iter().filter(move |l| l.stage.stage() == Some(stage))
    }

    /// The `let`s of a constant a local of which is read at the stage
    /// `stage`, in their order: the function of the stage defines them
    /// (§11.3, [`FlowInfo::read_at`]).
    pub fn consts_at(&self, stage: ClockStage) -> impl Iterator<Item = &FlowLet> {
        let read = move |v: &LocalId| self.read_at.get(v).is_some_and(|r| r.contains(&stage));
        self.lets.iter().filter(move |l| l.stage == Clock::Const && l.locals.iter().any(read))
    }
}

#[cfg(test)]
mod tests;
