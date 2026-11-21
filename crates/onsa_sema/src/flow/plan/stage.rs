//! What each stage of a flow reads (§11.3, §11.4, S-05): the questions the
//! lowering asks of the plan for the function of a stage, so that it does
//! not judge them itself (R-91 (1)).

use super::*;

impl FlowInfo {
    /// The stage of the local `l` (of an input its `api_clock`, of a `let`
    /// its stage, S-1196); `None` of a constant or a local the walk gave no
    /// clock. The one place of the stage of a local.
    pub fn own_stage(&self, l: LocalId) -> Option<ClockStage> {
        self.clocks.local_stage(l).and_then(Clock::stage)
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
    /// tick of a ratio (`sample / N`, §11.3): the Core lowers no stage of it
    /// until W7-16, which stops at it (E0200, R-91 (1)).
    pub fn multirate_at(&self) -> Option<Span> {
        let lets = self.lets.iter().filter(|l| l.stage.of_ratio()).map(|l| l.span);
        let nodes = self.nodes.iter().filter(|n| n.clock.of_ratio()).map(|n| n.span);
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
