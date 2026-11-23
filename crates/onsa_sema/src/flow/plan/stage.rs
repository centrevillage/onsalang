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
                // The held output of a guard, until it first runs (§11.10).
                FieldOf::Node(_, Part::Held(_)) => true,
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
        self.counter() != Counter::None
    }

    /// Where its counter of the phase advances (§11.9, S-1217): at the end
    /// of `tick` of the grid of its slower stages (a callee's too, whose
    /// phase its chains read), else, of the time alone, in the outermost
    /// `process`. The one test of it (D-15, R-91 (1)).
    pub fn counter(&self) -> Counter {
        match (self.stages.is_empty(), self.reads_time()) {
            (false, _) => Counter::Tick,
            (true, true) => Counter::Process,
            (true, false) => Counter::None,
        }
    }

    /// The words of the time the function of the stage `s` takes: 0 to 2.
    pub fn time_words(&self, s: ClockStage) -> usize {
        self.time.get(&s).map_or(0, |&w| w as usize)
    }

    /// The most words of the time a function of its stages takes, those the
    /// outermost `process` reads of its state: 0 to 2.
    pub fn most_time_words(&self) -> usize {
        self.time.values().max().map_or(0, |&w| w as usize)
    }

    /// Whether it or a flow it runs, through flows, reads `sample_tick()`
    /// (§11.4, S-1129 (1)): a stage of it takes the time.
    pub fn reads_time(&self) -> bool {
        !self.time.is_empty()
    }

    /// Whether a `.down~` is on a path from its body to a reader of
    /// `sample_tick()` (§12.4, S-1211): its state has `_tick_hi`.
    pub fn wide(&self) -> bool {
        self.time.values().any(|&w| w == Words::Two)
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

    /// Whether the `let` k (the output by `lets.len()`) holds a hoisted
    /// field or a check of the stage `s` (`FlowInfo::writes`): the
    /// function of `s` walks it for them (§11.3).
    pub fn writes_in(&self, k: usize, s: ClockStage) -> bool {
        u32::try_from(k).is_ok_and(|k| self.writes.contains(&(k, s)))
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
    /// Its entry of the stage `s` of this flow whose `read` is `read`
    /// (§11.9, [`Entry`]): the one question the Core asks of its work.
    pub fn entry(&self, s: ClockStage, read: bool) -> Option<&Entry> {
        self.entries.iter().find(|e| e.caller == s && e.read == read)
    }

    /// The innermost boundary from the boundary `from` out that gathers the
    /// input `input` of its head (§11.9): of `from` 0, the ring the head
    /// reads it from; of the one outside a boundary, the ring that ring is
    /// written from ([`Feed`]). The one walk of it (D-15).
    pub fn ring_of(&self, from: usize, input: u32) -> Option<u32> {
        let gathers = |b: &(u32, &PlanBound)| b.1.gathers.iter().any(|g| g.0 == input);
        (0u32..).zip(&self.bounds).skip(from).find(gathers).map(|b| b.0)
    }

    /// What the `.reset_if~` at the place `at` of its chain sets back to
    /// `T.default()` (§11.10): the rings and the array of each boundary
    /// inside it and the held output of each guard inside it, not the
    /// conditions and the counts. The one list of it (D-15).
    pub fn reset_parts(&self, at: u32) -> Vec<Part> {
        let mut parts = Vec::new();
        for (b, x) in (0u32..).zip(&self.bounds).filter(|b| b.1.at < at) {
            parts.extend(x.gathers.iter().map(|&(input, _)| Part::Gather { bound: b, input }));
            parts.extend(x.deals.then_some(Part::Deal(b)));
        }
        parts.extend((0u32..).zip(&self.guards).filter(|g| g.1.at < at).map(|g| Part::Held(g.0)));
        parts
    }
}

/// The ticks of the body of `info` slower than its `sample`, slowest
/// first ([`FlowInfo::stages`]): of its inputs and its output, and those
/// the marking evaluates at ([`FlowInfo::eval_at`]).
pub(super) fn slow_stages(info: &FlowInfo) -> Vec<ClockStage> {
    // S-1213: an output at `sample / N` is made at its own tick, so a
    // value of a parameter kind it reads is the one of that tick until the next.
    let inputs = info.inputs.iter().filter_map(|&l| info.own_stage(l)).chain(info.out_stage);
    let all = inputs.chain(info.eval_at.iter().copied());
    let slow: BTreeSet<ClockStage> = all.filter(|s| s.tick_slower_than(ClockStage::SAMPLE)).collect();
    slow.into_iter().collect()
}

#[cfg(test)]
mod tests;
