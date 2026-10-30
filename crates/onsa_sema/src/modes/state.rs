//! The states of the walk (W4-07 memo 1.2, 3): which bindings are not live
//! at a point, the effect of a region on any state (one type for both), and
//! a loop's summary.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};

use onsa_diag::Span;

use crate::body::LocalId;

/// What a binding is at a point, if not live: moved (`via_loop`: by the back
/// edge of a loop, §5.2's E0704), or unusable where it overlaps a place
/// changed at one of `changes` (§7, §5.4, S-803: kept in `Walker`'s `Made`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Status {
    Moved { at: Span, via_loop: bool },
    Stale { changes: BTreeMap<u32, Span> },
}

impl Status {
    /// A semilattice: moved over stale, of two moved the earlier place, then
    /// not by the loop; of two stale the changes of both.
    fn join(self, other: Status) -> Status {
        match (self, other) {
            (Status::Stale { mut changes }, Status::Stale { changes: more }) => {
                for (k, at) in more {
                    changes.entry(k).and_modify(|c| *c = (*c).min(at)).or_insert(at);
                }
                Status::Stale { changes }
            }
            (s @ Status::Moved { .. }, Status::Stale { .. }) | (Status::Stale { .. }, s @ Status::Moved { .. }) => s,
            (Status::Moved { at, via_loop }, Status::Moved { at: b, via_loop: v }) => {
                let key = |at: Span, v: bool| Reverse((at.start, at.end, v));
                if key(b, v) > key(at, via_loop) {
                    Status::Moved { at: b, via_loop: v }
                } else {
                    Status::Moved { at, via_loop }
                }
            }
        }
    }
}

type Out = BTreeMap<LocalId, Status>;

fn join_into(into: &mut Out, from: &Out) {
    for (&l, s) in from {
        match into.remove(&l) {
            Some(t) => into.insert(l, t.join(s.clone())),
            None => into.insert(l, s.clone()),
        };
    }
}

/// The effect of a region on any state `x` (memo 3, the gen/kill form):
/// `gens ⊔ (x − kill)`, a binding declared or assigned again in `kill`;
/// `reach == false`: it does not fall through. It is the state at a point
/// too, as the effect of the body up to it on the state where all is live:
/// the bindings in `gens` are not live there. Both walks carry it, the one
/// that reports and the one that makes a loop's summary (memo 1.2), so their
/// states differ only where the second does not know the state before the
/// loop (review 12: the text of an E0704 at a loop's head). Every operation
/// keeps an unreachable state unreachable.
#[derive(Debug, Clone, Default, PartialEq)]
pub(super) struct Delta {
    reach: bool,
    kill: BTreeSet<LocalId>,
    gens: Out,
}

impl Delta {
    /// Where the walk starts: all live (the identity).
    pub(super) fn start() -> Delta {
        Delta { reach: true, ..Delta::default() }
    }

    /// No path reaches here (the unit of the join).
    pub(super) fn bottom() -> Delta {
        Delta::default()
    }

    /// This state, then the region `next`.
    pub(super) fn then(&self, next: &Delta) -> Delta {
        if !self.reach || !next.reach {
            return Delta::default();
        }
        let mut gens: Out =
            self.gens.iter().filter(|(l, _)| !next.kill.contains(l)).map(|(&l, s)| (l, s.clone())).collect();
        join_into(&mut gens, &next.gens);
        Delta { reach: true, kill: self.kill.union(&next.kill).copied().collect(), gens }
    }

    pub(super) fn status(&self, l: LocalId) -> Option<&Status> {
        self.gens.get(&l)
    }

    /// `l` is `s` here; it joins (a binding moved twice keeps the first).
    pub(super) fn set(&mut self, l: LocalId, s: Status) {
        if self.reach {
            let s = match self.gens.remove(&l) {
                Some(t) => t.join(s),
                None => s,
            };
            self.gens.insert(l, s);
        }
    }

    /// Live again: declared, or assigned as a whole.
    pub(super) fn revive(&mut self, l: LocalId) {
        if self.reach {
            self.kill.insert(l);
            self.gens.remove(&l);
        }
    }

    /// Out of the table: a binding whose scope ended (no later point reads it).
    pub(super) fn forget(&mut self, l: LocalId) {
        self.kill.remove(&l);
        self.gens.remove(&l);
    }

    pub(super) fn join(&mut self, other: &Delta) {
        match (self.reach, other.reach) {
            (_, false) => {}
            (false, true) => *self = other.clone(),
            (true, true) => {
                join_into(&mut self.gens, &other.gens);
                self.kill.retain(|l| other.kill.contains(l));
            }
        }
    }
}

/// A loop's summary, made once: the back edge from its head (through the
/// condition of a `while` and the body, and its `continue`s), and its exit
/// from the state before its head (the end of the condition or of the
/// iteration, and its `break`s).
#[derive(Debug, Clone)]
pub(super) struct LoopSum {
    pub(super) back: Delta,
    pub(super) exit: Delta,
}

impl LoopSum {
    /// The head from the state `x` before it: `x ⊔ G` for the `gens` G of the
    /// back edge, the least solution of `h = x ⊔ back(h)` (memo 3).
    pub(super) fn head(back: &Delta) -> Delta {
        let by_loop = |s: Status| match s {
            Status::Moved { at, .. } => Status::Moved { at, via_loop: true },
            s => s,
        };
        Delta {
            reach: true,
            kill: BTreeSet::new(),
            gens: back.gens.iter().map(|(&l, s)| (l, by_loop(s.clone()))).collect(),
        }
    }
}
