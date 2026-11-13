//! The states of the walk (§5.2, §7): how the paths through a region leave
//! each binding ([`Ends`]), the effect of a region on any state (one type,
//! [`Delta`], for a state, an effect and a loop's summary), the state of a
//! walk with the record of its changes ([`Trail`]: the paths from a mark,
//! [`Paths`], joined in the time of the changes, not of the table), and a
//! loop's summary ([`LoopSum`]).

use std::collections::BTreeMap;
use std::mem::replace;

use onsa_diag::internal::bug;

use onsa_diag::Span;

use crate::body::LocalId;

/// What a binding is at a point, if not live: moved (`via_loop`: by the back
/// edge of a loop, §5.2's E0704), or unusable where it overlaps a place
/// changed at one of `changes` (§7, §5.4, S-803: the place's number in
/// `Walker`'s `Made`, and where).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Status {
    Moved { at: Span, via_loop: bool },
    Stale { changes: BTreeMap<u32, Span> },
}

impl Status {
    /// A semilattice (so the order of a join does not matter): moved over
    /// stale; of two moved the earlier place, then not by the loop; of two
    /// stale the changes of both, of one place the earlier. The first reason
    /// stays: an E0704 names the first move (§5.2).
    fn join(&mut self, other: &Status) {
        match (&mut *self, other) {
            (Status::Moved { .. }, Status::Stale { .. }) => {}
            (Status::Stale { .. }, Status::Moved { .. }) => *self = other.clone(),
            (Status::Moved { at, via_loop }, &Status::Moved { at: b, via_loop: v }) => {
                if (b, v) < (*at, *via_loop) {
                    (*at, *via_loop) = (b, v);
                }
            }
            (Status::Stale { changes }, Status::Stale { changes: more }) => {
                for (&k, &c) in more {
                    changes.entry(k).and_modify(|x| *x = (*x).min(c)).or_insert(c);
                }
            }
        }
    }

    /// The same, by the back edge of a loop.
    fn by_loop(&self) -> Status {
        match self {
            &Status::Moved { at, .. } => Status::Moved { at, via_loop: true },
            s => s.clone(),
        }
    }
}

/// `a ⊔ b` of two maybe-statuses, `None` the unit.
fn join_dead(a: &mut Option<Status>, b: Option<&Status>) {
    match (a.as_mut(), b) {
        (_, None) => {}
        (None, Some(s)) => *a = Some(s.clone()),
        (Some(x), Some(s)) => x.join(s),
    }
}

/// How the paths through a region leave a binding: some go `through` it
/// untouched (they keep the state before), some end with it not live
/// (`dead`, the first reason), some end with it live again (`live`: declared
/// or assigned as a whole). Not in a table: [`Ends::SAME`], all go through.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Ends {
    through: bool,
    dead: Option<Status>,
    live: bool,
}

impl Ends {
    /// The identity of [`Ends::then`]: no path touches the binding.
    const SAME: Ends = Ends { through: true, dead: None, live: false };

    /// Declared, or assigned as a whole: no path goes through. (Not yet
    /// `live`: the drops that read it come later; the state reads `dead`.)
    const NEW: Ends = Ends { through: false, dead: None, live: false };

    /// The paths of both: `self ⊔ other`, each field joined.
    fn join(&mut self, other: &Ends) {
        self.through |= other.through;
        self.live |= other.live;
        join_dead(&mut self.dead, other.dead.as_ref());
    }

    /// The paths of `self`, then of `next`: those of `next` that go through
    /// it keep what `self` left (associative; it distributes over the join).
    fn then(&self, next: &Ends) -> Ends {
        let mut dead = next.dead.clone();
        if next.through {
            join_dead(&mut dead, self.dead.as_ref());
        }
        Ends { through: self.through && next.through, dead, live: next.live || (next.through && self.live) }
    }
}

/// The effect of a region on any state: the [`Ends`] of each binding it
/// touches (the others [`Ends::SAME`], and not kept, so the table does not
/// grow); `reach == false`: no path falls through. It is the state at a
/// point too, as the effect of the body up to it on the state where all is
/// live: the bindings with `dead` may not be live there. Both walks carry
/// it (in a [`Trail`]), the one that reports and the one that makes a
/// loop's summary, so
/// their states differ only where the second does not know the state before
/// the loop (the text of an E0704 at a loop's head, not whether it is one).
/// Every operation keeps an unreachable state unreachable.
#[derive(Clone, Debug)]
pub(super) struct Delta {
    reach: bool,
    ends: BTreeMap<LocalId, Ends>,
}

impl Delta {
    /// Where the walk starts: all live (the identity).
    pub(super) fn start() -> Delta {
        Delta { reach: true, ends: BTreeMap::new() }
    }

    /// No path reaches here (the unit of the join).
    pub(super) fn bottom() -> Delta {
        Delta { reach: false, ends: BTreeMap::new() }
    }

    /// This state, then the region `next`.
    pub(super) fn then(&self, next: &Delta) -> Delta {
        if !(self.reach && next.reach) {
            return Delta::bottom();
        }
        let mut out = self.clone();
        for (&l, e) in &next.ends {
            let ends = out.ends.get(&l).unwrap_or(&Ends::SAME).then(e);
            out.put(l, ends);
        }
        out
    }

    /// Why `l` may not be live here, the first reason; `None`: live.
    pub(super) fn status(&self, l: LocalId) -> Option<&Status> {
        self.ends.get(&l)?.dead.as_ref()
    }

    /// `l` is `s` here; it joins (a binding moved twice keeps the first).
    pub(super) fn set(&mut self, l: LocalId, s: Status) {
        match &mut self.ends.entry(l).or_insert(Ends::SAME).dead {
            Some(x) => x.join(&s),
            dead => *dead = Some(s),
        }
    }

    /// Live again: declared, or assigned as a whole.
    pub(super) fn revive(&mut self, l: LocalId) {
        self.ends.insert(l, Ends::NEW);
    }

    /// Out of the table: a binding whose scope ended (no later point reads it).
    pub(super) fn forget(&mut self, l: LocalId) {
        self.ends.remove(&l);
    }

    /// The paths of both (`self ⊔ other`): an unreachable side is the unit.
    /// What the joins of a [`Trail`] equal (the walks join on it only).
    #[cfg(test)]
    pub(super) fn join(&mut self, other: &Delta) {
        if !other.reach {
            return;
        }
        if !self.reach {
            return *self = other.clone();
        }
        // The two tables in the order of their bindings, side by side; a
        // binding one side does not touch is `SAME` there. Of two in the
        // tables (neither `SAME`) the join is not `SAME`.
        let mut theirs = other.ends.iter().peekable();
        let (mut new, mut gone) = (Vec::new(), Vec::new());
        let same = |o: &Ends| {
            let mut e = Ends::SAME;
            e.join(o);
            e
        };
        for (&l, e) in self.ends.iter_mut() {
            while let Some((&k, o)) = theirs.next_if(|&(&k, _)| k < l) {
                new.push((k, same(o)));
            }
            match theirs.next_if(|&(&k, _)| k == l) {
                Some((_, o)) => e.join(o),
                None => e.through = true,
            }
            if *e == Ends::SAME {
                gone.push(l);
            }
        }
        new.extend(theirs.map(|(&k, o)| (k, same(o))));
        for l in gone {
            self.ends.remove(&l);
        }
        self.ends.extend(new.into_iter().filter(|(_, e)| *e != Ends::SAME));
    }

    /// `l` leaves the region as `e`; [`Ends::SAME`] is not kept.
    fn put(&mut self, l: LocalId, e: Ends) {
        if e == Ends::SAME {
            self.ends.remove(&l);
        } else {
            self.ends.insert(l, e);
        }
    }
}

/// A change of a walk's state, to undo: a binding's [`Ends`] before it
/// (`None`: not in the table), or the whole state before it stopped.
#[derive(Clone, Debug)]
enum Undo {
    Ends(LocalId, Option<Ends>),
    Stop(Delta),
}

/// The state of a walk and the record of its changes (X-20 A): a mark is
/// the length of the record. Each path from a mark (a branch, an arm, to a
/// `break`) joins its changes into [`Paths`] and is undone, the next walks
/// from the same state, and the state after is that of the paths: the work
/// is of the bindings changed, not of the table. A state that stopped (no
/// path falls through) is that of [`Delta::bottom`]; a path goes on from a
/// mark only if it has not stopped since.
pub(super) struct Trail {
    now: Delta,
    log: Vec<Undo>,
}

impl Trail {
    pub(super) fn new() -> Trail {
        Trail { now: Delta::start(), log: Vec::new() }
    }

    pub(super) fn state(&self) -> &Delta {
        &self.now
    }

    /// A change `f` of the binding `l` ([`Delta::set`], `revive`, `forget`), recorded.
    pub(super) fn change(&mut self, l: LocalId, f: impl FnOnce(&mut Delta)) {
        self.keep(l);
        f(&mut self.now);
    }

    /// No path falls through (`return`, `break`, a call that does not come
    /// back): the state of [`Delta::bottom`], the one before kept.
    pub(super) fn stop(&mut self) {
        let before = replace(&mut self.now, Delta::bottom());
        self.log.push(Undo::Stop(before));
    }

    /// This state, then the region `next` (each binding `next` touches).
    pub(super) fn then(&mut self, next: &Delta) {
        if !(self.now.reach && next.reach) {
            return self.stop();
        }
        for (&l, e) in &next.ends {
            let ends = self.get(l).then(e);
            self.put(l, ends);
        }
    }

    pub(super) fn mark(&self) -> usize {
        self.log.len()
    }

    /// The state at the mark `m`, the changes since undone.
    pub(super) fn back_to(&mut self, m: usize) {
        let Trail { now, log } = self;
        for u in log.drain(m..).rev() {
            match u {
                Undo::Ends(l, Some(e)) => drop(now.ends.insert(l, e)),
                Undo::Ends(l, None) => drop(now.ends.remove(&l)),
                Undo::Stop(before) => *now = before,
            }
        }
    }

    /// `paths ⊔=` this state, a path from the mark `m` (of `paths` too).
    pub(super) fn join_into(&self, m: usize, paths: &mut Paths) {
        if !self.now.reach {
            return;
        }
        let at = self.since(m);
        let Paths { ends: Delta { reach, ends }, lone } = paths;
        let first = !replace(reach, true);
        // Changed on every path before, not on this one: as at the mark here.
        lone.retain(|l| {
            let kept = at.contains_key(l);
            match ends.get_mut(l) {
                Some(e) if !kept => e.join(self.get(*l)),
                Some(_) => {}
                None => bug(None, "a binding every path changed and none kept"),
            }
            kept
        });
        for (l, was) in at {
            let now = self.get(l);
            if let Some(e) = ends.get_mut(&l) {
                e.join(now);
            } else if *now != was {
                let mut e = now.clone();
                match first {
                    true => lone.push(l),
                    false => e.join(&was),
                }
                ends.insert(l, e);
            }
        }
    }

    /// Back to the mark `m`, then the state of `paths` from it (stopped if
    /// none falls through).
    pub(super) fn settle(&mut self, m: usize, paths: &Paths) {
        self.back_to(m);
        if !paths.ends.reach {
            return self.stop();
        }
        for (&l, e) in &paths.ends.ends {
            self.put(l, e.clone());
        }
    }

    /// The bindings changed since the mark `m`, each as it was at `m`.
    fn since(&self, m: usize) -> BTreeMap<LocalId, Ends> {
        let mut at = BTreeMap::new();
        for u in self.log[m..].iter().rev() {
            match u {
                Undo::Ends(l, e) => drop(at.insert(*l, e.clone().unwrap_or(Ends::SAME))),
                Undo::Stop(_) => bug(None, "a path that stopped and goes on"),
            }
        }
        at
    }

    fn get(&self, l: LocalId) -> &Ends {
        self.now.ends.get(&l).unwrap_or(&Ends::SAME)
    }

    /// The change of `l`, recorded.
    fn keep(&mut self, l: LocalId) {
        self.log.push(Undo::Ends(l, self.now.ends.get(&l).cloned()));
    }

    fn put(&mut self, l: LocalId, e: Ends) {
        if *self.get(l) != e {
            self.keep(l);
            self.now.put(l, e);
        }
    }
}

/// The join of paths from a mark of a [`Trail`] (two branches, the arms of
/// a `match`, a loop's `break`s): the [`Ends`] of each binding a path
/// changed, as a state's are (a binding not here is as at the mark on
/// every path; unlike a state's table, [`Ends::SAME`] stays, of a binding
/// forgotten). `lone`: those every path changed, which do not hold the
/// ends at the mark (each other path joins it in, `Trail::join_into`).
pub(super) struct Paths {
    ends: Delta,
    lone: Vec<LocalId>,
}

impl Paths {
    /// No path.
    pub(super) fn none() -> Paths {
        Paths { ends: Delta::bottom(), lone: Vec::new() }
    }
}

/// A loop's summary, made once: the back edge from its head (through the
/// condition of a `while` and the body, and its `continue`s), and its exit
/// from the state before its head (the end of the condition or of the
/// iteration, and its `break`s).
#[derive(Clone, Debug)]
pub(super) struct LoopSum {
    pub(super) back: Delta,
    pub(super) exit: Delta,
}

impl LoopSum {
    /// The head from the state `x` before it, the least solution of
    /// `h = x ⊔ back(h)`. Each field of a binding solves alone:
    /// `h.dead = x.dead ⊔ back.dead ⊔ (back.through ? h.dead)` is least at
    /// `x.dead ⊔ back.dead`, and `live` the same, so the head's effect is
    /// `{through: true, dead: back.dead (by the loop), live: back.live}`:
    /// no iteration. A back edge no path reaches leaves `x`.
    pub(super) fn head(back: &Delta) -> Delta {
        let mut head = Delta::start();
        if back.reach {
            for (&l, e) in &back.ends {
                let ends = Ends { through: true, dead: e.dead.as_ref().map(Status::by_loop), live: e.live };
                head.put(l, ends);
            }
        }
        head
    }
}

#[cfg(test)]
mod tests;
