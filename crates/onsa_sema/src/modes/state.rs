//! The states of the walk (§5.2, §7): how the paths through a region leave
//! each binding ([`Ends`]), the effect of a region on any state (one type,
//! [`Delta`], for a state, an effect and a loop's summary), the state of a
//! walk with the record of its changes ([`Trail`]: the paths from a mark,
//! [`Paths`], joined in the time of the changes, not of the table), and a
//! loop's summary ([`LoopSum`]).

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::mem::replace;
use std::rc::Rc;

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::internal::bug;

use onsa_diag::Span;
use onsa_syntax::ast::ExprId;

use crate::body::LocalId;

/// What a binding is at a point, if not live: moved (`via_loop`: by the back
/// edge of a loop, §5.2's E0704), or unusable where it overlaps a place
/// changed at one of `changes` (§7, §5.4, S-803: the place's number in
/// `Walker`'s `Made`, and where), or its Dup value released at the
/// consuming expressions `at` (§5.2, S-1030: moved unless used after,
/// then each a copy and the binding live, `Walker::restore`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Status {
    Moved { at: Span, via_loop: bool },
    Stale { changes: BTreeMap<u32, Span> },
    Released { at: Releases },
}

/// The consuming expressions that released a binding (S-1030), shared by
/// the states that hold them (a copy is made only when a join adds to it).
pub(super) type Releases = Rc<BTreeSet<ExprId>>;

impl Status {
    /// A semilattice (so the order of a join does not matter): moved over
    /// stale; of two moved the earlier place, then not by the loop; of two
    /// stale the changes of both, of one place the earlier; of two released
    /// the releases of both. The first reason stays: an E0704 names the
    /// first move (§5.2). A binding is Affine or Dup, owned or a borrow, so
    /// a release meets no other.
    fn join(&mut self, other: &Status) {
        match (&mut *self, other) {
            (Status::Released { at }, Status::Released { at: more }) => {
                if !Rc::ptr_eq(at, more) {
                    Rc::make_mut(at).extend(more.iter())
                }
            }
            (Status::Released { .. }, _) | (_, Status::Released { .. }) => {
                bug(None, "a release joined with a move or a change of the same binding")
            }
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

    /// Declared, or assigned as a whole: no path goes through, all end live.
    const NEW: Ends = Ends { through: false, dead: None, live: true };

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
/// Every operation keeps an unreachable state unreachable, and its table empty.
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

    /// Whether a path reaches here.
    pub(super) fn reaches(&self) -> bool {
        self.reach
    }

    /// Why `l` may not be live here, the first reason; `None`: live.
    pub(super) fn status(&self, l: LocalId) -> Option<&Status> {
        self.ends.get(&l)?.dead.as_ref()
    }

    /// Whether `l` may hold its value here, and whether surely: live (a
    /// path that reaches here leaves it untouched, declared or assigned),
    /// surely if no path leaves it dead; else, live on no path but by its
    /// releases (`unless`, not empty), held unless each of them moves.
    /// `None`: on no path, or no path reaches here.
    pub(super) fn lives(&self, l: LocalId) -> Option<(bool, Option<&Releases>)> {
        let e = self.ends.get(&l).unwrap_or(&Ends::SAME);
        match &e.dead {
            _ if !self.reach => None,
            _ if e.through || e.live => Some((e.dead.is_none(), None)),
            Some(Status::Released { at }) => Some((false, Some(at))),
            _ => None,
        }
    }

    /// `l` moved here: no path goes through or ends live; the reason joins
    /// (a binding moved twice keeps the first, its E0704 the record only).
    pub(super) fn moved(&mut self, l: LocalId, at: Span) {
        self.consumed(l, Status::Moved { at, via_loop: false });
    }

    /// The Dup value of `l` released by the expression `at`: as a move,
    /// until a use after it ([`Delta::restored`]).
    pub(super) fn released(&mut self, l: LocalId, at: ExprId) {
        self.consumed(l, Status::Released { at: Rc::new(BTreeSet::from([at])) });
    }

    /// Its releases copied (each path that released `l` holds it): live.
    pub(super) fn restored(&mut self, l: LocalId) {
        if let Some(e) = self.ends.get_mut(&l).filter(|e| matches!(e.dead, Some(Status::Released { .. }))) {
            (e.dead, e.live) = (None, true);
        }
    }

    fn consumed(&mut self, l: LocalId, s: Status) {
        if self.reach {
            let e = self.ends.entry(l).or_insert(Ends::SAME);
            (e.through, e.live) = (false, false);
            join_dead(&mut e.dead, Some(&s));
        }
    }

    /// The borrow `l` is unusable here by the change `s` ([`Status::Stale`]);
    /// it joins, and whether it is live is as before (no drop reads it).
    pub(super) fn stale(&mut self, l: LocalId, s: Status) {
        if self.reach {
            join_dead(&mut self.ends.entry(l).or_insert(Ends::SAME).dead, Some(&s));
        }
    }

    /// Live again: declared, or assigned as a whole.
    pub(super) fn revive(&mut self, l: LocalId) {
        if self.reach {
            self.ends.insert(l, Ends::NEW);
        }
    }

    /// Out of the table: a binding whose scope ended (no later point reads it).
    pub(super) fn forget(&mut self, l: LocalId) {
        self.ends.remove(&l);
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
/// (`was`, `None`: not in the table), with its change before in the record
/// (`prev`, its place + 1; 0: none) and whether it (or a later change kept
/// in it, `Trail::keep`) declared the binding; or the whole state before it stopped.
#[derive(Clone, Debug)]
enum Undo {
    Ends { l: LocalId, was: Option<Ends>, prev: usize, declares: bool },
    Stop(Delta),
}

/// The state of a walk and the record of its changes (X-20 A): a mark is
/// the length of the record. Each path from a mark (a branch, an arm, to a
/// `break`) joins its changes into [`Paths`] and is undone, the next walks
/// from the same state, and the state after is that of the paths: the work
/// is of the bindings changed, not of the table. A state that stopped (no
/// path falls through) is that of [`Delta::bottom`] and records no change;
/// a path goes on from a mark only if it has not stopped since. `marks`:
/// those open (innermost last); a binding is recorded once since the
/// innermost (a later change keeps the ends before the first), so a path
/// from a mark finds one change of each binding for each mark open since.
/// `last`: of each binding, the place + 1 of its last change in the record
/// (none: 0, and not kept). `copies`: the releases this walk found used
/// after (S-1030, [`Trail::restore`]); `copied`: the sets of them it added,
/// by their address (each kept, so the address is not used again).
pub(super) struct Trail {
    now: Delta,
    log: Vec<Undo>,
    marks: Vec<usize>,
    last: HashMap<LocalId, usize>,
    copies: HashSet<ExprId>,
    copied: HashMap<*const BTreeSet<ExprId>, Releases>,
}

impl Trail {
    pub(super) fn new() -> Trail {
        let (log, marks, last, copies, copied) = Default::default();
        Trail { now: Delta::start(), log, marks, last, copies, copied }
    }

    /// `l` used: its releases here copy, and it is live ([`Delta::restored`]);
    /// them, unless this walk found the same set used before (a loop's
    /// head, met by each arm: the work of a use is not of the set).
    pub(super) fn restore(&mut self, l: LocalId) -> Option<Releases> {
        let Some(Status::Released { at }) = self.now.status(l) else { return None };
        let at = at.clone();
        self.change(l, |d| d.restored(l));
        if self.copied.insert(Rc::as_ptr(&at), at.clone()).is_some() {
            return None;
        }
        self.copies.extend(at.iter());
        Some(at)
    }

    /// `e` as known now: a path that released at a place that copies holds
    /// the binding (live), so a join meets only the releases that may move
    /// (a set of them does not grow with the joins of the paths before).
    fn known<'e>(&self, e: &'e Ends) -> Cow<'e, Ends> {
        let Some(Status::Released { at }) = &e.dead else { return Cow::Borrowed(e) };
        if !at.iter().any(|x| self.copies.contains(x)) {
            return Cow::Borrowed(e);
        }
        let left: BTreeSet<ExprId> = at.iter().filter(|x| !self.copies.contains(x)).copied().collect();
        let dead = (!left.is_empty()).then(|| Status::Released { at: Rc::new(left) });
        Cow::Owned(Ends { through: e.through, dead, live: true })
    }

    pub(super) fn state(&self) -> &Delta {
        &self.now
    }

    /// A change `f` of the binding `l` ([`Delta::moved`], `released`, `restored`, `stale`, `revive`, `forget`), recorded.
    pub(super) fn change(&mut self, l: LocalId, f: impl FnOnce(&mut Delta)) {
        if self.now.reach {
            self.keep(l, false);
            f(&mut self.now);
        }
    }

    /// `l` declared (live again), recorded as its declaration.
    pub(super) fn declare(&mut self, l: LocalId) {
        if self.now.reach {
            self.keep(l, true);
            self.now.revive(l);
        }
    }

    /// No path falls through (`return`, `break`, a call that does not come
    /// back): the state of [`Delta::bottom`], the one before kept.
    pub(super) fn stop(&mut self) {
        if self.now.reach {
            let before = replace(&mut self.now, Delta::bottom());
            self.log.push(Undo::Stop(before));
        }
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

    /// A mark opened (until [`Trail::settle`]).
    pub(super) fn mark(&mut self) -> usize {
        self.marks.push(self.log.len());
        self.log.len()
    }

    /// The state at the mark `m`, the changes since undone.
    pub(super) fn back_to(&mut self, m: usize) {
        let Trail { now, log, last, .. } = self;
        for u in log.drain(m..).rev() {
            match u {
                Undo::Ends { l, was, prev, .. } => {
                    match prev {
                        0 => drop(last.remove(&l)),
                        p => drop(last.insert(l, p)),
                    }
                    match was {
                        Some(e) => drop(now.ends.insert(l, e)),
                        None => drop(now.ends.remove(&l)),
                    }
                }
                Undo::Stop(before) => *now = before,
            }
        }
    }

    /// `paths ⊔=` this state, a path from the mark `m` (of `paths` too),
    /// which joins them as `how` ([`Joins`]; the work is of the bindings
    /// changed). The one place that decides what a path leaves.
    pub(super) fn join_into(&self, m: usize, paths: &mut Paths, how: Joins) {
        if !self.now.reach {
            return;
        }
        let Paths { ends: Delta { reach, ends }, lone } = paths;
        let first = !replace(reach, true);
        // Changed on every path before, not on this one: as at the mark here.
        lone.retain(|&l| {
            let kept = self.last.get(&l).is_some_and(|&p| p > m);
            match ends.get_mut(&l) {
                Some(e) if !kept => e.join(&self.known(self.get(l))),
                Some(_) => {}
                None => bug(None, "a binding every path changed and none kept"),
            }
            kept
        });
        // Each binding changed since the mark, at its first change since: as it was at the mark.
        for u in &self.log[m..] {
            let Undo::Ends { l, was, prev, declares } = u else { bug(None, "a path that stopped and goes on") };
            if *prev > m {
                continue;
            }
            let leaves = how == Joins::Jumps && (*declares || self.declared_since(*l, m));
            let now = if leaves { Cow::Borrowed(&Ends::SAME) } else { self.known(self.get(*l)) };
            let (l, was) = match ends.get_mut(l) {
                Some(e) => {
                    e.join(&now);
                    continue;
                }
                None => (*l, self.known(was.as_ref().unwrap_or(&Ends::SAME))),
            };
            if now != was {
                let mut e = now.into_owned();
                match first {
                    true => lone.push(l),
                    false => e.join(&was),
                }
                ends.insert(l, e);
            }
        }
    }

    /// The mark `m` closed: back to it, then the state of `paths` from it.
    pub(super) fn settle(&mut self, m: usize, paths: &Paths) {
        if self.marks.pop() != Some(m) {
            bug(None, "a mark settled that is not the innermost open");
        }
        self.reset(m, paths);
    }

    /// Back to the mark `m`, then the state of `paths` from it (stopped if
    /// none falls through); the mark stays open.
    pub(super) fn reset(&mut self, m: usize, paths: &Paths) {
        self.back_to(m);
        if !paths.ends.reach {
            return self.stop();
        }
        for (&l, e) in &paths.ends.ends {
            self.put(l, e.clone());
        }
    }

    /// Whether a change of `l` since the mark `m` declared it.
    fn declared_since(&self, l: LocalId, m: usize) -> bool {
        let mut p = self.last.get(&l).copied().unwrap_or(0);
        while p > m {
            let Undo::Ends { prev, declares, .. } = &self.log[p - 1] else { bug(None, "a change that stopped") };
            if *declares {
                return true;
            }
            p = *prev;
        }
        false
    }

    fn get(&self, l: LocalId) -> &Ends {
        self.now.ends.get(&l).unwrap_or(&Ends::SAME)
    }

    /// The change of `l` (`declares`: its declaration), recorded, unless `l`
    /// has a change since the innermost open mark (which keeps the ends before).
    fn keep(&mut self, l: LocalId, declares: bool) {
        let prev = self.last.get(&l).copied().unwrap_or(0);
        if prev > self.marks.last().copied().unwrap_or(0) {
            let Undo::Ends { declares: d, .. } = &mut self.log[prev - 1] else { bug(None, "a change that stopped") };
            return *d |= declares;
        }
        self.last.insert(l, self.log.len() + 1);
        self.log.push(Undo::Ends { l, was: self.now.ends.get(&l).cloned(), prev, declares });
    }

    fn put(&mut self, l: LocalId, e: Ends) {
        if *self.get(l) != e {
            self.keep(l, false);
            self.now.put(l, e);
        }
    }
}

/// How a path joins the paths from a mark ([`Trail::join_into`]): it falls
/// through the end of its region, or jumps out of it to the join (a `break`, a
/// `continue`, a guard that is false, back to the head of its `match`),
/// the bindings declared since the mark first, as if forgotten, with no
/// drop point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Joins {
    Falls,
    Jumps,
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

    pub(super) fn reaches(&self) -> bool {
        self.ends.reach
    }
}

/// A loop's summary, made once: the back edge from its head (through the
/// condition of a `while` and the body, and its `continue`s), and its exit
/// from the state before its head (the end of the condition or of the
/// iteration, and its `break`s); `leaves`: its condition leaves the loop
/// around it (§7), by paths a summary does not hold.
#[derive(Clone, Debug)]
pub(super) struct LoopSum {
    pub(super) back: Delta,
    pub(super) exit: Delta,
    pub(super) leaves: bool,
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
