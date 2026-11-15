//! The laws of the states (`state.rs`), over every combination of the
//! fields of [`Ends`]: the join is a semilattice, `then` has the identity
//! [`Ends::SAME`], is associative and distributes over the join (a trail of
//! changes, undone and joined at a mark, relies on these), the table keeps
//! no identity, and a loop's head is the least fixpoint of `h = x ⊔ back(h)`.

use std::collections::BTreeMap;
use std::rc::Rc;

use onsa_diag::{FileId, Span};
use onsa_syntax::ast::ExprId;

use super::{Delta, Ends, Joins, LoopSum, Paths, Status, Trail, Undo};
use crate::body::LocalId;

impl Delta {
    /// The paths of both (`self ⊔ other`): an unreachable side is the unit.
    /// What the joins of a [`Trail`] equal (the walks join on it only).
    pub(in crate::modes) fn join(&mut self, other: &Delta) {
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
}

fn at(n: u32) -> Span {
    Span::new(FileId(0), n, n + 1)
}

/// Each value of each field: of `dead`, none, moved (two places, by the
/// loop or not) and stale (two places of one change, and another change).
fn all() -> Vec<Ends> {
    let stale = |k, n| Some(Status::Stale { changes: BTreeMap::from([(k, at(n))]) });
    let deads = [
        None,
        Some(Status::Moved { at: at(1), via_loop: false }),
        Some(Status::Moved { at: at(1), via_loop: true }),
        Some(Status::Moved { at: at(2), via_loop: false }),
        stale(0, 3),
        stale(0, 4),
        stale(1, 5),
    ];
    with_deads(&deads)
}

/// Of a binding of a Dup value (S-1030), which is only released: none, and
/// released at one place, another, or both.
fn released() -> Vec<Ends> {
    let rel = |xs: &[u32]| Some(Status::Released { at: Rc::new(xs.iter().map(|&x| ExprId(x)).collect()) });
    with_deads(&[None, rel(&[1]), rel(&[2]), rel(&[1, 2])])
}

fn with_deads(deads: &[Option<Status>]) -> Vec<Ends> {
    let mut out = Vec::new();
    for through in [false, true] {
        for dead in deads {
            for live in [false, true] {
                out.push(Ends { through, dead: dead.clone(), live });
            }
        }
    }
    out
}

fn join(a: &Ends, b: &Ends) -> Ends {
    let mut x = a.clone();
    x.join(b);
    x
}

#[test]
fn the_join_of_ends_is_a_semilattice_with_the_unit_of_none_of_the_paths() {
    let none = Ends { through: false, dead: None, live: false };
    for all in [all(), released()] {
        for a in &all {
            assert_eq!(join(a, a), *a, "idempotent");
            assert_eq!(join(a, &none), *a, "the unit");
            for b in &all {
                assert_eq!(join(a, b), join(b, a), "commutative");
                for c in &all {
                    assert_eq!(join(&join(a, b), c), join(a, &join(b, c)), "associative");
                }
            }
        }
    }
}

#[test]
fn then_of_ends_is_associative_with_the_identity_and_distributes_over_the_join() {
    for all in [all(), released()] {
        for a in &all {
            assert_eq!(Ends::SAME.then(a), *a, "the identity before");
            assert_eq!(a.then(&Ends::SAME), *a, "the identity after");
            for b in &all {
                for c in &all {
                    assert_eq!(a.then(b).then(c), a.then(&b.then(c)), "associative");
                    assert_eq!(join(a, b).then(c), join(&a.then(c), &b.then(c)), "from the right");
                    assert_eq!(a.then(&join(b, c)), join(&a.then(b), &a.then(c)), "from the left");
                }
            }
        }
    }
}

/// The first reason stays: of two moves the earlier place, then not by the
/// loop, over a stale; of one change the earlier place (S-803).
#[test]
fn the_join_keeps_the_first_reason() {
    let dead = |d: Option<Status>| Ends { through: true, dead: d, live: false };
    let moved = |n, via_loop| Some(Status::Moved { at: at(n), via_loop });
    let stale = |n| Some(Status::Stale { changes: BTreeMap::from([(0, at(n))]) });
    assert_eq!(join(&dead(moved(2, false)), &dead(moved(1, true))).dead, moved(1, true));
    assert_eq!(join(&dead(moved(1, true)), &dead(moved(1, false))).dead, moved(1, false));
    assert_eq!(join(&dead(stale(3)), &dead(moved(9, true))).dead, moved(9, true));
    assert_eq!(join(&dead(stale(4)), &dead(stale(3))).dead, stale(3));
}

/// One binding `l` as each [`Ends`], and the unreachable state.
fn deltas() -> Vec<Delta> {
    let mut out = vec![Delta::bottom()];
    for e in all() {
        let mut d = Delta::start();
        d.put(LocalId(0), e);
        out.push(d);
    }
    out
}

fn same(a: &Delta, b: &Delta) -> bool {
    a.reach == b.reach && (!a.reach || a.ends == b.ends)
}

#[test]
fn a_delta_keeps_no_identity_and_the_unreachable_is_the_unit() {
    let all = deltas();
    for a in &all {
        assert!(a.ends.values().all(|e| *e != Ends::SAME));
        let mut x = a.clone();
        x.join(&Delta::bottom());
        assert!(same(&x, a), "the unit after");
        let mut y = Delta::bottom();
        y.join(a);
        assert!(same(&y, a), "the unit before");
        assert!(!a.then(&Delta::bottom()).reach && !Delta::bottom().then(a).reach, "kept unreachable");
        for b in &all {
            let mut j = a.clone();
            j.join(b);
            assert!(j.ends.values().all(|e| *e != Ends::SAME), "no identity after a join");
            assert!(a.then(b).ends.values().all(|e| *e != Ends::SAME), "no identity after then");
        }
    }
}

/// The head of a loop from `x`, `x; head(back)`, is a solution of
/// `h = x ⊔ h; back` and the one the iteration from `x` reaches (all the
/// fields, by the loop: the statuses without the mark of the loop).
#[test]
fn the_head_of_a_loop_is_the_fixpoint_of_the_iteration() {
    let plain = |d: &Delta| {
        let mut d = d.clone();
        for e in d.ends.values_mut() {
            if let Some(Status::Moved { via_loop, .. }) = &mut e.dead {
                *via_loop = false;
            }
        }
        d
    };
    let all = deltas();
    for x in &all {
        for back in &all {
            let head = x.then(&LoopSum::head(back));
            let mut again = x.clone();
            again.join(&head.then(back));
            assert!(same(&plain(&head), &plain(&again)), "a solution: {x:?} {back:?}");
            let mut h = x.clone();
            for _ in 0..3 {
                let mut next = x.clone();
                next.join(&h.then(back));
                h = next;
            }
            assert!(same(&plain(&head), &plain(&h)), "the least: {x:?} {back:?}");
        }
    }
}

/// The join and `then` of two tables are those of each binding, a binding
/// not in a table [`Ends::SAME`] (the tables merged in the order of their
/// bindings: interleaved, the same, or apart).
#[test]
fn the_join_of_deltas_is_the_join_of_each_binding() {
    let all = all();
    let of = |pairs: &[(u32, &Ends)]| {
        let mut d = Delta::start();
        for &(l, e) in pairs {
            d.put(LocalId(l), e.clone());
        }
        d
    };
    let get = |d: &Delta, l| d.ends.get(&LocalId(l)).cloned().unwrap_or(Ends::SAME);
    for a in &all {
        for b in &all {
            for (ka, kb) in [([0, 2], [1, 3]), ([0, 1], [0, 1]), ([0, 1], [2, 3]), ([2, 3], [0, 1]), ([1, 2], [0, 3])] {
                let (x, y) = (of(&[(ka[0], a), (ka[1], b)]), of(&[(kb[0], b), (kb[1], a)]));
                let mut j = x.clone();
                j.join(&y);
                let t = x.then(&y);
                for l in 0..4 {
                    assert_eq!(get(&j, l), join(&get(&x, l), &get(&y, l)), "join {l}: {a:?} {b:?}");
                    assert_eq!(get(&t, l), get(&x, l).then(&get(&y, l)), "then {l}: {a:?} {b:?}");
                }
            }
        }
    }
}

/// A change a walk makes of its state, on two bindings.
#[derive(Clone, Copy, Debug)]
enum Op {
    Move(u32, u32),
    Stale(u32, u32),
    Revive(u32),
    Forget(u32),
    Stop,
    Then(u32),
    Declare(u32),
}

const OPS: [Op; 10] = [
    Op::Move(0, 1),
    Op::Move(1, 2),
    Op::Move(0, 3),
    Op::Stale(0, 4),
    Op::Stale(1, 5),
    Op::Revive(0),
    Op::Forget(1),
    Op::Stop,
    Op::Then(0),
    Op::Then(1),
];

/// The regions an [`Op::Then`] applies: a loop's head that moved `0` by
/// the loop, and one that declared `1` on some paths and left it stale.
fn region(i: u32) -> Delta {
    let mut d = Delta::start();
    let moved = Some(Status::Moved { at: at(6), via_loop: true });
    let stale = Some(Status::Stale { changes: BTreeMap::from([(2, at(7))]) });
    match i {
        0 => d.put(LocalId(0), Ends { through: true, dead: moved, live: false }),
        _ => d.put(LocalId(1), Ends { through: true, dead: stale, live: true }),
    }
    d
}

fn status(op: Op) -> Option<(u32, Status)> {
    match op {
        Op::Move(l, n) => Some((l, Status::Moved { at: at(n), via_loop: false })),
        Op::Stale(l, n) => Some((l, Status::Stale { changes: BTreeMap::from([(n, at(n))]) })),
        _ => None,
    }
}

/// The walk before the trail: a whole state, copied at a branch.
fn on_delta(d: &mut Delta, ops: &[Op]) {
    for &op in ops {
        match op {
            Op::Move(l, n) => d.moved(LocalId(l), at(n)),
            Op::Stale(..) => {
                let (l, s) = status(op).unwrap();
                d.stale(LocalId(l), s)
            }
            Op::Revive(l) | Op::Declare(l) => d.revive(LocalId(l)),
            Op::Forget(l) => d.forget(LocalId(l)),
            Op::Stop => *d = Delta::bottom(),
            Op::Then(i) => *d = d.then(&region(i)),
        }
    }
}

fn on_trail(t: &mut Trail, ops: &[Op]) {
    for &op in ops {
        match op {
            Op::Move(l, n) => t.change(LocalId(l), |d| d.moved(LocalId(l), at(n))),
            Op::Stale(..) => {
                let (l, s) = status(op).unwrap();
                t.change(LocalId(l), |d| d.stale(LocalId(l), s))
            }
            Op::Revive(l) => t.change(LocalId(l), |d| d.revive(LocalId(l))),
            Op::Declare(l) => t.declare(LocalId(l)),
            Op::Forget(l) => t.change(LocalId(l), |d| d.forget(LocalId(l))),
            Op::Stop => t.stop(),
            Op::Then(i) => t.then(&region(i)),
        }
    }
}

/// The sequences of at most `n` changes (`n` ≤ 2).
fn seqs(n: usize) -> Vec<Vec<Op>> {
    let mut out = vec![vec![]];
    out.extend(OPS.iter().map(|&a| vec![a]));
    if n > 1 {
        out.extend(OPS.iter().flat_map(|&a| OPS.iter().map(move |&b| vec![a, b])));
    }
    out
}

/// The states before a branch: all live, some moved or stale, stopped.
fn prefixes() -> Vec<Vec<Op>> {
    vec![vec![], vec![Op::Move(0, 1)], vec![Op::Revive(1), Op::Stale(1, 4)], vec![Op::Stop, Op::Move(1, 2)]]
}

fn check(t: &Trail, want: &Delta, what: &str) {
    assert!(same(&t.now, want), "{what}: {:?} != {want:?}", t.now);
    assert!(t.now.ends.values().all(|e| *e != Ends::SAME), "{what}: an identity kept");
}

/// An `if`: the trail's join of the two branches from a mark is the join of
/// the two whole states (`else ⊔ then`, as the walk before it), and the
/// mark gives back the state before the branch as it was.
#[test]
fn the_trail_joins_two_branches_as_the_whole_states() {
    let (pre, seqs) = (prefixes(), seqs(2));
    for p in &pre {
        let mut before = Delta::start();
        on_delta(&mut before, p);
        for a in &seqs {
            let mut then = before.clone();
            on_delta(&mut then, a);
            for b in &seqs {
                let mut want = before.clone();
                on_delta(&mut want, b);
                want.join(&then);
                let mut t = Trail::new();
                on_trail(&mut t, p);
                let (m, mut paths) = (t.mark(), Paths::none());
                on_trail(&mut t, a);
                t.join_into(m, &mut paths, Joins::Falls);
                t.back_to(m);
                assert!(t.now.reach == before.reach && t.now.ends == before.ends, "back: {p:?} {a:?}");
                on_trail(&mut t, b);
                t.join_into(m, &mut paths, Joins::Falls);
                t.settle(m, &paths);
                check(&t, &want, &format!("{p:?} {a:?} {b:?}"));
            }
        }
    }
}

/// A `match` (and a loop's `break`s): the arms from the paths they are tried
/// at (the head, and each guard that was false), three or more paths joined
/// (a binding every path before changed, which this one does not).
#[test]
fn the_trail_joins_the_arms_of_a_match_as_the_whole_states() {
    let (pre, seqs) = (prefixes(), seqs(1));
    let guards: Vec<Option<&Vec<Op>>> = std::iter::once(None).chain(seqs.iter().map(Some)).collect();
    let mut arms = Vec::new();
    for g0 in &guards {
        for g1 in &guards {
            for (i, b0) in seqs.iter().enumerate() {
                for b1 in &seqs {
                    arms.push([(*g0, b0), (*g1, b1), (None, &seqs[(i + 3) % seqs.len()])]);
                }
            }
        }
    }
    for p in &pre {
        let mut before = Delta::start();
        on_delta(&mut before, p);
        for arms in &arms {
            let (mut tried, mut out) = (before.clone(), Delta::bottom());
            for &(g, body) in arms {
                let mut cur = tried.clone();
                if let Some(g) = g {
                    on_delta(&mut cur, g);
                    tried.join(&cur);
                }
                on_delta(&mut cur, body);
                out.join(&cur);
            }
            let mut t = Trail::new();
            on_trail(&mut t, p);
            let (m, mut tried, mut paths) = (t.mark(), Paths::none(), Paths::none());
            t.join_into(m, &mut tried, Joins::Falls);
            for &(g, body) in arms {
                t.reset(m, &tried);
                if let Some(g) = g {
                    on_trail(&mut t, g);
                    t.join_into(m, &mut tried, Joins::Falls);
                }
                on_trail(&mut t, body);
                t.join_into(m, &mut paths, Joins::Falls);
            }
            t.settle(m, &paths);
            check(&t, &out, &format!("{p:?} {arms:?}"));
        }
    }
}

/// A `break` (D4): the bindings declared since the mark leave before the
/// join, as if forgotten (those declared before it stay), the other path
/// before or after it; the mark gives back the state before as it was.
#[test]
fn a_break_joins_as_if_the_bindings_declared_since_the_mark_were_forgotten() {
    let ops: Vec<Op> = OPS.iter().copied().chain([Op::Declare(0), Op::Declare(1)]).collect();
    let mut breaks = vec![vec![]];
    breaks.extend(ops.iter().map(|&a| vec![a]));
    breaks.extend(ops.iter().flat_map(|&a| ops.iter().map(move |&b| vec![a, b])));
    let mut pre = prefixes();
    pre.push(vec![Op::Declare(1), Op::Move(1, 2)]);
    for p in &pre {
        let mut before = Delta::start();
        on_delta(&mut before, p);
        for a in &breaks {
            let mut left = before.clone();
            on_delta(&mut left, a);
            for op in a {
                if let &Op::Declare(l) = op {
                    left.forget(LocalId(l));
                }
            }
            for b in &seqs(1) {
                let mut want = before.clone();
                on_delta(&mut want, b);
                want.join(&left);
                for leaves_first in [true, false] {
                    let mut t = Trail::new();
                    on_trail(&mut t, p);
                    let (m, mut paths) = (t.mark(), Paths::none());
                    for leaving in [leaves_first, !leaves_first] {
                        on_trail(&mut t, if leaving { a } else { b });
                        t.join_into(m, &mut paths, if leaving { Joins::Jumps } else { Joins::Falls });
                        t.back_to(m);
                        assert!(t.now.reach == before.reach && t.now.ends == before.ends, "back: {p:?} {a:?}");
                    }
                    t.settle(m, &paths);
                    check(&t, &want, &format!("{p:?} {a:?} {b:?} {leaves_first}"));
                }
            }
        }
    }
}

/// Since the mark `m`, at most `n` changes of each binding (one for each
/// mark open since) and `n` stops.
fn recorded_once_per_mark(t: &Trail, m: usize, n: usize) {
    for l in 0..2 {
        let count = t.log[m..].iter().filter(|u| matches!(u, Undo::Ends { l: k, .. } if k.0 == l)).count();
        assert!(count <= n, "{l} recorded {count} times since {m}: {:?}", t.log);
    }
    assert!(t.log[m..].iter().filter(|u| matches!(u, Undo::Stop(_))).count() <= n, "stops: {:?}", t.log);
}

/// Marks inside a mark (an `if` in a loop, before its `break`), each change
/// made twice: a binding changed again since the innermost open mark is not
/// recorded again, and the joins and the marks are as of the whole states.
#[test]
fn a_mark_inside_a_mark_records_each_binding_once_and_joins_as_the_whole_states() {
    let (pre, seqs) = (prefixes(), seqs(1));
    let twice = |s: &Vec<Op>| [s.as_slice(), s.as_slice()].concat();
    for p in &pre {
        let mut before = Delta::start();
        on_delta(&mut before, p);
        for (i, a) in seqs.iter().enumerate() {
            let (a, c, other) = (twice(a), &seqs[(i + 5) % seqs.len()], &seqs[(i + 3) % seqs.len()]);
            for x in seqs.iter().map(twice) {
                for y in &seqs {
                    // The body: `a`, then `if { x } else { y }`, then `c`, to a `break`; `other`: the other path.
                    let mut body = before.clone();
                    on_delta(&mut body, &a);
                    let mut then = body.clone();
                    on_delta(&mut then, &x);
                    on_delta(&mut body, y);
                    body.join(&then);
                    on_delta(&mut body, c);
                    let mut want = before.clone();
                    on_delta(&mut want, other);
                    want.join(&body);
                    let mut t = Trail::new();
                    on_trail(&mut t, p);
                    let (m, mut paths) = (t.mark(), Paths::none());
                    on_trail(&mut t, &a);
                    let (n, mut branches) = (t.mark(), Paths::none());
                    on_trail(&mut t, &x);
                    recorded_once_per_mark(&t, n, 1);
                    recorded_once_per_mark(&t, m, 2);
                    t.join_into(n, &mut branches, Joins::Falls);
                    t.back_to(n);
                    on_trail(&mut t, y);
                    t.join_into(n, &mut branches, Joins::Falls);
                    t.settle(n, &branches);
                    on_trail(&mut t, c);
                    recorded_once_per_mark(&t, m, 1);
                    t.join_into(m, &mut paths, Joins::Falls);
                    t.back_to(m);
                    assert!(t.now.reach == before.reach && t.now.ends == before.ends, "back: {p:?} {a:?}");
                    on_trail(&mut t, other);
                    t.join_into(m, &mut paths, Joins::Falls);
                    t.settle(m, &paths);
                    check(&t, &want, &format!("{p:?} {a:?} {x:?} {y:?} {c:?}"));
                }
            }
        }
    }
}

/// A binding released at two places, used in each arm from a mark (a
/// loop's head met by each arm): the first use gives the releases, the
/// arms after it meet the same shared set and get none (copied once, the
/// work of a use not of the set); each use leaves it live, and the mark
/// gives back the set as it was.
#[test]
fn a_set_of_releases_used_again_is_copied_once() {
    let (mut t, l) = (Trail::new(), LocalId(0));
    t.change(l, |d| d.released(l, ExprId(1)));
    t.change(l, |d| d.released(l, ExprId(2)));
    let Some(Status::Released { at: head }) = t.now.status(l).cloned() else { panic!("not released") };
    let m = t.mark();
    for arm in 0..3 {
        t.back_to(m);
        assert!(matches!(t.now.status(l), Some(Status::Released { at }) if Rc::ptr_eq(at, &head)), "arm {arm}");
        let got = t.restore(l);
        assert_eq!(got.as_deref().cloned(), (arm == 0).then(|| (*head).clone()), "arm {arm}");
        assert!(t.now.status(l).is_none(), "arm {arm}: live");
    }
    assert_eq!(t.copies.len(), 2);
}
