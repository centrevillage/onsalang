//! The laws of the states (`state.rs`), over every combination of the
//! fields of [`Ends`]: the join is a semilattice, `then` has the identity
//! [`Ends::SAME`], is associative and distributes over the join (a trail of
//! changes, undone and joined at a mark, relies on these), the table keeps
//! no identity, and a loop's head is the least fixpoint of `h = x ⊔ back(h)`.

use std::collections::BTreeMap;

use onsa_diag::{FileId, Span};

use super::{Delta, Ends, LoopSum, Status};
use crate::body::LocalId;

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
    let mut out = Vec::new();
    for through in [false, true] {
        for dead in &deads {
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
    let all = all();
    let none = Ends { through: false, dead: None, live: false };
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

#[test]
fn then_of_ends_is_associative_with_the_identity_and_distributes_over_the_join() {
    let all = all();
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
