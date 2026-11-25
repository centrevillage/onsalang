//! The twins of the order of the work of a stage (`twin_order.rs`, W7-11 U2b-e, S-1233).

use std::collections::BTreeSet;

use super::twin_order::{PLACES, make, run};

/// The seeds of the gate that the interpreter (the Core of `562ab2e1`) agrees with the evaluator on, which hold every place of the table.
const SAME: [u64; 5] = [7, 17, 68, 218, 236];
/// The seeds of the gate that hold every place of the table where the order of S-1233 changes which division is first (the call of a flow where it is written before the parts of the stage, a delay's `init` and the first
/// argument of a delay where they are written, the `init` of a child before the parts of `init` that are written after it): the Core of `562ab2e1` reports another one.
const ORDER: [u64; 6] = [6, 11, 37, 70, 112, 159];

/// The seeds are run one at a time: each has a scene that panics, and what is wrong is nothing.
fn check(seeds: &[u64], compared: bool) {
    for s in seeds {
        let (panicked, bad) = run(vec![*s], compared);
        assert!(panicked > 0 && bad.is_empty(), "seed {s}: {panicked} scenes panicked\n{}", bad.join("\n\n"));
    }
}

#[test]
fn the_first_division_is_the_same_in_the_interpreter_and_where_each_term_is_moved_into_a_let() {
    check(&SAME, true);
}

#[test]
fn the_first_division_is_the_same_in_the_interpreter_where_the_order_of_s1233_changes_it() {
    check(&ORDER, true);
}

#[test]
fn each_term_moved_into_a_let_gives_the_same_first_division_on_the_evaluator_where_the_order_changes() {
    check(&ORDER, false);
}

#[test]
fn the_seeds_hold_every_place_of_the_table_and_the_move_changes_each_program() {
    for set in [&SAME[..], &ORDER[..]] {
        let held: BTreeSet<_> = set.iter().flat_map(|s| make(*s, false).1).collect();
        let missing: Vec<_> = PLACES.iter().map(|p| p.0).filter(|t| !held.contains(t)).collect();
        assert!(missing.is_empty(), "the seeds {set:?} do not hold {missing:?}: choose them again");
    }
    for s in SAME.iter().chain(&ORDER) {
        let (a, b) = (make(*s, false).0, make(*s, true).0);
        assert!(a != b, "seed {s}: the move changed nothing");
    }
}
