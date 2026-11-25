//! The twins of the reference to what is below (`twin_back.rs`, W7-11 U2b/t2): the pairs of the table and the crossed programs of fixed seeds give the same outputs on the evaluator and in the interpreter, a pair that is
//! made different is caught, and the divisions that panic are reported at the same stage and place on both sides. The forms that wait for the stage (`late`, S-1244) are run in the interpreter as the others are.

use std::collections::BTreeSet;

use super::twin::{Family, run};
use super::twin_back::{DIVIDING, HEADS, PAIRS, WRAPS, cross_seed, make_cross, make_pair, run_dividing};
use super::twin_tests::check;

const PAIR: Family = ("back_pairs", make_pair);
const CROSS: Family = ("back_cross", make_cross);

/// The seeds of the pairs of the table (the seed is the number of the pair) that wait for the stage, or that do not.
fn pairs(late: bool) -> Vec<u64> {
    (0..PAIRS.len() as u64).filter(|s| PAIRS[*s as usize].1 == late).collect()
}

/// The crossed programs: every head that waits for the stage with every wrap, or every head that does not with every wrap.
fn crossed(late: bool) -> Vec<u64> {
    let heads = (0..HEADS.len()).filter(move |h| HEADS[*h].1 == late);
    heads.flat_map(|h| (0..WRAPS.len()).map(move |w| cross_seed(h, w))).collect()
}

#[test]
fn the_pairs_that_read_a_let_below_agree_on_the_evaluator_and_in_the_interpreter() {
    let seeds = pairs(false);
    assert_eq!(seeds.len(), 7);
    println!("{:?}", check(seeds, PAIR));
}

#[test]
fn the_pairs_that_read_a_let_below_in_a_part_that_waits_for_the_stage_agree() {
    let seeds = pairs(true);
    assert_eq!(seeds.len(), 5);
    println!("{:?}", check(seeds, PAIR));
}

#[test]
fn the_crossed_heads_and_wraps_that_read_a_let_below_agree_on_the_evaluator_and_in_the_interpreter() {
    let seeds = crossed(false);
    assert_eq!(seeds.len(), 3 * WRAPS.len());
    println!("{:?}", check(seeds, CROSS));
}

#[test]
fn the_crossed_heads_and_wraps_that_wait_for_the_stage_agree() {
    let seeds = crossed(true);
    assert_eq!(seeds.len(), 2 * WRAPS.len());
    println!("{:?}", check(seeds, CROSS));
}

#[test]
fn the_seeds_hold_every_pair_every_wrap_and_every_head_once_at_least() {
    let held: BTreeSet<_> = (0..PAIRS.len() as u64).flat_map(|s| make_pair(s, false).1).collect();
    assert!(PAIRS.iter().all(|p| held.contains(p.0)) && held.contains("late"), "{held:?}");
    let reads: Vec<_> =
        (0..(HEADS.len() * WRAPS.len()) as u64).filter(|s| !make_cross(*s, false).0.contains('^')).collect();
    assert!(reads.is_empty(), "the crossed programs {reads:?} read no `^`");
    let seeds: Vec<u64> = [crossed(false), crossed(true)].concat();
    let held: BTreeSet<_> = seeds.iter().flat_map(|s| make_cross(*s, false).1).collect();
    let missing: Vec<_> =
        WRAPS.iter().map(|w| w.0).chain(HEADS.iter().map(|h| h.0)).filter(|t| !held.contains(t)).collect();
    assert!(missing.is_empty(), "the seeds of the crossed programs do not hold {missing:?}");
    let names: BTreeSet<_> = PAIRS.iter().map(|p| p.0).collect();
    assert_eq!(names.len(), PAIRS.len(), "two pairs have a name");
}

#[test]
fn a_twin_that_is_made_different_is_caught_by_the_asserts_of_the_evaluator() {
    // The output of `r` is one more: the asserts that the two give the same have to fail, for the pairs and for the crossed programs (the interpreter is not run on the mutant).
    for (family, seeds) in [(PAIR, pairs(false)), (CROSS, crossed(false))] {
        let (s, bad) = run(seeds.clone(), family, true);
        let caught = bad.iter().filter(|m| m.contains("does not hold")).count();
        assert_eq!((s.programs, caught), (seeds.len(), seeds.len()), "{bad:?}");
    }
}

#[test]
fn the_first_division_is_at_the_same_stage_and_place_where_the_reads_are_moved_into_lets() {
    // `k` is 0 in some scenes: the divisions of `w` panic at `block`, in the program where `w` is below with `^w` and in the one where it is above (a move that changes no stage, §11.3), and the interpreter panics where the evaluator does.
    let (panicked, bad) = run_dividing(&DIVIDING);
    assert!(panicked >= DIVIDING.len() && bad.is_empty(), "{panicked} scenes panicked\n{}", bad.join("\n\n"));
}
