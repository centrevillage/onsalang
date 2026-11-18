//! The loops of the `let`s (`flow/loops.rs`, W7-02 U2a) on graphs made by
//! hand: `deps[v]` are the `let`s the `let` `v` reads.

use onsa_diag::internal::InternalBug;

use super::{Scc, components, tarjan};

fn scc(lets: &[usize], looped: bool) -> Scc {
    Scc { lets: lets.to_vec(), looped }
}

/// Every read goes to the same component or to one before it.
fn reads_go_before(deps: &[Vec<usize>], out: &[Scc]) {
    let mut at = vec![usize::MAX; deps.len()];
    for (i, c) in out.iter().enumerate() {
        for &v in &c.lets {
            assert_eq!(at[v], usize::MAX, "the let {v} in two components");
            at[v] = i;
        }
    }
    for (v, reads) in deps.iter().enumerate() {
        for &w in reads {
            assert!(at[w] <= at[v], "the let {v} reads {w}, which comes after it");
        }
    }
}

#[test]
fn no_let_and_one_let() {
    assert_eq!(components(&[]), vec![]);
    assert_eq!(components(&[vec![]]), vec![scc(&[0], false)]);
}

#[test]
fn a_let_that_reads_itself_is_a_loop() {
    // `let c = prev~(^c) + 1`
    assert_eq!(components(&[vec![0]]), vec![scc(&[0], true)]);
    // The same read twice, and a `let` after it that reads it.
    let deps = [vec![0, 0], vec![0]];
    assert_eq!(components(&deps), vec![scc(&[0], true), scc(&[1], false)]);
}

#[test]
fn two_back_edges_make_one_component() {
    // let a = prev~(^c); let b = a + ^c; let c = b; let d = c
    let deps = [vec![2], vec![0, 2], vec![1], vec![2]];
    let out = components(&deps);
    assert_eq!(out, vec![scc(&[0, 1, 2], true), scc(&[3], false)]);
    reads_go_before(&deps, &out);
}

#[test]
fn a_component_comes_after_the_components_it_reads() {
    // let a = ^c; let b = 1; let c = 2: `c` first, then `a`, then `b`.
    let deps = [vec![2], vec![], vec![]];
    assert_eq!(components(&deps), vec![scc(&[2], false), scc(&[0], false), scc(&[1], false)]);
    // The loop {0, 4} reads the loop {1, 2, 3} (4 reads 3); 5 reads both.
    let deps = [vec![4], vec![2], vec![1, 3], vec![2], vec![0, 3], vec![3, 4]];
    let out = components(&deps);
    assert_eq!(out, vec![scc(&[1, 2, 3], true), scc(&[0, 4], true), scc(&[5], false)]);
    reads_go_before(&deps, &out);
}

#[test]
fn the_lets_of_a_component_are_in_the_order_of_the_text() {
    // The search finds them as 0, 3, 1, 2.
    let deps = [vec![3], vec![2], vec![0], vec![1]];
    assert_eq!(components(&deps), vec![scc(&[0, 1, 2, 3], true)]);
}

#[test]
fn a_chain_of_ten_thousand_lets_needs_no_recursion() {
    const N: usize = 10_000;
    // Each `let` reads the next one: a recursive search would go N deep.
    let chain: Vec<Vec<usize>> = (0..N).map(|v| if v + 1 < N { vec![v + 1] } else { vec![] }).collect();
    let (out, deepest) = tarjan(&chain);
    assert_eq!(deepest, N);
    assert_eq!(out.len(), N);
    assert!(out.iter().zip((0..N).rev()).all(|(c, v)| *c == scc(&[v], false)));
    // Closed into one loop.
    let ring: Vec<Vec<usize>> = (0..N).map(|v| vec![(v + 1) % N]).collect();
    let (out, deepest) = tarjan(&ring);
    assert_eq!(deepest, N);
    assert_eq!(out, vec![Scc { lets: (0..N).collect(), looped: true }]);
}

#[test]
fn a_read_of_no_let_is_an_internal_error() {
    let payload = std::panic::catch_unwind(|| components(&[vec![1]])).expect_err("no let 1");
    assert!(payload.downcast_ref::<InternalBug>().is_some());
}
