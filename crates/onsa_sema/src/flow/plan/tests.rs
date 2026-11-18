//! The table of the nodes of a flow (R-91 (1)): the owner of each node by
//! the tree of the body, the `children` of a `par~`, the one index
//! [`NodeId`], the order of [`FlowInfo::roots`] and the empty table of a
//! flow in error.

use super::{NodeId, Owner, PlanKind};
use crate::clock::Clock;
use crate::flow::FlowInfo;
use crate::tests::check;
use crate::{Analysis, DefId};

const SRC: &str = "pub flow g(x: F32 at sample) -> F32 at sample {
  prev~(x)
}
pub flow f(x: F32 at sample) -> F32 at sample {
  let a = prev~(x)
  let b = g~(a) + delay~(x, 4)
  let s = (par~ i in 0..<2 { prev~(x) + (par~ j in 0..<2 { delay~(x, 2) })[0] })[1]
  a + b + s + prev~(b)
}
";

fn flow<'a>(a: &'a Analysis, name: &str) -> &'a FlowInfo {
    let id = DefId(a.defs.iter().position(|d| d.name == name).expect("the flow") as u32);
    &a.flows[&id]
}

/// The names of the nodes of `ids`.
fn names<'a>(f: &'a FlowInfo, ids: &[NodeId]) -> Vec<&'a str> {
    ids.iter().map(|&id| f.node(id).name.as_str()).collect()
}

/// The node named `name`.
fn named(f: &FlowInfo, name: &str) -> NodeId {
    let k = f.nodes.iter().position(|n| n.name == name).unwrap_or_else(|| panic!("no node {name}"));
    NodeId(k as u32)
}

/// Each node is held by the `let` or the output whose tree it is in.
#[test]
fn the_owner_is_the_let_or_the_output() {
    let a = check(SRC);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = flow(&a, "f");
    assert_eq!(f.node(named(f, "a")).owner, Owner::Let(0));
    assert_eq!(f.node(named(f, "g_0")).owner, Owner::Let(1));
    assert_eq!(f.node(named(f, "delay_0")).owner, Owner::Let(1));
    assert_eq!(f.node(named(f, "par_1")).owner, Owner::Let(2));
    assert_eq!(f.node(named(f, "prev_1")).owner, Owner::Output);
    // The clock of a delay and the clock its argument is read at (§11.4).
    let prev = f.node(named(f, "prev_1"));
    assert_eq!(prev.clock, Clock::SAMPLE);
    assert_eq!(prev.args.iter().map(|r| r.at).collect::<Vec<_>>(), vec![Clock::SAMPLE]);
}

/// A `par~` holds the nodes of its body, an inner `par~` its own; the slot
/// of a `par~` comes before those of its body.
#[test]
fn a_par_holds_the_nodes_of_its_body() {
    let a = check(SRC);
    let f = flow(&a, "f");
    let (outer, inner) = (named(f, "par_1"), named(f, "par_0"));
    assert!(outer.0 < inner.0);
    assert_eq!(names(f, f.roots(Owner::Par(outer))), vec!["prev_0", "par_0"]);
    assert_eq!(names(f, f.roots(Owner::Par(inner))), vec!["delay_1"]);
    for (p, kids) in [(outer, f.roots(Owner::Par(outer))), (inner, f.roots(Owner::Par(inner)))] {
        let PlanKind::Par { children, .. } = &f.node(p).kind else { panic!("not a par~") };
        assert_eq!(children.as_slice(), kids);
        assert!(kids.iter().all(|&k| f.node(k).owner == Owner::Par(p)));
    }
    assert!(f.node(outer).args.is_empty());
}

/// `node_of` gives the one index of a node, of a `par~` and of a node in
/// its body too.
#[test]
fn node_of_gives_the_node_id() {
    let a = check(SRC);
    let f = flow(&a, "f");
    assert_eq!(f.node_of.len(), f.nodes.len());
    assert_eq!(f.nodes.len(), 8);
    for (k, n) in f.nodes.iter().enumerate() {
        assert_eq!(f.node_of[&n.expr], NodeId(k as u32), "{}", n.name);
    }
}

/// The nodes of an owner are in the order of the table; `top` is those of
/// the `let`s in their order, then of the output.
#[test]
fn roots_are_in_the_order_of_the_table() {
    let a = check(SRC);
    let f = flow(&a, "f");
    assert_eq!(names(f, f.roots(Owner::Let(0))), vec!["a"]);
    assert_eq!(names(f, f.roots(Owner::Let(1))), vec!["g_0", "delay_0"]);
    assert_eq!(names(f, f.roots(Owner::Let(2))), vec!["par_1"]);
    assert_eq!(names(f, f.roots(Owner::Output)), vec!["prev_1"]);
    assert!(f.roots(Owner::Let(3)).is_empty());
    let top: Vec<NodeId> = f.top().collect();
    assert_eq!(names(f, &top), vec!["a", "g_0", "delay_0", "par_1", "prev_1"]);
    for owner in [Owner::Let(1), Owner::Par(named(f, "par_1"))] {
        assert!(f.roots(owner).windows(2).all(|w| w[0].0 < w[1].0));
    }
}

/// A flow in error has an empty table.
#[test]
fn a_flow_in_error_has_no_nodes() {
    let src = "pub flow f(x: F32 at sample, g: F32 at block) -> F32 at sample {
  let a = prev~(x)
  let b = x at block
  a + prev~(g)
}
";
    let a = check(src);
    let f = flow(&a, "f");
    assert!(!a.diagnostics.is_empty() && !f.complete);
    assert!(f.nodes.is_empty() && f.node_of.is_empty());
    assert!(f.roots(Owner::Let(0)).is_empty() && f.roots(Owner::Output).is_empty());
    assert_eq!(f.top().count(), 0);
}

/// The first argument of a delay is read a tick later (`lookback`, §11.4),
/// its `d` and `init` and the arguments of an instance as the node computes
/// (RF-8 (C)), each at its clock.
#[test]
fn the_first_argument_of_a_delay_is_a_lookback() {
    let src = "pub flow g(x: F32 at sample, k: F32 at block) -> F32 at sample {
  x * k
}
pub flow f(x: F32 at sample, k: F32 at block, t: F32 at init) -> F32 at sample {
  vdelay~(x, 2.0, 4, t) + prev~(x) + g~(x, k)
}
";
    let a = check(src);
    let f = flow(&a, "f");
    let reads = |k: usize| {
        let n = f.node(f.roots(Owner::Output)[k]);
        n.args.iter().map(|r| (r.at, r.lookback)).collect::<Vec<_>>()
    };
    assert_eq!(reads(0), vec![(Clock::SAMPLE, true), (Clock::SAMPLE, false), (Clock::Init, false)]);
    assert_eq!(reads(1), vec![(Clock::SAMPLE, true)]);
    assert_eq!(reads(2), vec![(Clock::SAMPLE, false), (Clock::Block, false)]);
}
