//! The table of the nodes of a flow (R-91 (1)): the owner of each node by
//! the tree of the body, the `children` of a `par~`, the one index
//! [`NodeId`], the order of [`FlowInfo::roots`] and the empty table of a
//! flow in error.

use super::Vertex::{Let, Local, Node, Output};
use super::{Edge, NodeId, Owner, PlanKind};
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

/// The paths of the nodes of `ids`.
fn names<'a>(f: &'a FlowInfo, ids: &[NodeId]) -> Vec<&'a str> {
    ids.iter().map(|&id| f.node(id).path.as_str()).collect()
}

/// The node of the path `name`.
fn named(f: &FlowInfo, name: &str) -> NodeId {
    let k = f.nodes.iter().position(|n| n.path == name).unwrap_or_else(|| panic!("no node {name}"));
    NodeId(k as u32)
}

/// Each node is held by the `let` or the output whose tree it is in.
#[test]
fn the_owner_is_the_let_or_the_output() {
    let a = check(SRC);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = flow(&a, "f");
    assert_eq!(f.node(named(f, "a")).owner, Owner::Let(0));
    assert_eq!(f.node(named(f, "b.g_0")).owner, Owner::Let(1));
    assert_eq!(f.node(named(f, "b.delay_0")).owner, Owner::Let(1));
    assert_eq!(f.node(named(f, "s.par_0")).owner, Owner::Let(2));
    assert_eq!(f.node(named(f, "_out.prev_0")).owner, Owner::Output);
    // The clock of a delay and the clock its argument is read at (§11.4).
    let prev = f.node(named(f, "_out.prev_0"));
    assert_eq!(prev.clock, Clock::SAMPLE);
    assert_eq!(prev.args.iter().map(|r| r.at).collect::<Vec<_>>(), vec![Clock::SAMPLE]);
}

/// A `par~` holds the nodes of its body, an inner `par~` its own; the slot
/// of a `par~` comes before those of its body.
#[test]
fn a_par_holds_the_nodes_of_its_body() {
    let a = check(SRC);
    let f = flow(&a, "f");
    let (outer, inner) = (named(f, "s.par_0"), named(f, "s.par_0.par_0"));
    assert!(outer.0 < inner.0);
    assert_eq!(names(f, f.roots(Owner::Par(outer))), vec!["s.par_0.prev_0", "s.par_0.par_0"]);
    assert_eq!(names(f, f.roots(Owner::Par(inner))), vec!["s.par_0.par_0.delay_0"]);
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
    assert_eq!(names(f, f.roots(Owner::Let(1))), vec!["b.g_0", "b.delay_0"]);
    assert_eq!(names(f, f.roots(Owner::Let(2))), vec!["s.par_0"]);
    assert_eq!(names(f, f.roots(Owner::Output)), vec!["_out.prev_0"]);
    assert!(f.roots(Owner::Let(3)).is_empty());
    let top: Vec<NodeId> = f.top().collect();
    assert_eq!(names(f, &top), vec!["a", "b.g_0", "b.delay_0", "s.par_0", "_out.prev_0"]);
    for owner in [Owner::Let(1), Owner::Par(named(f, "s.par_0"))] {
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

/// The first argument of a delay is read a tick later (`lookback` of its
/// edges, §11.4), its `d` and `init` and the arguments of an instance as the
/// node computes (RF-8 (C)), each at its clock.
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
    let node = |k: usize| f.roots(Owner::Output)[k];
    let at = |k: usize| f.node(node(k)).args.iter().map(|r| r.at).collect::<Vec<_>>();
    assert_eq!(at(0), vec![Clock::SAMPLE, Clock::SAMPLE, Clock::Init]);
    assert_eq!(at(1), vec![Clock::SAMPLE]);
    assert_eq!(at(2), vec![Clock::SAMPLE, Clock::Block]);
    let [x, k, t] = [0, 1, 2].map(|i| Local(f.inputs[i]));
    let [d0, d1, d2] = [0, 1, 2].map(|k| Node(node(k)));
    let edges = [(d0, Output, false), (x, d0, true), (t, d0, false), (d1, Output, false), (x, d1, true)];
    let edges = edges.into_iter().chain([(d2, Output, false), (x, d2, false), (k, d2, false)]);
    assert_eq!(f.edges, edges.map(|(from, to, lookback)| Edge { from, to, lookback }).collect::<Vec<_>>());
}

/// The edges of the plan: each read by the innermost node, `let` or output
/// around it, once, in the order of the text; a node read by the one around
/// its call, not the whole value of a `let`, which is its vertex; a node in
/// the first argument of a delay and what is in it, a tick later; the index
/// of a `par~` read in its body.
#[test]
fn the_edges_are_the_reads_in_the_order_of_the_text() {
    let src = "pub flow h(x: F32 at sample) -> F32 at sample {
  x
}
pub flow f(x: F32 at sample) -> F32 at sample {
  let a = x * x
  let y = prev~(h~(a) + ^y)
  let s = par~ i in 0..<2 { h~(x * F32.round_from(i)) }
  a + y + s[0]
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = flow(&a, "f");
    let local = |k: usize| Local(f.lets[k].locals[0]);
    let (x, la, ly, ls) = (Local(f.inputs[0]), local(0), local(1), local(2));
    let [y, h, s, sh] = ["y", "y.h_0", "s", "s.h_0"].map(|p| Node(named(f, p)));
    let PlanKind::Par { var, .. } = f.node(named(f, "s")).kind else { panic!("not a par~") };
    let edges = [(x, Let(0), false), (h, y, true), (la, h, false), (ly, y, true)];
    let edges = edges.into_iter().chain([(sh, s, false), (x, sh, false), (Local(var), sh, false)]);
    let edges = edges.chain([(la, Output, false), (ly, Output, false), (ls, Output, false)]);
    assert_eq!(f.edges, edges.map(|(from, to, lookback)| Edge { from, to, lookback }).collect::<Vec<_>>());
}

/// S-1131, §11.4: the record of each `match~` (the bindings of its arms in
/// order, the `par~`s around it, the outermost first), the arms around each
/// node, and the bindings read in the first argument of a delay, which the
/// end of `tick` reads (of each replica); not one read elsewhere.
#[test]
fn the_plan_records_the_match_tildes_the_arms_of_the_nodes_and_the_bindings_stored() {
    let src = "pub flow acc(x: F32 at sample) -> F32 at sample {
  x + prev~(x)
}
pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {
  let o = if x > 0.0 { Some(x) } else { None }
  let a = match~ o { Some(v) => acc~(v), None => acc~(x) }
  let s = (par~ i in 0..<2 { match~ k { 0 => prev~(x), n => prev~(F32.round_from(n)) } })[0]
  a + s
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = flow(&a, "f");
    let arms = |path: &str| f.node(named(f, path)).arms.clone();
    let (outer, inner) = (arms("a.acc_0")[0].0, arms("s.par_0.prev_0")[0].0);
    assert_eq!(arms("a.acc_0"), [(outer, 0)]);
    assert_eq!(arms("a.acc_1"), [(outer, 1)]);
    assert_eq!(arms("s.par_0"), []);
    assert_eq!(arms("s.par_0.prev_0"), [(inner, 0)]);
    assert_eq!(arms("s.par_0.prev_1"), [(inner, 1)]);
    assert_eq!(f.tilde_matches.keys().copied().collect::<Vec<_>>(), [outer, inner]);
    let (o, i) = (&f.tilde_matches[&outer], &f.tilde_matches[&inner]);
    assert_eq!((o.arms.iter().map(Vec::len).collect::<Vec<_>>(), o.pars.as_slice()), (vec![1, 0], &[][..]));
    assert_eq!(
        (i.arms.iter().map(Vec::len).collect::<Vec<_>>(), i.pars.as_slice()),
        (vec![0, 1], &[named(f, "s.par_0")][..])
    );
    // `n` is read in the first argument of a delay, `v` in that of an instance.
    assert_eq!(f.store_bindings.iter().copied().collect::<Vec<_>>(), [i.arms[1][0]]);
}
