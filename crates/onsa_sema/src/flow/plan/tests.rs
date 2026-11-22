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

/// The head of a chain of modifiers is the node of the chain (§11.9,
/// S-1088): its frame is the sum of the ratios, its chain the modifiers in
/// the order they are written, its boundaries one of each of them, its
/// clock the output in that frame, and a whole `let` names it through the
/// chain (S-148) unless the `let` is a tick of a ratio (S-1139 (a)). Its
/// value read at `sample` is hoisted to a field of its tick (S-1185). A
/// chain stops the Core until W7-16, its ratio one too. Of an `.up~` in a
/// `.down~`, the head runs at the tick of the `.down~` though the frame is
/// 0 (S-1207).
#[test]
fn the_head_of_a_chain_has_its_frame_and_its_modifiers() {
    use crate::clock::{ClockStage, Ratio};
    use crate::flow_names::Modifier;
    let src = "pub flow lp(x: F32 at sample) -> F32 at sample {
  x
}
pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let d = lp~(x).down~(2).up~(2)
  let b = lp~(p).down~(4).down~(2)
  d + (b at sample) + (lp~(p).down~(4) at sample)
}
pub flow g(x: F32 at sample) -> F32 at sample {
  lp~(x).down~(2).up~(2)
}
pub flow u(x: F32 at sample) -> F32 at sample {
  lp~(x).up~(2).down~(2)
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = flow(&a, "f");
    let d = f.node(named(f, "d"));
    assert_eq!((d.frame, d.clock), (Ratio(0), Clock::SAMPLE));
    let mods: Vec<_> = d.chain.iter().map(|m| (m.modifier, m.ratio)).collect();
    assert_eq!(mods, [(Modifier::Down, Some(Ratio(-1))), (Modifier::Up, Some(Ratio(1)))]);
    let bounds: Vec<_> = d.bounds.iter().map(|b| (b.at, b.gathers.len(), b.deals)).collect();
    assert_eq!(bounds, [(0, 0, false), (1, 0, false)]);
    // The output made at `sample / 2` inside the `.down~(2)`, at `sample` out of the `.up~(2)`.
    assert_eq!(drawn(d), "0*: Each(1,j)[-1: R(0,V)]   read=Run");
    let b = f.node(named(f, "b.lp_0"));
    assert_eq!((b.frame, b.clock, b.chain.len()), (Ratio(-3), Clock::Tick(Ratio(-3)), 2));
    assert_eq!(b.args.iter().map(|r| r.at).collect::<Vec<_>>(), [Clock::Tick(Ratio(-3))]);
    let out = f.node(named(f, "_out.lp_0"));
    let hoisted: Vec<_> = f.hoists.iter().map(|h| (h.span, h.stage)).collect();
    let chain = src.find("lp~(p).down~(4) at").unwrap();
    assert_eq!(hoisted.len(), 1, "{hoisted:?}");
    assert_eq!((hoisted[0].0.start as usize, hoisted[0].1), (chain, ClockStage::Tick(Ratio(-2))));
    assert_eq!(out.frame, Ratio(-2));
    assert!(f.multirate_at().is_some());
    let g = flow(&a, "g");
    assert_eq!(g.multirate_at(), Some(g.nodes[0].span), "a chain of the ratio one stops the Core too");
    let u = flow(&a, "u");
    // Its `.down~(2)` deals the burst of the `.up~(2)`: read from the array, not where the head runs.
    assert_eq!(u.nodes[0].frame, Ratio(0));
    assert_eq!(drawn(&u.nodes[0]), "-1: Each(0,j)[0: R(0,D(1))] | 0: G(1,0,arg)   read=Array(1)");
    assert_eq!(u.stages, [ClockStage::Tick(Ratio(-1))]);
    let runs = super::Entry::runs(&g.nodes[0].entries);
    assert_eq!(runs, [(ClockStage::SAMPLE, ClockStage::SAMPLE)], "a `.down~` in an `.up~` runs at `sample`");
}

/// The boundaries of a chain (§11.9, S-1207, S-1214), each `.down~` and
/// `.up~` running the part on its left as one part: the stages of the
/// caller of the outermost (`St_L`, with the tick of a boundary that deals),
/// the one that makes its output (`made_L`), and the inputs each gathers
/// and whether it deals, of the forms of the model of the review of W7-21
/// (`target/notes/176/w721/review/model.py`, its rows 1–13 but 8, and two
/// with boundaries that deal on and on).
#[test]
fn the_boundaries_of_a_chain() {
    use crate::clock::{ClockStage, Ratio};
    let heads = "pub flow id(x: F32 at sample) -> F32 at sample { x }
pub flow osc(f: F32 at block) -> F32 at sample { f }
pub flow g2(x: F32 at (sample * 2)) -> F32 at sample { x[0] }
pub flow g4(x: F32 at (sample * 4)) -> F32 at sample { x[0] }
pub flow sl(p: F32 at (sample / 4)) -> F32 at sample { p at sample }
pub flow mk2(x: F32 at sample) -> F32 at (sample * 2) { [x, x] }
pub flow dbl(x: F32 at sample) -> F32 at (sample * 2) { [x, x] }
pub flow mk4(c: F32 at block) -> F32 at (sample * 4) { [c, c, c, c] }
pub flow mid(x: F32 at sample) -> F32 at sample { id~(x).up~(2).down~(2) }
pub flow h1(x: F32 at sample, p: F32 at block) -> F32 at sample {
  let a = prev~(p at (sample / 2))
  x + (a at sample)
}
";
    // The flow, the ports, the chain; `St_L`, `made_L`, and of each
    // boundary the inputs it gathers and whether it deals.
    type Row = (&'static str, &'static str, &'static str, &'static [i32], i32, &'static [(&'static [u32], bool)]);
    let rows: &[Row] = &[
        (
            "r1",
            "x: F32 at sample) -> F32 at sample",
            "id~(x).up~(2).down~(2)",
            &[-1, 0],
            -1,
            &[(&[], false), (&[0], true)],
        ),
        (
            "r2",
            "x: F32 at sample) -> F32 at sample",
            "id~(x).up~(4).down~(4)",
            &[-2, 0],
            -2,
            &[(&[], false), (&[0], true)],
        ),
        (
            "r3",
            "x: F32 at sample) -> F32 at sample",
            "id~(x).up~(4).down~(2).down~(2)",
            &[-2, -1, 0],
            -1,
            &[(&[], false), (&[0], true), (&[0], true)],
        ),
        (
            "r4",
            "s: F32 at (sample / 2)) -> F32 at (sample / 2)",
            "id~(s).up~(2).down~(4)",
            &[-2, -1],
            -2,
            &[(&[], false), (&[0], true)],
        ),
        ("r5", "x: F32 at sample) -> F32 at sample", "id~(x).down~(2).up~(2)", &[0], 0, &[(&[], false), (&[], false)]),
        (
            "r6",
            "x: F32 at sample) -> F32 at sample",
            "g2~(dbl~(x)).down~(2).up~(2)",
            &[0],
            0,
            &[(&[0], false), (&[], false)],
        ),
        ("r7", "p: F32 at block) -> F32 at sample", "osc~(p).up~(2).down~(2)", &[-1], -1, &[(&[], false), (&[], true)]),
        (
            "r9",
            "x: F32 at sample) -> F32 at (sample / 4)",
            "g4~(x).down~(2).down~(2)",
            &[-2, -1, 0],
            -2,
            &[(&[0], false), (&[0], false)],
        ),
        (
            "r10",
            "p: F32 at (sample / 4)) -> F32 at sample",
            "sl~(p).up~(2).down~(2)",
            &[-2, -1],
            -1,
            &[(&[], false), (&[], true)],
        ),
        (
            "r11",
            "x: F32 at sample) -> F32 at sample",
            "g2~(mk2~(x).down~(2).up~(2))",
            &[0],
            0,
            &[(&[], true), (&[], false)],
        ),
        (
            "r12",
            "x: F32 at sample) -> F32 at sample",
            "g2~(id~(dbl~(x)).up~(4).down~(2))",
            &[-1, 0],
            -1,
            &[(&[], false), (&[0], true)],
        ),
        (
            "r13",
            "x: F32 at sample) -> F32 at sample",
            "mid~(x).up~(2).down~(2)",
            &[-1, 0],
            -1,
            &[(&[], false), (&[0], true)],
        ),
        (
            "ra",
            "p: F32 at block) -> F32 at sample",
            "osc~(p).up~(4).down~(2).down~(2)",
            &[-2, -1],
            -1,
            &[(&[], false), (&[], true), (&[], true)],
        ),
        (
            "rb",
            "p: F32 at block) -> F32 at sample",
            "mk4~(p).down~(2).down~(2)",
            &[-2, -1],
            -1,
            &[(&[], true), (&[], true)],
        ),
        (
            "rx7",
            "x: F32 at sample, p: F32 at block) -> F32 at sample",
            "h1~(x, p).up~(4).down~(4)",
            &[-2, 0],
            -2,
            &[(&[], false), (&[0], true)],
        ),
    ];
    let callers: String = rows.iter().map(|r| format!("pub flow {}({} {{ {} }}\n", r.0, r.1, r.2)).collect();
    let a = check(&format!("{heads}{callers}"));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let tick = |k| ClockStage::Tick(Ratio(k));
    for &(name, _, chain, st, made, bounds) in rows {
        let f = flow(&a, name);
        let n = f.nodes.iter().find(|n| !n.bounds.is_empty()).unwrap_or_else(|| panic!("{name}: no chain"));
        let callers: Vec<_> = n.entries.iter().map(|e| e.caller).collect();
        assert_eq!(callers, st.iter().map(|&k| tick(k)).collect::<Vec<_>>(), "{name} {chain}");
        assert_eq!(made_at(n), tick(made), "{name} {chain}");
        let got: Vec<(Vec<u32>, bool)> =
            n.bounds.iter().map(|b| (b.gathers.iter().map(|g| g.0).collect(), b.deals)).collect();
        let want: Vec<(Vec<u32>, bool)> = bounds.iter().map(|(g, d)| (g.to_vec(), *d)).collect();
        assert_eq!(got, want, "{name} {chain}");
        // The slow stages of `St_L` are the caller's.
        assert!(st.iter().filter(|&&k| k < 0).all(|&k| f.stages.contains(&tick(k))), "{name}: {:?}", f.stages);
    }
    // Of `id~(x).up~(4).down~(2).down~(2)` (r3): the rings are written at
    // `sample` of the frames around their boundaries, the head runs at
    // `sample / 4` and not where it is read, and the stages move one by
    // one: the `.up~` at `sample` to `sample / 4`, the ring of the middle
    // boundary at `sample / 2`, that of the outermost at `sample`.
    let r3 = &flow(&a, "r3").nodes[0];
    let rings: Vec<_> = r3.bounds.iter().flat_map(|b| b.gathers.iter().map(|g| g.1)).collect();
    assert_eq!(rings, [tick(0), tick(0)]);
    assert_eq!(runs_read(r3), [(tick(0), tick(-2), false)]);
    let row = "-2: Each(0,j)[0: R(0,D(1))] | -1: G(1,0,ring2), Deal(2<-1) | 0: G(2,0,arg)   read=Array(2)";
    assert_eq!(drawn(r3), row);
    assert_eq!(r3.bounds[2].ins, [Some(Ratio(1))], "the input of the part the outermost wraps is at `sample * 2`");
    downs_that_gather_and_deal(heads);
    steps_of_a_chain(heads, &callers);
}

/// The chains of `.down~(N)` of [`downs_that_gather_and_deal`], of the heads
/// of [`the_boundaries_of_a_chain`].
const DOWNS: &str = "pub flow id4(x: F32 at (sample * 4)) -> F32 at (sample * 4) { x }
pub flow mk2p(p: F32 at block) -> F32 at (sample * 2) { [p, p] }
pub flow two(x: F32 at (sample * 2), y: F32 at (sample * 2)) -> F32 at sample { x[0] + y[1] }
pub flow db(x: F32 at sample) -> F32 at sample { g4~(x).down~(4) at sample }
pub flow dc(p: F32 at block) -> F32 at sample { g4~(p).down~(4).down~(2) at sample }
pub flow dd(p: F32 at block) -> F32 at sample { mk4~(p).down~(4) }
pub flow de(x: F32 at sample) -> F32 at sample { id4~(x).down~(4) }
pub flow df(p: F32 at block) -> F32 at sample { mk2p~(p).down~(4) at sample }
pub flow dg(p: F32 at block) -> F32 at sample {
  let h = prev~(p at (sample / 2))
  g2~(h).down~(4) at sample
}
pub flow dh(p: F32 at block) -> F32 at sample { h1~(p, p).down~(2) at sample }
pub flow dx(x: F32 at sample) -> F32 at sample { two~(x, x).down~(2) at sample }
pub flow dy(p: F32 at block) -> F32 at sample { mk4~(p).down~(4).down~(2) at sample }
";

/// Of a chain of `.down~(N)` whose innermost boundary alone gathers or
/// deals (W7-16 U6a2): each boundary (its ports, the inputs it gathers with
/// the stage of the frame around it, whether it deals), the stage of this
/// flow each ring is written at (of its [`super::Op::Ring`]), the runs
/// (of its entries, [`runs_read`]), and the stage the node is read at. Of the hand table of the memo of U6a0 (1.5, its rows b–h, the
/// row c of a parameter kind gathered, S-1214), each ring, `St_L`, `made_L`
/// and the stages of the head as the model of W7-21
/// (`target/notes/176/w721/u1/b/mymodel.py`, as `plansweep.py` reads it)
/// sees them; a chain that deals is read from its array, not where its
/// head runs (its `read`, the review of U6a0).
fn downs_that_gather_and_deal(heads: &str) {
    use crate::clock::{ClockStage, Ratio};
    let a = check(&format!("{heads}{DOWNS}"));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let t = |k| ClockStage::Tick(Ratio(k));
    // A boundary: ins, out, gathers (input, stage of the frame around it), deals.
    type B = (Vec<Option<i32>>, i32, Vec<(u32, i32)>, bool);
    // The flow, its boundaries, the stage of this flow of each ring, the runs (body, caller, read), the stage it is read at.
    type Row = (&'static str, Vec<B>, Vec<i32>, Vec<(i32, i32, bool)>, i32);
    let rows: Vec<Row> = vec![
        ("db", vec![(vec![Some(2)], 0, vec![(0, 0)], false)], vec![0], vec![(0, -2, true)], -2),
        (
            "dc",
            vec![(vec![Some(2)], 0, vec![(0, 0)], false), (vec![Some(0)], -2, vec![], false)],
            vec![-1],
            vec![(0, -3, true)],
            -3,
        ),
        ("dd", vec![(vec![None], 2, vec![], true)], vec![], vec![(0, -2, false)], 0),
        ("de", vec![(vec![Some(2)], 2, vec![(0, 0)], true)], vec![0], vec![(0, -2, false)], 0),
        ("df", vec![(vec![None], 1, vec![], true)], vec![], vec![(0, -2, false)], -1),
        ("dg", vec![(vec![Some(1)], 0, vec![(0, -1)], false)], vec![-1], vec![(0, -2, true)], -2),
        ("dh", vec![(vec![Some(0), None], 0, vec![], false)], vec![], vec![(-1, -2, false), (0, -1, true)], -1),
        ("dx", vec![(vec![Some(1), Some(1)], 0, vec![(0, 0), (1, 0)], false)], vec![0, 0], vec![(0, -1, true)], -1),
        ("dy", vec![(vec![None], 2, vec![], true), (vec![None], 0, vec![], false)], vec![], vec![(0, -3, false)], -1),
    ];
    for (name, bounds, rings, runs, read) in rows {
        let f = flow(&a, name);
        let n = f.nodes.iter().find(|n| !n.bounds.is_empty()).unwrap_or_else(|| panic!("{name}: no chain"));
        let got: Vec<B> = n
            .bounds
            .iter()
            .map(|b| {
                let st = |s: ClockStage| match s {
                    ClockStage::Tick(k) => k.0,
                    _ => 1,
                };
                (
                    b.ins.iter().map(|k| k.map(|k| k.0)).collect(),
                    b.out.map_or(9, |k| k.0),
                    b.gathers.iter().map(|g| (g.0, st(g.1))).collect(),
                    b.deals,
                )
            })
            .collect();
        assert_eq!(got, bounds, "{name}");
        let mut written = Vec::new();
        for e in &n.entries {
            super::Op::walk(&e.ops, &mut |op| {
                if let super::Op::Ring { bound: 0, input, .. } = *op {
                    written.push((input, e.caller));
                }
            });
        }
        written.sort();
        let want: Vec<_> = (0u32..).zip(rings.iter().map(|&k| t(k))).collect();
        assert_eq!(written, want, "{name}");
        let got = runs_read(n);
        assert_eq!(got, runs.iter().map(|&(b, c, r)| (t(b), t(c), r)).collect::<Vec<_>>(), "{name}");
        let dealt = matches!(n.read, super::Read::Array(_));
        assert_eq!(dealt, n.bounds.iter().any(|b| b.deals), "{name}");
        let id = super::NodeId(f.nodes.iter().position(|m| m.expr == n.expr).unwrap() as u32);
        assert_eq!(f.node_stage(id), Some(t(read)), "{name}");
        assert!(n.lowered_chain() && f.multirate_at().is_none(), "{name}");
    }
    // §11.6 (S-1208): after the state of the instance, by boundary, its rings by input, then its array.
    let names = |name: &str| flow(&a, name).fields.iter().map(|x| x.name.clone()).collect::<Vec<_>>();
    assert_eq!(names("de")[1..4], ["_out.id4_0", "_out.id4_0._gather_0_0", "_out.id4_0._deal_0"]);
    assert_eq!(names("dx")[1..4], ["_out.two_0", "_out.two_0._gather_0_0", "_out.two_0._gather_0_1"]);
    assert!(names("dc").contains(&"_out.g4_0._gather_0_0".to_string()), "{:?}", names("dc"));
}

/// The table of the work of each instance in the stages of its caller
/// (§11.9, S-1207, S-1214, W7-16 U6b0a), drawn as the memo of U6b0 writes
/// it: of each entry its stage (`*` of the one read) and its ops, `R(body,
/// out)` a run (`-` nowhere, `V` the value, `D(b)` the array of `b`),
/// `G(b,input,from)` a ring, `Deal(b<-from)`, `Each(b,j|once)[stage: ops;
/// …]`, then how the caller reads it. Each row as the memo (2.6, 5.2) drew
/// it by hand from §11.9 and the model of its review
/// (`target/notes/178/w716/u6b0/review/model.py`, `mine()`) gave it on its
/// own: the order of the groups of an `Each` (r6) and of a `Deal` after the
/// work inside (r3, m8u) are of the values (§11.9). The sources are those
/// of [`the_boundaries_of_a_chain`] and [`DOWNS`], with two of a head
/// dealing at `sample * 8` read by a head of `sample * N` (as r11). Of
/// every instance of them, a ring written from the argument is written in
/// the function its argument is read in: the marking ([`super::ArgRead`])
/// and the table agree.
fn steps_of_a_chain(heads: &str, callers: &str) {
    let eight = "pub flow mk8(c: F32 at block) -> F32 at (sample * 8) { [c, c, c, c, c, c, c, c] }
pub flow m8(p: F32 at block) -> F32 at sample { g2~(mk8~(p).down~(2).down~(2)) }
pub flow m8u(p: F32 at block) -> F32 at sample { g4~(mk8~(p).down~(2).up~(2).down~(2)) }
";
    let a = check(&format!("{heads}{callers}{DOWNS}{eight}"));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let rows = [
        ("db", "-2*: R(0,V) | 0: G(0,0,arg)   read=Run"),
        ("dc", "-3*: R(0,V) | -1: G(0,0,arg)   read=Run"),
        ("dd", "-2: R(0,D(0))   read=Array(0)"),
        ("de", "-2: R(0,D(0)) | 0: G(0,0,arg)   read=Array(0)"),
        ("df", "-2: R(0,D(0))   read=Array(0)"),
        ("dg", "-2*: R(0,V) | -1: G(0,0,arg)   read=Run"),
        ("dh", "-2: R(-1,-) | -1*: R(0,V)   read=Run"),
        ("dx", "-1*: R(0,V) | 0: G(0,0,arg), G(0,1,arg)   read=Run"),
        ("dy", "-3: R(0,D(0))   read=Array(0)"),
        // S-1214 (1): `g4~(x).down~(2).down~(2)`.
        ("r9", "-2*: R(0,V) | -1: G(0,0,ring1) | 0: G(1,0,arg)   read=Run"),
        ("rx7", "-2: Each(0,j)[-1: R(-1,-); 0: R(0,D(1))] | 0: G(1,0,arg)   read=Array(1)"),
        ("ra", "-2: Each(0,j)[0: R(0,D(1))] | -1: Deal(2<-1)   read=Array(2)"),
        ("m8", "-2: R(0,D(0)) | -1: Deal(1<-0)   read=Array(1)"),
        ("r6", "0*: Each(1,j)[-1: R(0,V); 0: G(0,0,arg)]   read=Run"),
        ("r3", "-2: Each(0,j)[0: R(0,D(1))] | -1: G(1,0,ring2), Deal(2<-1) | 0: G(2,0,arg)   read=Array(2)"),
        ("m8u", "-1: Each(1,j)[-1: R(0,D(0))], Deal(2<-0)   read=Array(2)"),
    ];
    for (name, want) in rows {
        let f = flow(&a, name);
        let n = f.nodes.iter().find(|n| !n.bounds.is_empty()).unwrap_or_else(|| panic!("{name}: no chain"));
        assert_eq!(drawn(n), want, "{name}");
    }
    let mut seen = 0;
    for f in a.flows.values() {
        for n in &f.nodes {
            for e in &n.entries {
                super::Op::walk(&e.ops, &mut |op| {
                    if let super::Op::Ring { input, from: super::Feed::Arg, .. } = *op {
                        let at = n.args[input as usize].at.stage().map(|s| f.run_stage(s));
                        assert_eq!(at, Some(e.caller), "{}", n.path);
                        seen += 1;
                    }
                });
            }
        }
    }
    assert!(seen > 0, "no ring written from an argument");
}

/// The stage `s` as the memo of U6b0 writes it: the exponent of a tick.
fn st(s: crate::clock::ClockStage) -> String {
    match s {
        crate::clock::ClockStage::Tick(k) => k.0.to_string(),
        s => format!("{s:?}"),
    }
}

/// The ops `ops` drawn ([`steps_of_a_chain`]).
fn drawn_ops(ops: &[super::Op]) -> String {
    use super::{Feed, Op, Out};
    let op = |op: &Op| match op {
        Op::Run { body, out } => {
            let out = match out {
                Out::None => "-".to_string(),
                Out::Value => "V".to_string(),
                Out::Deal(b) => format!("D({b})"),
            };
            format!("R({},{out})", st(*body))
        }
        Op::Ring { bound, input, from: Feed::Arg } => format!("G({bound},{input},arg)"),
        Op::Ring { bound, input, from: Feed::Ring(r) } => format!("G({bound},{input},ring{r})"),
        Op::Deal { bound, from } => format!("Deal({bound}<-{from})"),
        Op::Each { bound, once, groups } => {
            let groups: Vec<_> = groups.iter().map(|(y, ops)| format!("{}: {}", st(*y), drawn_ops(ops))).collect();
            format!("Each({bound},{})[{}]", if *once { "once" } else { "j" }, groups.join("; "))
        }
    };
    ops.iter().map(op).collect::<Vec<_>>().join(", ")
}

/// The table of the work of the node `n` drawn ([`steps_of_a_chain`]).
fn drawn(n: &super::PlanNode) -> String {
    let entry = |e: &super::Entry| format!("{}{}: {}", st(e.caller), if e.read { "*" } else { "" }, drawn_ops(&e.ops));
    let read = match n.read {
        super::Read::Run => "Run".to_string(),
        super::Read::Array(b) => format!("Array({b})"),
    };
    format!("{}   read={read}", n.entries.iter().map(entry).collect::<Vec<_>>().join(" | "))
}

/// The runs of the entries of `n` ([`super::Entry::runs`]), each with
/// whether its entry is read where the call is.
fn runs_read(n: &super::PlanNode) -> Vec<(crate::clock::ClockStage, crate::clock::ClockStage, bool)> {
    let read = |c| n.entries.iter().any(|e| e.caller == c && e.read);
    super::Entry::runs(&n.entries).into_iter().map(|(b, c)| (b, c, read(c))).collect()
}

/// The stage of the caller that makes what it reads of the instance `n`
/// (§11.9): of the entry read, else of the entry that writes the array it
/// reads (a run that deals into it, or the copy of it).
fn made_at(n: &super::PlanNode) -> crate::clock::ClockStage {
    use super::{Op, Out, Read};
    let makes = |e: &super::Entry| {
        let mut makes = e.read;
        Op::walk(&e.ops, &mut |op| {
            makes |= match (n.read, op) {
                (Read::Array(b), Op::Run { out: Out::Deal(d), .. } | Op::Deal { bound: d, .. }) => b == *d,
                _ => false,
            }
        });
        makes
    };
    n.entries.iter().find(|e| makes(e)).map(|e| e.caller).unwrap_or_else(|| panic!("{}: nothing makes it", n.path))
}

/// The Core lowers the body of a flow with a port at `sample * N` (W7-16
/// U6a2, §11.9) and stops until U6b at an instance that gathers or deals
/// one in its caller (its value or an argument at `sample * N`). A port at
/// `sample / N` and an instance of a flow with one do not stop it (W7-16
/// U5b2), and the flow with one is known by its `derived_port` (no
/// `process`, the review's M3).
#[test]
fn a_burst_in_the_caller_stops_the_core() {
    let src = "pub flow f(p: F32 at block, x: F32 at (sample * 2)) -> F32 at sample {\n  x[0] * p\n}\n\
               pub flow g(x: F32 at sample) -> F32 at (sample * 2) {\n  [x, x]\n}\n\
               pub flow h(x: F32 at sample) -> F32 at sample {\n  x\n}\n\
               pub flow sl(x: F32 at (sample / 4)) -> F32 at (sample / 4) {\n  x\n}\n\
               pub flow k(p: F32 at block) -> F32 at sample {\n  sl~(p at (sample / 4)) at sample\n}\n\
               pub flow m(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  f~(p, g~(x))\n}\n";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let at = |name: &str| flow(&a, name).multirate_at().map(|s| &src[s.start as usize..s.end as usize]);
    assert_eq!([at("f"), at("g"), at("h"), at("sl"), at("k")], [None, None, None, None, None]);
    assert_eq!(at("m"), Some("f~(p, g~(x))"), "an instance of a port at `sample * N`");
    let port = |name: &str| flow(&a, name).derived_port.map(|s| &src[s.start as usize..s.end as usize]);
    assert_eq!([port("sl"), port("h"), port("k")], [Some("x: F32 at (sample / 4)"), None, None]);
}

/// The gate passes a chain of `.down~(N)` alone (W7-16 U6a1, §11.9),
/// nested too, of a callee that reads the time through a flow (U6a3,
/// S-1217), and one whose innermost boundary alone gathers or deals
/// (U6a2); and stops, at the node, one with an `.up~(N)`, one that gathers
/// at two boundaries and one that gathers or deals a burst in its caller
/// (U6b). Each modifier of a chain has its receiver.
#[test]
fn the_gate_passes_a_chain_of_downs_that_gathers_and_deals_at_its_innermost_alone() {
    let src = "flow lp(x: F32 at sample) -> F32 at sample {\n  x + prev~(x)\n}\n\
               flow tk() -> U32 at sample {\n  sample_tick()\n}\n\
               flow mid() -> U32 at sample {\n  tk~()\n}\n\
               flow g4(x: F32 at (sample * 4)) -> F32 at sample {\n  x[0]\n}\n\
               flow mk4(p: F32 at block) -> F32 at (sample * 4) {\n  [p, p, p, p]\n}\n\
               pub flow down(p: F32 at block) -> F32 at sample {\n  lp~(p).down~(4).down~(2) at sample\n}\n\
               pub flow timed(p: F32 at block) -> U32 at sample {\n  mid~().down~(2) at sample\n}\n\
               pub flow gathers(p: F32 at block) -> F32 at sample {\n  g4~(p).down~(4) at sample\n}\n\
               pub flow deals(p: F32 at block) -> F32 at sample {\n  mk4~(p).down~(4)\n}\n\
               pub flow up(p: F32 at block) -> F32 at sample {\n  lp~(p).down~(2).up~(2)\n}\n\
               pub flow twice(x: F32 at sample) -> F32 at sample {\n  g4~(x).down~(2).down~(2) at sample\n}\n\
               flow g2(x: F32 at (sample * 2)) -> F32 at sample {\n  x[0]\n}\n\
               pub flow burst_in(p: F32 at block) -> F32 at sample {\n  g4~(p).down~(2) at sample\n}\n\
               pub flow burst_out(p: F32 at block) -> F32 at sample {\n  g2~(mk4~(p).down~(2))\n}\n";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let at = |name: &str| flow(&a, name).multirate_at().map(|s| &src[s.start as usize..s.end as usize]);
    assert_eq!([at("down"), at("timed"), at("gathers"), at("deals")], [None, None, None, None]);
    assert_eq!(
        [at("up"), at("twice"), at("burst_in"), at("burst_out")],
        [Some("lp~(p)"), Some("g4~(x)"), Some("g4~(p)"), Some("g2~(mk4~(p).down~(2))")]
    );
    let lowered = |name: &str| flow(&a, name).nodes.iter().all(|n| n.lowered_chain());
    assert_eq!(["gathers", "deals", "twice", "burst_in", "burst_out"].map(lowered), [true, true, false, true, true]);
    let (down, timed) = (flow(&a, "down"), flow(&a, "timed"));
    assert!(down.nodes[0].lowered_chain() && timed.nodes[0].lowered_chain());
    // `.down~(4)` of the head, then `.down~(2)` of that.
    let of = |r| down.modifiers.iter().find(|&(_, &x)| x == r).map(|(&m, _)| m);
    let inner = of(down.nodes[0].expr);
    assert_eq!((down.modifiers.len(), inner.and_then(of).is_some()), (2, true), "{:?}", down.modifiers);
}

/// The words of the time each stage takes (§11.4, §12.4, S-1217, S-1211,
/// W7-16 U6a3; worked out by hand from the rules of the table): `t` where
/// `sample_tick()` is read, at the stage of its clock (a hoisted one at its
/// tick, one in an argument a chain gathers at the stage of the argument);
/// where a callee's stage that takes it runs, its words, two under a
/// `.down~`, through a flow of no modifier too; none where neither. The
/// counter of a flow with no slower stage advances in `process`, of one
/// with them in `tick`; `_tick_hi` follows `_tick` (S-1179 (2)).
#[test]
fn the_table_gives_the_words_of_the_time_of_each_stage() {
    let src = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\
               flow so() -> U32 at (sample / 4) {\n  sample_tick()\n}\n\
               flow mid() -> U32 at sample {\n  so~() at sample\n}\n\
               pub flow top() -> U32 at sample {\n  mid~()\n}\n\
               pub flow both() -> U32 at sample {\n  tk~() + (tk~().down~(2) at sample)\n}\n\
               flow mid2() -> U32 at sample {\n  tk~().down~(2) at sample\n}\n\
               pub flow outer() -> U32 at sample {\n  mid2~().down~(2) at sample\n}\n\
               pub flow hoisted() -> U32 at sample {\n  (sample_tick() at (sample / 4)) at sample\n}\n\
               flow g4(v: U32 at (sample * 4)) -> U32 at sample {\n  v[3]\n}\n\
               pub flow gat() -> U32 at sample {\n  g4~(sample_tick()).down~(4) at sample\n}\n";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let tick = |k| crate::clock::ClockStage::Tick(crate::clock::Ratio(k));
    let time = |name: &str| flow(&a, name).time.iter().map(|(&s, &w)| (s, w)).collect::<Vec<_>>();
    use super::Words::{One, Two};
    assert_eq!(time("tk"), [(tick(0), One)]);
    assert_eq!([time("so"), time("mid"), time("top")], [[(tick(-2), One)], [(tick(-2), One)], [(tick(-2), One)]]);
    assert_eq!(time("both"), [(tick(-1), Two), (tick(0), One)]);
    assert_eq!([time("mid2"), time("outer")], [[(tick(-1), Two)], [(tick(-2), Two)]]);
    assert_eq!([time("hoisted"), time("gat")], [[(tick(-2), One)], [(tick(0), One)]]);
    assert!(time("g4").is_empty() && !flow(&a, "g4").counts_time());
    let wide = ["tk", "top", "both", "mid2", "outer", "hoisted", "gat"].map(|f| flow(&a, f).wide());
    assert_eq!(wide, [false, false, true, true, true, false, false]);
    let counter = ["tk", "both", "top", "gat"].map(|f| flow(&a, f).counter());
    assert_eq!(counter, [super::Counter::Process, super::Counter::Tick, super::Counter::Tick, super::Counter::Tick]);
    let names = |f: &str| flow(&a, f).fields.iter().take(2).map(|x| x.name.clone()).collect::<Vec<_>>();
    assert_eq!([names("both"), names("outer")], [["_tick", "_tick_hi"], ["_tick", "_tick_hi"]]);
    assert!(flow(&a, "top").fields.iter().all(|x| x.name != "_tick_hi"));
}

/// The stages the marking evaluates at and those of `sample_tick()` (S-05,
/// §11.4, §11.9, W7-16 U6a4; worked out by hand): an argument of a node is
/// a root at the stage it is read at (`sample / 4`), so the caller has that
/// stage and reads the time there whether or not the table of its callee
/// (here in error) has it; an output at `sample / 2` with nothing else
/// there has that stage (S-1213); `h + 1` of `sample / 2` in the argument
/// a chain gathers at `sample` is hoisted to `sample / 2` (as the output of
/// the chain, of `sample / 2`, read at `sample`, §11.3), a write of that
/// stage held by the `let` `r` (index 1), not by `h` nor at `sample`.
#[test]
fn the_marking_records_the_stages_it_evaluates_at() {
    let src = "flow bad(a: U32 at (sample / 4)) -> U32 at sample {\n  (a at sample) + true\n}\n\
               pub flow arg() -> U32 at sample {\n  bad~(sample_tick() at (sample / 4))\n}\n\
               pub flow out() -> U32 at (sample / 2) {\n  7\n}\n\
               flow cnt(i0: U32 at block) -> U32 at sample {\n  let n = (i0 + prev~(^n)) % 997\n  n\n}\n\
               flow g2(a: U32 at (sample * 2)) -> U32 at sample {\n  a[0] * 10 + a[1]\n}\n\
               pub flow gat(p: U32 at block) -> U32 at sample {\n  let h = cnt~(p).down~(2)\n  \
               let r = g2~((h + 1) at sample).down~(2) at sample\n  r + 1\n}\n";
    let a = check(src);
    let codes: Vec<String> = a.diagnostics.iter().map(|d| format!("{:?}", d.code)).collect();
    assert_eq!(codes.len(), 1, "{codes:?}");
    let tick = |k| crate::clock::ClockStage::Tick(crate::clock::Ratio(k));
    let set = |s: &std::collections::BTreeSet<_>| s.iter().copied().collect::<Vec<_>>();
    let (arg, out, gat) = (flow(&a, "arg"), flow(&a, "out"), flow(&a, "gat"));
    assert!(arg.complete && out.complete && gat.complete && !flow(&a, "bad").complete);
    assert_eq!([set(&arg.eval_at), set(&arg.time_at)], [vec![tick(-2), tick(0)], vec![tick(-2)]]);
    assert_eq!(arg.stages, [tick(-2)]);
    assert_eq!(arg.time.iter().map(|(&s, &w)| (s, w)).collect::<Vec<_>>(), [(tick(-2), super::Words::One)]);
    assert_eq!([set(&out.eval_at), out.stages.clone()], [vec![tick(-1)], vec![tick(-1)]]);
    let hoists: Vec<_> = gat.hoists.iter().map(|h| (h.stage, h.owner)).collect();
    assert_eq!(hoists, [(tick(-1), Owner::Let(1)); 2], "`h + 1` and the output of the chain, read at `sample`");
    assert_eq!(gat.stages, [tick(-1)]);
    assert!(gat.writes_in(1, tick(-1)) && !gat.writes_in(0, tick(-1)) && !gat.writes_in(1, tick(0)));
    assert!(!gat.writes_in(2, tick(-1)), "the output holds no write");
}

/// The Core lowers the slower ticks of one flow and `sample_tick()` (W7-16
/// U5a): the gate passes a flow with a `let`, a node and a hoisted field
/// at `sample / 4` or `sample / 2` and one that reads `sample_tick()`,
/// whose ticks are slowest first and whose state has the counter of the
/// phase after `_sample_rate` (S-1179 (2)); and an instance of a flow that
/// counts the time, whose stages and time its caller gives (W7-16 U5b2).
#[test]
fn the_gate_passes_the_slower_ticks_of_one_flow_and_an_instance_of_one() {
    let src = "pub flow slow(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let a = prev~(p at (sample / 4)) + 1.0
  let b = prev~(a at (sample / 2))
  x * sample_rate() + (a at sample) + (b at sample) + (prev~(b) at sample)
}
pub flow tk(x: F32 at sample) -> F32 at sample {
  x * F32.round_from(sample_tick())
}
pub flow plain(x: F32 at sample) -> F32 at sample {
  prev~(x)
}
pub flow calls(x: F32 at sample) -> F32 at sample {
  plain~(x) + tk~(x)
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let (slow, tk, plain, calls) = (flow(&a, "slow"), flow(&a, "tk"), flow(&a, "plain"), flow(&a, "calls"));
    let tick = |k| crate::clock::ClockStage::Tick(crate::clock::Ratio(k));
    assert_eq!(slow.stages, [tick(-2), tick(-1)]);
    assert!(tk.stages.is_empty() && plain.stages.is_empty());
    // A caller of a flow that reads the time reads it too (S-1129 (1)).
    assert!(slow.counts_time() && tk.counts_time() && !plain.counts_time() && calls.counts_time());
    let names = |f: &FlowInfo| f.fields.iter().take(2).map(|x| x.name.clone()).collect::<Vec<_>>();
    assert_eq!(names(slow), ["_sample_rate", "_tick"]);
    assert_eq!(names(tk)[0], "_tick");
    assert!(plain.fields.iter().all(|x| x.name != "_tick"));
    assert_eq!([slow, tk, plain, calls].map(|f| f.multirate_at()), [None, None, None, None]);
    assert_eq!(slow.run_stage(tick(2)), tick(0), "a burst is of the function of the `sample` of the body");
    assert_eq!(slow.run_stage(tick(-2)), tick(-2));
}

/// The table of the entries of the stages (S-1088, W7-16 U5b1): an
/// instance of `sample` (r = 0) runs each stage of the body of its callee
/// in the same stage of its caller, the slow ones first, and reads it at
/// the one that makes the output; the caller has those stages too, of a
/// grandchild through its child and of a child in a `par~`, and reads the
/// time when a callee does. A node is of the stage of its clock, a `par~`
/// of none ([`FlowInfo::node_stage`]).
#[test]
fn the_table_gives_the_runs_of_the_stages_of_the_callees() {
    let src = "pub flow gc(x: F32 at sample, p: F32 at block) -> F32 at sample {
  let a = prev~(p at (sample / 4)) + 1.0
  x + (a at sample)
}
pub flow ch(x: F32 at sample, p: F32 at block) -> F32 at sample {
  gc~(x, p) * F32.round_from(sample_tick())
}
pub flow top(x: F32 at sample, p: F32 at block) -> F32 at sample {
  let d = prev~(p at (sample / 2))
  ch~(x, p) + (par~ i in 0..<2 { ch~(x, p) })[1] + (d at sample)
}
pub flow plain(x: F32 at sample) -> F32 at sample {
  prev~(x)
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let tick = |k| crate::clock::ClockStage::Tick(crate::clock::Ratio(k));
    let run = |b, c, read| (tick(b), tick(c), read);
    let (gc, ch, top, plain) = (flow(&a, "gc"), flow(&a, "ch"), flow(&a, "top"), flow(&a, "plain"));
    assert_eq!([&gc.stages, &ch.stages], [&[tick(-2)], &[tick(-2)]]);
    assert_eq!(top.stages, [tick(-2), tick(-1)]);
    assert_eq!(runs_read(ch.node(named(ch, "_out.gc_0"))), [run(-2, -2, false), run(0, 0, true)]);
    for path in ["_out.ch_0", "_out.par_0.ch_0"] {
        assert_eq!(runs_read(top.node(named(top, path))), [run(-2, -2, false), run(0, 0, true)], "{path}");
    }
    assert!(top.node(named(top, "d.prev_0")).entries.is_empty());
    assert_eq!([gc.reads_time(), ch.reads_time(), top.reads_time(), plain.reads_time()], [false, true, true, false]);
    assert!(top.counts_time() && !plain.counts_time());
    assert_eq!(top.fields.iter().take(1).map(|f| f.name.as_str()).collect::<Vec<_>>(), ["_tick"]);
    let stage = |path| top.node_stage(named(top, path));
    assert_eq!([stage("d.prev_0"), stage("_out.ch_0"), stage("_out.par_0")], [Some(tick(-1)), Some(tick(0)), None]);
    assert_eq!(top.out_stage, Some(tick(0)));
}

/// A loop of calls (E0817 of the names stage) and a callee in error give
/// the walk of the table nothing to run and nothing to count: it ends, with
/// no internal error.
#[test]
fn the_table_ends_at_a_loop_of_calls_and_a_callee_in_error() {
    let src = "pub flow f(x: F32 at sample) -> F32 at sample { g~(x) }
pub flow g(x: F32 at sample) -> F32 at sample { f~(x) }
pub flow bad(x: F32 at sample) -> F32 at sample { x + true }
pub flow h(x: F32 at sample) -> F32 at sample { bad~(x).down~(4096) at sample }
";
    let a = check(src);
    let codes: Vec<String> = a.diagnostics.iter().map(|d| format!("{:?}", d.code)).collect();
    assert!(codes.contains(&"E0817".to_string()), "{codes:?}");
    assert!(!codes.contains(&"E0808".to_string()), "{codes:?}");
    for name in ["f", "g", "h"] {
        assert!(flow(&a, name).nodes.iter().all(|n| n.entries.is_empty()), "{name}");
    }
}

/// The N on a path through flows (S-1089): past 2^24, E0808 at the
/// modifier of the chain of the caller past which they are, with a note at
/// each step of the path; 2^24 is none; a flow past it alone has its own
/// E0808 and its callers none; a callee in error is not counted.
#[test]
fn the_n_on_a_path_through_flows_are_2_to_the_24_at_most() {
    let leaf = "pub flow leaf(x: F32 at sample) -> F32 at sample { x }
pub flow mid(x: F32 at (sample / 4096)) -> F32 at sample { leaf~(x).down~(4096) at sample }
";
    let past = |caller: &str| {
        let src = format!("{leaf}{caller}");
        let a = check(&src);
        let at = |s: onsa_diag::Span| src[s.start as usize..s.end as usize].to_string();
        a.diagnostics.iter().map(|d| (format!("{:?}", d.code), at(d.span), d.notes.len())).collect::<Vec<_>>()
    };
    let t = "pub flow t(p: F32 at block) -> F32 at sample { mid~(p).up~(2).down~(4096).down~(4) at sample }\n";
    let got = past(t);
    assert_eq!(got, [("E0808".to_string(), "down".to_string(), 2)]);
    let a = check(&format!("{leaf}{t}"));
    // Multiplied in the order they are written, the N are past 2^24 at `.down~(4096)`.
    assert_eq!(a.diagnostics[0].span.start as usize, leaf.len() + t.find("down~(4096)").unwrap());
    let notes: Vec<&str> = a.diagnostics[0].notes.iter().map(|n| n.message.as_str()).collect();
    assert!(notes[0].contains("`t`") && notes[0].contains("`mid`") && notes[1].contains("`leaf`"), "{notes:?}");
    assert!(past("pub flow t(p: F32 at block) -> F32 at sample { mid~(p).down~(4096) at sample }\n").is_empty());
    let alone = "pub flow m2(p: F32 at block) -> F32 at sample { leaf~(p).down~(1048576).down~(1048576) at sample }
pub flow t(p: F32 at block) -> F32 at sample { m2~(p).down~(2) at sample }
";
    assert_eq!(past(alone).iter().map(|d| d.1.as_str()).collect::<Vec<_>>(), ["down"]);
    assert!(past(alone)[0].2 == 1, "the E0808 of `m2` alone, with the note of its chain");
}

/// The places of E0808 the parent read of S-1089 and §18.1 (W7-16 U5b1):
/// (1) on a path through flows, the modifier of the caller's chain past
/// which the N are, multiplied from the count of the callee in the order
/// they are written; (2) a chain with an N in error and N past 2^24 has
/// the error of its N alone; (3) the callers of a flow past it alone, and
/// theirs, are quiet.
#[test]
fn the_places_of_the_e0808_of_a_path() {
    let leaf = "pub flow leaf(x: F32 at sample) -> F32 at sample { x }
pub flow mid(x: F32 at (sample / 4096)) -> F32 at sample { leaf~(x).down~(4096) at sample }
";
    let errors = |body: &str| {
        let src = format!("{leaf}{body}");
        let a = check(&src);
        let at = |d: &onsa_diag::Diagnostic| (format!("{:?}", d.code), src[d.span.start as usize..].to_string());
        a.diagnostics.iter().map(at).collect::<Vec<_>>()
    };
    // (1) 2^12 of `mid`, then 2^24 at `.down~(4096)`, past it at `.down~(2)`.
    let got = errors("pub flow t(p: F32 at block) -> F32 at sample { mid~(p).down~(4096).down~(2) at sample }\n");
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(got[0].0 == "E0808" && got[0].1.starts_with("down~(2)"), "{got:?}");
    // (2) The N of 3 is the error, not the product past 2^24, in either order.
    for chain in ["down~(3).down~(33554432)", "down~(33554432).down~(3)"] {
        let got = errors(&format!("pub flow t(p: F32 at block) -> F32 at sample {{ leaf~(p).{chain} at sample }}\n"));
        assert_eq!(got.len(), 1, "{chain}: {got:?}");
        assert!(got[0].0 == "E0808" && got[0].1.starts_with("3)"), "{chain}: {got:?}");
    }
    // (3) Only `past` has the error: `user` calls it, `outer` calls `user`.
    let got = errors(
        "pub flow past(p: F32 at block) -> F32 at sample { leaf~(p).down~(8192).down~(8192) at sample }
pub flow user(p: F32 at block) -> F32 at sample { past~(p) }
pub flow outer(p: F32 at block) -> F32 at sample { user~(p).down~(8192) at sample }
",
    );
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(got[0].1.starts_with("down~(8192) at sample }\npub flow user"), "{got:?}");
}
