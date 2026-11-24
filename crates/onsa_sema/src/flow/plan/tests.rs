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
/// value read at `sample` is hoisted to a field of its tick (S-1185). Of an `.up~` in a
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
    let g = flow(&a, "g");
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
            n.bounds.iter().map(|b| (b.gathers.iter().map(|g| input(g.0)).collect(), b.deals)).collect();
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
                    b.gathers.iter().map(|g| (input(g.0), st(g.1))).collect(),
                    b.deals,
                )
            })
            .collect();
        assert_eq!(got, bounds, "{name}");
        let mut written = Vec::new();
        for e in &n.entries {
            super::Op::walk(&e.ops, &mut |op| {
                if let super::Op::Ring { bound: 0, port, .. } = *op {
                    written.push((input(port), e.caller));
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
                    if let super::Op::Ring { port: super::Port::Input(input), from: super::Feed::Arg, .. } = *op {
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

/// The table of the work of a chain (§11.9, S-1207, S-1214, W7-16 U6b1) of
/// the rows of the value model of the review of U6b
/// (`target/notes/178/w716/u6b/review/model.py`, its `table` and `show`,
/// with the rule of its high 1 of `review/fix.py`: an entry is read where the
/// node is read when it writes the array the node is read from), not of the
/// output of the implementation: of a fixed seed (1216), 34 forms of the
/// model (one input, one output, a stage of the head of its own) with an
/// `.up~` first, in the middle and last, a head with a stage of its own, two
/// rings of an input, two `.up~`, a copy into a wider window (into an array
/// and into the value, written each run j of the `.up~` after its writer)
/// and an entry read by the high 1, with the source each is written in
/// (`P/w716/u6b1/i/rows/gen_rows.py` of the ticket of U6b1). The model
/// draws the boundary of the window of a copy (`by`) as `@by` where it is
/// not that of its array.
#[test]
fn the_table_of_the_model_of_the_review_of_u6b() {
    let callers: String = U6B_ROWS.iter().map(|r| format!("{}\n", r.1)).collect();
    let a = check(&format!("{U6B_HEADS}{callers}"));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    for &(name, _, want) in U6B_ROWS {
        let f = flow(&a, name);
        let n = f.nodes.iter().find(|n| !n.bounds.is_empty()).unwrap_or_else(|| panic!("{name}: no chain"));
        assert_eq!(drawn(n), want, "{name}");
    }
}

/// The heads of [`U6B_ROWS`]: `h_<k>_<m>[_s<e>]` of an input at `sample * 2^k`
/// (`p` of none), an output at `sample * 2^m` and a stage `sample / 2^e` of
/// its own (`n` of a minus); `b<q>` makes a burst of 2^q, `r<o>` reads one.
const U6B_HEADS: &str = "flow b1(x: F32 at sample) -> F32 at (sample * 2) { [x, x] }
flow b2(x: F32 at sample) -> F32 at (sample * 4) { [x, x, x, x] }
flow b3(x: F32 at sample) -> F32 at (sample * 8) { [x, x, x, x, x, x, x, x] }
flow r1(x: F32 at (sample * 2)) -> F32 at sample { x[0] }
flow r2(x: F32 at (sample * 4)) -> F32 at sample { x[0] }
flow r3(x: F32 at (sample * 8)) -> F32 at sample { x[0] }
flow h_n1_n1_s2(x: F32 at (sample / 2), c: F32 at block) -> F32 at (sample / 2) {
  let a = prev~(c at (sample / 4))
  x + (a at (sample / 2))
}
flow h_n1_0_s1(x: F32 at (sample / 2), c: F32 at block) -> F32 at sample {
  let a = prev~(c at (sample / 2))
  (x at sample) + (a at sample)
}
flow h_n1_0_s2(x: F32 at (sample / 2), c: F32 at block) -> F32 at sample {
  let a = prev~(c at (sample / 4))
  (x at sample) + (a at sample)
}
flow h_n1_2_s1(x: F32 at (sample / 2), c: F32 at block) -> F32 at (sample * 4) {
  let a = prev~(c at (sample / 2))
  [(x at sample) + (a at sample), (x at sample) + (a at sample), (x at sample) + (a at sample), (x at sample) + (a at sample)]
}
flow h_n2_n1_s1(x: F32 at (sample / 4), c: F32 at block) -> F32 at (sample / 2) {
  let a = prev~(c at (sample / 2))
  (x at (sample / 2)) + a
}
flow h_n2_n1(x: F32 at (sample / 4)) -> F32 at (sample / 2) {
  (x at (sample / 2))
}
flow h_n2_n2(x: F32 at (sample / 4)) -> F32 at (sample / 4) {
  x
}
flow h_n2_0_s2(x: F32 at (sample / 4), c: F32 at block) -> F32 at sample {
  let a = prev~(c at (sample / 4))
  (x at sample) + (a at sample)
}
flow h_n2_0(x: F32 at (sample / 4)) -> F32 at sample {
  (x at sample)
}
flow h_n2_1_s1(x: F32 at (sample / 4), c: F32 at block) -> F32 at (sample * 2) {
  let a = prev~(c at (sample / 2))
  [(x at sample) + (a at sample), (x at sample) + (a at sample)]
}
flow h_n2_1(x: F32 at (sample / 4)) -> F32 at (sample * 2) {
  [(x at sample), (x at sample)]
}
flow h_n2_2(x: F32 at (sample / 4)) -> F32 at (sample * 4) {
  [(x at sample), (x at sample), (x at sample), (x at sample)]
}
flow h_0_2_s2(x: F32 at sample, c: F32 at block) -> F32 at (sample * 4) {
  let a = prev~(c at (sample / 4))
  [x + (a at sample), x + (a at sample), x + (a at sample), x + (a at sample)]
}
flow h_0_3_s1(x: F32 at sample, c: F32 at block) -> F32 at (sample * 8) {
  let a = prev~(c at (sample / 2))
  [x + (a at sample), x + (a at sample), x + (a at sample), x + (a at sample), x + (a at sample), x + (a at sample), x + (a at sample), x + (a at sample)]
}
flow h_1_n1_s2(x: F32 at (sample * 2), c: F32 at block) -> F32 at (sample / 2) {
  let a = prev~(c at (sample / 4))
  (a at (sample / 2))
}
flow h_1_n1(x: F32 at (sample * 2)) -> F32 at (sample / 2) {
  1.0
}
flow h_1_n2(x: F32 at (sample * 2)) -> F32 at (sample / 4) {
  1.0
}
flow h_1_2_s1(x: F32 at (sample * 2), c: F32 at block) -> F32 at (sample * 4) {
  let a = prev~(c at (sample / 2))
  [x[0] + (a at sample), x[0] + (a at sample), x[0] + (a at sample), x[0] + (a at sample)]
}
flow h_1_2_s2(x: F32 at (sample * 2), c: F32 at block) -> F32 at (sample * 4) {
  let a = prev~(c at (sample / 4))
  [x[0] + (a at sample), x[0] + (a at sample), x[0] + (a at sample), x[0] + (a at sample)]
}
flow h_2_0_s1(x: F32 at (sample * 4), c: F32 at block) -> F32 at sample {
  let a = prev~(c at (sample / 2))
  x[0] + (a at sample)
}
flow h_2_0_s2(x: F32 at (sample * 4), c: F32 at block) -> F32 at sample {
  let a = prev~(c at (sample / 4))
  x[0] + (a at sample)
}
flow h_2_0(x: F32 at (sample * 4)) -> F32 at sample {
  x[0]
}
flow h_2_1_s1(x: F32 at (sample * 4), c: F32 at block) -> F32 at (sample * 2) {
  let a = prev~(c at (sample / 2))
  [x[0] + (a at sample), x[0] + (a at sample)]
}
flow h_2_1_s2(x: F32 at (sample * 4), c: F32 at block) -> F32 at (sample * 2) {
  let a = prev~(c at (sample / 4))
  [x[0] + (a at sample), x[0] + (a at sample)]
}
flow h_p_n1_s2(c: F32 at block) -> F32 at (sample / 2) {
  let a = prev~(c at (sample / 4))
  (a at (sample / 2))
}
flow h_p_n2_s1(c: F32 at block) -> F32 at (sample / 4) {
  let _ = prev~(c at (sample / 2))
  1.0
}
flow h_p_2_s1(c: F32 at block) -> F32 at (sample * 4) {
  let a = prev~(c at (sample / 2))
  [(a at sample), (a at sample), (a at sample), (a at sample)]
}
flow h_p_2_s2(c: F32 at block) -> F32 at (sample * 4) {
  let a = prev~(c at (sample / 4))
  [(a at sample), (a at sample), (a at sample), (a at sample)]
}
flow h_p_2() -> F32 at (sample * 4) {
  [1.0, 1.0, 1.0, 1.0]
}
flow h_p_3_s2(c: F32 at block) -> F32 at (sample * 8) {
  let a = prev~(c at (sample / 4))
  [(a at sample), (a at sample), (a at sample), (a at sample), (a at sample), (a at sample), (a at sample), (a at sample)]
}
";

/// The rows of the model of the review of U6b ([`the_table_of_the_model_of_the_review_of_u6b`]):
/// the flow, its source, its table drawn.
const U6B_ROWS: &[(&str, &str, &str)] = &[
    (
        "ch00",
        "pub flow ch00(x: F32 at (sample / 8)) -> F32 at (sample / 4) { h_n2_n1~(x).up~(2).down~(4).down~(4).up~(4) }",
        "-3: Each(3,once)[-5: Each(0,once)[-2: R(-2,-)]] | -2*: Each(3,once)[-4: Each(0,j)[-1: R(-1,V); 0: R(0,-)]]   read=Run",
    ),
    (
        "ch01",
        "pub flow ch01(x: F32 at (sample / 4)) -> F32 at (sample / 2) { h_1_2_s2~(x, 1.0).up~(2).down~(4).down~(2).down~(2) }",
        "-5: Each(0,once)[-2: R(-2,-)] | -4: Each(0,j)[0: R(0,D(1))] | -2: G(1,0,arg), Deal(2<-1)   read=Array(2)",
    ),
    (
        "ch02",
        "pub flow ch02(x: F32 at (sample / 8)) -> F32 at (sample / 8) { h_n1_n1_s2~(x, 1.0).up~(2).up~(2).down~(4).down~(4) }",
        "-4: Each(1,j)[-1: Each(0,once)[-2: R(-2,-)]; 0: Each(0,j)[-1: R(-1,D(2)); 0: R(0,-)]] | -3: G(2,0,arg)   read=Array(2)",
    ),
    (
        "ch03",
        "pub flow ch03(x: F32 at (sample / 8)) -> F32 at (sample / 4) { h_n1_0_s1~(x, 1.0).down~(4).up~(4).down~(4) }",
        "-3: Each(1,once)[-3: R(-1,-)] | -2*: Each(1,j)[-2: R(0,V)]   read=Run",
    ),
    (
        "ch04",
        "pub flow ch04(x: F32 at (sample / 2)) -> F32 at sample { r3~(h_n2_2~(x).down~(2).up~(2).up~(2)) }",
        "-1: Each(2,once)[-2: Each(1,once)[-3: R(-2,-)]] | 0*: Each(2,j)[0: Each(1,j)[-1: R(0,D(0)), Deal(V<-0@0)]]   read=Run",
    ),
    (
        "ch05",
        "pub flow ch05() -> F32 at sample { r1~(h_p_2_s2~(1.0).down~(2).down~(4).up~(4)) }",
        "-3: Each(2,once)[-5: R(-2,-)] | -1: Each(2,once)[-3: R(0,D(0))] | 0*: Each(2,j)[-2: Deal(1<-0)]   read=Array(1)",
    ),
    (
        "ch06",
        "pub flow ch06(x: F32 at sample) -> F32 at (sample / 4) { h_2_0_s1~(x, 1.0).down~(4).up~(2).down~(2) }",
        "-3: Each(1,once)[-3: R(-1,-)] | -2*: Each(1,once)[-2: R(0,V)] | -1: Each(1,j)[0: G(0,0,ring2)] | 0: G(2,0,arg)   read=Run",
    ),
    (
        "ch07",
        "pub flow ch07(x: F32 at (sample / 8)) -> F32 at (sample / 16) { h_2_1_s2~(x, 1.0).down~(2).down~(4).down~(2).down~(2) }",
        "-7: R(-2,-) | -5: R(0,D(0)) | -4: G(0,0,ring1) | -3: G(1,0,arg)   read=Array(0)",
    ),
    (
        "ch08",
        "pub flow ch08(x: F32 at sample) -> F32 at sample { r1~(h_2_1_s1~(b2~(x), 1.0).down~(2).up~(4).down~(2)) }",
        "-1: Each(1,j)[-2: R(-1,-); -1: R(0,D(0)), Deal(2<-0@0); 0: G(0,0,ring2)] | 0: G(2,0,arg)   read=Array(2)",
    ),
    (
        "ch09",
        "pub flow ch09(x: F32 at (sample / 4)) -> F32 at sample { h_0_2_s2~(x, 1.0).down~(2).up~(4).down~(4).down~(2) }",
        "-4: Each(1,once)[-3: R(-2,-)] | -3: Each(1,j)[-1: R(0,D(0)), Deal(2<-0@0)] | -2: G(2,0,arg) | -1: Deal(3<-2)   read=Array(3)",
    ),
    (
        "ch10",
        "pub flow ch10(x: F32 at sample) -> F32 at sample { r2~(h_1_2_s1~(b1~(x), 1.0).down~(2).up~(2).up~(4).down~(4)) }",
        "-2: Each(2,j)[-1: Each(1,once)[-2: R(-1,-)]; 0: Each(1,j)[-1: R(0,D(0)), Deal(3<-0@0); 0: G(0,0,ring3)]] | 0: G(3,0,arg)   read=Array(3)",
    ),
    (
        "ch11",
        "pub flow ch11(x: F32 at sample) -> F32 at sample { r2~(h_1_2_s1~(b1~(x), 1.0).down~(2).down~(2).up~(4)) }",
        "-1: Each(2,once)[-3: R(-1,-)] | 0*: Each(2,j)[-2: R(0,D(0)); -1: G(0,0,arg), Deal(1<-0), Deal(V<-1@1)]   read=Run",
    ),
    (
        "ch12",
        "pub flow ch12(x: F32 at sample) -> F32 at sample { r2~(h_n1_0_s2~(b1~(x), 1.0).up~(2).down~(2).up~(4)) }",
        "0*: Each(2,j)[-2: Each(0,once)[-2: R(-2,-)]; -1: Each(0,j)[-1: R(-1,-); 0: R(0,D(1))], Deal(V<-1@1)]   read=Run",
    ),
    (
        "ch13",
        "pub flow ch13() -> F32 at sample { r3~(h_p_2~().up~(4).down~(2).down~(2).up~(2)) }",
        "-1: Each(3,once)[-2: Each(0,j)[0: R(0,D(1))]] | 0*: Each(3,j)[-1: Deal(2<-1)]   read=Array(2)",
    ),
    (
        "ch14",
        "pub flow ch14(x: F32 at (sample / 4)) -> F32 at sample { r1~(h_n2_1_s1~(x, 1.0).down~(4).down~(2).up~(4).up~(2)) }",
        "-2: Each(3,once)[-3: Each(2,once)[-5: R(-2,-)]] | -1: Each(3,once)[-2: Each(2,once)[-4: R(-1,-)]] | 0*: Each(3,j)[-1: Each(2,once)[-3: R(0,D(0))]]   read=Array(0)",
    ),
    (
        "ch15",
        "pub flow ch15(x: F32 at (sample / 32)) -> F32 at (sample / 16) { h_n2_n1_s1~(x, 1.0).down~(2).down~(4).up~(4).down~(4) }",
        "-5: Each(2,once)[-5: R(-2,-)] | -4*: Each(2,once)[-4: R(-1,V)] | -3: Each(2,once)[-3: R(0,-)]   read=Run",
    ),
    (
        "ch16",
        "pub flow ch16(x: F32 at (sample / 2)) -> F32 at sample { r2~(h_0_3_s1~(x, 1.0).down~(4).up~(2).up~(2).down~(2)) }",
        "-2: Each(2,once)[-2: Each(1,once)[-3: R(-1,-)]] | -1: Each(2,j)[-1: Each(1,once)[-2: R(0,D(0))]], Deal(3<-0)   read=Array(3)",
    ),
    (
        "ch17",
        "pub flow ch17(x: F32 at (sample / 16)) -> F32 at (sample / 8) { h_n2_n1~(x).down~(2).down~(2).up~(2).down~(2) }",
        "-4: Each(2,once)[-4: R(-2,-)] | -3*: Each(2,once)[-3: R(-1,V)] | -2: Each(2,once)[-2: R(0,-)]   read=Run",
    ),
    (
        "ch18",
        "pub flow ch18(x: F32 at (sample / 16)) -> F32 at (sample / 8) { h_n1_0_s2~(x, 1.0).down~(2).down~(4) }",
        "-5: R(-2,-) | -4: R(-1,-) | -3*: R(0,V)   read=Run",
    ),
    (
        "ch19",
        "pub flow ch19() -> F32 at (sample / 16) { h_p_n2_s1~(1.0).down~(4).down~(2).down~(2).up~(4) }",
        "-4*: Each(3,once)[-6: R(-2,V)] | -3: Each(3,once)[-5: R(-1,-)] | -2: Each(3,once)[-4: R(0,-)]   read=Run",
    ),
    (
        "ch20",
        "pub flow ch20(x: F32 at (sample / 4)) -> F32 at sample { h_n2_0~(x).down~(4).up~(4).up~(4).down~(4) }",
        "-2: Each(2,j)[-2: Each(1,once)[-4: R(-2,-)]; 0: Each(1,j)[-2: R(0,D(3))]]   read=Array(3)",
    ),
    (
        "ch21",
        "pub flow ch21(x: F32 at (sample / 8)) -> F32 at (sample / 32) { h_1_n1~(x).down~(4).down~(4).down~(4).up~(4) }",
        "-5*: Each(3,once)[-7: R(-1,V)] | -4: Each(3,once)[-6: R(0,-)] | -3: Each(3,once)[-5: G(0,0,arg)]   read=Run",
    ),
    (
        "ch22",
        "pub flow ch22(x: F32 at (sample / 2)) -> F32 at (sample / 8) { h_1_n1_s2~(x, 1.0).down~(2).up~(2).down~(4) }",
        "-4: Each(1,once)[-3: R(-2,-)] | -3*: Each(1,once)[-2: R(-1,V)] | -2: Each(1,j)[-1: R(0,-); 0: G(0,0,ring2)] | -1: G(2,0,arg)   read=Run",
    ),
    (
        "ch23",
        "pub flow ch23() -> F32 at (sample / 4) { h_p_3_s2~(1.0).down~(2).down~(2).down~(4).down~(2) }",
        "-7: R(-2,-) | -5: R(0,D(0)) | -4: Deal(1<-0) | -3: Deal(2<-1)   read=Array(2)",
    ),
    (
        "ch24",
        "pub flow ch24() -> F32 at (sample / 2) { h_p_2_s1~(1.0).down~(2).down~(4).down~(2).up~(2) }",
        "-4: Each(3,once)[-5: R(-1,-)] | -3: Each(3,once)[-4: R(0,D(0))] | -2: Each(3,once)[-3: Deal(1<-0)]   read=Array(1)",
    ),
    (
        "ch25",
        "pub flow ch25(x: F32 at sample) -> F32 at (sample / 2) { h_2_0_s2~(b1~(x), 1.0).down~(2).down~(2).up~(2) }",
        "-3: Each(2,once)[-4: R(-2,-)] | -1*: Each(2,once)[-2: R(0,V)] | 0: Each(2,j)[-1: G(0,0,ring1); 0: G(1,0,arg)]   read=Run",
    ),
    (
        "ch26",
        "pub flow ch26(x: F32 at sample) -> F32 at sample { r3~(h_n2_n1~(b2~(x)).up~(4).up~(2).up~(4).down~(2)) }",
        "-1: Each(2,j)[0: Each(1,j)[0: Each(0,j)[-2: R(-2,-); -1: R(-1,D(3)); 0: R(0,-)]]] | 0: G(3,0,arg)   read=Array(3)",
    ),
    (
        "ch27",
        "pub flow ch27(x: F32 at (sample / 2)) -> F32 at sample { r2~(h_n2_1~(x).up~(4).up~(4).down~(4).down~(2)) }",
        "-3: Each(1,j)[0: Each(0,j)[-2: R(-2,-); 0: R(0,D(2))]] | -1: G(2,0,arg), Deal(3<-2)   read=Array(3)",
    ),
    (
        "ch28",
        "pub flow ch28(x: F32 at (sample / 32)) -> F32 at (sample / 4) { h_n1_2_s1~(x, 1.0).down~(2).down~(4).down~(2) }",
        "-5: R(-1,-) | -4: R(0,D(0)) | -3: Deal(1<-0)   read=Array(1)",
    ),
    (
        "ch29",
        "pub flow ch29() -> F32 at (sample / 32) { h_p_n1_s2~(1.0).down~(4).down~(2).up~(2).down~(4) }",
        "-6: Each(2,once)[-5: R(-2,-)] | -5*: Each(2,once)[-4: R(-1,V)] | -4: Each(2,once)[-3: R(0,-)]   read=Run",
    ),
    (
        "ch30",
        "pub flow ch30(x: F32 at (sample / 2)) -> F32 at (sample / 8) { h_2_0~(x).down~(2).down~(4).up~(2).down~(2) }",
        "-3*: Each(2,once)[-3: R(0,V)] | -2: Each(2,once)[-2: G(0,0,ring1)] | -1: Each(2,j)[-1: G(1,0,arg)]   read=Run",
    ),
    (
        "ch31",
        "pub flow ch31(x: F32 at (sample / 4)) -> F32 at (sample / 32) { h_1_n2~(x).down~(2).down~(2).down~(2) }",
        "-5*: R(-2,V) | -3: R(0,-) | -2: G(0,0,arg)   read=Run",
    ),
    (
        "ch32",
        "pub flow ch32(x: F32 at (sample / 16)) -> F32 at (sample / 16) { h_n2_n2~(x).down~(2).up~(2).down~(4) }",
        "-4*: Each(1,once)[-3: R(-2,V)] | -2: Each(1,j)[-1: R(0,-)]   read=Run",
    ),
    (
        "ch33",
        "pub flow ch33(x: F32 at sample) -> F32 at sample { r3~(h_n2_0_s2~(b1~(x), 1.0).up~(4).up~(4).down~(2)) }",
        "-1: Each(1,j)[0: Each(0,j)[-2: R(-2,-); 0: R(0,D(2))]] | 0: G(2,0,arg)   read=Array(2)",
    ),
];

/// The stage `s` as the memo of U6b0 writes it: the exponent of a tick.
fn st(s: crate::clock::ClockStage) -> String {
    match s {
        crate::clock::ClockStage::Tick(k) => k.0.to_string(),
        s => format!("{s:?}"),
    }
}

/// The ops `ops` drawn ([`steps_of_a_chain`]).
fn drawn_ops(ops: &[super::Op]) -> String {
    use super::{CondRead, Feed, Op, Out, To};
    let out = |out: &Out| match out {
        Out::None => "-".to_string(),
        Out::Value => "V".to_string(),
        Out::Deal(b) => format!("D({b})"),
        Out::Held(g) => format!("H({g})"),
    };
    let op = |op: &Op| match op {
        Op::Run { body, out: o } => format!("R({},{})", st(*body), out(o)),
        // A guard: `r` reads its condition, `l` as read before it, `k` as kept; `@y` its
        // stage driven by its count, `+` the count after it.
        Op::When { guard, cond, due, ops, advance } => {
            let cond = match cond {
                CondRead::Read => "r",
                CondRead::Local => "l",
                CondRead::Kept => "k",
            };
            let due = due.map_or(String::new(), |y| format!("@{}", st(y)));
            format!("W({guard},{cond}{due}{})[{}]", if *advance { "+" } else { "" }, drawn_ops(ops))
        }
        Op::Hold { guard, out: o } => format!("Hold({guard},{})", out(o)),
        Op::Reset { at } => format!("Reset({at})"),
        Op::Ring { bound, port, from } => {
            let port = match port {
                super::Port::Input(i) => i.to_string(),
                super::Port::Cond(at) => format!("c{at}"),
            };
            let from = match from {
                Feed::Arg => "arg".to_string(),
                Feed::Ring(r) => format!("ring{r}"),
            };
            format!("G({bound},{port},{from})")
        }
        // `@by` of a copy in the window of `by` not that of its array (§11.9: the narrower).
        Op::Deal { to, from, by } => match to {
            To::Array(b) if *b == *by => format!("Deal({b}<-{from})"),
            To::Array(b) => format!("Deal({b}<-{from}@{by})"),
            To::Value => format!("Deal(V<-{from}@{by})"),
            To::Held(g) => format!("Deal(H({g})<-{from}@{by})"),
        },
        Op::Each { bound, once, groups } => {
            let groups: Vec<_> = groups.iter().map(|(y, ops)| format!("{}: {}", st(*y), drawn_ops(ops))).collect();
            format!("Each({bound},{})[{}]", if *once { "once" } else { "j" }, groups.join("; "))
        }
    };
    ops.iter().map(op).collect::<Vec<_>>().join(", ")
}

/// The index of the input `port` of a head (none of these chains gathers a
/// condition).
fn input(port: super::Port) -> u32 {
    match port {
        super::Port::Input(i) => i,
        super::Port::Cond(at) => panic!("a ring of the condition at {at}"),
    }
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
    use super::{Op, Out, Read, To};
    let makes = |e: &super::Entry| {
        let mut makes = e.read;
        Op::walk(&e.ops, &mut |op| {
            makes |= match (n.read, op) {
                (Read::Array(b), Op::Run { out: Out::Deal(d), .. } | Op::Deal { to: To::Array(d), .. }) => b == *d,
                _ => false,
            }
        });
        makes
    };
    n.entries.iter().find(|e| makes(e)).map(|e| e.caller).unwrap_or_else(|| panic!("{}: nothing makes it", n.path))
}

/// A flow with a port at `sample / N` is known by its `derived_port` (no
/// `process`, the review's M3 of W7-16 U5b2), one at `sample * N` too, and
/// not a caller of one.
#[test]
fn a_port_of_a_derived_clock_is_known() {
    let src = "pub flow f(p: F32 at block, x: F32 at (sample * 2)) -> F32 at sample {\n  x[0] * p\n}\n\
               pub flow g(x: F32 at sample) -> F32 at (sample * 2) {\n  [x, x]\n}\n\
               pub flow h(x: F32 at sample) -> F32 at sample {\n  x\n}\n\
               pub flow sl(x: F32 at (sample / 4)) -> F32 at (sample / 4) {\n  x\n}\n\
               pub flow k(p: F32 at block) -> F32 at sample {\n  sl~(p at (sample / 4)) at sample\n}\n\
               pub flow m(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  f~(p, g~(x))\n}\n";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let port = |name: &str| flow(&a, name).derived_port.map(|s| &src[s.start as usize..s.end as usize]);
    assert_eq!([port("sl"), port("h"), port("k")], [Some("x: F32 at (sample / 4)"), None, None]);
}

/// Each modifier of a chain has its receiver (§11.9), of nested `.down~`
/// too.
#[test]
fn each_modifier_of_a_chain_has_its_receiver() {
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
    let down = flow(&a, "down");
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

/// The slower ticks of one flow and `sample_tick()` (W7-16 U5a): a flow
/// with a `let`, a node and a hoisted field at `sample / 4` or `sample / 2`
/// and one that reads `sample_tick()`,
/// whose ticks are slowest first and whose state has the counter of the
/// phase after `_sample_rate` (S-1179 (2)); and an instance of a flow that
/// counts the time, whose stages and time its caller gives (W7-16 U5b2).
#[test]
fn the_slower_ticks_of_one_flow_and_an_instance_of_one() {
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

/// The table of a chain with `.when~` (§11.10, S-1209, W7-10 U1), each row
/// worked out by hand from the arm of the memo of W7-10 (3.2, 3.5) with the
/// tags of the high 1 of its review and its middle 1 (`target/notes/179/
/// w710/decided.md`), not of the output of the implementation: W the
/// `sample` of the frame with a stage of the head slower (`xh` has one at
/// `sample / 2`), W slower than the frame (the read, the slower stage moved
/// to it under the count, the count at the `sample` of the frame under the
/// condition kept), both orders with `.down~`, a converter flow (its
/// `sample` guarded by the condition kept), `.up~` inside and outside, two
/// guards, a burst held, the array of a boundary dealt inside it and the
/// array read outside it held. Each guard then the fields its table reads,
/// in the order of the chain, inner first (S-1208, S-1220 provisional).
#[test]
fn the_table_of_a_chain_with_when() {
    let src = "flow cnt() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}
flow xh(a: F32 at sample) -> F32 at sample {
  let h = cnt~().down~(2)
  a + (h at sample)
}
flow last4(x: F32 at (sample * 4)) -> F32 at sample { x[3] }
flow dws4(x: F32 at sample) -> F32 at (sample / 4) { last4~(x).down~(4) }
flow dup2(x: F32 at sample) -> F32 at (sample * 2) { [x, x] }
flow r0(x: F32 at (sample * 2)) -> F32 at sample { x[0] }
flow mk4(p: F32 at block) -> F32 at (sample * 4) { [p, p, p, p] }
flow pick0(x: F32 at (sample * 4)) -> F32 at sample { x[0] }
pub flow w0(x: F32 at sample, c: Bool at sample) -> F32 at sample { xh~(x).when~(c) }
pub flow w1(x: F32 at sample, c: Bool at block) -> F32 at sample { xh~(dws4~(x)).down~(4).when~(c) at sample }
pub flow w2(x: F32 at sample, c: Bool at block) -> F32 at sample { xh~(dws4~(x)).when~(c).down~(4) at sample }
pub flow w3(x: F32 at sample, c: Bool at block) -> F32 at sample { dws4~(x).when~(c) at sample }
pub flow w4(x: F32 at sample, c: Bool at sample) -> F32 at sample { r0~(xh~(dup2~(x)).when~(c).up~(2)) }
pub flow w5(x: F32 at sample, c: Bool at sample) -> F32 at sample { r0~(xh~(dup2~(x)).up~(2).when~(c)) }
pub flow w6(x: F32 at sample, a: Bool at block, b: Bool at block) -> F32 at sample {
  xh~(dws4~(x)).when~(a).down~(4).when~(b) at sample
}
pub flow w7(p: F32 at block, c: Bool at sample) -> F32 at sample { pick0~(mk4~(p).when~(c)) }
pub flow w8(p: F32 at block, c: Bool at block) -> F32 at sample { mk4~(p).when~(c).down~(4) }
pub flow w9(p: F32 at block, c: Bool at sample) -> F32 at sample { mk4~(p).down~(4).when~(c) }
flow mk2() -> F32 at (sample * 2) { [cnt~(), 0.0] }
pub flow w10(c: Bool at init) -> F32 at sample { pick0~(mk2~().down~(2).when~(c).up~(2).up~(2)) }
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let rows = [
        ("w0", "0*: W(0,r)[], W(0,l@-1)[R(-1,-)], W(0,l+)[R(0,H(0))], Hold(0,V)   read=Run", "._tick_0 .held"),
        (
            "w1",
            "-2*: W(0,r)[], W(0,l@-3)[R(-1,-)], W(0,l)[R(0,H(0))], Hold(0,V) | 0: W(0,k+)[]   read=Run",
            "._on_0 ._tick_0 .held",
        ),
        ("w2", "-2*: W(0,r)[], W(0,l@-1)[R(-1,-)], W(0,l+)[R(0,H(0))], Hold(0,V)   read=Run", "._tick_0 .held"),
        ("w3", "-2*: W(0,r)[R(-2,H(0))], Hold(0,V) | 0: W(0,k)[R(0,-)]   read=Run", "._on_0 .held"),
        (
            "w4",
            "0*: Each(0,j)[0: W(0,r)[], W(0,l@-1)[R(-1,-)], W(0,l+)[R(0,H(0))], Hold(0,V)]   read=Run",
            "._tick_0 .held",
        ),
        ("w5", "0*: W(0,r)[Each(0,j)[-1: R(-1,-); 0: R(0,V)]], Hold(0,V)   read=Run", ".held"),
        (
            "w6",
            "-2*: W(1,r)[W(0,r)[], W(0,l@-1)[R(-1,-)], W(0,l+)[R(0,H(0))], Hold(0,H(1))], Hold(1,V)   read=Run",
            "._tick_0 ._held_0 .held",
        ),
        ("w7", "0*: W(0,r)[R(0,V)], Hold(0,V)   read=Run", ".held"),
        ("w8", "-2: W(0,r)[R(0,D(0))], Hold(0,D(0))   read=Array(0)", ".held ._deal_0"),
        (
            "w9",
            "0*: W(0,r)[], W(0,l@-2)[R(0,D(0))], W(0,l+)[Deal(H(0)<-0@1)], Hold(0,V)   read=Run",
            "._deal_0 ._tick_0 .held",
        ),
        // The two `.up~` widen the window of the array dealt, but the `when~` holds the value
        // in its own frame: no copy of the whole array past it (W7-10 U1e).
        (
            "w10",
            "0*: Each(2,j)[0: Each(1,j)[0: W(0,r)[], W(0,l@-1)[R(0,D(0))], W(0,l+)[Deal(H(0)<-0@1)], Hold(0,V)]]   read=Run",
            "._deal_0 ._tick_0 .held",
        ),
    ];
    for (name, want, fields) in rows {
        let f = flow(&a, name);
        let id = f.nodes.iter().position(|n| !n.guards.is_empty()).unwrap_or_else(|| panic!("{name}: no guard"));
        let n = &f.nodes[id];
        assert_eq!(drawn(n), want, "{name}");
        let own = |x: &&super::Field| matches!(x.of, super::FieldOf::Node(k, p) if k.0 as usize == id && p != super::Part::Own);
        let got: Vec<_> = f.fields.iter().filter(own).map(|x| x.name.trim_start_matches(n.path.as_str())).collect();
        assert_eq!(got.join(" "), fields, "{name}");
    }
}

/// The table of a chain whose head is a built-in delay (§11.10, W7-10 U3b):
/// the head is its one stage K (P = W = the clock of its first argument), its
/// run the read of its value, and the arms of `.when~` and `.reset_if~` are
/// those of an instance; worked out by hand from the memo of W7-10 U3 (3.3,
/// 3.5) and S-1228 (the reset first in the stage of its tick). A delay a
/// guard stops has the field `_ran` after those of its guards (S-1220
/// provisional); one with a `.reset_if~` alone has none.
#[test]
fn the_table_of_a_chain_of_a_delay() {
    let src = "flow cnt() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}
pub flow d0(x: F32 at sample, c: Bool at sample) -> F32 at sample { prev~(x).when~(c) }
pub flow d1(x: F32 at sample, r: Bool at sample) -> F32 at sample { delay~(x, 2).reset_if~(r) }
pub flow d2(x: F32 at sample) -> F32 at sample {
  let k = cnt~().down~(4)
  prev~(x).reset_if~(k == 2.0)
}
pub flow d3(x: F32 at sample, c: Bool at sample, r: Bool at sample) -> F32 at sample { prev~(x).when~(c).reset_if~(r) }
pub flow d4(x: F32 at sample, c: Bool at sample, r: Bool at sample) -> F32 at sample { prev~(x).reset_if~(r).when~(c) }
pub flow d5(x: F32 at sample) -> F32 at sample {
  let l = cnt~().down~(4)
  let q = cnt~().down~(16)
  let v = prev~(l).reset_if~(q == 2.0).when~(l != 3.0)
  v at sample
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let rows = [
        ("d0", "0*: W(0,r)[R(0,H(0))], Hold(0,V)   read=Run", ".held ._ran"),
        ("d1", "0*: Reset(0), R(0,V)   read=Run", ".buf .w"),
        ("d2", "-2: Reset(0) | 0*: R(0,V)   read=Run", ""),
        ("d3", "0*: Reset(1), W(0,r)[R(0,H(0))], Hold(0,V)   read=Run", ".held ._ran"),
        ("d4", "0*: W(0,r)[Reset(0), R(0,H(0))], Hold(0,V)   read=Run", ".held ._ran"),
        (
            "d5",
            "-2*: W(0,r)[], W(0,l@-4)[Reset(0)], W(0,l)[R(-2,H(0))], Hold(0,V) | 0: W(0,k+)[]   read=Run",
            "._on_0 ._tick_0 .held ._ran",
        ),
    ];
    for (name, want, fields) in rows {
        let f = flow(&a, name);
        let id = f.nodes.iter().position(|n| !n.chain.is_empty() && n.kind.delay().is_some());
        let id = id.unwrap_or_else(|| panic!("{name}: no chain of a delay"));
        let n = &f.nodes[id];
        assert_eq!(drawn(n), want, "{name}");
        let own = |x: &&super::Field| matches!(x.of, super::FieldOf::Node(k, p) if k.0 as usize == id && p != super::Part::Own);
        let got: Vec<_> = f.fields.iter().filter(own).map(|x| x.name.trim_start_matches(n.path.as_str())).collect();
        assert_eq!(got.join(" "), fields, "{name}");
    }
}

/// The table of a chain with `.reset_if~` around a `.when~` that moves a
/// stage slower than the tick R of its condition to its W (§11.10, S-1209,
/// S-1228): the reset first in the stage R, before all the work of the part
/// there, the slower stages the guard runs in its W too (outside the run of
/// an `.up~`, before a guard outside, two `.reset_if~`s); worked out from
/// the rule of S-1228, the work of a guard being the work of its W. No
/// field of a `.reset_if~` (the flag of W7-10 U2b is gone).
#[test]
fn the_table_of_a_reset_if_around_a_when() {
    let src = "flow cnt() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}
flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}
flow slot4(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(4)
  (s at sample) + cnt~()
}
flow slot8(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(8)
  (s at sample) + cnt~()
}
flow g2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] }
pub flow r1(p: Bool at block, c: Bool at sample) -> F32 at sample { slot4~(1.0).when~(c).reset_if~(p at (sample / 2)) }
pub flow r2(p: Bool at block, c: Bool at sample) -> F32 at sample {
  g2~(slot8~(1.0).when~(c).up~(2).reset_if~(p at (sample / 2)))
}
pub flow r3(p: Bool at block, q: Bool at block, c: Bool at sample) -> F32 at sample {
  slot4~(1.0).when~(c).reset_if~(p at (sample / 2)).when~(q)
}
pub flow r4(c: Bool at sample, r: Bool at sample) -> F32 at sample { cnt~().when~(c).reset_if~(r) }
pub flow r5(p: Bool at block, q: Bool at block, c: Bool at sample) -> F32 at sample {
  slot8~(1.0).when~(c).reset_if~(p at (sample / 4)).when~(q).reset_if~(p at (sample / 2))
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let rows = [
        (
            "r1",
            "-1: Reset(1) | 0*: W(0,r)[], W(0,l@-2)[R(-2,-)], W(0,l+)[R(0,H(0))], Hold(0,V)   read=Run",
            "._tick_0 .held",
        ),
        (
            "r2",
            "-1: Reset(2) | 0*: Each(0,j)[0: W(0,r)[], W(0,l@-3)[R(-3,-)], W(0,l+)[R(0,H(0))], Hold(0,V)]   read=Run",
            "._tick_0 .held",
        ),
        (
            "r3",
            "0*: W(1,r)[], W(1,l@-1)[Reset(1)], W(1,l+)[W(0,r)[], W(0,l@-2)[R(-2,-)], W(0,l+)[R(0,H(0))], Hold(0,H(1))], Hold(1,V)   read=Run",
            "._tick_0 ._held_0 ._tick_1 .held",
        ),
        ("r4", "0*: Reset(1), W(0,r)[R(0,H(0))], Hold(0,V)   read=Run", ".held"),
        (
            "r5",
            "-1: Reset(3) | 0*: W(1,r)[], W(1,l@-2)[Reset(1)], W(1,l+)[W(0,r)[], W(0,l@-3)[R(-3,-)], W(0,l+)[R(0,H(0))], Hold(0,H(1))], Hold(1,V)   read=Run",
            "._tick_0 ._held_0 ._tick_1 .held",
        ),
    ];
    for (name, want, fields) in rows {
        let f = flow(&a, name);
        let id = f.nodes.iter().position(|n| !n.guards.is_empty()).unwrap_or_else(|| panic!("{name}: no guard"));
        let n = &f.nodes[id];
        assert_eq!(drawn(n), want, "{name}");
        let own = |x: &&super::Field| matches!(x.of, super::FieldOf::Node(k, p) if k.0 as usize == id && p != super::Part::Own);
        let got: Vec<_> = f.fields.iter().filter(own).map(|x| x.name.trim_start_matches(n.path.as_str())).collect();
        assert_eq!(got.join(" "), fields, "{name}");
    }
}

/// Of chains whose conditions are gathered in a block, read at its runs or
/// at a stage of their own (§11.10, the memo of W7-10 U3, 2.6; the break
/// side of U2a): each condition is read where the table lowers it. Its
/// [`super::ArgRead`] (the stage the marking evaluates its expression at) is
/// the stage of the entry of the op that lowers that expression: the ring
/// written from it, else the read of its guard or its reset.
#[test]
fn a_condition_is_read_at_the_stage_of_the_op_that_lowers_it() {
    let heads = "flow cnt() -> F32 at sample {\n  let n = prev~(^n) + 1.0\n  n\n}
flow acc(f: F32 at block) -> F32 at sample {\n  let n = f + prev~(^n)\n  n\n}
flow slot2(f: F32 at block) -> F32 at sample {\n  let s = acc~(f).down~(2)\n  (s at sample) + cnt~()\n}
flow mk4() -> F32 at (sample * 4) {\n  let n = cnt~()\n  [n, n, n, n]\n}
flow g2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] }
flow pk2(x: Bool at (sample * 2)) -> Bool at sample { x[1] }
flow h2(c: Bool at sample) -> Bool at (sample / 2) { pk2~(c).down~(2) }
";
    let chains = [
        "cnt~().when~(c).up~(2).down~(2)",
        "cnt~().when~(p).up~(2).down~(2)",
        "cnt~().when~(h2~(c)).up~(2).down~(2)",
        "cnt~().when~(h2~(c)).up~(4).down~(4)",
        "g2~(cnt~().when~(c).up~(4).down~(2))",
        "cnt~().reset_if~(p).up~(2).down~(2)",
        "cnt~().reset_if~(r).up~(2).down~(2)",
        "cnt~().reset_if~(h2~(r)).up~(2).down~(2)",
        "cnt~().reset_if~(p at (sample / 2)).up~(2).down~(2)",
        "cnt~().when~(c).up~(2).down~(2).reset_if~(r)",
        "cnt~().when~(sample_tick() % 3 == 0).up~(2).down~(2)",
        "cnt~().when~(c).up~(2).down~(2).when~(c)",
        "cnt~().when~(c).up~(2).up~(2).down~(2).down~(2)",
        "cnt~().when~(c).up~(2).down~(2).up~(2).down~(2)",
        "slot2~(1.0).when~(c).up~(2).down~(2).when~(h2~(c)).reset_if~(p at (sample / 2))",
        "g2~(slot2~(1.0).reset_if~(r).when~(c).up~(4).down~(2).when~(c))",
        "g2~(mk4~().down~(2).when~(c).up~(4).down~(4))",
        "cnt~().up~(2).reset_if~(h2~(r)).down~(2)",
        "cnt~().up~(2).when~(h2~(c)).down~(2)",
        "cnt~().when~(p at sample).up~(2).down~(2)",
        "cnt~().reset_if~(p at sample).up~(2).down~(2)",
        "cnt~().reset_if~(p at (sample / 2)).up~(4).down~(4)",
    ];
    let mut src = heads.to_string();
    for (k, ch) in chains.iter().enumerate() {
        src += &format!(
            "pub flow t{k}(p: Bool at block, c: Bool at sample, r: Bool at sample) -> F32 at sample {{ {ch} }}\n"
        );
    }
    let a = check(&src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let mut seen = (0, 0);
    for (k, chain) in chains.iter().enumerate() {
        let f = flow(&a, &format!("t{k}"));
        let n = f.nodes.iter().find(|n| n.chain.len() > 1).unwrap_or_else(|| panic!("t{k}: no chain"));
        let frame = |place: u32| n.inside(place) as usize;
        let ringed = |place: u32| n.ring_of(frame(place), super::Port::Cond(place)).is_some();
        let read_at = |place: u32| {
            let cond = n.chain[place as usize].cond.expect("a condition");
            let r = n.args.iter().find(|r| r.expr == cond).expect("a read of the condition");
            r.stage.or(r.at.stage()).map(|s| f.run_stage(s))
        };
        for e in &n.entries {
            super::Op::walk(&e.ops, &mut |op| {
                let place = match *op {
                    super::Op::Ring { port: super::Port::Cond(at), from: super::Feed::Arg, .. } => {
                        seen.0 += 1;
                        Some(at)
                    }
                    super::Op::When { guard, cond: super::CondRead::Read, .. } => Some(n.guards[guard as usize].at),
                    super::Op::Reset { at } => Some(at),
                    _ => None,
                }
                .filter(|&at| matches!(op, super::Op::Ring { .. }) || !ringed(at));
                if let Some(at) = place {
                    assert_eq!(read_at(at), Some(e.caller), "t{k} `{chain}` at {at}");
                    seen.1 += 1;
                }
            });
        }
    }
    assert!(seen.0 > 10 && seen.1 > seen.0, "{seen:?}");
}

/// §11.3: a value of the parameter kinds alone `at` a tick (through a `let`
/// too) is not gathered into a ring in a block, as with no `at`; a signal
/// is (the review of W7-10 U3a, its 1b).
#[test]
fn a_condition_of_the_parameter_kinds_at_a_tick_has_no_port() {
    let src = "flow cnt() -> F32 at sample {\n  let n = prev~(^n) + 1.0\n  n\n}
pub flow t(p: Bool at block, q: Bool at block, c: Bool at sample) -> F32 at sample {
  let b = p at sample
  let x = cnt~().when~(p at sample).up~(2).down~(2)
  let y = cnt~().reset_if~(p at (sample / 2)).up~(4).down~(4)
  let z = cnt~().when~(b).reset_if~((p && q) at sample).up~(2).down~(2)
  let s = cnt~().when~(c && (p at sample)).up~(2).down~(2)
  x + y + z + s
}
";
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = flow(&a, "t");
    let ports: Vec<Vec<bool>> = f
        .nodes
        .iter()
        .filter(|n| n.chain.len() > 1)
        .map(|n| n.chain.iter().filter(|m| m.cond.is_some()).map(|m| m.port.is_some()).collect())
        .collect();
    assert_eq!(ports, [vec![false], vec![false], vec![false, false], vec![true]]);
}
