//! `onsa graph` (T3-12; spec §18.2, `spec/tools.md` §1): the signal graph of
//! a flow as DOT, in two steps: the drawing ([`Drawing`]: the vertices, the
//! frames of the `par~`s and the edges), made of the plan of the flow, then
//! its text ([`Drawing::dot`]).
//! - Vertices: the inputs, the top-level `let`s (by their scopes, §11.6),
//!   the output, the stateful nodes that are not the whole value of a `let`
//!   (by their §11.6 paths), and the index of each `par~` (§1.3).
//! - Frames: one of each `par~`, holding its index and the nodes of its body
//!   (with the frames of the `par~`s in it).
//! - Edges: the edges of the plan ([`FlowInfo::edges`]), the look-back ones
//!   (`prev~` / `delay~` / `vdelay~`, `^y`) dashed.
//!
//! A label is `name: type at clock` (no clock for a constant), and clocks
//! colour the vertices (§1.1). No cycle of solid edges (§1.2):
//! [`Drawing::solid_cycle`] finds one, and the cases check it of every flow
//! ([`check_graphs`]).

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use onsa_diag::Span;
use onsa_diag::internal::bug;
use onsa_sema::body::LocalId;
use onsa_sema::clock::Clock;
use onsa_sema::def::{DefKind, FlowDef};
use onsa_sema::flow::{FlowInfo, NodeId, Owner, PlanKind, PlanNode, Vertex};
use onsa_sema::flow_names::{OUTPUT_SCOPE, qualify};
use onsa_sema::{Analysis, DefId};
use onsa_syntax::ast::{Ast, ExprId, RangeEnd};

use crate::Analyzed;

struct Edge {
    from: String,
    to: String,
    dashed: bool,
}

/// The drawing of a flow while it is made, of its plan.
struct Graph<'a> {
    a: &'a Analysis,
    ast: &'a Ast,
    info: &'a FlowInfo,
    /// Local → vertex (an input, a local of a `let`, the index of a `par~`);
    /// a binding of an arm has none.
    local_node: HashMap<LocalId, String>,
    /// The vertex of each `let`.
    let_names: Vec<String>,
    d: Drawing,
    seen: HashSet<(String, String, bool)>,
}

impl Graph<'_> {
    fn edge(&mut self, from: &str, to: &str, dashed: bool) {
        if self.seen.insert((from.into(), to.into(), dashed)) {
            self.d.edges.push(Edge { from: from.into(), to: to.into(), dashed });
        }
    }

    fn rate_of(&self, e: ExprId) -> Clock {
        self.info.clocks.exprs.get(&e).copied().unwrap_or(Clock::SAMPLE)
    }

    fn ty_of(&self, e: ExprId) -> String {
        self.info.body.expr_types.get(&e).map(|&t| self.a.display_type(t)).unwrap_or_else(|| "?".into())
    }

    /// The vertex `v` is drawn as: a node of the whole value of a `let` is
    /// the `let`'s (they have one name); none of a binding of an arm.
    fn vertex(&self, v: Vertex) -> Option<String> {
        match v {
            Vertex::Local(l) => self.local_node.get(&l).cloned(),
            Vertex::Node(id) => Some(self.info.node(id).path.clone()),
            Vertex::Let(k) => match self.let_names.get(k as usize) {
                Some(name) => Some(name.clone()),
                None => onsa_diag::internal::bug(None, "an edge of a `let` the flow has not"),
            },
            Vertex::Output => Some(OUTPUT_SCOPE.to_string()),
        }
    }

    /// The edges of the plan as edges of the graph, in their order.
    fn copy_edges(&mut self) {
        for e in &self.info.edges {
            // A binding of an arm has no vertex (none in spec/tools.md §1.1).
            let Some(from) = self.vertex(e.from) else { continue };
            let Some(to) = self.vertex(e.to) else { onsa_diag::internal::bug(None, "an edge read by a local") };
            self.edge(&from, &to, e.lookback);
        }
    }

    /// The clock of the local `l` in the plan, at `span`.
    fn clock_of(&self, l: LocalId, span: Span) -> Clock {
        match self.info.clocks.locals.get(&l) {
            Some(&c) => c,
            None => bug(Some(span), "a local with no clock in the plan"),
        }
    }

    fn push(&mut self, name: String, label: String, shape: &'static str, (clock, at): (Clock, Span)) -> Item {
        self.d.vertices.push(Vert { name, label, shape, color: rate_color(clock, at) });
        Item::Vertex(self.d.vertices.len() - 1)
    }

    fn inputs(&mut self, flow: &FlowDef) -> Vec<Item> {
        let info = self.info;
        if info.inputs.len() != flow.inputs.len() {
            bug(Some(self.ast.expr(flow.body).span), "a plan with other inputs than its flow")
        }
        let mut items = Vec::new();
        // SPEC-GAP(S-1256): a vertex by the name of the input, so two inputs
        // `_` are one vertex (provisional: as it is).
        for (&l, input) in info.inputs.iter().zip(&flow.inputs) {
            let name = info.body.locals[l.0 as usize].name.clone();
            self.local_node.insert(l, name.clone());
            // As the declaration writes it (§1.1): the clock of a caller, not the body's view of it.
            let rate = input.caller_clock();
            let label = format!("{name}: {}", typed(&self.a.display_type(input.ty), rate, input.span));
            items.push(self.push(name, label, "shape=ellipse ", (rate, input.span)));
        }
        items
    }

    /// The `let`s, each a vertex of its scope (§11.6): its name.
    // SPEC-GAP(S-1169): a `let` of a pattern is the vertex of its first
    // name, and one that binds none `_<m>`, as its nodes are qualified.
    fn lets(&mut self) -> Vec<Item> {
        let info = self.info;
        self.let_names = info.let_scopes();
        let mut items = Vec::new();
        for (i, l) in info.lets.iter().enumerate() {
            let name = self.let_names[i].clone();
            for &loc in &l.locals {
                self.local_node.insert(loc, name.clone());
            }
            let label = match info.whole(i as u32).map(|id| info.node(id)) {
                // Its node has its name (S-148).
                Some(node) => self.node_label(node, l.init),
                None => format!("{name}: {}", typed(&self.a.display_type(l.ty), l.clock, l.span)),
            };
            items.push(self.push(name, label, "", (l.clock, l.span)));
        }
        items
    }

    /// The output: the vertex of a name no input, `let` or node has (R-497).
    fn output(&mut self, flow: &FlowDef) -> Option<Item> {
        let o = self.info.output?;
        let (rate, at) = (self.rate_of(o), self.ast.expr(o).span);
        // Of a derived clock (§11.9) or an event (§11.11), as the declaration writes the port: not the body's view of it.
        let (ty, rate) = if flow.out_clock.of_ratio() || flow.out_clock.is_event() {
            (self.a.display_type(flow.out), flow.out_clock)
        } else {
            (self.ty_of(o), rate)
        };
        let label = format!("out: {}", typed(&ty, rate, at));
        Some(self.push(OUTPUT_SCOPE.to_string(), label, "shape=doubleoctagon ", (rate, at)))
    }

    /// The vertex of the node `id`, but of the whole value of a `let` (it
    /// is the `let`'s), and the frame of a `par~`.
    fn node(&mut self, id: NodeId) -> Vec<Item> {
        let node = self.info.node(id);
        let mut items = Vec::new();
        if !node.whole {
            let (label, at) = (self.node_label(node, node.expr), (self.rate_of(node.expr), node.span));
            items.push(self.push(node.path.clone(), label, "style=rounded ", at));
        }
        if let PlanKind::Par { .. } = node.kind {
            items.push(self.frame(id));
        }
        items
    }

    /// The frame of the `par~` `id` (§1.3): the heading of its range, its
    /// index as an input of its clock (`init`), and the nodes of its body.
    // SPEC-GAP(S-1176): the vertex of a `par~` in the body is in the frame,
    // beside its own frame; that of a `par~` in no body is in none.
    fn frame(&mut self, id: NodeId) -> Item {
        let info = self.info;
        let node = info.node(id);
        let PlanKind::Par { var, count, children, .. } = &node.kind else {
            bug(Some(node.span), "a frame of no `par~`")
        };
        let local = &info.body.locals[var.0 as usize];
        let name = index_name(info, id, &local.name);
        self.local_node.insert(*var, name.clone());
        let clock = self.clock_of(*var, local.span);
        let label = format!("{}: {}", local.name, typed(&self.a.display_type(local.ty), clock, local.span));
        let heading = format!("{} {} in {}（×{count}）", spelling(self.ast, node.expr), local.name, range(node));
        let mut items = vec![self.push(name, label, "shape=ellipse ", (clock, local.span))];
        for &child in children {
            items.extend(self.node(child));
        }
        self.d.frames.push(Frame { path: node.path.clone(), heading, items });
        Item::Frame(self.d.frames.len() - 1)
    }

    fn node_label(&self, node: &PlanNode, e: ExprId) -> String {
        // `prev_0 = prev~`, `src = saw~`: the name without its scope
        // (spec/tools.md §1.1).
        // SPEC-GAP(S-1084): with the modifiers of its chain, the N as a
        // value (`lp~.down~(4)`, `prev~.when~(…)`), of the plan (provisional (2)).
        let chain = node.chain.iter().map(|m| match m.ratio.and_then(|r| r.n()) {
            Some(n) => format!(".{}~({n})", m.modifier.name()),
            None => format!(".{}~(…)", m.modifier.name()),
        });
        let chain: String = chain.collect();
        let what = match (&node.kind, node.kind.delay()) {
            // A delay is its kind, with no length (§1.1).
            (_, Some(d)) => format!("{}~{chain}", d.name()),
            (PlanKind::Instance { callee, .. }, None) => format!("{}~{chain}", self.a.def(*callee).name),
            // SPEC-GAP(S-1170): as written and with its range, as the heading
            // of its frame.
            (PlanKind::Par { .. }, None) => format!("{} {}", spelling(self.ast, node.expr), range(node)),
            // `PlanKind::delay` names every delay.
            (PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. }, None) => {
                onsa_diag::internal::bug(None, "a delay node without its delay")
            }
        };
        format!("{} = {what}: {}", node.name, typed(&self.ty_of(e), self.rate_of(e), self.ast.expr(e).span))
    }
}

/// The vertex of the index `var` of the `par~` `id` (§1.3): `<path>.<var>`
/// (`saws.i`), unless a node of its body has that name.
// SPEC-GAP(S-1168): then `<path>._<var>`, of the form no user writes (`_`
// first, §2.3, §11.6), which no node of the body has (`<kind>_<n>`).
fn index_name(info: &FlowInfo, id: NodeId, var: &str) -> String {
    let node = info.node(id);
    let name = qualify(&node.path, var);
    let children = info.roots(Owner::Par(id));
    match children.iter().any(|&c| info.node(c).path == name) {
        true => qualify(&node.path, &format!("_{var}")),
        false => name,
    }
}

/// The replication `e` as written (spec/tools.md §1.3): `par` or `par~`.
fn spelling(ast: &Ast, e: ExprId) -> &'static str {
    match ast.expr(e).kind {
        onsa_syntax::ast::ExprKind::Par { tilde: Some(_), .. } => "par~",
        _ => "par",
    }
}

/// The range of the `par~` `node` as written (§11.5): `0..<4`, `1..=3`.
// SPEC-GAP(S-1171): `a..=b` as written, not as `a..<b + 1` (no `U32` holds
// the end past `U32`'s maximum).
fn range(node: &PlanNode) -> String {
    let PlanKind::Par { from, count, end, .. } = node.kind else { bug(Some(node.span), "a range of no `par~`") };
    // One replica or more (§11.5), and the end written is a `U32`.
    let to = match end {
        RangeEnd::Excluded => from.checked_add(count),
        RangeEnd::Included => count.checked_sub(1).and_then(|n| from.checked_add(n)),
    };
    let Some(to) = to else { bug(Some(node.span), "a `par~` whose end is out of `U32`") };
    format!("{from}{}{to}", end.symbol())
}

/// `type at clock`, or the type alone for a constant (§11.3, §1.1); a clock
/// with no text is an internal error at `at`.
fn typed(ty: &str, r: Clock, at: Span) -> String {
    match r {
        Clock::Const => ty.to_string(),
        r => format!("{ty} at {}", r.written(at)),
    }
}

/// The colour of a clock at `at` (§1.1): the stages before `block` gray,
/// `block` blue, `sample` black.
// SPEC-GAP(S-1084): the other ticks, an event and the ambient clock are
// black too.
fn rate_color(r: Clock, at: Span) -> &'static str {
    match r {
        Clock::Const | Clock::Init => "gray40",
        Clock::Block => "blue",
        Clock::Tick(_) | Clock::Event(_) | Clock::Ambient => "black",
        Clock::Error => bug(Some(at), "a vertex of a clock in error"),
    }
}

/// The flows of the user's package, in their order. The package by its
/// place, not its name: a dependency may have the same name (R-88).
pub(crate) fn own_flows(a: &Analysis) -> impl Iterator<Item = DefId> + '_ {
    let own = |d: &onsa_sema::def::Def| matches!(d.kind, DefKind::Flow(_)) && a.modules.is_own(d.module);
    a.defs.iter().enumerate().filter(move |(_, d)| own(d)).map(|(i, _)| DefId(i as u32))
}

/// The flow `name` names in `scope` (§18.2): the module of the file passed,
/// or the whole package (`None`). A name with `.` is a module-qualified one
/// (`dsp.voice`), which must name a flow of `scope`; another name must be
/// one flow's name in `scope`, else the candidates are listed.
// SPEC-GAP(S-658): only the flows a module declares are in its scope: a
// flow the module of the file passed takes in by `use`, and a name that is
// not a flow (a `fn`), are not found (exit 2). A name with no flow in the
// scope lists no candidates, even when other modules have a flow of that name.
fn find_flow(analyzed: &Analyzed, name: &str, scope: Option<&str>) -> Result<DefId, String> {
    let a = &analyzed.analysis;
    let module_of = |id: DefId| a.modules.get(a.def(id).module).path.as_str();
    let mut flows = own_flows(a);
    let place = match scope {
        Some(m) => format!("module `{m}`, the module of the file passed"),
        None => format!("package `{}`", analyzed.pkg.name),
    };
    if name.contains('.') {
        let Some(id) = flows.find(|&id| a.qualified_name(id) == name) else {
            return Err(format!("no flow named `{name}` in package `{}`", analyzed.pkg.name));
        };
        return match scope {
            Some(m) if module_of(id) != m => Err(format!("`{name}` is not in {place}")),
            _ => Ok(id),
        };
    }
    let hits: Vec<DefId> =
        flows.filter(|&id| a.def(id).name == name && scope.is_none_or(|m| module_of(id) == m)).collect();
    match hits.as_slice() {
        [one] => Ok(*one),
        [] => Err(format!("no flow named `{name}` in {place}")),
        many => Err(format!(
            "`{name}` names more than one flow in {place}; use the module path: {}",
            many.iter().map(|&d| a.qualified_name(d)).collect::<Vec<_>>().join(", ")
        )),
    }
}

/// Why `onsa graph` drew nothing.
#[derive(Debug, Clone)]
pub enum GraphError {
    /// No such flow, or it does not check (the command could not work).
    Usage(String),
    Internal(crate::InternalError),
}

/// DOT source of the signal graph of `flow` (a short or module-qualified
/// name) in `scope`: the module of the file passed
/// ([`crate::Loaded::focus_module`]), or the whole package (`None`).
pub fn graph(analyzed: &Analyzed, flow: &str, scope: Option<&str>) -> Result<String, GraphError> {
    crate::guard(|| graph_of(analyzed, flow, scope)).map_err(GraphError::Internal)?
}

fn graph_of(analyzed: &Analyzed, flow: &str, scope: Option<&str>) -> Result<String, GraphError> {
    let id = find_flow(analyzed, flow, scope).map_err(GraphError::Usage)?;
    Ok(draw(analyzed, id).map_err(GraphError::Usage)?.dot())
}

/// The drawing of the flow `id`, which checks.
fn draw(analyzed: &Analyzed, id: DefId) -> Result<Drawing, String> {
    let a = &analyzed.analysis;
    let def = a.def(id);
    let Some(info) = a.flows.get(&id) else {
        return Err(format!("flow `{}` was not checked (it has diagnostics)", def.name));
    };
    if !info.planned() {
        return Err(format!("flow `{}` has diagnostics; fix them first", def.name));
    }
    let Some(module) = a.ast(&analyzed.pkg, def.module) else {
        return Err("flow is not in a source module".into());
    };
    let Some(flow) = def.as_flow() else { bug(Some(def.span), "a flow with no flow definition") };
    let (vertices, frames, top, edges) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let d = Drawing { title: def.name.clone(), vertices, frames, top, edges };
    let (local_node, let_names, seen) = (HashMap::new(), Vec::new(), HashSet::new());
    let mut g = Graph { a, ast: &module.parsed.ast, info, local_node, let_names, d, seen };
    let mut top = g.inputs(flow);
    top.extend(g.lets());
    top.extend(g.output(flow));
    // The nodes in no `par~`, in the order of the table, with their frames.
    for (i, node) in info.nodes.iter().enumerate() {
        if !matches!(node.owner, Owner::Par(_)) {
            top.extend(g.node(NodeId(i as u32)));
        }
    }
    g.copy_edges();
    g.d.top = top;
    Ok(g.d)
}

/// A vertex drawn: its name, its label, its shape (`shape=… ` or
/// `style=… `, empty for a box) and the colour of its clock.
struct Vert {
    name: String,
    label: String,
    shape: &'static str,
    color: &'static str,
}

/// A vertex or a frame, in the order drawn.
#[derive(Clone, Copy)]
enum Item {
    Vertex(usize),
    Frame(usize),
}

/// The frame of a `par~` (a Graphviz cluster, §1.3).
struct Frame {
    /// The path of the `par~` (`saws`, `m.par_0`).
    path: String,
    heading: String,
    items: Vec<Item>,
}

/// The graph of a flow before its text.
pub struct Drawing {
    title: String,
    vertices: Vec<Vert>,
    frames: Vec<Frame>,
    /// The items in no frame, in their order.
    top: Vec<Item>,
    edges: Vec<Edge>,
}

impl Drawing {
    /// The DOT text: the vertices and the frames in their order, then the
    /// edges in theirs.
    pub fn dot(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "digraph \"{}\" {{", self.title);
        let _ = writeln!(out, "  rankdir=LR");
        let _ = writeln!(out, "  node [shape=box fontname=\"monospace\"]");
        self.items(&mut out, &self.top, 1);
        for e in &self.edges {
            let style = if e.dashed { " [style=dashed]" } else { "" };
            let _ = writeln!(out, "  \"{}\" -> \"{}\"{style}", e.from, e.to);
        }
        out.push_str("}\n");
        out
    }

    fn items(&self, out: &mut String, items: &[Item], depth: usize) {
        let pad = "  ".repeat(depth);
        for &item in items {
            match item {
                Item::Vertex(k) => {
                    let Vert { name, label, shape, color } = &self.vertices[k];
                    let _ = writeln!(
                        out,
                        "{pad}\"{name}\" [label=\"{label}\" {shape}color=\"{color}\" fontcolor=\"{color}\"]"
                    );
                }
                Item::Frame(k) => {
                    let Frame { path, heading, items } = &self.frames[k];
                    let _ = writeln!(out, "{pad}subgraph \"cluster_{path}\" {{");
                    let _ = writeln!(out, "{pad}  label=\"{heading}\"");
                    self.items(out, items, depth + 1);
                    let _ = writeln!(out, "{pad}}}");
                }
            }
        }
    }

    /// A cycle of the solid edges, by the names of its vertices from one back
    /// to it, or none (§1.2: a flow has none, §11.2). An iterative
    /// depth-first search that closes each vertex once: O(V + E).
    pub fn solid_cycle(&self) -> Option<Vec<String>> {
        let mut index: HashMap<&str, usize> = HashMap::new();
        let mut next: Vec<Vec<usize>> = Vec::new();
        for e in self.edges.iter().filter(|e| !e.dashed) {
            let [from, to] = [&e.from, &e.to].map(|n| {
                let k = index.len();
                *index.entry(n.as_str()).or_insert(k)
            });
            next.resize(index.len(), Vec::new());
            next[from].push(to);
        }
        let mut names = vec![""; index.len()];
        for (n, k) in index {
            names[k] = n;
        }
        // 0: not met, 1: on the path, 2: closed.
        let mut state = vec![0u8; names.len()];
        for start in 0..names.len() {
            if state[start] != 0 {
                continue;
            }
            state[start] = 1;
            let mut path = vec![(start, 0usize)];
            while let Some(top) = path.last_mut() {
                let (v, k) = *top;
                let Some(&w) = next[v].get(k) else {
                    state[v] = 2;
                    path.pop();
                    continue;
                };
                top.1 += 1;
                match state[w] {
                    0 => {
                        state[w] = 1;
                        path.push((w, 0));
                    }
                    1 => {
                        let Some(from) = path.iter().position(|&(u, _)| u == w) else {
                            bug(None, "a vertex on the path that is not on it")
                        };
                        let cycle = path[from..].iter().map(|&(u, _)| u).chain([w]);
                        return Some(cycle.map(|u| names[u].to_string()).collect());
                    }
                    _ => {}
                }
            }
        }
        None
    }
}

/// What [`check_graphs`] found.
#[derive(Debug, Clone, Default)]
pub struct GraphCheck {
    /// The flows drawn.
    pub flows: usize,
    /// Each flow not drawn, or whose solid edges make a cycle.
    pub problems: Vec<String>,
}

/// Every flow of the user's package whose plan is complete, drawn, and the
/// cycles of its solid edges (§1.2: none): the property the cases check of
/// every flow.
pub fn check_graphs(analyzed: &Analyzed) -> Result<GraphCheck, crate::InternalError> {
    crate::guard(|| {
        let a = &analyzed.analysis;
        let mut check = GraphCheck::default();
        for id in own_flows(a).filter(|id| a.flows.get(id).is_some_and(|f| f.planned())) {
            match draw(analyzed, id).map(|d| d.solid_cycle()) {
                Ok(cycle) => {
                    check.flows += 1;
                    if let Some(c) = cycle {
                        let (name, c) = (a.qualified_name(id), c.join(" -> "));
                        check.problems.push(format!("flow `{name}`: a cycle of solid edges {c}"));
                    }
                }
                Err(e) => check.problems.push(format!("flow `{}`: {e}", a.qualified_name(id))),
            }
        }
        check
    })
}

/// Render DOT to SVG with the `dot` command, if installed.
pub fn to_svg(dot: &str) -> Result<String, String> {
    use std::io::Write as _;
    use std::process::{Command, Stdio};
    let mut child = Command::new("dot")
        .arg("-Tsvg")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run `dot` (install Graphviz): {e}"))?;
    child.stdin.take().expect("stdin").write_all(dot.as_bytes()).map_err(|e| e.to_string())?;
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(format!("`dot` failed: {}", String::from_utf8_lossy(&out.stderr)));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

#[cfg(test)]
mod tests;
