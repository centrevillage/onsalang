//! `onsa graph` (T3-12; spec §18.2): the signal graph of a flow as DOT.
//! Nodes are the inputs, the top-level `let`s, the stateful nodes that are not
//! a `let` of their own (named per S-06) and the output; edges follow the
//! reads of each initializer. The look-back edges of `prev` / `delay` /
//! `vdelay` are dashed. Rates colour the nodes (`Init` gray, `Ctl` blue,
//! `Sig` black).

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use onsa_sema::body::{LocalId, Target};
use onsa_sema::def::DefKind;
use onsa_sema::flow::{FlowInfo, FlowRate, InitArg, Node};
use onsa_sema::{Analysis, DefId};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, StmtKind};

use crate::Analyzed;

struct Edge {
    from: String,
    to: String,
    dashed: bool,
}

struct Graph<'a> {
    a: &'a Analysis,
    ast: &'a Ast,
    info: &'a FlowInfo,
    /// Local → node name (inputs, `let`s, `par` variables).
    local_node: HashMap<LocalId, String>,
    /// Extra nodes (stateful nodes that are not a `let`): name, label, rate.
    extra: Vec<(String, String, FlowRate)>,
    edges: Vec<Edge>,
    seen: HashSet<(String, String, bool)>,
}

impl Graph<'_> {
    fn edge(&mut self, from: &str, to: &str, dashed: bool) {
        if from == to && !dashed {
            return;
        }
        if self.seen.insert((from.into(), to.into(), dashed)) {
            self.edges.push(Edge { from: from.into(), to: to.into(), dashed });
        }
    }

    fn rate_of(&self, e: ExprId) -> FlowRate {
        self.info.expr_rates.get(&e).copied().unwrap_or(FlowRate::Sig)
    }

    fn ty_of(&self, e: ExprId) -> String {
        self.info.body.expr_types.get(&e).map(|&t| self.a.display_type(t)).unwrap_or_else(|| "?".into())
    }

    /// Reads inside `e` become edges into `target`. A stateful sub-node gets a
    /// node of its own (unless it IS the target's initializer) and its own edges.
    fn visit(&mut self, e: ExprId, target: &str, dashed: bool, nodes: &[Node]) {
        if let Some(&idx) = self.info.node_of_expr.get(&e)
            && let Some(node) = nodes.get(idx)
            && node.expr() == e
        {
            let name = node.name().to_string();
            let label = self.node_label(node, e);
            self.extra.push((name.clone(), label, self.rate_of(e)));
            self.edge(&name, target, dashed);
            self.visit_node(node, &name, nodes);
            return;
        }
        if let Some(Target::Local(l)) = self.info.body.targets.get(&e)
            && let Some(from) = self.local_node.get(l).cloned()
        {
            self.edge(&from, target, dashed);
            return;
        }
        for child in children(self.ast, e) {
            self.visit(child, target, dashed, nodes);
        }
    }

    /// The arguments of a stateful node: look-backs dashed, the rest solid.
    fn visit_node(&mut self, node: &Node, name: &str, nodes: &[Node]) {
        match node {
            Node::Prev { arg, init, .. } | Node::Delay { arg, init, .. } => {
                self.visit(*arg, name, true, nodes);
                if let InitArg::Init(i) = init {
                    self.visit(*i, name, false, nodes);
                }
            }
            Node::Vdelay { arg, d, init, .. } => {
                self.visit(*arg, name, true, nodes);
                self.visit(*d, name, false, nodes);
                if let InitArg::Init(i) = init {
                    self.visit(*i, name, false, nodes);
                }
            }
            Node::Instance { args, .. } => {
                for &arg in args {
                    self.visit(arg, name, false, nodes);
                }
            }
            Node::Par { var, body, nodes: inner, .. } => {
                self.local_node.insert(*var, name.to_string());
                let inner_nodes: Vec<Node> = inner.clone();
                self.visit(*body, name, false, &inner_nodes);
            }
        }
    }

    fn node_label(&self, node: &Node, e: ExprId) -> String {
        let what = match node {
            Node::Prev { .. } => "prev".to_string(),
            Node::Delay { n, .. } => format!("delay({n})"),
            Node::Vdelay { max, .. } => format!("vdelay({max})"),
            Node::Instance { callee, .. } => format!("{}~", self.a.def(*callee).name),
            Node::Par { from, to, .. } => format!("par {from}..{to}"),
        };
        format!("{} = {what}: {} @{}", node.name(), self.ty_of(e), rate_name(self.rate_of(e)))
    }
}

fn rate_name(r: FlowRate) -> &'static str {
    match r {
        FlowRate::Const => "const",
        FlowRate::Init => "Init",
        FlowRate::Ctl => "Ctl",
        FlowRate::Sig => "Sig",
    }
}

fn rate_color(r: FlowRate) -> &'static str {
    match r {
        FlowRate::Const | FlowRate::Init => "gray40",
        FlowRate::Ctl => "blue",
        FlowRate::Sig => "black",
    }
}

/// Direct sub-expressions of `e` (statements of blocks included).
fn children(ast: &Ast, e: ExprId) -> Vec<ExprId> {
    let mut out = Vec::new();
    match &ast.expr(e).kind {
        ExprKind::Lit(_) | ExprKind::Path(_) | ExprKind::Hole => {}
        ExprKind::Paren(x)
        | ExprKind::Unary { expr: x, .. }
        | ExprKind::Cast { expr: x, .. }
        | ExprKind::Try(x)
        | ExprKind::Move(x)
        | ExprKind::Field { base: x, .. }
        | ExprKind::TupleIndex { base: x, .. }
        | ExprKind::Unsafe(x) => out.push(*x),
        ExprKind::Tuple(xs) | ExprKind::Array(xs) => out.extend(xs.iter().copied()),
        ExprKind::Repeat { elem, len } => out.extend([*elem, *len]),
        ExprKind::Struct { fields, .. } => out.extend(fields.iter().map(|(_, x)| *x)),
        ExprKind::Block(b) => {
            for &s in &b.stmts {
                match &ast.stmt(s).kind {
                    StmtKind::Let { init, .. } | StmtKind::Var { init, .. } => out.push(*init),
                    StmtKind::Assign { target, value } => out.extend([*target, *value]),
                    StmtKind::For { iter, body, .. } => out.extend([*iter, *body]),
                    StmtKind::While { cond, body } => out.extend([*cond, *body]),
                    StmtKind::Return(Some(x)) | StmtKind::Assert(x) | StmtKind::Expr(x) => out.push(*x),
                    StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue => {}
                }
            }
            out.extend(b.tail);
        }
        ExprKind::If { cond, then, else_ } => {
            out.extend([*cond, *then]);
            out.extend(*else_);
        }
        ExprKind::Match { scrutinee, arms } => {
            out.push(*scrutinee);
            for arm in arms {
                out.extend(arm.guard);
                out.push(arm.body);
            }
        }
        ExprKind::Closure { body, .. } | ExprKind::Handle { body, .. } => out.push(*body),
        ExprKind::Par { from, to, body, .. } => out.extend([*from, *to, *body]),
        ExprKind::Binary { operands, .. } => out.extend(operands.iter().copied()),
        ExprKind::Call { callee, args, .. } => {
            out.push(*callee);
            out.extend(args.iter().map(|a| a.expr));
        }
        ExprKind::Index { base, index } => out.extend([*base, *index]),
        ExprKind::Range { lo, hi } => out.extend([*lo, *hi]),
    }
    out
}

fn find_flow(analyzed: &Analyzed, name: &str) -> Result<DefId, String> {
    let a = &analyzed.analysis;
    let user_pkg = a.modules.names.iter().position(|n| *n == analyzed.pkg.name);
    let mut hits: Vec<DefId> = a
        .defs
        .iter()
        .enumerate()
        .filter(|(_, d)| matches!(d.kind, DefKind::Flow(_)))
        .filter(|(_, d)| user_pkg.is_none_or(|p| a.modules.pkg_of(d.module) == p))
        .map(|(i, _)| DefId(i as u32))
        .filter(|&id| a.def(id).name == name || a.qualified_name(id) == name)
        .collect();
    hits.sort();
    hits.dedup();
    match hits.as_slice() {
        [one] => Ok(*one),
        [] => Err(format!("no flow named `{name}` in package `{}`", analyzed.pkg.name)),
        many => Err(format!(
            "`{name}` is ambiguous; use the module path: {}",
            many.iter().map(|&d| a.qualified_name(d)).collect::<Vec<_>>().join(", ")
        )),
    }
}

/// DOT source of the signal graph of `flow` (a short or module-qualified name).
pub fn graph(analyzed: &Analyzed, flow: &str) -> Result<String, String> {
    let a = &analyzed.analysis;
    let def_id = find_flow(analyzed, flow)?;
    let def = a.def(def_id);
    let Some(info) = a.flows.get(&def_id) else {
        return Err(format!("flow `{}` was not checked (it has diagnostics)", def.name));
    };
    if !info.complete {
        return Err(format!("flow `{}` has diagnostics; fix them first", def.name));
    }
    let Some(module) = a.ast(&analyzed.pkg, def.module) else {
        return Err("flow is not in a source module".into());
    };
    let ast = &module.parsed.ast;
    let flow_def = def.as_flow().expect("flow");
    let mut g =
        Graph { a, ast, info, local_node: HashMap::new(), extra: Vec::new(), edges: Vec::new(), seen: HashSet::new() };

    let mut out = String::new();
    let _ = writeln!(out, "digraph \"{}\" {{", def.name);
    let _ = writeln!(out, "  rankdir=LR");
    let _ = writeln!(out, "  node [shape=box fontname=\"monospace\"]");

    // Inputs.
    for (i, &l) in info.inputs.iter().enumerate() {
        let name = info.body.locals[l.0 as usize].name.clone();
        g.local_node.insert(l, name.clone());
        let input = &flow_def.inputs[i];
        let rate = FlowRate::from_rate(input.rate);
        let _ = writeln!(
            out,
            "  \"{name}\" [label=\"{name}: {} @{}\" shape=ellipse color=\"{}\" fontcolor=\"{}\"]",
            a.display_type(input.ty),
            rate_name(rate),
            rate_color(rate),
            rate_color(rate)
        );
    }
    // `let` nodes.
    let mut let_names: Vec<String> = Vec::new();
    for (i, l) in info.lets.iter().enumerate() {
        let name = l.name.clone().unwrap_or_else(|| format!("let_{i}"));
        for &loc in &l.locals {
            g.local_node.insert(loc, name.clone());
        }
        let_names.push(name);
    }
    for (i, l) in info.lets.iter().enumerate() {
        let name = &let_names[i];
        let whole = info.node_of_expr.get(&l.init).and_then(|&idx| info.nodes.get(idx)).filter(|n| n.expr() == l.init);
        let label = match whole {
            Some(node) => g.node_label(node, l.init).replacen(&format!("{} =", node.name()), &format!("{name} ="), 1),
            None => format!("{name}: {} @{}", a.display_type(l.ty), rate_name(l.rate)),
        };
        let _ = writeln!(
            out,
            "  \"{name}\" [label=\"{label}\" color=\"{}\" fontcolor=\"{}\"]",
            rate_color(l.rate),
            rate_color(l.rate)
        );
        match whole {
            Some(node) => {
                let node = node.clone();
                g.visit_node(&node, name, &info.nodes);
            }
            None => g.visit(l.init, name, false, &info.nodes),
        }
    }
    // Output.
    if let Some(o) = info.output {
        let rate = g.rate_of(o);
        let _ = writeln!(
            out,
            "  \"out\" [label=\"out: {} @{}\" shape=doubleoctagon color=\"{}\" fontcolor=\"{}\"]",
            g.ty_of(o),
            rate_name(rate),
            rate_color(rate),
            rate_color(rate)
        );
        g.visit(o, "out", false, &info.nodes);
    }
    for (name, label, rate) in &g.extra {
        let _ = writeln!(
            out,
            "  \"{name}\" [label=\"{label}\" style=rounded color=\"{}\" fontcolor=\"{}\"]",
            rate_color(*rate),
            rate_color(*rate)
        );
    }
    for e in &g.edges {
        if e.dashed {
            let _ = writeln!(out, "  \"{}\" -> \"{}\" [style=dashed]", e.from, e.to);
        } else {
            let _ = writeln!(out, "  \"{}\" -> \"{}\"", e.from, e.to);
        }
    }
    out.push_str("}\n");
    Ok(out)
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
mod tests {
    use onsa_diag::SourceMap;

    const RESONATOR: &str = "use std.math.{exp, cos}\n\
pub flow resonator(x: Sig[F32], fc: Ctl[F32], bw: Ctl[F32]) -> Sig[F32] {\n\
  let r  = exp(-(F32.PI * bw) / sample_rate())\n\
  let w  = (2.0 * F32.PI * fc) / sample_rate()\n\
  let b1 = 2.0 * r * cos(w)\n\
  let b2 = r * r\n\
  let y1 = prev(y, 0.0)\n\
  let y2 = prev(y1, 0.0)\n\
  let y  = ((1.0 - r) * x) + (b1 * y1) - (b2 * y2)\n\
  y\n\
}\n";

    #[test]
    fn resonator_graph() {
        let mut sources = SourceMap::default();
        let file = sources.add("res.onsa", RESONATOR);
        let analyzed = crate::analyze_package(&mut sources, "res", &[(file, "res".to_string())]);
        assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&sources, &analyzed.diagnostics));
        let dot = super::graph(&analyzed, "resonator").unwrap();
        let node_lines = dot.lines().filter(|l| l.contains("[label=")).count();
        // 3 inputs + 7 lets + out
        assert_eq!(node_lines, 11, "{dot}");
        let dashed: Vec<&str> = dot.lines().filter(|l| l.contains("style=dashed")).collect();
        assert_eq!(dashed, vec!["  \"y\" -> \"y1\" [style=dashed]", "  \"y1\" -> \"y2\" [style=dashed]"], "{dot}");
        assert!(dot.contains("\"r\" [label=\"r: F32 @Ctl\" color=\"blue\""), "{dot}");
        assert!(dot.contains("\"y1\" [label=\"y1 = prev: F32 @Sig\""), "{dot}");
        assert!(dot.contains("  \"x\" -> \"y\"\n"), "{dot}");
        assert!(dot.contains("  \"y\" -> \"out\"\n"), "{dot}");
    }
}
