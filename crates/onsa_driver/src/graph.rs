//! `onsa graph` (T3-12; spec §18.2): the signal graph of a flow as DOT.
//! Nodes are the inputs, the top-level `let`s, the stateful nodes that are not
//! a `let` of their own (named per S-06) and the output; edges follow the
//! reads of each initializer. The look-back edges of `prev~` / `delay~` /
//! `vdelay~` are dashed. A label is `name: type at clock` (no clock for a
//! constant), and clocks colour the nodes (`init` and constants gray,
//! `block` blue, `sample` black; `spec/tools.md` §1.1).

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use onsa_diag::Span;
use onsa_sema::body::{LocalId, Target};
use onsa_sema::clock::Clock;
use onsa_sema::def::DefKind;
use onsa_sema::flow::{FlowInfo, PlanKind, PlanNode};
use onsa_sema::{Analysis, DefId};
use onsa_syntax::ast::{Ast, ExprId, ExprKind};

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
    extra: Vec<(String, String, Clock)>,
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

    fn rate_of(&self, e: ExprId) -> Clock {
        self.info.clocks.exprs.get(&e).copied().unwrap_or(Clock::SAMPLE)
    }

    fn ty_of(&self, e: ExprId) -> String {
        self.info.body.expr_types.get(&e).map(|&t| self.a.display_type(t)).unwrap_or_else(|| "?".into())
    }

    /// Reads inside `e` become edges into `target`. A stateful sub-node gets a
    /// node of its own (unless it IS the target's initializer) and its own edges.
    fn visit(&mut self, e: ExprId, target: &str, dashed: bool) {
        // The graph is drawn only for a package without diagnostics (S-59).
        if let ExprKind::Error = self.ast.expr(e).kind {
            onsa_diag::internal::bug(Some(self.ast.expr(e).span), "the graph met a body a syntax error left unread")
        }
        if let Some(&id) = self.info.node_of.get(&e) {
            let node = self.info.node(id);
            let label = self.node_label(node, e);
            self.extra.push((node.name.clone(), label, self.rate_of(e)));
            self.edge(&node.name, target, dashed);
            self.visit_node(node, &node.name);
            return;
        }
        if let Some(Target::Local(l)) = self.info.body.targets.get(&e)
            && let Some(from) = self.local_node.get(l).cloned()
        {
            self.edge(&from, target, dashed);
            return;
        }
        for child in self.ast.sub_exprs(e) {
            self.visit(child, target, dashed);
        }
    }

    /// The arguments of a stateful node: look-backs dashed, the rest solid
    /// ([`onsa_sema::flow::ArgRead::lookback`]); the body of a `par~`.
    fn visit_node(&mut self, node: &PlanNode, name: &str) {
        for r in &node.args {
            self.visit(r.expr, name, r.lookback);
        }
        if let PlanKind::Par { var, body, .. } = &node.kind {
            self.local_node.insert(*var, name.to_string());
            self.visit(*body, name, false);
        }
    }

    fn node_label(&self, node: &PlanNode, e: ExprId) -> String {
        // `prev_0 = prev~`, `src = saw~` (spec/tools.md §1.1).
        let what = match (&node.kind, node.kind.delay()) {
            (_, Some(d)) => format!("{}~", d.name()),
            (PlanKind::Instance { callee, .. }, None) => format!("{}~", self.a.def(*callee).name),
            (PlanKind::Par { from, to, .. }, None) => format!("par~ {from}..<{to}"),
            // `PlanKind::delay` names every delay.
            (PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. }, None) => {
                onsa_diag::internal::bug(None, "a delay node without its delay")
            }
        };
        format!("{} = {what}: {}", node.name, typed(&self.ty_of(e), self.rate_of(e), self.ast.expr(e).span))
    }
}

/// `type at clock`, or the type alone for a constant (§11.3); a clock with
/// no text is an internal error at `at`.
fn typed(ty: &str, r: Clock, at: Span) -> String {
    match r {
        Clock::Const => ty.to_string(),
        r => format!("{ty} at {}", r.shown(at)),
    }
}

/// The color of a clock (W7-15 redraws them): the stages before `block`
/// gray, `block` blue, the others black.
fn rate_color(r: Clock) -> &'static str {
    match r {
        Clock::Const | Clock::Init => "gray40",
        Clock::Block => "blue",
        _ => "black",
    }
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
    // The user's package by its place, not its name: a dependency may have the same name (R-88).
    let module_of = |id: DefId| a.modules.get(a.def(id).module).path.as_str();
    let mut flows = a
        .defs
        .iter()
        .enumerate()
        .filter(|(_, d)| matches!(d.kind, DefKind::Flow(_)) && a.modules.is_own(d.module))
        .map(|(i, _)| DefId(i as u32));
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
    crate::guard(|| graph_of(analyzed, flow, scope)).map_err(GraphError::Internal)?.map_err(GraphError::Usage)
}

fn graph_of(analyzed: &Analyzed, flow: &str, scope: Option<&str>) -> Result<String, String> {
    let a = &analyzed.analysis;
    let def_id = find_flow(analyzed, flow, scope)?;
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
        let rate = input.clock;
        let _ = writeln!(
            out,
            "  \"{name}\" [label=\"{name}: {}\" shape=ellipse color=\"{}\" fontcolor=\"{}\"]",
            typed(&a.display_type(input.ty), rate, input.span),
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
        let whole = info.node_of.get(&l.init).map(|&id| info.node(id));
        let label = match whole {
            Some(node) => g.node_label(node, l.init).replacen(&format!("{} =", node.name), &format!("{name} ="), 1),
            None => format!("{name}: {}", typed(&a.display_type(l.ty), l.clock, l.span)),
        };
        let _ = writeln!(
            out,
            "  \"{name}\" [label=\"{label}\" color=\"{}\" fontcolor=\"{}\"]",
            rate_color(l.clock),
            rate_color(l.clock)
        );
        match whole {
            Some(node) => g.visit_node(node, name),
            None => g.visit(l.init, name, false),
        }
    }
    // Output.
    if let Some(o) = info.output {
        let rate = g.rate_of(o);
        let _ = writeln!(
            out,
            "  \"out\" [label=\"out: {}\" shape=doubleoctagon color=\"{}\" fontcolor=\"{}\"]",
            typed(&g.ty_of(o), rate, ast.expr(o).span),
            rate_color(rate),
            rate_color(rate)
        );
        g.visit(o, "out", false);
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
    use crate::{Analyzed, Loaded, ManifestForm, ManifestSource, PackageInput, SourceFile};

    const RESONATOR: &str = "use std.math.{exp, cos}\n\
pub flow resonator(x: F32 at sample, fc: F32 at block, bw: F32 at block) -> F32 at sample {\n\
  let r  = exp(-(F32.PI * bw) / sample_rate())\n\
  let w  = (2.0 * F32.PI * fc) / sample_rate()\n\
  let b1 = 2.0 * r * cos(w)\n\
  let b2 = r * r\n\
  let y1 = prev~(^y)\n\
  let y2 = prev~(y1)\n\
  let y  = ((1.0 - r) * x) + (b1 * y1) - (b2 * y2)\n\
  y\n\
}\n";

    /// The analysis of `input`, which checks.
    fn analyzed(input: PackageInput) -> Analyzed {
        let mut loaded = Loaded::from_input(input).expect("the input loads");
        let analyzed = crate::analyze_loaded(&mut loaded).expect("no internal error");
        assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
        analyzed
    }

    /// A package `name` of the files `files` (path, text).
    fn package(name: &str, files: &[(&str, &str)]) -> PackageInput {
        let text = format!("[package]\nname = \"{name}\"\nedition = \"2026\"\n");
        PackageInput {
            manifest: Some(ManifestSource { path: "onsa.toml".into(), text, form: ManifestForm::File }),
            files: files
                .iter()
                .map(|(path, text)| SourceFile { path: path.to_string(), text: text.to_string() })
                .collect(),
            ..PackageInput::default()
        }
    }

    #[test]
    fn resonator_graph() {
        let analyzed = analyzed(PackageInput::single_file("res.onsa", RESONATOR));
        let dot = super::graph(&analyzed, "resonator", None).unwrap();
        let node_lines = dot.lines().filter(|l| l.contains("[label=")).count();
        // 3 inputs + 7 lets + out
        assert_eq!(node_lines, 11, "{dot}");
        let dashed: Vec<&str> = dot.lines().filter(|l| l.contains("style=dashed")).collect();
        assert_eq!(dashed, vec!["  \"y\" -> \"y1\" [style=dashed]", "  \"y1\" -> \"y2\" [style=dashed]"], "{dot}");
        assert!(dot.contains("\"r\" [label=\"r: F32 at block\" color=\"blue\""), "{dot}");
        assert!(dot.contains("\"y1\" [label=\"y1 = prev~: F32 at sample\""), "{dot}");
        assert!(dot.contains("  \"x\" -> \"y\"\n"), "{dot}");
        assert!(dot.contains("  \"y\" -> \"out\"\n"), "{dot}");
    }

    /// The node of a `par~` names the replication with its `~` and its range,
    /// as an instance names its flow (`saw~`, spec/tools.md §1.1, S-745).
    #[test]
    fn a_par_node_is_labelled_with_its_tilde() {
        let src = "pub flow f(x: F32 at sample) -> [F32; 2] at sample {\n  let xs = par~ i in 0 ..< 2 { x }\n  xs\n}\n";
        let analyzed = analyzed(PackageInput::single_file("p.onsa", src));
        let dot = super::graph(&analyzed, "f", None).unwrap();
        assert!(dot.contains("[label=\"xs = par~ 0..<2: [F32; 2] at sample\""), "{dot}");
    }

    /// §18.2 (S-323): a name is the one flow of that name in the scope (the
    /// module of the file passed, or the package), else the candidates are
    /// listed; a module-qualified name must be in the scope.
    #[test]
    fn the_flow_is_named_in_its_scope() {
        let analyzed = analyzed(package("p", &[("a.onsa", RESONATOR), ("b.onsa", RESONATOR)]));
        let usage = |flow: &str, scope: Option<&str>| match super::graph(&analyzed, flow, scope) {
            Err(super::GraphError::Usage(e)) => e,
            other => panic!("{flow} in {scope:?}: {other:?}"),
        };
        let many = usage("resonator", None);
        assert!(many.contains("a.resonator, b.resonator"), "{many}");
        for (flow, scope) in [("resonator", Some("a")), ("a.resonator", None), ("a.resonator", Some("a"))] {
            assert!(super::graph(&analyzed, flow, scope).is_ok(), "{flow} in {scope:?}");
        }
        assert!(usage("b.resonator", Some("a")).contains("not in module `a`"));
        assert!(usage("lowpass", Some("a")).contains("no flow named `lowpass` in module `a`"));
        assert!(usage("c.resonator", None).contains("no flow named `c.resonator`"));
    }
}
