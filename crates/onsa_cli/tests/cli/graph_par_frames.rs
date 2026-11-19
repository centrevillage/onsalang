//! `onsa graph` of a `par~`: the frame, the vertex of the index, the edges, and no cycle of the solid edges (spec
//! `spec/tools.md` §1.1, §1.2, §1.3; §11.5, §11.6; R-76; W7-15 U3/t).
//!
//! What the spec fixes, and so what is checked (the text of the DOT is read by a small reader of this file, `Dot`, that
//! knows the clusters, the vertices with their attributes and the edges; no whole text of an output is compared):
//! - §1.3: every `par~` is a Graphviz cluster (`subgraph cluster_…`) whose heading is `par~ <index> in <a>..<<b>（×<N>）`
//!   (`N` is the number of replicas, §11.5) and a `par~` inside a `par~` is a cluster inside the cluster; the cluster of
//!   `let saws = par~ …` is `cluster_saws` (the text of the example of the spec); a flow with no `par~` has no cluster;
//! - §1.3: the index is a vertex inside the frame, named by the name of the `par~` and the index (`saws.i`, for the inner `par~` of
//!   `m` the name of the `par~` is `m.par_0`, so `m.par_0.j`; §11.6), an ellipse of the colour of `init` (gray) with the label
//!   `i: U32 at init`, and the vertices of the body that read the index have an edge from it; the vertices do not collide when
//!   two `par~` have an index of one name;
//! - §1.3: an edge from the result of the body to the vertex of the `par~`; the body does not read the result (no edge back);
//! - §1.2: no cycle of the solid edges (the edges that are not `style=dashed`), for every flow; the look-back of a delay and the
//!   feedback `^y` are dashed edges and the edge to the reader of a delay is the one that is dashed;
//! - §1.1: the labels and the shapes of an input (an ellipse, `x: F32 at sample`), a `let` (a box), a node without a name (rounded,
//!   `lp_0 = lp~: F32 at sample`, the name `_out.lp_0` for the output) and the output (a double octagon, label `out: …`, the name
//!   `_out`); the colour is of the clock (gray `init`, blue `block`, black `sample`).
//!
//! The details that the spec leaves open are checked in the form the work ticket gives them provisionally, each with a mark of the
//! gap (the form of `tools/gap_marks.py`) at the assertion (S-397, S-1084, S-1168, S-1169, S-1170, S-1171, S-1175).
//!
//! Not asked: the order of the statements, the attributes other than `label`, `shape`, `style` and `color` (the font, the rank
//! direction), which vertices of the frame the vertex of the result is in, the name of the cluster of an inner `par~`, the exact
//! name of a colour, and the label of a `let` whose value is not a call (`scaled: F32 at sample`).

use crate::test_support;

use std::collections::BTreeMap;
use std::path::Path;

use test_support::*;

/// The two flows of R-76 (`unison`, `nest`) and the case that holds their golden files.
const FRAMES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/spec/flow/graph_par_frames.onsa");
/// The other flows of these tests (each is for one test; the file is checked as a program).
const LABELS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/spec/flow/graph_labels.onsa");

// ---------------------------------------------------------------------------------------------------------------------
// A small reader of the DOT of `onsa graph`.

#[derive(Debug)]
struct Node {
    id: String,
    attrs: BTreeMap<String, String>,
    /// The innermost frame (a cluster) the statement is in.
    frame: Option<usize>,
}

#[derive(Debug)]
struct Edge {
    from: String,
    to: String,
    attrs: BTreeMap<String, String>,
}

impl Edge {
    fn dashed(&self) -> bool {
        self.attrs.get("style").is_some_and(|s| s.contains("dashed"))
    }
}

#[derive(Debug)]
struct Frame {
    id: String,
    label: Option<String>,
    parent: Option<usize>,
}

#[derive(Debug, PartialEq)]
enum Tok {
    Id(String),
    Arrow,
    Open,
    Close,
    LBracket,
    RBracket,
    Semi,
    Comma,
    Eq,
}

fn tokens(text: &str) -> Vec<Tok> {
    let cs: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '/' && cs.get(i + 1) == Some(&'/') {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if c == '"' {
            i += 1;
            let mut s = String::new();
            while i < cs.len() && cs[i] != '"' {
                if cs[i] == '\\' && cs.get(i + 1) == Some(&'"') {
                    s.push('"');
                    i += 2;
                } else {
                    s.push(cs[i]);
                    i += 1;
                }
            }
            assert!(i < cs.len(), "a string of the DOT is not closed: {text}");
            i += 1;
            out.push(Tok::Id(s));
        } else if c == '-' && cs.get(i + 1) == Some(&'>') {
            out.push(Tok::Arrow);
            i += 2;
        } else if let Some(t) = match c {
            '{' => Some(Tok::Open),
            '}' => Some(Tok::Close),
            '[' => Some(Tok::LBracket),
            ']' => Some(Tok::RBracket),
            ';' => Some(Tok::Semi),
            ',' => Some(Tok::Comma),
            '=' => Some(Tok::Eq),
            _ => None,
        } {
            out.push(t);
            i += 1;
        } else {
            let mut s = String::new();
            while i < cs.len() && !cs[i].is_whitespace() && !"{}[];,=\"".contains(cs[i]) {
                if cs[i] == '-' && cs.get(i + 1) == Some(&'>') {
                    break;
                }
                s.push(cs[i]);
                i += 1;
            }
            out.push(Tok::Id(s));
        }
    }
    out
}

#[derive(Debug, Default)]
struct Dot {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    frames: Vec<Frame>,
}

struct Reader {
    toks: Vec<Tok>,
    pos: usize,
    dot: Dot,
}

impl Reader {
    fn id(&mut self) -> String {
        match self.toks.get(self.pos) {
            Some(Tok::Id(s)) => {
                self.pos += 1;
                s.clone()
            }
            t => panic!("a name was expected at the token {} of the DOT, found {t:?}", self.pos),
        }
    }

    fn eat(&mut self, t: Tok) -> bool {
        if self.toks.get(self.pos) == Some(&t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn attrs(&mut self) -> BTreeMap<String, String> {
        let mut m = BTreeMap::new();
        if !self.eat(Tok::LBracket) {
            return m;
        }
        while !self.eat(Tok::RBracket) {
            if self.eat(Tok::Comma) || self.eat(Tok::Semi) {
                continue;
            }
            let k = self.id();
            let v = if self.eat(Tok::Eq) { self.id() } else { String::new() };
            m.insert(k, v);
        }
        m
    }

    /// The statements up to the closing brace. `enclosing` is the frame the vertices are in, `own` the frame whose
    /// `label=…` the statements of this level are.
    fn stmts(&mut self, enclosing: Option<usize>, own: Option<usize>) {
        loop {
            let Some(t) = self.toks.get(self.pos) else { panic!("the DOT ends before the closing brace") };
            match t {
                Tok::Close => {
                    self.pos += 1;
                    return;
                }
                Tok::Semi => self.pos += 1,
                Tok::Id(w) if w == "subgraph" => {
                    self.pos += 1;
                    let name = if let Some(Tok::Id(n)) = self.toks.get(self.pos) {
                        let n = n.clone();
                        self.pos += 1;
                        Some(n)
                    } else {
                        None
                    };
                    assert!(self.eat(Tok::Open), "`{{` was expected after `subgraph`");
                    match name.filter(|n| n.starts_with("cluster")) {
                        Some(id) => {
                            self.dot.frames.push(Frame { id, label: None, parent: enclosing });
                            let k = self.dot.frames.len() - 1;
                            self.stmts(Some(k), Some(k));
                        }
                        None => self.stmts(enclosing, None),
                    }
                }
                Tok::Id(w)
                    if matches!(w.as_str(), "node" | "edge" | "graph")
                        && self.toks.get(self.pos + 1) == Some(&Tok::LBracket) =>
                {
                    self.pos += 1;
                    self.attrs();
                }
                Tok::Id(_) => {
                    let a = self.id();
                    if self.eat(Tok::Eq) {
                        let v = self.id();
                        if let (Some(k), "label") = (own, a.as_str()) {
                            self.dot.frames[k].label = Some(v);
                        }
                    } else if self.toks.get(self.pos) == Some(&Tok::Arrow) {
                        let mut chain = vec![a];
                        while self.eat(Tok::Arrow) {
                            chain.push(self.id());
                        }
                        let attrs = self.attrs();
                        for w in chain.windows(2) {
                            self.dot.edges.push(Edge { from: w[0].clone(), to: w[1].clone(), attrs: attrs.clone() });
                        }
                    } else {
                        let attrs = self.attrs();
                        self.dot.nodes.push(Node { id: a, attrs, frame: enclosing });
                    }
                }
                t => panic!("a statement was expected at the token {}, found {t:?}", self.pos),
            }
        }
    }
}

impl Dot {
    fn parse(text: &str) -> Dot {
        let mut r = Reader { toks: tokens(text), pos: 0, dot: Dot::default() };
        r.eat_name("strict");
        assert!(r.eat_name("digraph") || r.eat_name("graph"), "no `digraph` in: {text}");
        if let Some(Tok::Id(_)) = r.toks.get(r.pos) {
            r.pos += 1;
        }
        assert!(r.eat(Tok::Open), "`{{` was expected after the head of the graph: {text}");
        r.stmts(None, None);
        r.dot
    }

    fn ids(&self) -> Vec<&str> {
        self.nodes.iter().map(|n| n.id.as_str()).collect()
    }

    fn find(&self, id: &str) -> Option<&Node> {
        self.nodes.iter().find(|n| n.id == id)
    }

    fn node(&self, id: &str) -> &Node {
        self.find(id).unwrap_or_else(|| panic!("no vertex \"{id}\"; the vertices: {:?}", self.ids()))
    }

    fn label(&self, id: &str) -> &str {
        self.node(id).attrs.get("label").unwrap_or_else(|| panic!("the vertex \"{id}\" has no label"))
    }

    fn edge(&self, from: &str, to: &str) -> &Edge {
        self.edges
            .iter()
            .find(|e| e.from == from && e.to == to)
            .unwrap_or_else(|| panic!("no edge \"{from}\" -> \"{to}\"; the edges: {:?}", self.edge_list()))
    }

    fn has_edge(&self, from: &str, to: &str) -> bool {
        self.edges.iter().any(|e| e.from == from && e.to == to)
    }

    fn edge_list(&self) -> Vec<String> {
        self.edges
            .iter()
            .map(|e| format!("{} -> {}{}", e.from, e.to, if e.dashed() { " (dashed)" } else { "" }))
            .collect()
    }

    fn solid(&self, from: &str, to: &str) {
        assert!(!self.edge(from, to).dashed(), "the edge \"{from}\" -> \"{to}\" is solid");
    }

    fn dashed(&self, from: &str, to: &str) {
        assert!(self.edge(from, to).dashed(), "the edge \"{from}\" -> \"{to}\" is dashed");
    }

    /// The frame (cluster) the vertex is in, innermost.
    fn frame_of(&self, id: &str) -> &Frame {
        let k = self.node(id).frame.unwrap_or_else(|| panic!("the vertex \"{id}\" is in no frame"));
        &self.frames[k]
    }

    fn frame_index_of(&self, id: &str) -> usize {
        self.node(id).frame.unwrap_or_else(|| panic!("the vertex \"{id}\" is in no frame"))
    }

    fn frame_with_label(&self, label: &str) -> usize {
        let at: Vec<usize> =
            self.frames.iter().enumerate().filter(|(_, f)| f.label.as_deref() == Some(label)).map(|(k, _)| k).collect();
        assert_eq!(at.len(), 1, "one frame with the heading `{label}`; the frames: {:?}", self.frames);
        at[0]
    }

    /// The vertices that were declared more than once (Graphviz makes them one vertex).
    fn declared_twice(&self) -> Vec<&str> {
        let mut seen = BTreeMap::new();
        for n in &self.nodes {
            *seen.entry(n.id.as_str()).or_insert(0) += 1;
        }
        seen.into_iter().filter(|(_, c)| *c > 1).map(|(id, _)| id).collect()
    }

    /// A cycle of the solid edges (the edges that are not dashed), as the names of its vertices (the first again at the end).
    fn solid_cycle(&self) -> Option<Vec<String>> {
        let mut adj: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for e in self.edges.iter().filter(|e| !e.dashed()) {
            adj.entry(e.from.as_str()).or_default().push(e.to.as_str());
            adj.entry(e.to.as_str()).or_default();
        }
        // 0: not seen, 1: on the path, 2: done.
        let mut state: BTreeMap<&str, u8> = adj.keys().map(|k| (*k, 0)).collect();
        for start in adj.keys().copied() {
            if state[start] != 0 {
                continue;
            }
            state.insert(start, 1);
            let mut stack = vec![(start, 0usize)];
            let mut path = vec![start];
            while let Some(&(n, i)) = stack.last() {
                if let Some(&m) = adj[n].get(i) {
                    stack.last_mut().unwrap().1 += 1;
                    match state[m] {
                        0 => {
                            state.insert(m, 1);
                            stack.push((m, 0));
                            path.push(m);
                        }
                        1 => {
                            let at = path.iter().position(|p| *p == m).unwrap();
                            let mut cycle: Vec<String> = path[at..].iter().map(|s| s.to_string()).collect();
                            cycle.push(m.to_string());
                            return Some(cycle);
                        }
                        _ => {}
                    }
                } else {
                    state.insert(n, 2);
                    stack.pop();
                    path.pop();
                }
            }
        }
        None
    }
}

impl Reader {
    fn eat_name(&mut self, w: &str) -> bool {
        if matches!(self.toks.get(self.pos), Some(Tok::Id(s)) if s == w) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
}

/// `onsa graph <flow> <file>`: the DOT, read.
fn graph_of(file: &str, flow: &str) -> Dot {
    let out = run(Path::new(env!("CARGO_MANIFEST_DIR")), &["graph", flow, file]);
    assert_eq!(out.code, 0, "onsa graph {flow} {file}: {}{}", out.stdout, out.stderr);
    Dot::parse(&out.stdout)
}

fn attr<'a>(n: &'a Node, key: &str) -> Option<&'a str> {
    n.attrs.get(key).map(String::as_str)
}

/// The clock a colour stands for (§1.1: `init` and a constant gray, `block` blue, `sample` black).
fn clock_of_color(n: &Node) -> &'static str {
    // SPEC-GAP(S-1084): the spec names the colours by word (灰色, 青, 黒) and the example of §1.3 writes `gray40`; the test reads any
    // `gray…` or `grey…` as gray, `blue` as blue and `black` as black, and no other colour.
    let c = attr(n, "color").unwrap_or_else(|| panic!("the vertex \"{}\" has no colour: {n:?}", n.id));
    if c.starts_with("gray") || c.starts_with("grey") {
        "init"
    } else if c == "blue" {
        "block"
    } else if c == "black" {
        "sample"
    } else {
        panic!("the colour `{c}` of the vertex \"{}\" is none of gray, blue and black", n.id)
    }
}

fn assert_cycle_free(dot: &Dot, what: &str) {
    if let Some(cycle) = dot.solid_cycle() {
        panic!("{what}: a cycle of solid edges: {}", cycle.join(" -> "));
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// The reader itself: the checks below read through it, so it is checked on a hand-written text (the example of §1.3).

/// The DOT of the example of `spec/tools.md` §1.3, in a graph.
const SPEC_EXAMPLE: &str = r#"digraph "unison" {
subgraph cluster_saws {
  label="par~ i in 0..<4（×4）"
  "saws.i" [label="i: U32 at init" shape=ellipse color="gray40"]
  "saws.saw_0" [label="saw_0 = saw~: F32 at sample" style=rounded]
}
"f0" -> "saws.saw_0"; "detune" -> "saws.saw_0"; "saws.i" -> "saws.saw_0"
"saws.saw_0" -> "saws"; "saws" -> "_out"
}"#;

#[test]
fn the_reader_reads_the_example_of_the_spec() {
    let dot = Dot::parse(SPEC_EXAMPLE);
    assert_eq!(dot.frames.len(), 1);
    assert_eq!(dot.frames[0].id, "cluster_saws");
    assert_eq!(dot.frames[0].label.as_deref(), Some("par~ i in 0..<4（×4）"));
    assert_eq!(dot.label("saws.i"), "i: U32 at init");
    assert_eq!(dot.frame_of("saws.i").id, "cluster_saws");
    assert_eq!(dot.frame_of("saws.saw_0").id, "cluster_saws");
    assert_eq!(attr(dot.node("saws.i"), "shape"), Some("ellipse"));
    assert_eq!(clock_of_color(dot.node("saws.i")), "init");
    assert_eq!(dot.edges.len(), 5, "{:?}", dot.edge_list());
    dot.solid("saws.i", "saws.saw_0");
    dot.solid("saws", "_out");
    assert_cycle_free(&dot, "the example of the spec");
}

#[test]
fn the_cycle_check_finds_a_cycle_and_leaves_the_dashed_edges_out() {
    let text = |extra: &str| format!("digraph \"g\" {{ \"a\" -> \"b\" -> \"c\"\n  \"x\" [label=\"x\"] {extra} }}");
    assert_cycle_free(&Dot::parse(&text("")), "a chain");
    assert_cycle_free(&Dot::parse(&text("\"c\" -> \"a\" [style=dashed]")), "a loop closed by a dashed edge");
    let cycle = Dot::parse(&text("\"c\" -> \"a\"")).solid_cycle().expect("a cycle of three");
    assert_eq!(cycle.len(), 4, "{cycle:?}");
    assert!(Dot::parse(&text("\"c\" -> \"c\"")).solid_cycle().is_some(), "an edge from a vertex to itself is a cycle");
    // A frame in a frame, and a `label` of the graph outside the frames.
    let nested = Dot::parse(
        "digraph g { label=top subgraph cluster_a { label=\"A\" subgraph cluster_b { label=\"B\" \"n\" } \"m\" } \"o\" }",
    );
    assert_eq!(nested.frames.len(), 2);
    assert_eq!(nested.frames[1].parent, Some(0));
    assert_eq!(nested.frames[0].label.as_deref(), Some("A"));
    assert_eq!(nested.frames[1].label.as_deref(), Some("B"));
    assert_eq!(nested.frame_of("n").id, "cluster_b");
    assert_eq!(nested.frame_of("m").id, "cluster_a");
    assert!(nested.node("o").frame.is_none());
}

// ---------------------------------------------------------------------------------------------------------------------
// §1.3: `unison` (the example of §11.5, R-76).

#[test]
fn a_par_is_a_frame_with_the_heading_of_the_range_and_the_number_of_replicas() {
    let dot = graph_of(FRAMES, "unison");
    assert_eq!(dot.frames.len(), 1, "one `par~`, one frame: {:?}", dot.frames);
    assert_eq!(dot.frames[0].id, "cluster_saws", "the frame of `let saws = par~ …`");
    assert_eq!(dot.frames[0].label.as_deref(), Some("par~ i in 0..<4（×4）"));
    assert_eq!(dot.frames[0].parent, None);
}

#[test]
fn the_index_is_an_init_input_vertex_in_the_frame_named_by_the_par() {
    let dot = graph_of(FRAMES, "unison");
    let i = dot.node("saws.i");
    assert_eq!(dot.label("saws.i"), "i: U32 at init");
    assert_eq!(attr(i, "shape"), Some("ellipse"), "an input is an ellipse");
    assert_eq!(clock_of_color(i), "init");
    assert_eq!(dot.frame_of("saws.i").id, "cluster_saws");
    assert!(dot.declared_twice().is_empty(), "no vertex is declared twice: {:?}", dot.declared_twice());
}

#[test]
fn the_node_of_the_body_is_in_the_frame_and_reads_the_index_and_the_inputs() {
    let dot = graph_of(FRAMES, "unison");
    let body = dot.node("saws.saw_0");
    assert_eq!(dot.label("saws.saw_0"), "saw_0 = saw~: F32 at sample");
    assert!(attr(body, "style").is_some_and(|s| s.contains("rounded")), "a node without a name is rounded: {body:?}");
    assert_eq!(clock_of_color(body), "sample");
    assert_eq!(dot.frame_of("saws.saw_0").id, "cluster_saws");
    // The inputs are outside the frame; the body reads them and the index.
    assert!(dot.node("f0").frame.is_none() && dot.node("detune").frame.is_none());
    for from in ["f0", "detune", "saws.i"] {
        dot.solid(from, "saws.saw_0");
    }
}

#[test]
fn the_result_of_the_body_goes_to_the_vertex_of_the_par_and_the_body_does_not_read_it() {
    let dot = graph_of(FRAMES, "unison");
    dot.solid("saws.saw_0", "saws");
    dot.solid("saws", "_out");
    assert!(
        !dot.has_edge("saws", "saws.saw_0") && !dot.has_edge("saws", "saws.i"),
        "the body does not read the result of the `par~`: {:?}",
        dot.edge_list()
    );
}

#[test]
fn the_solid_edges_of_unison_have_no_cycle() {
    // R-76: `saws` -> `saws.saw_0` -> `saws`.
    assert_cycle_free(&graph_of(FRAMES, "unison"), "unison");
}

#[test]
fn the_vertex_of_a_par_that_is_a_let_is_a_box_with_the_range_in_its_label() {
    let dot = graph_of(FRAMES, "unison");
    let saws = dot.node("saws");
    assert!(attr(saws, "shape").is_none_or(|s| s == "box"), "a `let` is a box: {saws:?}");
    assert_eq!(clock_of_color(saws), "sample");
    // SPEC-GAP(S-1170): §1.1 gives a `let` the label `名前 = 式の種類: 型 at クロック` and does not say whether the label of the
    // vertex of a `par~` has the range; the provisional form writes it (the heading of the frame has it too).
    assert_eq!(dot.label("saws"), "saws = par~ 0..<4: [F32; 4] at sample");
}

// ---------------------------------------------------------------------------------------------------------------------
// §1.3: `nest` (a `par~` in a `par~`, R-76).

#[test]
fn a_par_in_a_par_is_a_frame_in_the_frame() {
    let dot = graph_of(FRAMES, "nest");
    assert_eq!(dot.frames.len(), 2, "two `par~`, two frames: {:?}", dot.frames);
    let outer = dot.frame_with_label("par~ i in 1..<3（×2）");
    let inner = dot.frame_with_label("par~ j in 0..<2（×2）");
    assert_eq!(dot.frames[outer].id, "cluster_m", "the frame of `let m = par~ …`");
    assert_eq!(dot.frames[outer].parent, None);
    assert_eq!(dot.frames[inner].parent, Some(outer), "the inner frame is inside the outer");
    assert_ne!(dot.frames[inner].id, dot.frames[outer].id, "two frames of one name are one frame for Graphviz");
}

#[test]
fn the_indices_of_nested_pars_are_qualified_by_the_name_of_their_par() {
    let dot = graph_of(FRAMES, "nest");
    let outer = dot.frame_with_label("par~ i in 1..<3（×2）");
    let inner = dot.frame_with_label("par~ j in 0..<2（×2）");
    // The inner `par~` is the node `m.par_0` (§11.6), so its index is `m.par_0.j`.
    for (id, label, frame) in [("m.i", "i: U32 at init", outer), ("m.par_0.j", "j: U32 at init", inner)] {
        let n = dot.node(id);
        assert_eq!(dot.label(id), label);
        assert_eq!(attr(n, "shape"), Some("ellipse"), "{id}");
        assert_eq!(clock_of_color(n), "init", "{id}");
        assert_eq!(dot.frame_index_of(id), frame, "the frame of {id}");
    }
    assert_eq!(dot.label("m.par_0.acc_0"), "acc_0 = acc~: F32 at sample");
    assert_eq!(dot.frame_index_of("m.par_0.acc_0"), inner);
    assert!(dot.declared_twice().is_empty(), "no vertex is declared twice: {:?}", dot.declared_twice());
}

#[test]
fn the_edges_of_nested_pars_go_from_the_indices_and_the_body_to_the_results() {
    let dot = graph_of(FRAMES, "nest");
    // `acc~(x, F32.round_from((i * 10) + j))` reads the input and both indices.
    for from in ["x", "m.i", "m.par_0.j"] {
        dot.solid(from, "m.par_0.acc_0");
    }
    // The result of the body of the inner `par~` goes to the vertex of the inner `par~`, whose value is the body of the outer.
    dot.solid("m.par_0.acc_0", "m.par_0");
    dot.solid("m.par_0", "m");
    dot.solid("m", "_out");
    assert!(
        !dot.has_edge("m", "m.par_0.acc_0")
            && !dot.has_edge("m", "m.par_0")
            && !dot.has_edge("m.par_0", "m.par_0.acc_0"),
        "no edge from a result to the body that makes it: {:?}",
        dot.edge_list()
    );
}

#[test]
fn the_solid_edges_of_nest_have_no_cycle() {
    // R-76: `m` -> `m.par_0.acc_0` -> `m.par_0` -> `m`.
    assert_cycle_free(&graph_of(FRAMES, "nest"), "nest");
}

// ---------------------------------------------------------------------------------------------------------------------
// §1.2: no cycle of the solid edges, and the dashed edges of the look-back.

#[test]
fn the_solid_edges_of_a_flow_with_a_feedback_and_delays_have_no_cycle() {
    for flow in ["lp", "labels"] {
        assert_cycle_free(&graph_of(LABELS, flow), flow);
    }
    // The feedback of `saw` and `acc` (`prev~(^phase)`, `prev~(^y)`) is in the flows that read them.
    for flow in ["saw", "acc"] {
        assert_cycle_free(&graph_of(FRAMES, flow), flow);
    }
}

#[test]
fn the_solid_edges_of_a_delay_in_a_nested_par_have_no_cycle() {
    let dot = graph_of(LABELS, "nested_delay");
    assert_cycle_free(&dot, "nested_delay");
    assert_eq!(dot.frames.len(), 2);
    let inner = dot.frame_with_label("par~ j in 0..<2（×2）");
    assert_eq!(dot.frames[inner].parent, Some(dot.frame_with_label("par~ i in 0..<2（×2）")));
    assert_eq!(dot.frame_index_of("m.par_0.delay_0"), inner);
    assert_eq!(dot.frame_index_of("m.par_0.j"), inner);
    // The read of the value to delay is the look-back: dashed; the delayed value goes on to the result with a solid edge.
    dot.dashed("x", "m.par_0.delay_0");
    dot.solid("m.par_0.delay_0", "m.par_0");
}

#[test]
fn the_feedback_and_the_look_back_edges_are_dashed_and_the_others_are_solid() {
    let lp = graph_of(LABELS, "lp");
    // `let y = (0.5 * x) + (0.5 * prev~(^y))`: the node `y.prev_0` reads `y` of the past (dashed) and gives the value to `y` (solid).
    lp.dashed("y", "y.prev_0");
    lp.solid("y.prev_0", "y");
    lp.solid("x", "y");
    lp.solid("y", "_out");
    let labels = graph_of(LABELS, "labels");
    labels.dashed("scaled", "d"); // `delay~(scaled, 4)`
    labels.dashed("d", "p"); // `prev~(d * k)`
    labels.solid("p", "_out");
    labels.solid("scaled", "_out.lp_0");
    labels.solid("_out.lp_0", "_out");
    for (from, to) in [("x", "scaled"), ("g", "scaled"), ("two", "scaled")] {
        labels.solid(from, to);
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// §1.1: the labels, the shapes and the colours.

#[test]
fn an_input_is_an_ellipse_with_its_declaration_and_the_colour_of_its_clock() {
    let dot = graph_of(LABELS, "labels");
    for (id, label, clock) in
        [("x", "x: F32 at sample", "sample"), ("g", "g: F32 at block", "block"), ("k", "k: F32 at init", "init")]
    {
        let n = dot.node(id);
        assert_eq!(dot.label(id), label);
        assert_eq!(attr(n, "shape"), Some("ellipse"), "{id}");
        assert_eq!(clock_of_color(n), clock, "{id}");
    }
}

#[test]
fn the_output_is_a_double_octagon_named_out_with_an_underscore() {
    let dot = graph_of(LABELS, "labels");
    let out = dot.node("_out");
    assert_eq!(dot.label("_out"), "out: F32 at sample");
    assert_eq!(attr(out, "shape"), Some("doubleoctagon"));
    assert_eq!(clock_of_color(out), "sample");
    assert!(dot.find("out").is_none(), "the output is `_out`, not `out`: {:?}", dot.ids());
}

#[test]
fn a_let_is_a_box_and_a_node_without_a_name_is_rounded_with_its_kind_and_type() {
    let dot = graph_of(LABELS, "labels");
    let scaled = dot.node("scaled");
    assert!(attr(scaled, "shape").is_none_or(|s| s == "box"), "a `let` is a box: {scaled:?}");
    assert_eq!(clock_of_color(scaled), "sample");
    // The label of a `let` whose value is not a call is not fixed (`名前 = 式の種類`); its name and its type and clock are.
    let label = dot.label("scaled");
    assert!(label.starts_with("scaled") && label.ends_with(": F32 at sample"), "{label}");
    // The node of an instance written in the output expression is qualified by `_out` (§11.6) and the label has no qualification.
    let lp = dot.node("_out.lp_0");
    assert_eq!(dot.label("_out.lp_0"), "lp_0 = lp~: F32 at sample");
    assert!(attr(lp, "style").is_some_and(|s| s.contains("rounded")), "{lp:?}");
    assert_eq!(clock_of_color(lp), "sample");
    // The `let` of an instance or a delay is named by the `let` (§11.6, §1.1: `名前 = 式の種類`).
    let p = dot.node("p");
    assert_eq!(clock_of_color(p), "sample");
    assert_eq!(dot.label("p"), "p = prev~: F32 at sample");
}

#[test]
fn a_flow_with_no_par_has_no_frame() {
    for flow in ["lp", "labels"] {
        let dot = graph_of(LABELS, flow);
        assert!(dot.frames.is_empty(), "{flow}: {:?}", dot.frames);
    }
}

#[test]
fn the_label_of_a_constant_let_has_no_clock_and_is_gray() {
    let dot = graph_of(LABELS, "labels");
    let two = dot.node("two");
    assert_eq!(clock_of_color(two), "init", "a constant is gray (§1.1)");
    // SPEC-GAP(S-397): §1.1 gives a `let` the label `名前 = 式の種類: 型 at クロック` and does not say what a constant has for a clock;
    // the provisional form writes no clock (there is no name for it after `at`).
    assert_eq!(dot.label("two"), "two: F32");
}

#[test]
fn the_label_of_a_delay_is_its_kind_without_the_length() {
    let dot = graph_of(LABELS, "labels");
    // SPEC-GAP(S-397): §1.1 writes the label of a node `saw_0 = saw~: 型 at クロック` and does not say whether a delay shows its length
    // and its maximum; the provisional form shows the kind only.
    assert_eq!(dot.label("d"), "d = delay~: F32 at sample");
}

#[test]
fn no_vertex_has_a_colour_other_than_the_three_of_the_clocks() {
    // SPEC-GAP(S-1084): the clocks that derive from `sample` (`sample / N`, `sample * N`, an event) have no colour in §1.1; no flow here has
    // one, and the provisional reading is that no colour is added, so every vertex of these flows is gray, blue or black.
    for (file, flow) in
        [(FRAMES, "unison"), (FRAMES, "nest"), (LABELS, "labels"), (LABELS, "two_frames"), (LABELS, "destructure")]
    {
        let dot = graph_of(file, flow);
        for n in &dot.nodes {
            clock_of_color(n);
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// §1.3: the names of the vertices of the indices do not collide.

#[test]
fn the_indices_of_two_pars_with_one_index_name_are_two_vertices_in_two_frames() {
    let dot = graph_of(LABELS, "two_frames");
    assert_eq!(dot.frames.len(), 3, "{:?}", dot.frames);
    let (fa, fb, fk) = (
        dot.frame_with_label("par~ i in 0..<2（×2）"),
        dot.frame_with_label("par~ i in 0..<3（×3）"),
        dot.frame_with_label("par~ k in 0..<2（×2）"),
    );
    // `a` and `b` are the names of their `par~`; the `par~` inside the output expression is `_out.par_0` (§11.6).
    for (idx, label, frame, body) in [
        ("a.i", "i: U32 at init", fa, "a.lp_0"),
        ("b.i", "i: U32 at init", fb, "b.lp_0"),
        ("_out.par_0.k", "k: U32 at init", fk, "_out.par_0.lp_0"),
    ] {
        assert_eq!(dot.label(idx), label, "{idx}");
        assert_eq!(dot.frame_index_of(idx), frame, "the frame of {idx}");
        assert_eq!(dot.frame_index_of(body), frame, "the frame of {body}");
        dot.solid(idx, body);
    }
    let ids: Vec<&str> = dot.frames.iter().map(|f| f.id.as_str()).collect();
    let mut sorted = ids.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), ids.len(), "the frames have one name each: {ids:?}");
    assert!(dot.declared_twice().is_empty(), "no vertex is declared twice: {:?}", dot.declared_twice());
    assert_cycle_free(&dot, "two_frames");
}

#[test]
fn an_index_named_like_a_node_of_its_body_is_not_that_node() {
    let dot = graph_of(LABELS, "shadow");
    // SPEC-GAP(S-1168): the node of `lp~(x * F32.round_from(lp_0))` is named `lps.lp_0` by §11.6 and the vertex of the index `lp_0` is
    // `lps.lp_0` by §1.3, the same name. The provisional reading is that they are two vertices; the name of the vertex of the index is
    // the implementation's, and the test asks only that the two are different vertices and not declared twice.
    assert!(dot.declared_twice().is_empty(), "a vertex is declared twice: {:?}", dot.declared_twice());
    let of_label = |label: &str| -> Vec<&str> {
        dot.nodes.iter().filter(|n| n.attrs.get("label").is_some_and(|l| l == label)).map(|n| n.id.as_str()).collect()
    };
    let index = of_label("lp_0: U32 at init");
    let node = of_label("lp_0 = lp~: F32 at sample");
    assert_eq!((index.len(), node.len()), (1, 1), "the index and the node: {:?}", dot.ids());
    assert_ne!(index[0], node[0], "the index and the node of the body are different vertices");
    assert_eq!(dot.frame_index_of(index[0]), dot.frame_index_of(node[0]), "both are in the frame");
    dot.solid(index[0], node[0]);
    dot.solid("x", node[0]);
    dot.solid(node[0], "lps");
    assert_cycle_free(&dot, "shadow");
}

// ---------------------------------------------------------------------------------------------------------------------
// The forms the work ticket gives provisionally (S-1171, S-1169, S-1175), and a `par~` of a package module.

#[test]
fn the_heading_of_an_inclusive_range_is_the_written_form_with_the_number_of_replicas() {
    let dot = graph_of(LABELS, "inclusive");
    assert_eq!(dot.frames.len(), 2, "{:?}", dot.frames);
    // §11.5: `a ..= b` has `b - a + 1` replicas; `1 ..= 3` has 3 and the two ends of the `U32` range have 2, with no overflow of `b + 1`.
    // SPEC-GAP(S-1171): §1.3 gives the heading of `..<` only; the provisional form of `..=` keeps the written operator.
    dot.frame_with_label("par~ i in 1..=3（×3）");
    dot.frame_with_label("par~ k in 4294967294..=4294967295（×2）");
}

#[test]
fn a_let_with_more_than_one_name_and_a_let_of_the_wildcard_are_named_as_the_qualification() {
    let dot = graph_of(LABELS, "destructure");
    // SPEC-GAP(S-1169): §1.1 names the vertex of a `let` by the name of the `let` and does not name a `let` of more than one name or of no
    // name; the provisional reading is the qualification of §11.6: the first name of the pattern (`let Pair { l: p, r: q }` and
    // `let (a, b)` are `p` and `a`), and `_<number>` for a `let` with no name (the two `let _` are `_0` and `_1`).
    for id in ["p", "a", "_0", "_1"] {
        assert!(
            dot.find(id).is_some_and(|n| attr(n, "shape").is_none_or(|s| s == "box")),
            "the box \"{id}\": {:?}",
            dot.ids()
        );
    }
    // The nodes of the instances in those `let` are qualified by the same names (§11.6: `p.split_0`, `_0.lp_0`).
    for (node, label) in [
        ("p.split_0", "split_0 = split~: Pair at sample"),
        ("_0.lp_0", "lp_0 = lp~: F32 at sample"),
        ("_1.lp_0", "lp_0 = lp~: F32 at sample"),
    ] {
        assert_eq!(dot.label(node), label);
    }
    dot.solid("x", "p.split_0");
    dot.solid("p.split_0", "p");
    dot.solid("x", "_0.lp_0");
    dot.solid("_0.lp_0", "_0");
    dot.solid("p", "_1.lp_0");
    dot.solid("_1.lp_0", "_1");
    dot.solid("p", "a");
    assert!(dot.ids().iter().all(|id| !id.starts_with("let_")), "no name of the form `let_<number>`: {:?}", dot.ids());
    assert!(dot.declared_twice().is_empty(), "{:?}", dot.declared_twice());
    assert_cycle_free(&dot, "destructure");
}

#[test]
fn a_par_with_no_state_that_is_the_value_of_a_let_is_a_node_named_after_the_let() {
    let dot = graph_of(LABELS, "stateless");
    // SPEC-GAP(S-1175): §11.6 names the node of the `par~` that is the whole value of a `let` by the name of the `let`; the `par~` with no
    // instance and no delay in its body makes no field of the state, and the provisional form calls its node `<let>.par_<number>` (as a
    // `par~` inside a larger value), so the vertex of the `let` and the node of the `par~` are two vertices; the frame and the index
    // follow the name of the `par~` (§1.3).
    let par = dot.node("ys.par_0");
    assert!(attr(par, "style").is_some_and(|s| s.contains("rounded")), "{par:?}");
    assert!(dot.label("ys.par_0").starts_with("par_0 = par~"), "{}", dot.label("ys.par_0"));
    assert!(dot.find("ys").is_some(), "the vertex of the `let`: {:?}", dot.ids());
    assert_eq!(dot.frames.len(), 1, "{:?}", dot.frames);
    assert_eq!(dot.frames[0].label.as_deref(), Some("par~ i in 0..<2（×2）"));
    assert_eq!(dot.label("ys.par_0.i"), "i: U32 at init");
    assert_eq!(dot.frame_index_of("ys.par_0.i"), 0);
    dot.solid("ys.par_0", "ys");
    assert_cycle_free(&dot, "stateless");
}

#[test]
fn a_par_calling_a_flow_of_another_module_has_the_node_with_the_name_of_the_flow_only() {
    let d = Dir::pkg("graph_par_frames_module");
    d.write(
        "filters.onsa",
        "pub flow lp(x: F32 at sample) -> F32 at sample {\n  let y = (0.5 * x) + (0.5 * prev~(^y))\n  y\n}\n",
    );
    d.write(
        "voices.onsa",
        "use filters.lp\n\npub flow voices(x: F32 at sample) -> F32 at sample {\n  let ps = par~ i in 0 ..< 2 { lp~(x * F32.round_from(i)) }\n  ps[0] + ps[1]\n}\n",
    );
    let out = run(d.root(), &["graph", "voices", &d.arg()]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let dot = Dot::parse(&out.stdout);
    // The label of a node has the name of the flow without the module (§1.1: `修飾を除いた`).
    assert_eq!(dot.label("ps.lp_0"), "lp_0 = lp~: F32 at sample");
    assert_eq!(dot.frames.len(), 1);
    assert_eq!(dot.frames[0].label.as_deref(), Some("par~ i in 0..<2（×2）"));
    assert_eq!(dot.frame_of("ps.i").id, "cluster_ps");
    assert_eq!(dot.frame_of("ps.lp_0").id, "cluster_ps");
    dot.solid("ps.i", "ps.lp_0");
    dot.solid("ps.lp_0", "ps");
    assert_cycle_free(&dot, "voices");
}
