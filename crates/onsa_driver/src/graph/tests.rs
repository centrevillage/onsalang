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
        files: files.iter().map(|(path, text)| SourceFile { path: path.to_string(), text: text.to_string() }).collect(),
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
    // The output is a vertex of its own (R-497).
    assert!(dot.contains("  \"y\" -> \"_out\"\n"), "{dot}");
}

/// The node of a `par~` names the replication with its `~` and its range,
/// as an instance names its flow (`saw~`, spec/tools.md §1.1, S-745). One
/// whose body holds no node is named as one with no name (S-1175).
#[test]
fn a_par_node_is_labelled_with_its_tilde() {
    let src = "pub flow f(x: F32 at sample) -> [F32; 2] at sample {\n  let xs = par~ i in 0 ..< 2 { x }\n  xs\n}\n";
    let analyzed = analyzed(PackageInput::single_file("p.onsa", src));
    let dot = super::graph(&analyzed, "f", None).unwrap();
    assert!(dot.contains("\"xs.par_0\" [label=\"par_0 = par~ 0..<2: [F32; 2] at sample\""), "{dot}");
}

/// Only a `let` of a single name is its node (S-148, through
/// parentheses); the node of any other `let` is a vertex of its §11.6
/// name (spec/tools.md §1.1), as the plan decides ([`FlowInfo::whole`]),
/// and the `let` the vertex of its scope (S-1169).
#[test]
fn the_node_of_a_let_that_is_not_one_name_is_a_vertex_of_its_own() {
    let src = "pub flow f(x: F32 at sample) -> F32 at sample {\n  let a = (prev~(x))\n  let _ = prev~(x)\n  a\n}\n";
    let analyzed = analyzed(PackageInput::single_file("p.onsa", src));
    let dot = super::graph(&analyzed, "f", None).unwrap();
    assert!(dot.contains("\"a\" [label=\"a = prev~: F32 at sample\""), "{dot}");
    assert!(dot.contains("\"_0\" [label=\"_0: F32 at sample\""), "{dot}");
    assert!(dot.contains("\"_0.prev_0\" [label=\"prev_0 = prev~: F32 at sample\" style=rounded"), "{dot}");
    assert!(dot.contains("  \"_0.prev_0\" -> \"_0\"\n"), "{dot}");
}

/// Every clock has its colour (spec/tools.md §1.1); those past `sample`
/// are black (S-1084), and one in error is an internal error.
#[test]
fn every_clock_has_a_colour() {
    use onsa_sema::clock::{Clock, Ratio};
    let at = onsa_diag::Span::new(onsa_diag::FileId(0), 0, 0);
    let colours =
        [Clock::Const, Clock::Init, Clock::Block, Clock::SAMPLE, Clock::Tick(Ratio(1)), Clock::Tick(Ratio(-2))]
            .map(|c| super::rate_color(c, at));
    assert_eq!(colours, ["gray40", "gray40", "blue", "black", "black", "black"]);
    assert_eq!(super::rate_color(Clock::Ambient, at), "black");
    assert!(crate::guard(|| super::rate_color(Clock::Error, at)).is_err());
}

/// The search finds a cycle of solid edges, an edge to itself too, and
/// leaves the dashed edges out (spec/tools.md §1.2).
#[test]
fn the_search_finds_a_cycle_of_the_solid_edges() {
    let drawing = |edges: &[(&str, &str, bool)]| super::Drawing {
        title: "f".into(),
        vertices: Vec::new(),
        frames: Vec::new(),
        top: Vec::new(),
        edges: edges.iter().map(|&(f, t, d)| super::Edge { from: f.into(), to: t.into(), dashed: d }).collect(),
    };
    let chain = [("a", "b", false), ("b", "c", false), ("x", "a", false)];
    assert_eq!(drawing(&chain).solid_cycle(), None);
    assert_eq!(drawing(&[chain.as_slice(), &[("c", "a", true)]].concat()).solid_cycle(), None);
    let cycle = drawing(&[chain.as_slice(), &[("c", "a", false)]].concat()).solid_cycle();
    assert_eq!(cycle, Some(["a", "b", "c", "a"].map(String::from).to_vec()));
    assert_eq!(drawing(&[("a", "a", false)]).solid_cycle(), Some(vec!["a".into(), "a".into()]));
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
