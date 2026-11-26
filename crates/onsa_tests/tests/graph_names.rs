//! The graph of a flow of nested `par~`s whose indices are named as the nodes
//! of their bodies are (W7-17 L1/t, from W7-15 U3 (4); S-1168): the names of
//! the vertices are one each, the edges end at vertices, and a frame has its
//! index and its node (spec/tools.md §1.1, §1.3). A fixed table: each name of
//! a node a body generates (`lp_0`, `par_0`, `prev_0`, `delay_0`, `vdelay_0`,
//! `acc_0`) as the index of each level, one to three levels deep.

use onsa_tests::run::graph_props;

/// The names a body's nodes get, and the call of the node that gets each
/// (`par_0` is the nested `par~` itself).
const NAMES: [&str; 6] = ["lp_0", "par_0", "prev_0", "delay_0", "vdelay_0", "acc_0"];

const PRELUDE: &str = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  let y = (0.5 * x) + (0.5 * prev~(^y))\n  y\n}\n\n\
pub flow acc(x: F32 at sample, k: F32 at init) -> F32 at sample {\n  let y = prev~(^y) + (x * k)\n  y\n}\n";

/// A node of the kind `name` is the first of its kind in a body, so is named
/// `name`; one that makes the name of `par_0` is a nested `par~` the body has
/// (a `prev~` stands for it at the innermost level).
fn node(name: &str, arg: &str) -> String {
    match name {
        "lp_0" => format!("lp~({arg})"),
        "acc_0" => format!("acc~({arg}, k)"),
        "delay_0" => format!("delay~({arg}, 4)"),
        "vdelay_0" => format!("vdelay~({arg}, 2.0, 8)"),
        _ => format!("prev~({arg})"),
    }
}

/// The flow whose `par~`s, outermost first, have the indices `names`: each
/// body holds the node its index is named after and the next `par~`.
fn flow(names: &[&str]) -> (String, String) {
    let title = format!("f_{}", names.join("_"));
    let mut body = String::new();
    for (depth, name) in names.iter().enumerate().rev() {
        let arg = format!("x + F32.round_from({name})");
        let here = node(name, &arg);
        body = match body.as_str() {
            "" => here,
            inner => format!("{here} + (par~ {} in 0 ..< 2 {{ {inner} }})[0]", names[depth + 1]),
        };
    }
    let src = format!(
        "pub flow {title}(x: F32 at sample, k: F32 at init) -> F32 at sample {{\n  let m = par~ {} in 1 ..< 3 {{ {body} }}\n  m[0]\n}}\n",
        names[0]
    );
    (title, src)
}

/// Every name at each of the levels, one to three deep, none twice in a
/// nest (no shadowing, §5.1): 6 + 30 + 120 flows.
fn table() -> Vec<Vec<&'static str>> {
    let mut all: Vec<Vec<&str>> = NAMES.iter().map(|&n| vec![n]).collect();
    for a in NAMES {
        for b in NAMES.into_iter().filter(|&b| b != a) {
            all.push(vec![a, b]);
            all.extend(NAMES.iter().filter(|&&c| c != a && c != b).map(|&c| vec![a, b, c]));
        }
    }
    all
}

#[test]
fn the_names_of_the_vertices_stay_one_each_where_an_index_is_named_as_a_node() {
    let table = table();
    let mut src = String::from(PRELUDE);
    for names in &table {
        src.push('\n');
        src.push_str(&flow(names).1);
    }
    let mut loaded =
        onsa_driver::Loaded::from_input(onsa_driver::PackageInput::single_file("g.onsa", src.clone())).unwrap();
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    let drawn = onsa_driver::graph::check_graphs(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    assert!(drawn.problems.is_empty(), "{:#?}", drawn.problems);
    // The two flows of the prelude and the flows of the table, each drawn.
    assert_eq!(drawn.flows, table.len() + 2);
    let found = graph_props::check(&analyzed, drawn.flows);
    assert!(found.problems.is_empty(), "{:#?}", found.problems);
    // One frame of each `par~`: `m` and the nested ones.
    assert_eq!(found.frames, table.iter().map(Vec::len).sum::<usize>());
}

/// The table has the cases where an index is named as a node of its own body
/// (`par~ lp_0 in … { lp~(…) }`), which the vertices of the frame are drawn
/// with two names for (S-1168 leaves the text of the second name open).
#[test]
fn a_node_of_the_name_of_its_frames_index_is_drawn_beside_it() {
    let (title, src) = flow(&["lp_0"]);
    let mut loaded =
        onsa_driver::Loaded::from_input(onsa_driver::PackageInput::single_file("g.onsa", format!("{PRELUDE}\n{src}")))
            .unwrap();
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap();
    assert!(analyzed.diagnostics.is_empty());
    let dot = onsa_driver::graph(&analyzed, &title, None).unwrap();
    let in_frame = dot.lines().filter(|l| l.trim_start().starts_with("\"m.")).filter(|l| l.contains("[label=")).count();
    assert_eq!(in_frame, 2, "the index and the node of the body: {dot}");
    let indices = dot.lines().filter(|l| l.contains("[label=\"lp_0: U32 at init\"")).count();
    assert_eq!(indices, 1, "{dot}");
    let nodes = dot.lines().filter(|l| l.contains("[label=\"lp_0 = lp~: F32 at sample\"")).count();
    assert_eq!(nodes, 1, "{dot}");
}
