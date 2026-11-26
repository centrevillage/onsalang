use super::dot_problems;

/// The graph of `nest` of `tests/spec/flow/graph_par_frames.onsa` (spec/tools.md §1.3), which the spec's text fixes.
const NEST: &str = r#"digraph "nest" {
  rankdir=LR
  node [shape=box fontname="monospace"]
  "x" [label="x: F32 at sample" shape=ellipse color="black" fontcolor="black"]
  "m" [label="m = par~ 1..<3: [[F32; 2]; 2] at sample" color="black" fontcolor="black"]
  "_out" [label="out: F32 at sample" shape=doubleoctagon color="black" fontcolor="black"]
  subgraph "cluster_m" {
    label="par~ i in 1..<3（×2）"
    "m.i" [label="i: U32 at init" shape=ellipse color="gray40" fontcolor="gray40"]
    "m.par_0" [label="par_0 = par~ 0..<2: [F32; 2] at sample" style=rounded color="black" fontcolor="black"]
    subgraph "cluster_m.par_0" {
      label="par~ j in 0..<2（×2）"
      "m.par_0.j" [label="j: U32 at init" shape=ellipse color="gray40" fontcolor="gray40"]
      "m.par_0.acc_0" [label="acc_0 = acc~: F32 at sample" style=rounded color="black" fontcolor="black"]
    }
  }
  "m.par_0" -> "m"
  "m.par_0.acc_0" -> "m.par_0"
  "x" -> "m.par_0.acc_0"
  "m.i" -> "m.par_0.acc_0"
  "m.par_0.j" -> "m.par_0.acc_0"
  "m" -> "_out"
}
"#;

/// What `dot_problems` finds of `NEST` with `from` written as `to`.
fn broken(from: &str, to: &str) -> Vec<String> {
    assert!(NEST.contains(from), "`{from}` is not in the graph");
    dot_problems(&NEST.replacen(from, to, 1)).1
}

fn finds(problems: &[String], text: &str) {
    assert!(problems.iter().any(|p| p.contains(text)), "no problem has `{text}`: {problems:#?}");
}

const M_I: &str = "    \"m.i\" [label=\"i: U32 at init\" shape=ellipse color=\"gray40\" fontcolor=\"gray40\"]\n";
const M_PAR: &str = "    \"m.par_0\" [label=\"par_0 = par~ 0..<2: [F32; 2] at sample\" style=rounded color=\"black\" fontcolor=\"black\"]\n";
const ACC: &str = "      \"m.par_0.acc_0\" [label=\"acc_0 = acc~: F32 at sample\" style=rounded color=\"black\" fontcolor=\"black\"]\n";
const M: &str = "  \"m\" [label=\"m = par~ 1..<3: [[F32; 2]; 2] at sample\" color=\"black\" fontcolor=\"black\"]\n";
const EDGE: &str = "  \"m.par_0\" -> \"m\"\n";

#[test]
fn the_graph_the_spec_shows_has_none() {
    assert_eq!(dot_problems(NEST), (2, Vec::new()));
}

#[test]
fn a_range_with_an_included_end_counts_its_end() {
    for (heading, ok) in [
        ("par~ i in 0..=0（×1）", true),
        ("par~ i in 1..=3（×3）", true),
        ("par~ i in 4294967294..=4294967295（×2）", true),
        ("par~ i in 1..=3（×2）", false),
        ("par i in 1..<3（×2）", true),
        ("par i in 1..<3（×3）", false),
    ] {
        let problems = dot_problems(&NEST.replace("par~ i in 1..<3（×2）", heading)).1;
        assert_eq!(problems.is_empty(), ok, "{heading}: {problems:?}");
    }
}

#[test]
fn a_name_that_two_vertices_share_is_found() {
    finds(&broken("\"m.i\" [label", "\"m\" [label"), "the vertex `m` is declared twice");
}

#[test]
fn an_edge_to_a_name_with_no_vertex_is_found() {
    finds(&broken("\"x\" -> \"m.par_0.acc_0\"", "\"x\" -> \"nowhere\""), "ends at `nowhere`");
    finds(&broken("\"m\" -> \"_out\"", "\"gone\" -> \"_out\""), "ends at `gone`");
}

#[test]
fn a_frame_has_one_vertex_of_its_index() {
    let clock = broken("\"m.par_0.j\" [label=\"j: U32 at init\"", "\"m.par_0.j\" [label=\"j: U32 at block\"");
    finds(&clock, "the frame `m.par_0` has 0 vertices of its index `j: U32 at init`");
    let shape =
        broken("\"m.i\" [label=\"i: U32 at init\" shape=ellipse", "\"m.i\" [label=\"i: U32 at init\" shape=box");
    finds(&shape, "the frame `m` has 0 vertices");
    let second = format!("{M_PAR}    \"m.i2\" [label=\"i: U32 at init\" shape=ellipse color=\"gray40\"]\n");
    finds(&dot_problems(&NEST.replace(M_PAR, &second)).1, "the frame `m` has 2 vertices");
    // Out of the frame, and with a name that no path qualifies.
    let outside =
        NEST.replace(M_I, "").replace(EDGE, &format!("  \"m.i\" [label=\"i: U32 at init\" shape=ellipse]\n{EDGE}"));
    finds(&dot_problems(&outside).1, "the frame `m` has 0 vertices");
    let name = broken("\"m.i\" [label", "\"i\" [label");
    finds(&name, "the frame `m` has 0 vertices");
}

#[test]
fn a_heading_counts_as_its_range_does() {
    finds(&broken("1..<3（×2）", "1..<3（×3）"), "counts 3, and its range is 2");
    finds(&broken("0..<2（×2）", "0..<2（×1）"), "counts 1, and its range is 2");
    finds(&broken("par~ i in 1..<3（×2）", "par~ i in 3..<1（×2）"), "is not `par~ i in a..<b（×N）`");
    finds(&broken("par~ j in 0..<2（×2）", "par~ j on 0..<2"), "the heading `par~ j on 0..<2`");
}

#[test]
fn a_vertex_is_in_the_frame_its_name_gives() {
    // The node of the body out of its frame.
    let out = NEST.replace(ACC, "").replace(EDGE, &format!("  \"m.par_0.acc_0\" [label=\"acc_0 = acc~\"]\n{EDGE}"));
    finds(
        &dot_problems(&out).1,
        "the vertex `m.par_0.acc_0` is in no frame, and its name puts it in the frame `m.par_0`",
    );
    // The node of the inner `par~` in its own frame, not in the outer's.
    let inner_node = "      \"m.par_0\" [label=\"par_0 = par~\"]\n      \"m.par_0.j\"";
    let inner = NEST.replace(M_PAR, "").replace("      \"m.par_0.j\"", inner_node);
    finds(
        &dot_problems(&inner).1,
        "the vertex `m.par_0` is in the frame `m.par_0`, and its name puts it in the frame `m`",
    );
    // The index of the outer frame at the top.
    let top =
        NEST.replace(M_I, "").replace(EDGE, &format!("  \"m.i\" [label=\"i: U32 at init\" shape=ellipse]\n{EDGE}"));
    finds(&dot_problems(&top).1, "the vertex `m.i` is in no frame");
}

#[test]
fn a_frame_has_the_vertex_of_its_par_and_a_path_of_its_own() {
    finds(&dot_problems(&NEST.replace(M, "")).1, "the frame `m` has no vertex of its `par~`");
    finds(&dot_problems(&NEST.replace("cluster_m.par_0", "cluster_m")).1, "two frames of the path `m`");
    finds(
        &dot_problems(&NEST.replace("cluster_m.par_0", "cluster_k")).1,
        "the frame `k` is in the frame `m`, whose path does not qualify it",
    );
}
