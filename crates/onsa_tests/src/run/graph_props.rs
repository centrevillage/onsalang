//! The properties of the DOT of `onsa graph` that `spec/tools.md` §1 fixes,
//! checked of every flow of every case with no diagnostic (W7-17 L1/t, from
//! W7-15 U3 (4)), beside the cycle of solid edges (§1.2) that
//! [`onsa_driver::graph::check_graphs`] checks. Each is O(V + E) of the text:
//! - a name is one vertex's, and each end of an edge is a vertex declared;
//! - one frame (a cluster, §1.3) of each `par~` / `par`, named by the path of
//!   its node, which is a vertex of the enclosing frame; the heading
//!   `par~ i in a..<b（×N）` (or `..=`) counts `N` as the range does;
//! - in a frame, one vertex of its index (an ellipse of `i: U32 at init`
//!   named by the path of the frame), and each vertex named by a path
//!   `P.x` of a frame `P` is in the innermost such frame;
//! - the flows drawn are the flows of the package that are complete, and a
//!   case with no diagnostic has no flow that is not.
//!
//! The text of a name is not fixed (S-1168: how the index vertex avoids the
//! name of a node of the body), so a name is read only as "qualified by the
//! path of its frame".

use std::collections::{HashMap, HashSet};

use onsa_driver::Analyzed;
use onsa_sema::def::DefKind;

/// What the properties found in the flows of a package.
#[derive(Debug, Default)]
pub struct Found {
    /// The frames of the graphs drawn.
    pub frames: usize,
    pub problems: Vec<String>,
}

/// The flows of the package of `analyzed` (a case with no diagnostic): each
/// drawn and its DOT checked, `drawn` being the number [`check_graphs`]
/// reports.
///
/// [`check_graphs`]: onsa_driver::graph::check_graphs
pub fn check(analyzed: &Analyzed, drawn: usize) -> Found {
    let a = &analyzed.analysis;
    let own =
        a.defs.iter().enumerate().filter(|(_, d)| matches!(d.kind, DefKind::Flow(_)) && a.modules.is_own(d.module));
    let mut found = Found::default();
    let (mut total, mut complete) = (0, 0);
    for (i, def) in own {
        let id = onsa_sema::DefId(i as u32);
        total += 1;
        if !a.flows.get(&id).is_some_and(|f| f.planned()) {
            continue;
        }
        complete += 1;
        // The name in its own module, which no other flow of the package shares.
        let (name, scope) = (a.qualified_name(id), a.modules.get(def.module).path.clone());
        let named = if scope.is_empty() { (def.name.clone(), Some(String::new())) } else { (name.clone(), None) };
        match onsa_driver::graph(analyzed, &named.0, named.1.as_deref()) {
            Ok(dot) => {
                let (frames, problems) = dot_problems(&dot);
                found.frames += frames;
                found.problems.extend(problems.into_iter().map(|p| format!("flow `{name}`: {p}")));
            }
            Err(e) => found.problems.push(format!("flow `{name}` is complete, and `onsa graph` fails: {e:?}")),
        }
    }
    if complete != total {
        found.problems.push(format!(
            "{} of the {total} flows of the package are not complete, with no diagnostic",
            total - complete
        ));
    }
    if complete != drawn {
        found
            .problems
            .push(format!("{complete} flows are complete, and {drawn} were drawn by the check of the cycles"));
    }
    found
}

/// A vertex or a cluster read out of the DOT: its name (a cluster's is its
/// path), and where it is.
struct Vertex {
    label: String,
    ellipse: bool,
    /// The index (in the frames) of the innermost frame.
    frame: Option<usize>,
}

struct Frame {
    path: String,
    heading: String,
    parent: Option<usize>,
}

/// The text up to the `"` that closes a quoted name that starts at `s[0]`,
/// and the rest after it.
fn quoted(s: &str) -> Option<(&str, &str)> {
    let s = s.strip_prefix('"')?;
    let end = s.find('"')?;
    Some((&s[..end], &s[end + 1..]))
}

/// The number of frames in `dot`, and what it breaks of the properties.
pub fn dot_problems(dot: &str) -> (usize, Vec<String>) {
    let mut problems = Vec::new();
    let mut verts: HashMap<String, Vertex> = HashMap::new();
    let mut edges: Vec<(String, String)> = Vec::new();
    let mut frames: Vec<Frame> = Vec::new();
    let mut open: Vec<usize> = Vec::new();
    for line in dot.lines().map(str::trim) {
        if let Some(rest) = line.strip_prefix("subgraph ") {
            let Some((cluster, _)) = quoted(rest) else { continue };
            let path = cluster.strip_prefix("cluster_").unwrap_or(cluster).to_string();
            frames.push(Frame { path, heading: String::new(), parent: open.last().copied() });
            open.push(frames.len() - 1);
        } else if line == "}" {
            open.pop();
        } else if let Some(heading) = line.strip_prefix("label=\"").and_then(|h| h.strip_suffix('"')) {
            if let Some(&k) = open.last() {
                frames[k].heading = heading.to_string();
            }
        } else if let Some((name, rest)) = quoted(line) {
            if let Some(rest) = rest.strip_prefix(" -> ") {
                if let Some((to, _)) = quoted(rest) {
                    edges.push((name.to_string(), to.to_string()));
                }
            } else if let Some(rest) = rest.strip_prefix(" [label=\"") {
                let label = rest.split('"').next().unwrap_or("").to_string();
                let v = Vertex { label, ellipse: rest.contains(" shape=ellipse "), frame: open.last().copied() };
                if verts.insert(name.to_string(), v).is_some() {
                    problems.push(format!("the vertex `{name}` is declared twice"));
                }
            }
        }
    }
    for (from, to) in &edges {
        for end in [from, to] {
            if !verts.contains_key(end) {
                problems.push(format!("the edge `{from}` -> `{to}` ends at `{end}`, which is no vertex"));
            }
        }
    }
    let mut seen = HashSet::new();
    for (k, f) in frames.iter().enumerate() {
        if !seen.insert(f.path.as_str()) {
            problems.push(format!("two frames of the path `{}`", f.path));
        }
        problems.extend(frame_problems(k, f, &frames, &verts));
    }
    // A vertex named `P.x` of a frame `P` is in the innermost frame whose path
    // qualifies its name (the node of a nested `par~` in the frame of the outer).
    for (name, v) in &verts {
        let want = (0..frames.len())
            .filter(|&k| name.strip_prefix(frames[k].path.as_str()).is_some_and(|r| r.starts_with('.')))
            .max_by_key(|&k| frames[k].path.len());
        if v.frame != want {
            let at = |k: Option<usize>| k.map_or("no frame".to_string(), |k| format!("the frame `{}`", frames[k].path));
            problems.push(format!("the vertex `{name}` is in {}, and its name puts it in {}", at(v.frame), at(want)));
        }
    }
    problems.sort();
    (frames.len(), problems)
}

/// What the frame `k` breaks: its node, its heading and its index.
fn frame_problems(k: usize, f: &Frame, frames: &[Frame], verts: &HashMap<String, Vertex>) -> Vec<String> {
    let mut problems = Vec::new();
    let path = &f.path;
    if !verts.contains_key(path) {
        problems.push(format!("the frame `{path}` has no vertex of its `par~`"));
    }
    let Some((index, (written, range))) = heading(&f.heading) else {
        problems.push(format!("the heading `{}` of the frame `{path}` is not `par~ i in a..<b（×N）`", f.heading));
        return problems;
    };
    if written != range {
        problems.push(format!(
            "the heading `{}` of the frame `{path}` counts {written}, and its range is {range}",
            f.heading
        ));
    }
    let label = format!("{index}: U32 at init");
    let own: Vec<&String> = verts
        .iter()
        .filter(|(n, v)| v.frame == Some(k) && v.ellipse && v.label == label && n.starts_with(&format!("{path}.")))
        .map(|(n, _)| n)
        .collect();
    if own.len() != 1 {
        problems.push(format!("the frame `{path}` has {} vertices of its index `{label}`: {own:?}", own.len()));
    }
    if f.parent.is_some_and(|p| !path.starts_with(&format!("{}.", frames[p].path))) {
        problems.push(format!(
            "the frame `{path}` is in the frame `{}`, whose path does not qualify it",
            frames[f.parent.unwrap_or(k)].path
        ));
    }
    problems
}

/// The index variable of a heading `par~ i in a..<b（×N）`, and `N` against
/// the count the range gives.
fn heading(h: &str) -> Option<(String, (u64, u64))> {
    let rest = h.strip_prefix("par~ ").or_else(|| h.strip_prefix("par "))?;
    let (var, range) = rest.split_once(" in ")?;
    let (range, times) = range.split_once("（×")?;
    let n: u64 = times.strip_suffix('）')?.parse().ok()?;
    let (lo, hi, included) = match range.split_once("..<") {
        Some((lo, hi)) => (lo, hi, false),
        None => {
            let (lo, hi) = range.split_once("..=")?;
            (lo, hi, true)
        }
    };
    let (lo, hi): (u64, u64) = (lo.parse().ok()?, hi.parse().ok()?);
    let count = hi.checked_sub(lo)? + u64::from(included);
    Some((var.to_string(), (n, count)))
}

#[cfg(test)]
mod tests;
