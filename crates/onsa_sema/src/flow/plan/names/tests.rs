//! The names of the state (§11.6, S-1138, S-1136, S-148), of the table of
//! the design memo of W7-03 (2.3): the form of a name, and the paths of the
//! nodes of a flow in the order of the table.

use super::{let_scopes, local, part, qualify};
use crate::flow::{FlowInfo, Owner, Part};
use crate::tests::check;
use crate::{Analysis, DefId};

#[test]
fn the_forms_of_a_name() {
    assert_eq!(local("prev", 0), "prev_0");
    assert_eq!(local("_hoist", 2), "_hoist_2");
    assert_eq!(qualify("a", "lp_1"), "a.lp_1");
    let parts = [Part::Own, Part::Buf, Part::W, Part::Init].map(|p| part("a.delay_0", p, None));
    assert_eq!(parts, ["a.delay_0", "a.delay_0.buf", "a.delay_0.w", "a.delay_0.init"]);
    // The `let`s that bind no name count apart from the others.
    let scopes = let_scopes([Some("p"), None, Some("n"), None].into_iter());
    assert_eq!(scopes, ["p", "_0", "n", "_1"]);
}

const SRC: &str = "pub flow lp(x: F32 at sample) -> F32 at sample {
  let y = 0.5 * x + 0.5 * prev~(^y)
  y
}
pub rt fn pick(xs: [F32; 2]) -> F32 {
  xs[0]
}
pub flow top(x: F32 at sample) -> F32 at sample {
  let a = prev~(lp~(x), 0.0) + prev~(x, 1.0)
  let b = lp~(prev~(a, 0.0))
  let c = (prev~(b, 0.0))
  let (p, q) = (prev~(x), lp~(x) + prev~(x))
  let _ = lp~(x)
  let vs = par~ i in 0 ..< 2 { lp~(prev~(x, 0.0)) + lp~(x) }
  let m = par~ i in 0 ..< 2 { pick(par~ j in 0 ..< 2 { prev~(x) }) }
  let d = prev~(x) at sample
  lp~(lp~(x)) * c + vs[0] + pick(par~ k in 0 ..< 2 { delay~(x, 4) }) + p + q + m[0] + d
}
";

fn flow<'a>(a: &'a Analysis, name: &str) -> &'a FlowInfo {
    let id = DefId(a.defs.iter().position(|d| d.name == name).expect("the flow") as u32);
    &a.flows[&id]
}

/// The paths of the nodes of `owner` and, after each `par~`, of its body
/// in brackets.
fn paths(f: &FlowInfo, owner: Owner) -> Vec<String> {
    let mut out = Vec::new();
    for &id in f.roots(owner) {
        out.push(f.node(id).path.clone());
        let inner = paths(f, Owner::Par(id));
        if !inner.is_empty() {
            out.push(format!("[{}]", inner.join(" ")));
        }
    }
    out
}

/// Each `let` qualifies its nodes and numbers each kind from 0 in the order
/// of the text, the outer call first; a node that is the whole value of a
/// `let` of one name (through parentheses, not `at`) takes that name; the
/// output is `_out`; a `par~` qualifies its body and numbers it from 0.
#[test]
fn the_paths_of_the_nodes() {
    let a = check(SRC);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = flow(&a, "top");
    let lets: Vec<Vec<String>> = (0..f.lets.len() as u32).map(|k| paths(f, Owner::Let(k))).collect();
    let want: [&[&str]; 8] = [
        &["a.prev_0", "a.lp_0", "a.prev_1"],
        &["b", "b.prev_0"],
        &["c"],
        &["p.prev_0", "p.lp_0", "p.prev_1"],
        &["_0.lp_0"],
        &["vs", "[vs.lp_0 vs.prev_0 vs.lp_1]"],
        &["m", "[m.par_0 [m.par_0.prev_0]]"],
        &["d.prev_0"],
    ];
    assert_eq!(lets, want.map(|w| w.iter().map(|s| s.to_string()).collect::<Vec<_>>()));
    let out = paths(f, Owner::Output);
    assert_eq!(out, ["_out.lp_0", "_out.lp_1", "_out.par_0", "[_out.par_0.delay_0]"]);
    // The name is the path without the scope; the field of a node in the
    // replica of a `par~` is its name.
    let names: Vec<(&str, &str)> = f.nodes.iter().map(|n| (n.name.as_str(), n.path.as_str())).collect();
    assert!(names.contains(&("delay_0", "_out.par_0.delay_0")), "{names:?}");
    assert!(names.contains(&("c", "c")), "{names:?}");
    let fields: Vec<&str> = f.fields.iter().map(|x| x.name.as_str()).collect();
    assert!(fields.contains(&"_out.par_0") && fields.contains(&"vs"), "{fields:?}");
    assert!(!fields.iter().any(|x| x.contains("delay_0")), "{fields:?}");
}
