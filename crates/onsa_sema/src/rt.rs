//! `rt` rules (T2-9; spec §10): an `rt` body calls only `rt` functions
//! (E0901, rule 4), and `rt` functions do not recurse (E0903, rule 5). E0901
//! reads the record of the uses of a body, and E0903 the calls of the body
//! itself (`crate::uses`, D-15); what needs `Alloc` there is an E0601
//! (`crate::effects`, rule 1, S-77).
//! E0902 (`Alloc` in the effect row) is checked with the signature; E0904 /
//! E0905 need effects other than `Alloc` and are phase 2.

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Span, Stage};

use crate::def::DefKind;
use crate::uses::{Record, Use, What, rt_edges};
use crate::{Analysis, DefId, Package, module_of_def};

/// The E0901 of the `rt` scopes of `records` ([`crate::uses::records`]):
/// of an `rt` function and of an anonymous function of an `rt` type, in a
/// body `rt` or not (§8.1); and the E0903 of the `rt` functions.
pub(crate) fn check_all(pkg: &Package, a: &Analysis, records: &[Record]) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let mut rt_fns: Vec<DefId> = Vec::new();
    // Calls of each rt body, by their place: (span, callee) for rt callees.
    let mut edges: HashMap<DefId, Vec<(Span, DefId)>> = HashMap::default();
    for r in records {
        let _scope = onsa_diag::internal::item_scope(a.def(r.id).span);
        let calls = first_calls(pkg, a, r);
        // A body with an error of this stage in any scope adds no edge (§10 rule 5).
        let quiet = calls.is_empty() && r.lacking(a).is_empty();
        diags.extend(calls);
        if !a.rt_checked(r.id) {
            continue;
        }
        rt_fns.push(r.id);
        if let Some(m) = module_of_def(pkg, a, r.id).filter(|_| quiet) {
            edges.insert(r.id, rt_edges(a, &m.parsed.ast, &a.bodies[&r.id]));
        }
    }
    // E0903: cycles in the rt call graph (§10 rule 5), each reported once at
    // the call that closes it.
    let mut color: HashMap<DefId, u8> = HashMap::default(); // 1 = on stack, 2 = done
    let mut reported: Vec<HashSet<DefId>> = Vec::new();
    for &start in &rt_fns {
        if color.contains_key(&start) || !edges.contains_key(&start) {
            continue;
        }
        let mut stack: Vec<(DefId, usize)> = vec![(start, 0)];
        color.insert(start, 1);
        while let Some(&mut (node, ref mut next)) = stack.last_mut() {
            let calls = &edges[&node];
            if *next >= calls.len() {
                color.insert(node, 2);
                stack.pop();
                continue;
            }
            let (span, callee) = calls[*next];
            *next += 1;
            match color.get(&callee) {
                Some(1) => {
                    let pos = stack.iter().position(|(n, _)| *n == callee).unwrap_or(0);
                    let cycle: HashSet<DefId> = stack[pos..].iter().map(|(n, _)| *n).collect();
                    if reported.contains(&cycle) {
                        continue;
                    }
                    // The cycle's edges: each stack entry's last taken call, plus the closing one.
                    let mut cycle_edges: Vec<(DefId, Span, DefId)> = stack[pos..stack.len() - 1]
                        .iter()
                        .map(|(n, next)| {
                            let (s, c) = edges[n][*next - 1];
                            (*n, s, c)
                        })
                        .collect();
                    cycle_edges.push((node, span, callee));
                    // Report at the earliest call in source order (§10; one report per cycle).
                    let (from, at, to) =
                        *cycle_edges.iter().min_by_key(|(_, s, _)| (s.file, s.start)).expect("cycle has edges");
                    let start_idx = cycle_edges.iter().position(|(f, _, _)| *f == from).unwrap_or(0);
                    let mut path: Vec<String> = Vec::new();
                    for k in 0..cycle_edges.len() {
                        path.push(a.shown_name(cycle_edges[(start_idx + k) % cycle_edges.len()].0));
                    }
                    path.push(a.shown_name(from));
                    let what = if cycle.len() == 1 { "calls itself" } else { "is mutually recursive" };
                    let d = Diagnostic::new(
                        Stage::Effects,
                        Code::E0903,
                        at,
                        format!(
                            "`{}` {what}: `rt` functions cannot recurse (§10); cycle: {}",
                            a.shown_name(from),
                            path.join(" -> ")
                        ),
                    )
                    .with_found(src_of(pkg, a, from, at))
                    .with_note(a.def(to).name_span, "recursion target declared here");
                    diags.push(d);
                    reported.push(cycle);
                }
                Some(_) => {}
                None => {
                    if edges.contains_key(&callee) {
                        color.insert(callee, 1);
                        stack.push((callee, 0));
                    }
                }
            }
        }
    }
    diags
}

fn src_of(pkg: &Package, a: &Analysis, def: DefId, span: Span) -> String {
    module_of_def(pkg, a, def).map(|m| m.text[span.start as usize..span.end as usize].to_string()).unwrap_or_default()
}

impl Analysis {
    /// `id` is an `rt` function with a body that the rt stage checks: typed
    /// to its end, in a unit that did not fail in an earlier stage (§18.1).
    /// Only the calls of such a function are edges of the rt recursion (§10
    /// rule 5, S-776). The one test of it ([`check_all`], `crate::unread`).
    pub(crate) fn rt_checked(&self, id: DefId) -> bool {
        self.rt_with_body(id) && self.body_checked(id, Stage::Effects)
    }

    /// `id` is an `rt` function with a written body: a node of the rt calls.
    pub(crate) fn rt_with_body(&self, id: DefId) -> bool {
        matches!(&self.def(id).kind, DefKind::Fn(f) if f.rt && f.body.is_some())
    }
}

/// E0901 for each `rt` scope of the record `r`: its first use (by the
/// place, R-459) that calls what is not `rt` (§10 rule 4, S-77). O(U).
fn first_calls(pkg: &Package, a: &Analysis, r: &Record) -> Vec<Diagnostic> {
    let Some(module) = module_of_def(pkg, a, r.id) else { return Vec::new() };
    let (ast, text) = (&module.parsed.ast, &module.text);
    let src = |span: Span| text[span.start as usize..span.end as usize].to_string();
    let mut seen = HashSet::default();
    let firsts = r.uses.iter().filter(|u| u.rt == Some(false) && r.scopes[u.scope as usize].rt);
    let firsts = firsts.filter(|u| seen.insert(u.scope));
    let diag = |u: &Use| {
        let message = format!(
            "{}, which is not `rt`; an `rt` function calls only `rt` ones (§10 rule 4)",
            u.describe(a, ast, &src)
        );
        let d = Diagnostic::new(Stage::Effects, Code::E0901, u.at, message).with_found(src(u.at));
        match u.what {
            What::Call { callee } => d.with_note(a.def(callee).name_span, "declared here without `rt`"),
            _ => d,
        }
    };
    firsts.map(diag).collect()
}
