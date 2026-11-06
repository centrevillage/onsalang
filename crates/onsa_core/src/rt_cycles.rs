//! The recursion of `rt` functions that only the instances close (spec §10
//! rule 5, S-911): `T.default()` and what a derive makes reach a function by
//! the types, so a cycle through them has no name for `onsa_sema::rt` to see.
//! Core has every call an instance makes, so the cycles are the ones of its
//! calls, and each is an E0903 of lowering (§18.1).
//!
//! The graph is of the `rt` functions alone: an `rt` function calls only `rt`
//! functions (E0901), so a cycle with one in it has no other. A function used
//! as a value is no call (§12.5; lowered by W8-09). A cycle is reported when it
//! has a function written in the source: what lowering alone makes may recur
//! on a recursive type (`__eq`, S-914). O(F + C) for F functions and C calls,
//! no recursion over the functions.

use std::collections::{BTreeMap, HashMap, VecDeque};

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_sema::def::DefKind;
use onsa_sema::{Analysis, DefId, Package, cyclic, file_key};

use crate::ir::{ExprKind, FnDef, Module};
use crate::walk::walk_block;

/// A call in a body: the index of the function it calls, and where it is.
type Call = (usize, Span);

/// The first call of a cycle that a function written in the source makes.
struct First {
    /// Its place in the order of the diagnostics: the file by its path in
    /// the package (S-313), and the place in the file.
    order: (String, u32, u32),
    caller: usize,
    callee: usize,
    at: Span,
}

/// The E0903 of each cycle of `rt` functions of `m` that has a function
/// written in the source. A cycle is a strongly connected component: what
/// shares a function is one cycle (§18.1).
pub(crate) fn rt_cycles(m: &Module, a: &Analysis, flat: &[&Package]) -> Vec<Diagnostic> {
    let calls: Vec<Vec<Call>> = m.fns.iter().map(|f| rt_calls(m, f)).collect();
    let edges: Vec<Vec<usize>> = calls.iter().map(|c| c.iter().map(|&(to, _)| to).collect()).collect();
    let (comp, cycled) = cyclic(&edges);
    let mut firsts: BTreeMap<usize, First> = BTreeMap::new();
    for (caller, def) in m.fns.iter().enumerate().filter(|&(f, _)| cycled[f]) {
        let Some(decl) = written(a, def) else { continue };
        let file = file_key(flat, &a.modules, a.def(decl).module);
        for &(callee, at) in calls[caller].iter().filter(|&&(to, _)| comp[to] == comp[caller]) {
            let order = (file.clone(), at.start, at.end);
            if firsts.get(&comp[caller]).is_none_or(|first| order < first.order) {
                firsts.insert(comp[caller], First { order, caller, callee, at });
            }
        }
    }
    firsts.into_values().map(|first| diagnostic(m, a, &calls, &comp, &first)).collect()
}

/// The calls of the `rt` function `f` of `rt` functions, in evaluation order.
fn rt_calls(m: &Module, f: &FnDef) -> Vec<Call> {
    let mut calls = Vec::new();
    if let (true, Some(body)) = (f.rt, &f.body) {
        walk_block(body, &mut |e| {
            if let ExprKind::Call { fn_, .. } = &e.kind
                && m.fn_(*fn_).rt
            {
                calls.push((fn_.0 as usize, e.span));
            }
        });
    }
    calls
}

/// The declaration of `f` when `f` is written in the source: what a derive
/// makes and what a flow generates are declared with no body.
fn written(a: &Analysis, f: &FnDef) -> Option<DefId> {
    f.decl.filter(|&d| matches!(&a.def(d).kind, DefKind::Fn(s) if s.body.is_some()))
}

/// The E0903 at the call `first`. Its text has the two ends of that call, and
/// not the instances: the same call of two instances is one diagnostic
/// (§18.1). The note is the way back to the caller, by the declarations.
fn diagnostic(m: &Module, a: &Analysis, calls: &[Vec<Call>], comp: &[usize], first: &First) -> Diagnostic {
    let way = way_back(calls, comp, first);
    let decls: Vec<_> = way.iter().filter_map(|&f| m.fns[f].decl).collect();
    let path: Vec<String> = decls.iter().map(|&d| a.shown_name(d)).collect();
    // The caller is written, so it is at both ends of `decls`.
    let target = decls[1];
    let message = format!("`{}` recurses through `{}`: `rt` functions cannot recurse (§10)", path[0], path[1]);
    Diagnostic::new(Stage::Build, Code::E0903, first.at, message)
        .with_note(a.def(target).name_span, format!("recursion target declared here; cycle: {}", path.join(" -> ")))
}

/// The shortest way of calls in the cycle of `first`: the caller, the callee,
/// and on to the caller again.
fn way_back(calls: &[Vec<Call>], comp: &[usize], first: &First) -> Vec<usize> {
    let mut before = HashMap::new();
    let mut queue = VecDeque::from([first.callee]);
    while let Some(f) = queue.pop_front() {
        if f == first.caller {
            break;
        }
        for &(to, _) in calls[f].iter().filter(|&&(to, _)| comp[to] == comp[f]) {
            if to != first.callee && !before.contains_key(&to) {
                before.insert(to, f);
                queue.push_back(to);
            }
        }
    }
    let mut way = vec![first.caller];
    while let Some(&f) = way.last().and_then(|f| before.get(f)) {
        way.push(f);
    }
    way.push(first.caller);
    way.reverse();
    way
}
