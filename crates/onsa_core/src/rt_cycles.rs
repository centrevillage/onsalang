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

use onsa_diag::{Code, Diagnostic, Stage};
use onsa_sema::def::DefKind;
use onsa_sema::{Analysis, CycleCall, DefId, Package, RtCall, cycle_calls, file_key};

use crate::ir::{ExprKind, FnDef, Module};
use crate::walk::walk_block;

/// The E0903 of each cycle of `rt` functions of `m` that has a function
/// written in the source. A cycle is a strongly connected component: what
/// shares a function is one cycle (§18.1). The call it is at is the one of
/// `onsa_sema::rt` ([`cycle_calls`]), of the written functions.
pub(crate) fn rt_cycles(m: &Module, a: &Analysis, flat: &[&Package]) -> Vec<Diagnostic> {
    let calls: Vec<Vec<RtCall>> = m.fns.iter().map(|f| rt_calls(m, f)).collect();
    let file = |f: usize| written(a, &m.fns[f]).map(|decl| file_key(flat, &a.modules, a.def(decl).module));
    cycle_calls(&calls, file).iter().map(|first| diagnostic(m, a, first)).collect()
}

/// The calls of the `rt` function `f` of `rt` functions, in evaluation order.
fn rt_calls(m: &Module, f: &FnDef) -> Vec<RtCall> {
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
fn diagnostic(m: &Module, a: &Analysis, first: &CycleCall) -> Diagnostic {
    let decls: Vec<_> = first.way.iter().filter_map(|&f| m.fns[f].decl).collect();
    let path: Vec<String> = decls.iter().map(|&d| a.shown_name(d)).collect();
    // The caller is written, so it is at both ends of `decls`.
    let target = decls[1];
    let message = format!("`{}` recurses through `{}`: `rt` functions cannot recurse (§10)", path[0], path[1]);
    Diagnostic::new(Stage::Build, Code::E0903, first.at, message)
        .with_note(a.def(target).name_span, format!("recursion target declared here; cycle: {}", path.join(" -> ")))
}
