//! `rt` rules (T2-9; spec §10): an `rt` body calls only `rt` functions
//! (E0901, rule 4), and `rt` functions do not recurse (E0903, rule 5). E0901
//! reads the record of the uses of a body, and E0903 the calls of the body
//! itself (`crate::uses`, D-15); what needs `Alloc` there is an E0601
//! (`crate::effects`, rule 1, S-77).
//! E0902 (`Alloc` in the effect row) is checked with the signature; E0904 /
//! E0905 need effects other than `Alloc` and are phase 2.

use std::collections::{BTreeMap, VecDeque};

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, StmtKind};

use crate::body::{RowFrom, Target};
use crate::def::DefKind;
use crate::names::body::Origin;
use crate::names::{cyclic, file_key};
use crate::uses::{Record, Use, What, rt_edges};
use crate::{Analysis, DefId, Package, flatten, module_of_def};

/// The E0901 of the `rt` scopes of `records` ([`crate::uses::records`]):
/// of an `rt` function and of an anonymous function of an `rt` type, in a
/// body `rt` or not (§8.1); and the E0903 of the `rt` functions, at the
/// call of each set that [`cycle_calls`] gives.
pub(crate) fn check_all(pkg: &Package, a: &Analysis, records: &[Record]) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    // The rt functions the rt stage checks, and the calls of each body, by
    // their place: (span, callee) for rt callees.
    let (mut fns, mut edges): (Vec<DefId>, Vec<Vec<(Span, DefId)>>) = (Vec::new(), Vec::new());
    for r in records {
        let _scope = onsa_diag::internal::item_scope(a.def(r.id).span);
        let calls = first_calls(pkg, a, r);
        // A body with an error of this stage in any scope adds no edge (§10 rule 5).
        let quiet = calls.is_empty() && r.lacking(a).is_empty();
        diags.extend(calls);
        if !quiet || !a.rt_checked(r.id) {
            continue;
        }
        if let Some(m) = module_of_def(pkg, a, r.id) {
            fns.push(r.id);
            edges.push(rt_edges(a, &m.parsed.ast, &a.bodies[&r.id]));
        }
    }
    // E0903: one for each set of rt functions that reach each other (§10 rule 5, §18.1).
    let index: HashMap<DefId, usize> = fns.iter().enumerate().map(|(i, &f)| (f, i)).collect();
    let calls: Vec<Vec<RtCall>> =
        edges.iter().map(|e| e.iter().filter_map(|&(at, to)| Some((*index.get(&to)?, at))).collect()).collect();
    let flat = flatten(pkg);
    let file = |f: usize| Some(file_key(&flat, &a.modules, a.def(fns[f]).module));
    for first in cycle_calls(&calls, file) {
        let (from, to) = (fns[first.caller], fns[first.callee]);
        let path: Vec<String> = first.way.iter().map(|&f| a.shown_name(fns[f])).collect();
        let what = if from == to { "calls itself" } else { "is mutually recursive" };
        let message =
            format!("`{}` {what}: `rt` functions cannot recurse (§10); cycle: {}", path[0], path.join(" -> "));
        let d =
            Diagnostic::new(Stage::Effects, Code::E0903, first.at, message).with_found(src_of(pkg, a, from, first.at));
        diags.push(d.with_note(a.def(to).name_span, "recursion target declared here"));
    }
    diags
}

/// A call in the graph of the calls of `rt` functions ([`cycle_calls`]):
/// the index of the function it calls, and where it is.
pub type RtCall = (usize, Span);

/// The call an E0903 is at: `caller` calls `callee` at `at`; `way` is the
/// shortest way of calls in their set from `caller` through `callee` back
/// to `caller`.
pub struct CycleCall {
    pub caller: usize,
    pub callee: usize,
    pub at: Span,
    pub way: Vec<usize>,
}

/// The place of the E0903 of each set of the functions of `calls` that
/// reach each other ([`cyclic`]: a function that calls itself is a set):
/// of the calls a function of the set makes of one of the set, the first by
/// the file of the caller (`file`, S-313) and the place (§18.1). A call from
/// outside the set is not counted, nor one of a caller `file` gives `None`
/// (of Core, what lowering alone makes, S-914). This stage and the E0903 of
/// Core (`onsa_core::rt_cycles`) read it; in the order of the sets. O(F + C)
/// for F functions and C calls, and a file key for each function in a set.
pub fn cycle_calls(calls: &[Vec<RtCall>], file: impl Fn(usize) -> Option<String>) -> Vec<CycleCall> {
    let edges: Vec<Vec<usize>> = calls.iter().map(|c| c.iter().map(|&(to, _)| to).collect()).collect();
    let (comp, cycled) = cyclic(&edges);
    let mut firsts: BTreeMap<usize, ((String, u32, u32), CycleCall)> = BTreeMap::new();
    for caller in (0..calls.len()).filter(|&f| cycled[f]) {
        let Some(file) = file(caller) else { continue };
        for &(callee, at) in calls[caller].iter().filter(|&&(to, _)| comp[to] == comp[caller]) {
            let order = (file.clone(), at.start, at.end);
            if firsts.get(&comp[caller]).is_none_or(|(first, _)| order < *first) {
                firsts.insert(comp[caller], (order, CycleCall { caller, callee, at, way: Vec::new() }));
            }
        }
    }
    let way = |c: CycleCall| CycleCall { way: way_back(&edges, &comp, c.caller, c.callee), ..c };
    firsts.into_values().map(|(_, c)| way(c)).collect()
}

/// The shortest way of `edges` in the set of `caller`: `caller`, `callee`,
/// and on to `caller` again.
fn way_back(edges: &[Vec<usize>], comp: &[usize], caller: usize, callee: usize) -> Vec<usize> {
    let mut before = HashMap::default();
    let mut queue = VecDeque::from([callee]);
    while let Some(f) = queue.pop_front() {
        if f == caller {
            break;
        }
        for &to in edges[f].iter().filter(|&&to| comp[to] == comp[f]) {
            if to != callee && !before.contains_key(&to) {
                before.insert(to, f);
                queue.push_back(to);
            }
        }
    }
    let mut way = vec![caller];
    while let Some(&f) = way.last().and_then(|f| before.get(f)) {
        way.push(f);
    }
    way.push(caller);
    way.reverse();
    way
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
            u.describe(a, (ast, r.id), &src)
        );
        let d = Diagnostic::new(Stage::Effects, Code::E0901, u.at, message).with_found(src(u.at));
        match u.what {
            What::Call { callee } => d.with_note(a.def(callee).name_span, "declared here without `rt`"),
            What::ValueCall { callee } => match written_with_no_type(a, ast, r.id, callee) {
                Some((at, why)) => d.with_note(at, why),
                None => d,
            },
            _ => d,
        }
    };
    firsts.map(diag).collect()
}

/// The note of the E0901 of a call of the local `callee` names (S-1041 (3),
/// §10): where a `let` or a `var` binds it to an anonymous function no
/// function type is expected for (§8.1, `RowFrom::NoneExpected`), the `rt`
/// type to write. None of another value. The text is no promise.
fn written_with_no_type(a: &Analysis, ast: &Ast, id: DefId, callee: ExprId) -> Option<(Span, String)> {
    let body = &a.bodies[&id];
    let Some(Target::Local(l)) = body.targets.get(&callee) else { return None };
    let (kw, s) = match a.names.get(&id)?.bindings[l.0 as usize].origin {
        Origin::Let(s) => ("let", s),
        Origin::Var(s) => ("var", s),
        _ => return None,
    };
    let (StmtKind::Let { init, .. } | StmtKind::Var { init, .. }) = &ast.stmt(s).kind else { return None };
    if body.closure_rows.get(init) != Some(&RowFrom::NoneExpected) {
        return None;
    }
    let local = &body.locals[l.0 as usize];
    let ty = a.display_in(local.ty, id);
    let why = format!(
        "no function type is expected where `{0}` is bound to an anonymous function, so it is not `rt`; write the type: `{kw} {0}: rt {ty} = …` (§10, §8.1)",
        local.name
    );
    Some((ast.stmt(s).span, why))
}
