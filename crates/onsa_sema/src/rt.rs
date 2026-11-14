//! `rt` rules (T2-9; spec §10): an `rt` body calls only `rt` functions and
//! never needs `Alloc` (E0901), and `rt` functions do not recurse (E0903).
//! E0902 (`Alloc` in the effect row) is checked with the signature; E0904 /
//! E0905 need effects other than `Alloc` and are phase 2.

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{ExprKind, Lit, StrSeg};

use crate::body::Target;
use crate::def::DefKind;
use crate::drop_alloc::{Drop, alloc_drops};
use crate::ty::Ty;
use crate::{Analysis, DefId, Package, module_of_def};

pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) {
    let mut diags = Vec::new();
    let rt_fns: Vec<DefId> = a.new_defs().filter(|&id| a.rt_checked(id)).collect();
    // Calls of each rt body, in source order: (span, callee) for rt callees.
    let mut edges: HashMap<DefId, Vec<(Span, DefId)>> = HashMap::default();
    for &id in &rt_fns {
        let _scope = onsa_diag::internal::item_scope(a.def(id).span);
        if let Some(d) = body_rules(pkg, a, id) {
            diags.push(d);
            continue;
        }
        edges.insert(id, rt_calls(pkg, a, id));
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
    a.diagnostics.extend(diags);
}

fn src_of(pkg: &Package, a: &Analysis, def: DefId, span: Span) -> String {
    module_of_def(pkg, a, def).map(|m| m.text[span.start as usize..span.end as usize].to_string()).unwrap_or_default()
}

/// Calls to other rt functions from the body of `id`, in source order.
fn rt_calls(pkg: &Package, a: &Analysis, id: DefId) -> Vec<(Span, DefId)> {
    let Some(module) = module_of_def(pkg, a, id) else { return Vec::new() };
    let ast = &module.parsed.ast;
    let body = &a.bodies[&id];
    let mut out: Vec<(Span, DefId)> = body
        .targets
        .iter()
        .filter(|(e, _)| matches!(ast.expr(**e).kind, ExprKind::Call { .. }))
        .filter_map(|(e, t)| match t {
            Target::Fn { def, .. } | Target::Method { def, .. } => Some((ast.expr(*e).span, *def)),
            _ => None,
        })
        .filter(|(_, d)| a.rt_with_body(*d))
        .collect();
    out.sort_by_key(|(s, _)| s.start);
    out
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

/// E0901 for one rt body: the earliest violation in source order.
fn body_rules(pkg: &Package, a: &Analysis, id: DefId) -> Option<Diagnostic> {
    let module = module_of_def(pkg, a, id)?;
    let ast = &module.parsed.ast;
    let text = &module.text;
    let body = &a.bodies[&id];
    let src = |span: Span| text[span.start as usize..span.end as usize].to_string();
    let mut found: Vec<Diagnostic> = Vec::new();

    // Calls.
    for (&e, t) in &body.targets {
        let expr = ast.expr(e);
        let ExprKind::Call { callee, .. } = &expr.kind else { continue };
        let span = expr.span;
        match t {
            Target::Fn { def, .. } | Target::Method { def, .. } => {
                let callee_def = a.def(*def);
                let DefKind::Fn(f) = &callee_def.kind else { continue };
                if !f.rt {
                    let why = if f.effects.alloc { " (it needs `Alloc`)" } else { "" };
                    found.push(
                        Diagnostic::new(
                            Stage::Effects,
                            Code::E0901,
                            span,
                            format!("`rt` function calls `{}`, which is not `rt`{why} (§10 rule 4)", callee_def.name),
                        )
                        .with_found(src(span))
                        .with_note(callee_def.name_span, "declared here without `rt`"),
                    );
                }
            }
            Target::Value => {
                if let Some(t) = body.expr_types.get(callee)
                    && let Ty::Fn(f) = a.types.get(*t)
                    && !f.rt
                {
                    found.push(
                        Diagnostic::new(
                            Stage::Effects,
                            Code::E0901,
                            span,
                            "`rt` function calls a function value whose type is not `rt fn` (§10 rule 4)",
                        )
                        .with_found(src(span)),
                    );
                }
            }
            _ => {}
        }
    }
    // String interpolation builds a new `Str` (§2.4).
    for &e in body.expr_types.keys() {
        let expr = ast.expr(e);
        if let ExprKind::Lit(Lit::Str(s)) = &expr.kind
            && s.segments.iter().any(|seg| matches!(seg, StrSeg::Interp(_)))
        {
            found.push(
                Diagnostic::new(Stage::Effects, Code::E0901, expr.span, "string interpolation creates a `Str` and needs `Alloc`; `rt` functions cannot allocate (§10 rule 1)")
                    .with_found(src(expr.span)),
            );
        }
    }
    // Drops (§12.2) whose destruction needs `Alloc`.
    for d in alloc_drops(a, id) {
        let rt = "`rt` functions cannot allocate (§10, §12.2)";
        let (at, message, left) = match d {
            Drop::Local(l) => (
                l.span,
                format!(
                    "`{}` owns a `{}`, whose destruction needs `Alloc`; an `rt` function can only borrow it or move it on (§10, §12.2)",
                    l.name,
                    a.display_type(l.ty)
                ),
                None,
            ),
            Drop::Rest { at, root, .. } => {
                let of = root.name(ast, src);
                let message = format!(
                    "taking `{}` out of `{of}` drops the rest of it here, whose destruction needs `Alloc`; {rt}",
                    src(at)
                );
                (at, message, None)
            }
            Drop::Temp { value, .. } => {
                let at = ast.expr(value).span;
                let message =
                    format!("`{}` is dropped after it is used, whose destruction needs `Alloc`; {rt}", src(at));
                (at, message, None)
            }
            Drop::Value { value, exit, .. } => {
                let at = ast.expr(value).span;
                let message = format!(
                    "`{}` is dropped by an exit before it is consumed, whose destruction needs `Alloc`; {rt}",
                    src(at)
                );
                (at, message, Some(exit))
            }
            Drop::Overwrite { target, .. } => {
                let at = ast.expr(target).span;
                let message =
                    format!("assigning `{}` drops the value it held, whose destruction needs `Alloc`; {rt}", src(at));
                (at, message, None)
            }
            Drop::IterRest { iter, exit, early, .. } => {
                let (at, what) = (
                    ast.expr(iter).span,
                    if early { "what it has not iterated and its container" } else { "its container" },
                );
                let message = format!(
                    "the `for` that consumes `{}` drops {what} when it is left, whose destruction needs `Alloc`; {rt}",
                    src(at)
                );
                (at, message, early.then_some(exit))
            }
            Drop::Discard { at, .. } => {
                let message =
                    format!("what `{}` binds to no name is dropped, whose destruction needs `Alloc`; {rt}", src(at));
                (at, message, None)
            }
        };
        let d = Diagnostic::new(Stage::Effects, Code::E0901, at, message).with_found(src(at));
        found.push(left.into_iter().fold(d, |d, x| d.with_note(x, "left here")));
    }
    found.sort_by_key(|d| d.span.start);
    found.into_iter().next()
}
