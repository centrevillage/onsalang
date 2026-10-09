//! `rt` rules (T2-9; spec §10): an `rt` body calls only `rt` functions and
//! never needs `Alloc` (E0901), and `rt` functions do not recurse (E0903).
//! E0902 (`Alloc` in the effect row) is checked with the signature; E0904 /
//! E0905 need effects other than `Alloc` and are phase 2.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{ExprKind, Lit, Mode, StmtKind, StrSeg};

use crate::body::{LocalKind, Target};
use crate::def::{DefKind, Fields};
use crate::modes::MovedLocals;
use crate::ty::{BuiltinTy, Ty, TyId};
use crate::{Analysis, DefId, Package, module_of_def};

pub(crate) fn check_all(pkg: &Package, a: &mut Analysis, moved: &MovedLocals) {
    let mut diags = Vec::new();
    let mut rt_fns: Vec<DefId> = Vec::new();
    for (i, def) in a.defs.iter().enumerate() {
        if let DefKind::Fn(f) = &def.kind
            && f.rt
            && f.body.is_some()
            && a.bodies.get(&DefId(i as u32)).is_some_and(|b| b.complete)
        {
            rt_fns.push(DefId(i as u32));
        }
    }
    // Calls of each rt body, in source order: (span, callee) for rt callees.
    let mut edges: HashMap<DefId, Vec<(Span, DefId)>> = HashMap::new();
    for &id in &rt_fns {
        let _scope = onsa_diag::internal::item_scope(a.def(id).span);
        if let Some(d) = body_rules(pkg, a, id, moved.get(&id)) {
            diags.push(d);
            continue;
        }
        edges.insert(id, rt_calls(pkg, a, id));
    }
    // E0903: cycles in the rt call graph (§10 rule 5), each reported once at
    // the call that closes it.
    let mut color: HashMap<DefId, u8> = HashMap::new(); // 1 = on stack, 2 = done
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
                        path.push(a.def(cycle_edges[(start_idx + k) % cycle_edges.len()].0).name.clone());
                    }
                    path.push(a.def(from).name.clone());
                    let what = if cycle.len() == 1 { "calls itself" } else { "is mutually recursive" };
                    let d = Diagnostic::new(
                        Stage::Effects,
                        Code::E0903,
                        at,
                        format!(
                            "`{}` {what}: `rt` functions cannot recurse (§10); cycle: {}",
                            a.def(from).name,
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
        .filter(|(_, d)| matches!(&a.def(*d).kind, DefKind::Fn(f) if f.rt && f.body.is_some()))
        .collect();
    out.sort_by_key(|(s, _)| s.start);
    out
}

/// E0901 for one rt body: the earliest violation in source order.
fn body_rules(
    pkg: &Package,
    a: &Analysis,
    id: DefId,
    moved: Option<&HashSet<crate::body::LocalId>>,
) -> Option<Diagnostic> {
    let module = module_of_def(pkg, a, id)?;
    let ast = &module.parsed.ast;
    let text = &module.text;
    let body = &a.bodies[&id];
    let def_span = a.def(id).span;
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
            Target::BuiltinMethod { recv, name, .. } => {
                if name == "zeroed" && matches!(a.types.get(*recv), Ty::Builtin(BuiltinTy::Buf, _)) {
                    found.push(
                        Diagnostic::new(
                            Stage::Effects,
                            Code::E0901,
                            span,
                            "`Buf.zeroed` allocates and needs `Alloc`; `rt` functions cannot allocate (§10 rule 1)",
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
    // Drops (§12.2): an owned value whose destruction needs `Alloc` and that is not moved on.
    for (i, l) in body.locals.iter().enumerate() {
        let owned = !l.borrow
            && matches!(
                l.kind,
                LocalKind::Let
                    | LocalKind::Var
                    | LocalKind::Param(Mode::Move)
                    | LocalKind::SelfParam(Mode::Move)
                    | LocalKind::ClosureParam(Mode::Move)
                    | LocalKind::For { moved: true }
                    | LocalKind::MatchBind
            );
        if !owned || moved.is_some_and(|m| m.contains(&crate::body::LocalId(i as u32))) {
            continue;
        }
        if needs_alloc_drop(a, l.ty, &mut HashSet::new()) {
            let shown = a.display_type(l.ty);
            found.push(
                Diagnostic::new(
                    Stage::Effects, Code::E0901,
                    l.span,
                    format!(
                        "`{}` owns a `{shown}`, whose destruction needs `Alloc`; an `rt` function can only borrow it or move it on (§10, §12.2)",
                        l.name
                    ),
                )
                .with_found(src(l.span)),
            );
        }
    }
    // A temporary dropped by an expression statement.
    for stmt in &ast.stmts {
        if !def_span.contains(stmt.span.start) {
            continue;
        }
        if let StmtKind::Expr(e) = &stmt.kind
            && let Some(t) = body.expr_types.get(e)
            && needs_alloc_drop(a, *t, &mut HashSet::new())
        {
            let shown = a.display_type(*t);
            found.push(
                Diagnostic::new(
                    Stage::Effects, Code::E0901,
                    stmt.span,
                    format!("this `{shown}` is dropped here, which needs `Alloc`; `rt` functions cannot allocate (§10, §12.2)"),
                )
                .with_found(src(stmt.span)),
            );
        }
    }
    found.sort_by_key(|d| d.span.start);
    found.into_iter().next()
}

/// Whether dropping a value of this type needs `Alloc` (§12.2): Shared values
/// and `Buf`, or anything containing them. Flow state is Affine but drops freely.
pub(crate) fn needs_alloc_drop(a: &Analysis, t: TyId, visiting: &mut HashSet<DefId>) -> bool {
    match a.types.get(t) {
        Ty::Builtin(
            BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Buf,
            _,
        ) => true,
        Ty::Builtin(_, args) => args.iter().any(|&x| needs_alloc_drop(a, x, visiting)),
        Ty::Array(el, _) => needs_alloc_drop(a, *el, visiting),
        Ty::Tuple(ts) => ts.iter().any(|&x| needs_alloc_drop(a, x, visiting)),
        Ty::Named(d, args) => {
            if !visiting.insert(*d) {
                return false;
            }
            let r = match &a.def(*d).kind {
                DefKind::Struct(s) => match &s.fields {
                    Fields::Named(fs) => {
                        fs.iter().any(|f| needs_alloc_drop(a, crate::layout::subst(a, f.ty, args), visiting))
                    }
                    Fields::Tuple(x) => needs_alloc_drop(a, crate::layout::subst(a, *x, args), visiting),
                    Fields::Opaque => false,
                },
                DefKind::Enum(e) => e
                    .variants
                    .iter()
                    .flat_map(|v| v.fields.iter())
                    .any(|&x| needs_alloc_drop(a, crate::layout::subst(a, x, args), visiting)),
                DefKind::Alias(x) => needs_alloc_drop(a, *x, visiting),
                _ => false,
            };
            visiting.remove(d);
            r
        }
        _ => false,
    }
}
