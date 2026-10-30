//! `rt` rules (T2-9; spec §10): an `rt` body calls only `rt` functions and
//! never needs `Alloc` (E0901), and `rt` functions do not recurse (E0903).
//! E0902 (`Alloc` in the effect row) is checked with the signature; E0904 /
//! E0905 need effects other than `Alloc` and are phase 2.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{ExprKind, Lit, StmtKind, StrSeg};

use crate::body::{BodyInfo, Step, Target};
use crate::def::DefKind;
use crate::modes::MovedLocals;
use crate::ty::{BuiltinTy, Env, Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId, Package, module_of_def};

pub(crate) fn check_all(pkg: &Package, a: &mut Analysis, moved: &MovedLocals) {
    let mut diags = Vec::new();
    let rt_fns: Vec<DefId> = (0..a.defs.len() as u32).map(DefId).filter(|&id| a.rt_checked(id)).collect();
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
        let owned = l.state.owned();
        if !owned || moved.is_some_and(|m| m.contains(&crate::body::LocalId(i as u32))) {
            continue;
        }
        if needs_alloc_drop(a, l.ty) {
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
    // The rest of a value a field is taken out of (S-85).
    for (at, root) in rest_drops(a, body) {
        let message = format!(
            "taking `{}` out of `{root}` drops the rest of it here, whose destruction needs `Alloc`; `rt` functions cannot allocate (§10, §12.2)",
            src(at)
        );
        found.push(Diagnostic::new(Stage::Effects, Code::E0901, at, message).with_found(src(at)));
    }
    // A temporary dropped by an expression statement.
    for stmt in &ast.stmts {
        if !def_span.contains(stmt.span.start) {
            continue;
        }
        if let StmtKind::Expr(e) = &stmt.kind
            && let Some(t) = body.expr_types.get(e)
            && needs_alloc_drop(a, *t)
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
pub(crate) fn needs_alloc_drop(a: &Analysis, t: TyId) -> bool {
    drops_alloc(&Walk::new(a), t, None, 0).unwrap_or(false)
}

/// The fields taken out of a value in `body` whose rest needs `Alloc` to
/// drop (S-85, §12.2): where, and the name of the value.
pub(crate) fn rest_drops<'b>(a: &'b Analysis, body: &'b BodyInfo) -> impl Iterator<Item = (Span, &'b str)> {
    body.taken.iter().filter_map(move |t| {
        let local = &body.locals[t.root.0 as usize];
        // As `needs_alloc_drop`: a walk that stops is no answer, so no use.
        let rest = rest_drops_alloc(&Walk::new(a), (local.ty, None, 0), &t.path, t.at).unwrap_or(false);
        rest.then_some((t.at, local.name.as_str()))
    })
}

/// Whether dropping what is left of a value of the type `t` (read under
/// `env`, `depth` named types in) when `path` is taken out of it at `at`
/// needs `Alloc`: the parts beside each step ([`drops_alloc`]).
fn rest_drops_alloc(w: &Walk, (t, env, depth): (TyId, Option<&Env>, u32), path: &[Step], at: Span) -> Option<bool> {
    let Some((step, more)) = path.split_first() else { return Some(false) };
    let (ty, env) = w.at(t, env)?;
    let taken = |name: &str| matches!(step, Step::Field(n) if n == name);
    let (parts, inner, depth): (Vec<_>, _, _) = match (ty, step) {
        (Ty::Tuple(ts), Step::Elem(i)) => {
            (ts.iter().enumerate().map(|(k, &t)| (t, k as u32 == *i)).collect(), None, depth)
        }
        (Ty::Named(d, args), _) => match w.enter(*d, args, env, (depth, None))? {
            (Holds::Alias(t), inner, depth) => return rest_drops_alloc(w, (t, inner.as_ref(), depth), path, at),
            (Holds::Fields(fs, _), inner, depth) => (fs.iter().map(|f| (f.ty, taken(&f.name))).collect(), inner, depth),
            _ => (Vec::new(), None, depth),
        },
        _ => (Vec::new(), None, depth),
    };
    // A tuple's parts are read under `env`, the fields under their declaration's.
    let env = if inner.is_some() { inner.as_ref() } else { env };
    let mut on = None;
    for (t, taken) in parts {
        match taken {
            true => on = Some(t),
            false if drops_alloc(w, t, env, depth)? => return Some(true),
            false => {}
        }
    }
    let Some(t) = on else { onsa_diag::internal::bug(Some(at), "a field taken out that its type does not have") };
    rest_drops_alloc(w, (t, env, depth), more, at)
}

/// [`needs_alloc_drop`] of `t` read under `env` (R-30), `depth` named types
/// in; `None` when the walk stops ([`Walk`]; a type that holds itself: no).
fn drops_alloc(w: &Walk, t: TyId, env: Option<&Env>, depth: u32) -> Option<bool> {
    fn any(w: &Walk, ts: &[TyId], env: Option<&Env>, depth: u32) -> Option<bool> {
        for &t in ts {
            if drops_alloc(w, t, env, depth)? {
                return Some(true);
            }
        }
        Some(false)
    }
    let (ty, env) = w.at(t, env)?;
    match ty {
        Ty::Builtin(
            BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Buf,
            _,
        ) => Some(true),
        // A `Ptr` (Copy, §4.1) and a `Span` (a view) own nothing to drop.
        Ty::Builtin(BuiltinTy::Ptr | BuiltinTy::Span, _) => Some(false),
        Ty::Builtin(_, ts) | Ty::Tuple(ts) => any(w, ts, env, depth),
        Ty::Array(el, _) => drops_alloc(w, *el, env, depth),
        Ty::Named(d, args) => w.remember(&w.a.known.drops, (*d, args, env, depth), |depth, key| {
            let (holds, env, depth) = w.enter(*d, args, env, (depth, key))?;
            any(w, &holds.parts(), env.as_ref(), depth)
        }),
        _ => Some(false),
    }
}
