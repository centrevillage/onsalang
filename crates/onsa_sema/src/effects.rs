//! Effect-row consistency (T3-13, S-23; spec §8.1, §12.2): a function whose
//! effect row lacks `Alloc` cannot use anything that needs it (E0601).
//! Phase 1 tracks `Alloc` only; other effects are E0200 at the signature.
//! `rt` functions are covered by E0901 / E0902, `test` bodies get `Alloc`
//! from the runner (D-08), and `const` initializers from the compiler (§6.6).

use std::collections::HashSet;

use onsa_diag::{Code, Diagnostic, Fix, Span};
use onsa_syntax::ast::{ExprKind, ItemKind, Lit, Mode, StmtKind, StrSeg};

use crate::body::{LocalKind, Target};
use crate::def::DefKind;
use crate::modes::MovedLocals;
use crate::rt::needs_alloc_drop;
use crate::ty::{BuiltinTy, Ty};
use crate::{Analysis, DefId, Package, module_of_def};

pub(crate) fn check_all(pkg: &Package, a: &mut Analysis, moved: &MovedLocals) {
    let mut diags = Vec::new();
    for (i, def) in a.defs.iter().enumerate() {
        let id = DefId(i as u32);
        let DefKind::Fn(f) = &def.kind else { continue };
        if f.rt || f.effects.alloc || f.body.is_none() || !a.bodies.get(&id).is_some_and(|b| b.complete) {
            continue;
        }
        let _scope = onsa_diag::internal::item_scope(def.span);
        if let Some(d) = first_use(pkg, a, id, moved.get(&id)) {
            diags.push(d);
        }
    }
    a.diagnostics.extend(diags);
}

/// The earliest use of `Alloc` in the body of `id`, as an E0601 anchored at
/// the signature (so the fix can insert the effect row) with a note at the use.
fn first_use(
    pkg: &Package,
    a: &Analysis,
    id: DefId,
    moved: Option<&HashSet<crate::body::LocalId>>,
) -> Option<Diagnostic> {
    let module = module_of_def(pkg, a, id)?;
    let ast = &module.parsed.ast;
    let text = &module.text;
    let body = &a.bodies[&id];
    let def = a.def(id);
    let src = |span: Span| text[span.start as usize..span.end as usize].to_string();
    let mut uses: Vec<(Span, String)> = Vec::new();

    for (&e, t) in &body.targets {
        let expr = ast.expr(e);
        let ExprKind::Call { callee, .. } = &expr.kind else { continue };
        match t {
            Target::Fn { def: callee_def, .. } | Target::Method { def: callee_def, .. } => {
                if let DefKind::Fn(cf) = &a.def(*callee_def).kind
                    && cf.effects.alloc
                {
                    uses.push((expr.span, format!("calls `{}`, which has `uses {{Alloc}}`", a.def(*callee_def).name)));
                }
            }
            Target::Value => {
                if let Some(t) = body.expr_types.get(callee)
                    && let Ty::Fn(f) = a.types.get(*t)
                    && f.effects.alloc
                {
                    uses.push((expr.span, "calls a function value whose type has `uses {Alloc}`".into()));
                }
            }
            Target::BuiltinMethod { recv, name, .. } => {
                if name == "zeroed" && matches!(a.types.get(*recv), Ty::Builtin(BuiltinTy::Buf, _)) {
                    uses.push((expr.span, "`Buf.zeroed` allocates".into()));
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
            uses.push((expr.span, "string interpolation creates a `Str`".into()));
        }
    }
    // Drops (§12.2): owned values whose destruction needs `Alloc`, unless moved on.
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
            uses.push((
                l.span,
                format!("`{}` owns a `{}`, whose destruction needs `Alloc`", l.name, a.display_type(l.ty)),
            ));
        }
    }
    for stmt in &ast.stmts {
        if !def.span.contains(stmt.span.start) {
            continue;
        }
        if let StmtKind::Expr(e) = &stmt.kind
            && let Some(t) = body.expr_types.get(e)
            && needs_alloc_drop(a, *t, &mut HashSet::new())
        {
            uses.push((stmt.span, format!("a `{}` is dropped here, which needs `Alloc`", a.display_type(*t))));
        }
    }
    uses.sort_by_key(|(s, _)| s.start);
    let (at, why) = uses.into_iter().next()?;

    // Anchor: the signature, from the name to just before the body, so that
    // `fixes` can append the effect row (§18.1).
    let body_start = def
        .item
        .and_then(|it| match &ast.item(it).kind {
            ItemKind::Fn(f) => f.body,
            _ => None,
        })
        .map(|b| ast.expr(b).span.start)
        .unwrap_or(def.span.end);
    let mut sig_end = body_start as usize;
    while sig_end > def.name_span.start as usize && text.as_bytes()[sig_end - 1].is_ascii_whitespace() {
        sig_end -= 1;
    }
    let sig = Span::new(def.name_span.file, def.name_span.start, sig_end as u32);
    Some(
        Diagnostic::new(
            Code::E0601,
            sig,
            format!("`{}` uses `Alloc`, which is not in its effect row; add `uses {{Alloc}}` (§8.1)", def.name),
        )
        .with_found(src(sig))
        .with_fix(Fix::InsertAfter { insert_after: " uses {Alloc}".into() })
        .with_note(at, why),
    )
}
