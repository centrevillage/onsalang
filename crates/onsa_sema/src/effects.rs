//! Effect-row consistency (T3-13, S-23; spec §8.1, §12.2): a function whose
//! effect row lacks `Alloc` cannot use anything that needs it (E0601).
//! Phase 1 tracks `Alloc` only; other effects are E0200 at the signature.
//! `rt` functions are covered by E0901 / E0902, `test` bodies get `Alloc`
//! from the runner (D-08), and `const` initializers from the compiler (§6.6).

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Ast, ItemKind};

use crate::def::DefKind;
use crate::drop_alloc::Drop;
use crate::uses::{Record, Use, What};
use crate::{Analysis, Package, module_of_def};

/// The E0601 of the bodies of `records` ([`crate::uses::records`]).
pub(crate) fn check_all(pkg: &Package, a: &Analysis, records: &[Record]) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for r in records {
        let def = a.def(r.id);
        let DefKind::Fn(f) = &def.kind else { continue };
        if f.rt || a.uses_alloc(&f.effects) {
            continue;
        }
        let _scope = onsa_diag::internal::item_scope(def.span);
        if let Some(d) = first_use(pkg, a, r) {
            diags.push(d);
        }
    }
    diags
}

/// The earliest use of `Alloc` in the body of `r`, as an E0601 anchored at
/// the signature (so the fix can insert the effect row) with a note at the use.
fn first_use(pkg: &Package, a: &Analysis, r: &Record) -> Option<Diagnostic> {
    let module = module_of_def(pkg, a, r.id)?;
    let ast = &module.parsed.ast;
    let text = &module.text;
    let def = a.def(r.id);
    let src = |span: Span| text[span.start as usize..span.end as usize].to_string();
    let u = r.uses.iter().find(|u| u.needs_alloc(a))?;
    let (at, why) = (u.at, describe(a, ast, &src, u));

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
            Stage::Effects,
            Code::E0601,
            sig,
            format!("`{}` uses `Alloc`, which is not in its effect row; add `uses {{Alloc}}` (§8.1)", def.name),
        )
        .with_found(src(sig))
        .with_fix(Fix::insert("add `uses {Alloc}`", sig.file, sig.end, " uses {Alloc}"))
        .with_note(at, why),
    )
}

/// What the use `u` does that needs `Alloc`, as the note says it.
fn describe(a: &Analysis, ast: &Ast, src: &dyn Fn(Span) -> String, u: &Use) -> String {
    match &u.what {
        What::Call { callee } => format!("calls `{}`, which has `uses {{Alloc}}`", a.def(*callee).name),
        What::ValueCall => "calls a function value whose type has `uses {Alloc}`".into(),
        What::Interp => "string interpolation creates a `Str`".into(),
        What::Drop { drop: d @ Drop::Local(_), .. } => {
            format!("{}, whose destruction needs `Alloc`", dropped(a, ast, src, d, u.at))
        }
        What::Drop { drop, .. } => format!("{}, which needs `Alloc`", dropped(a, ast, src, drop, u.at)),
    }
}

/// What the drop `d` of the value written at `at` drops, as E0601 and
/// E0901 say it before why it needs `Alloc` (§12.2).
pub(crate) fn dropped(a: &Analysis, ast: &Ast, src: &dyn Fn(Span) -> String, d: &Drop, at: Span) -> String {
    let at = src(at);
    match d {
        Drop::Local(l) => format!("`{}` owns a `{}`", l.name, a.display_type(l.ty)),
        Drop::Rest { root, .. } => format!("taking `{at}` out of `{}` drops the rest of it", root.name(ast, src)),
        Drop::Temp { .. } => format!("`{at}` is dropped after it is used"),
        Drop::Value { .. } => format!("`{at}` is dropped by an exit before it is consumed"),
        Drop::Overwrite { .. } => format!("assigning `{at}` drops the value it held"),
        Drop::IterRest { early, .. } => {
            let what = if *early { "what it has not iterated and its container" } else { "its container" };
            format!("the `for` that consumes `{at}` drops {what} when it is left")
        }
        Drop::Discard { .. } => format!("what `{at}` binds to no name is dropped"),
    }
}
