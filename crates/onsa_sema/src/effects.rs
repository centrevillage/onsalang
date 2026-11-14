//! Effect-row consistency (T3-13, S-23, S-77, S-82; spec §8.1, §10, §12.2):
//! a body cannot use an effect its row lacks (E0601), at the first use of it
//! (S-783), `rt` or not. Phase 1 tracks `Alloc` only (`Record::lacking`);
//! other effects are E0200 at the signature. `test` bodies get `Alloc` from
//! the runner (D-08), and `const` initializers from the compiler (§6.6).

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{ItemKind, TypeKind};

use crate::def::DefKind;
use crate::resolve::Entity;
use crate::uses::{Record, Scope, Use};
use crate::{Analysis, DefId, Package, module_of_def};

/// The E0601 of the bodies of `records` ([`crate::uses::records`]): for
/// each, one for each effect its row lacks.
pub(crate) fn check_all(pkg: &Package, a: &Analysis, records: &[Record]) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for r in records {
        let _scope = onsa_diag::internal::item_scope(a.def(r.id).span);
        diags.extend(r.lacking(a).into_iter().filter_map(|(scope, effect, u)| first_use(pkg, a, r, scope, effect, u)));
    }
    diags
}

/// The E0601 of `u`, the first use in `scope` of the body of `r` of
/// `effect`, which its row lacks: at the use (S-82, S-783). Where the
/// function is not `rt`, the fix inserts the effect into the signature; an
/// `rt` one cannot have `Alloc` (§10 rule 1), which a note says, with no fix.
/// An anonymous function has no fix, and a note says how its row is decided
/// (§8.1, S-1041).
fn first_use(pkg: &Package, a: &Analysis, r: &Record, scope: &Scope, effect: DefId, u: &Use) -> Option<Diagnostic> {
    let module = module_of_def(pkg, a, r.id)?;
    let (ast, text) = (&module.parsed.ast, &module.text);
    let def = a.def(r.id);
    let src = |span: Span| text[span.start as usize..span.end as usize].to_string();
    let name = &a.def(effect).name;
    let of = scope.closure.map_or_else(|| format!("`{}`", def.name), |_| "the anonymous function".into());
    let message =
        format!("{}: that needs `{name}`, which is not in the effect row of {of} (§8.1)", u.describe(a, ast, &src));
    let d = Diagnostic::new(Stage::Effects, Code::E0601, u.at, message).with_found(src(u.at));
    let d = u.left_at().into_iter().fold(d, |d, x| d.with_note(x, "left here"));
    if let Some(c) = scope.closure {
        // SPEC-GAP(S-1041): no fix; one note of how its row is decided (W6-03 U6).
        let head = ast.expr(c).span;
        let why = "an anonymous function has the effect row it writes, else that of the function type expected where it is, else none (§8.1)";
        return Some(d.with_note(Span::new(head.file, head.start, head.start + 2), why));
    }
    let DefKind::Fn(_) = &def.kind else { return Some(d) };
    if scope.rt {
        let why = format!("`{}` is `rt`, which cannot have `{name}` in its effect row (§10 rule 1)", def.name);
        return Some(d.with_note(def.name_span, why));
    }
    // SPEC-GAP(S-1060): no fix where the name does not name the effect in the
    // module (an item of it, an E0304): the row would read that (§18.1).
    if a.modules.lookup(def.module, name, &a.prelude) != Some(Entity::Def(effect)) {
        return Some(d);
    }

    // The fix (§18.1): into the row of the function where it has one (after
    // its last effect or its `{`, W3-02/b); else a row after the signature,
    // where a result that is a function type with no parentheses goes in
    // them, or the row would be its own (`-> (fn(I32) -> I32) uses {Alloc}`,
    // R-455, the rule of S-364 on the type as written).
    let decl = def.item.and_then(|it| match &ast.item(it).kind {
        ItemKind::Fn(f) => Some(f),
        _ => None,
    });
    let (title, file) = (format!("add `uses {{{name}}}`"), def.name_span.file);
    if let Some(row) = decl.and_then(|f| f.effects.as_ref()) {
        let (at, sep) = row.effects.last().map_or((row.span.start + 1, ""), |p| (p.span.end, ", "));
        return Some(d.with_fix(Fix::insert(title, file, at, format!("{sep}{name}"))));
    }
    let row = format!(" uses {{{name}}}");
    if let Some(t) = decl.and_then(|f| f.ret).map(|t| ast.ty(t))
        && t.parens == 0
        && matches!(t.kind, TypeKind::Fn { .. })
    {
        let edits = vec![Edit::insert(file, t.span.start, "("), Edit::insert(file, t.span.end, format!("){row}"))];
        return Some(d.with_fix(Fix::new(title, edits)));
    }
    let body_start = decl.and_then(|f| f.body).map_or(def.span.end, |b| ast.expr(b).span.start);
    let mut sig_end = body_start as usize;
    while sig_end > def.name_span.start as usize && text.as_bytes()[sig_end - 1].is_ascii_whitespace() {
        sig_end -= 1;
    }
    Some(d.with_fix(Fix::insert(title, file, sig_end as u32, row)))
}
