//! Effect-row consistency (T3-13, S-23, S-77, S-82; spec §8.1, §10, §12.2):
//! a body cannot use an effect its row lacks (E0601), at the first use of it
//! (S-783), `rt` or not. Phase 1 tracks `Alloc` only (`Record::lacking`);
//! other effects are E0200 at the signature. `test` bodies get `Alloc` from
//! the runner (D-08), and `const` initializers from the compiler (§6.6).

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::ItemKind;

use crate::def::DefKind;
use crate::uses::{Record, Use};
use crate::{Analysis, DefId, Package, module_of_def};

/// The E0601 of the bodies of `records` ([`crate::uses::records`]): for
/// each, one for each effect its row lacks.
pub(crate) fn check_all(pkg: &Package, a: &Analysis, records: &[Record]) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for r in records {
        let _scope = onsa_diag::internal::item_scope(a.def(r.id).span);
        diags.extend(r.lacking(a).into_iter().filter_map(|(effect, u)| first_use(pkg, a, r, effect, u)));
    }
    diags
}

/// The E0601 of `u`, the first use in the body of `r` of `effect`, which its
/// row lacks: at the use (S-82, S-783). Where the function is not `rt`, the
/// fix inserts the effect into the signature; an `rt` one cannot have
/// `Alloc` (§10 rule 1), which a note says, with no fix.
fn first_use(pkg: &Package, a: &Analysis, r: &Record, effect: DefId, u: &Use) -> Option<Diagnostic> {
    let module = module_of_def(pkg, a, r.id)?;
    let (ast, text) = (&module.parsed.ast, &module.text);
    let def = a.def(r.id);
    let DefKind::Fn(f) = &def.kind else { return None };
    let src = |span: Span| text[span.start as usize..span.end as usize].to_string();
    let name = &a.def(effect).name;
    let message = format!(
        "{}: that needs `{name}`, which is not in the effect row of `{}` (§8.1)",
        u.describe(a, ast, &src),
        def.name
    );
    let d = Diagnostic::new(Stage::Effects, Code::E0601, u.at, message).with_found(src(u.at));
    let d = u.left_at().into_iter().fold(d, |d, x| d.with_note(x, "left here"));
    if f.rt {
        let why = format!("`{}` is `rt`, which cannot have `{name}` in its effect row (§10 rule 1)", def.name);
        return Some(d.with_note(def.name_span, why));
    }

    // The fix: the effect row after the signature, from the name to just
    // before the body (§18.1).
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
    let row = format!(" uses {{{name}}}");
    Some(d.with_fix(Fix::insert(format!("add `uses {{{name}}}`"), def.name_span.file, sig_end as u32, row)))
}
