//! Effect-row consistency (T3-13, S-23, S-77, S-82; spec §8.1, §10, §12.2):
//! a body cannot use an effect its row lacks (E0601), at the first use of it
//! (S-783), `rt` or not, of every effect (S-97, `Record::lacking`). `test`
//! bodies get `Alloc` and `Random` from the runner (§8.5), and `const`
//! initializers `Alloc` from the compiler (§6.6). A row can have `Alloc` alone
//! in this version (D-08), so the E0601 of another effect has no fix.

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, ItemKind, StmtKind, TypeKind};

use crate::binding::{Head, LitClass};
use crate::body::{RowFrom, generics_of};
use crate::def::{DefKind, GenericKind};
use crate::drop_alloc::{Drop, copy_would_free};
use crate::names::body::Origin;
use crate::resolve::Entity;
use crate::uses::{Record, Scope, Use, What, holds};
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
/// `effect`, which its row lacks: at the use (S-82, S-783), with the notes
/// of [`notes`]. Where the function is not `rt`, the fix inserts the effect
/// into the signature; an `rt` one cannot have `Alloc` (§10 rule 1), an
/// anonymous function, a `test` and an initializer have no fix (§8.1, S-1041),
/// nor an effect no row of the module can have (S-97, S-1054).
fn first_use(pkg: &Package, a: &Analysis, r: &Record, scope: &Scope, effect: DefId, u: &Use) -> Option<Diagnostic> {
    let module = module_of_def(pkg, a, r.id)?;
    let (ast, text) = (&module.parsed.ast, &module.text);
    let def = a.def(r.id);
    let src = |span: Span| text[span.start as usize..span.end as usize].to_string();
    let name = &a.def(effect).name;
    let of = scope.closure.map_or_else(|| format!("`{}`", def.name), |_| "the anonymous function".into());
    let message = format!(
        "{}: that needs `{name}`, which is not in the effect row of {of} (§8.1)",
        u.describe(a, (ast, r.id), &src)
    );
    let d = Diagnostic::new(Stage::Effects, Code::E0601, u.at, message).with_found(src(u.at));
    let d = notes(a, (ast, &src), r, (scope, effect), u).into_iter().fold(d, |d, (at, why)| d.with_note(at, why));
    let d = rules(a, r, scope, effect).into_iter().fold(d, |d, why| d.with_rule(why));
    if scope.closure.is_some()
        || scope.rt
        || !matches!(def.kind, DefKind::Fn(_))
        || !a.effect_written(effect, def.module)
    {
        return Some(d);
    }
    // No fix where the name does not name the effect in the module (an item
    // of it, an E0304): the row would read that (§18.1, S-1060).
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

/// The notes of the E0601 of `u` in `scope` of the body of `r` for `effect`,
/// all built here (§8.1 fixes what they show, not their text or order): (1)
/// of the scope and the effect; (2) the drop points away from where the value
/// is written (S-783 C1); (3) of the use: the first element that made a
/// literal owned (S-613), the type parameters `Copy` would free (S-1052);
/// (4) the other uses of the effect in the scope (R-83 (3)). No bound on
/// them: a use is in the notes of one report at most, so all the notes are
/// linear in the body. O(P + U + G) for P points, U uses, G type parameters.
fn notes(
    a: &Analysis,
    (ast, src): (&Ast, &dyn Fn(Span) -> String),
    r: &Record,
    (scope, effect): (&Scope, DefId),
    u: &Use,
) -> Vec<(Span, String)> {
    let mut notes = Vec::new();
    let name = &a.def(effect).name;
    let alloc = a.alloc == Some(effect);
    if let Some(c) = scope.closure {
        // No fix; a note of where its row comes from, of an expected type the
        // type alone (not where it was expected) (S-1041).
        let (e, fun) = (ast.expr(c), "the anonymous function");
        let fn_at = Span::new(e.span.file, e.span.start, e.span.start + 2);
        let ExprKind::Closure { body, .. } = &e.kind else { bug(Some(e.span), "a scope of no anonymous function") };
        let head = src(Span::new(e.span.file, e.span.start, ast.expr(*body).span.start));
        let write = match a.effect_written(effect, a.def(r.id).module) {
            true => format!("; write its row: `{} uses {{{name}}} {{ … }}`", head.trim_end()),
            false => String::new(),
        };
        let why = match scope.from {
            Some(RowFrom::Written) => format!("{fun} has the effect row it writes (§8.1)"),
            Some(RowFrom::Expected(t)) => {
                format!(
                    "{fun} has the effect row of the function type expected where it is, `{}` (§8.1)",
                    a.display_in(t, r.id)
                )
            }
            Some(RowFrom::Joining) => format!(
                "{fun} is a later branch of a merge, which takes no effect row from the one before, so its row is empty{write} (§4.7, §8.1)"
            ),
            // `Record::lacking` checks no use of it.
            Some(RowFrom::Unread) => bug(Some(fn_at), "an E0601 of an anonymous function whose row is not known"),
            Some(RowFrom::NoneExpected) | None => {
                format!("no function type is expected where {fun} is, so its effect row is empty{write} (§8.1)")
            }
        };
        notes.push((fn_at, why));
        if scope.rt && alloc {
            let why = format!(
                "{fun} is `rt` by the type expected, which cannot have `{name}` in its effect row (§10 rule 1)"
            );
            notes.push((fn_at, why));
        }
    } else if scope.rt && alloc {
        let def = a.def(r.id);
        notes.push((
            def.name_span,
            format!("`{}` is `rt`, which cannot have `{name}` in its effect row (§10 rule 1)", def.name),
        ));
    }
    if let What::Drop { drop, points } = &u.what {
        // Not where it is written: in or around its place (a temporary's,
        // a rest's), the end of the `let` that binds it to no name (S-1036).
        let lets: Vec<u32> = match drop {
            Drop::Discard { .. } => (a.bodies[&r.id].heads.keys())
                .filter_map(|h| if let Head::Let(s) = h { Some(ast.stmt(*s).span) } else { None })
                .filter(|&s| holds(s, u.at))
                .map(|s| s.end)
                .collect(),
            Drop::Local(..)
            | Drop::Rest { .. }
            | Drop::Value { .. }
            | Drop::IterRest { .. }
            | Drop::Temp { .. }
            | Drop::Overwrite { .. }
            | Drop::Unplaced { .. } => Vec::new(),
        };
        let away =
            |p: &&Span| (p.end <= u.at.start || u.at.end <= p.start) && !(p.is_empty() && lets.contains(&p.start));
        notes.extend(points.iter().filter(away).map(|&p| (p, "dropped here".to_string())));
        if let Some(e) = first_owned(a, ast, r.id, drop) {
            let why = format!("`{}` is the first element that makes the literal owned (§5.4)", src(ast.expr(e).span));
            notes.push((ast.expr(e).span, why));
        }
        // A note, and the fix `uses {Alloc}` alone (S-1052).
        let generics = generics_of(a, r.id);
        for g in copy_would_free(a, r.id, drop).into_iter().map(|i| &generics[i]) {
            let dup = if matches!(g.kind, GenericKind::Type { dup: false, .. }) { " in place of `?Dup`" } else { "" };
            notes.push((
                g.span,
                format!("with the bound `Copy` on `{}`{dup}, its drop needs no `Alloc` (§12.2)", g.name),
            ));
        }
        // S-1035 (W6-04): the note of why a Dup value is copied and not moved goes here.
    }
    // In an `rt` function and an anonymous function too, of the scope alone (S-1050).
    let others = r.uses.iter().filter(|o| o.scope == u.scope && o.at != u.at && o.needs(a, effect));
    notes.extend(others.map(|o| (o.at, format!("{}: it needs `{name}` too", o.describe(a, (ast, r.id), src)))));
    notes
}

/// The notes with no place of the E0601 of `effect` in `scope` of the body
/// of `r`: of the row the compiler gives an initializer (§6.6, S-1055), and
/// of an effect no row of the module can have in this version (S-97, S-1054).
fn rules(a: &Analysis, r: &Record, scope: &Scope, effect: DefId) -> Vec<String> {
    let def = a.def(r.id);
    let mut rules = Vec::new();
    if scope.closure.is_none() && matches!(def.kind, DefKind::Const(_)) {
        rules.push("an initializer has the effect row `{Alloc}` alone, which the compiler gives (§6.6)".into());
    }
    if !a.effect_written(effect, def.module) {
        rules.push(match a.modules.lang.random() == Some(effect) {
            true => "`Random` is given in the body of a `test` alone in this version (§8.5, §11.8)".into(),
            false => "an effect row can have `Alloc` alone in this version (§8.1)".into(),
        });
    }
    rules
}

/// The first element that made the aggregate literal the drop `d` drops
/// owned (S-613, §5.4: `BodyInfo::lits`), through the literals in it it
/// made owned: of a value, a `let`, a `for` or a `match` head. None where the
/// value is no such literal, or its own type makes it owned.
fn first_owned(a: &Analysis, ast: &Ast, id: DefId, d: &Drop) -> Option<ExprId> {
    let mut e = match d {
        Drop::Local(l, _) => match a.names.get(&id)?.bindings[l.0 as usize].origin {
            Origin::Let(s) | Origin::For(s) => match &ast.stmt(s).kind {
                StmtKind::Let { init: e, .. } | StmtKind::For { iter: e, .. } => *e,
                _ => return None,
            },
            Origin::Arm { scrutinee, .. } => scrutinee,
            _ => return None,
        },
        Drop::Value { value, .. }
        | Drop::Temp { value, .. }
        | Drop::IterRest { iter: value, .. }
        | Drop::Unplaced { value, .. } => *value,
        Drop::Rest { .. } | Drop::Overwrite { .. } | Drop::Discard { .. } => return None,
    };
    let (lits, start) = (&a.bodies[&id].lits, e);
    while let Some(&LitClass::Owned { first }) = lits.get(&e)
        && first != e
    {
        e = first;
    }
    (e != start).then_some(e)
}
