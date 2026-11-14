//! The record of the uses of a body (§8.1, §10, R-83, D-15): every use of
//! an effect, with its place, in a fixed order. The effects stage (E0601)
//! and the rt stage (E0901, the edges of E0903) read it, not the tables of
//! the body. The one list of what needs what
//! (M12): a call needs the row of the function or the function value it
//! calls ([`call_use`]), an interpolation ([`interp_use`]) and a drop
//! ([`alloc_drops`]) need `Alloc`. No stage after reads it, so it is not
//! kept in the analysis.

use onsa_diag::{Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, Lit, StrSeg};

use crate::body::{BodyInfo, Target};
use crate::def::DefKind;
use crate::drop_alloc::{Drop, alloc_drops};
use crate::ty::{EffectSet, Ty};
use crate::{Analysis, DefId, Package, module_of_def};

/// The record of the body of `id`: its uses, by their place (the start, then
/// the end), what makes or calls before a drop, then by the expression or
/// the order of the drops (R-459: not by the order of a table).
pub(crate) struct Record<'a> {
    pub id: DefId,
    pub uses: Vec<Use<'a>>,
}

/// A use of an effect (§8.1).
pub(crate) struct Use<'a> {
    /// The expression, or where the value dropped is written (S-783).
    pub at: Span,
    pub needs: Needs<'a>,
    /// Whether what it calls is `rt` (§10 rule 4); none where it calls
    /// nothing (a drop, until a `Drop` is called by one in phase 2).
    pub rt: Option<bool>,
    pub what: What<'a>,
}

/// The effects a use needs: the row of what it calls, or `Alloc` (§2.4,
/// §12.2).
pub(crate) enum Needs<'a> {
    Row(&'a EffectSet),
    Alloc,
}

pub(crate) enum What<'a> {
    /// A call of a function or a method.
    Call { callee: DefId },
    /// A call through a value of a function type.
    ValueCall,
    /// A string literal with a hole (§2.4).
    Interp,
    /// A value dropped (§12.2), as its first drop point tells it, with all
    /// those of its points that need `Alloc` (S-783).
    Drop {
        drop: Drop<'a>,
        #[cfg_attr(not(test), expect(dead_code, reason = "the note of the drop points (S-783 C1) reads them"))]
        points: Vec<Span>,
    },
}

impl Use<'_> {
    /// Whether the use needs the effect declared at `effect`: the one test
    /// of what a use needs (M12).
    pub(crate) fn needs(&self, a: &Analysis, effect: DefId) -> bool {
        match self.needs {
            Needs::Row(row) => row.has(effect),
            Needs::Alloc => a.alloc == Some(effect),
        }
    }

    /// What the use does, as a clause the diagnostics of it (E0601, E0901)
    /// go on from (M12): what it calls, makes or drops. `src` is the text of
    /// a span of its file.
    pub(crate) fn describe(&self, a: &Analysis, ast: &Ast, src: &dyn Fn(Span) -> String) -> String {
        let at = src(self.at);
        match &self.what {
            What::Call { callee } => format!("this calls `{}`", a.def(*callee).name),
            What::ValueCall => "this calls a function value".into(),
            What::Interp => "this string interpolation creates a `Str`".into(),
            What::Drop { drop, .. } => match drop {
                Drop::Local(l) => format!("`{}`, which owns a `{}`, is dropped", l.name, a.display_type(l.ty)),
                Drop::Rest { root, .. } => {
                    format!("taking `{at}` out of `{}` drops the rest of it", root.name(ast, src))
                }
                Drop::Temp { .. } => format!("`{at}` is dropped after it is used"),
                Drop::Value { .. } => format!("`{at}` is dropped by an exit before it is consumed"),
                Drop::Overwrite { .. } => format!("assigning `{at}` drops the value it held"),
                Drop::IterRest { early, .. } => {
                    let what = if *early { "what it has not iterated and its container" } else { "its container" };
                    format!("the `for` that consumes `{at}` drops {what} when it is left")
                }
                Drop::Discard { .. } => format!("what `{at}` binds to no name is dropped"),
            },
        }
    }

    /// The exit that leaves the value this use drops, where it is not where
    /// the value is written.
    pub(crate) fn left_at(&self) -> Option<Span> {
        match &self.what {
            What::Drop { drop: Drop::Value { exit, .. } | Drop::IterRest { exit, early: true, .. }, .. } => Some(*exit),
            _ => None,
        }
    }
}

impl<'a> Record<'a> {
    /// For each effect the row of the body lacks, its first use by the order
    /// of the record (§8.1, E0601): the one test of whether a use is out of
    /// the row, which the rt stage reads too (it adds no edge of a body with
    /// one, §10 rule 5).
    pub(crate) fn lacking(&self, a: &Analysis) -> Vec<(DefId, &Use<'a>)> {
        let DefKind::Fn(f) = &a.def(self.id).kind else { return Vec::new() };
        // SPEC-GAP(S-1053): one E0601 for each scope and effect.
        // `Alloc` alone until every effect is checked (W6-03 U7).
        let effects = a.alloc.into_iter().filter(|&e| !f.effects.has(e));
        effects.filter_map(|e| self.uses.iter().find(|u| u.needs(a, e)).map(|u| (e, u))).collect()
    }
}

/// The records of the bodies of the functions, `rt` or not, that the
/// effects stage reads (`Analysis::body_checked`), in the order of the defs.
pub(crate) fn records<'a>(pkg: &Package, a: &'a Analysis) -> Vec<Record<'a>> {
    let read = |id| matches!(&a.def(id).kind, DefKind::Fn(f) if f.body.is_some());
    a.new_defs()
        .filter(|&id| read(id) && a.body_checked(id, Stage::Effects))
        .filter_map(|id| record(pkg, a, id))
        .collect()
}

/// The record of the body of `id`. O(T + E + D + U log U) for T targets, E
/// typed expressions, D drop points and U uses.
fn record<'a>(pkg: &Package, a: &'a Analysis, id: DefId) -> Option<Record<'a>> {
    let _scope = onsa_diag::internal::item_scope(a.def(id).span);
    let ast = &module_of_def(pkg, a, id)?.parsed.ast;
    let body = &a.bodies[&id];
    let mut keyed = Vec::new();
    let made = body.targets.keys().filter_map(|&e| call_use(a, ast, body, e).map(|u| (e, u)));
    for (e, u) in made.chain(body.expr_types.keys().filter_map(|&e| interp_use(ast, e).map(|u| (e, u)))) {
        keyed.push(((u.at.start, u.at.end, 0, e.0), u));
    }
    for (n, (drop, points)) in alloc_drops(a, id).into_iter().enumerate() {
        let at = drop.at(ast);
        keyed.push((
            (at.start, at.end, 1, n as u32),
            Use { at, needs: Needs::Alloc, rt: None, what: What::Drop { drop, points } },
        ));
    }
    keyed.sort_unstable_by_key(|(k, _)| *k);
    Some(Record { id, uses: keyed.into_iter().map(|(_, u)| u).collect() })
}

/// The use of the expression `e` of `body` when it calls a function, a
/// method or a function value (§8.1).
pub(crate) fn call_use<'a>(a: &'a Analysis, ast: &Ast, body: &BodyInfo, e: ExprId) -> Option<Use<'a>> {
    let expr = ast.expr(e);
    let ExprKind::Call { callee, .. } = &expr.kind else { return None };
    let (row, rt, what) = match body.targets.get(&e)? {
        Target::Fn { def, .. } | Target::Method { def, .. } => {
            let DefKind::Fn(f) = &a.def(*def).kind else { return None };
            // SPEC-GAP(S-1059): the row as written, `Alloc` too where an `rt` callee has it (E0902).
            (&f.effects, f.rt, What::Call { callee: *def })
        }
        Target::Value => {
            let Ty::Fn(f) = a.types.get(*body.expr_types.get(callee)?) else { return None };
            (&f.effects, f.rt, What::ValueCall)
        }
        _ => return None,
    };
    Some(Use { at: expr.span, needs: Needs::Row(row), rt: Some(rt), what })
}

/// The use of the expression `e` when it is a string literal with a hole,
/// which makes a `Str` (§2.4).
pub(crate) fn interp_use<'a>(ast: &Ast, e: ExprId) -> Option<Use<'a>> {
    let expr = ast.expr(e);
    let ExprKind::Lit(Lit::Str(s)) = &expr.kind else { return None };
    let holes = s.segments.iter().any(|seg| matches!(seg, StrSeg::Interp(_)));
    holes.then_some(Use { at: expr.span, needs: Needs::Alloc, rt: None, what: What::Interp })
}
