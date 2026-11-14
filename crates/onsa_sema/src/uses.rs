//! The record of the uses of a body (§8.1, §10, R-83, D-15): its scopes (the
//! body, each anonymous function in it) and every use of an effect, with its
//! place and its scope, in a fixed order. The effects stage (E0601) and the
//! rt stage (E0901) read it, not the tables of the body. The one list of
//! what needs what (M12): a call needs the row of the function or the function value it
//! calls ([`call_use`]), an interpolation ([`interp_use`]) and a drop
//! ([`alloc_drops`]) need `Alloc`. No stage after reads it, so it is not
//! kept in the analysis.

use onsa_diag::hash::HashSet;
use onsa_diag::internal::bug;
use onsa_diag::{Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, Lit, StrSeg};

use crate::body::{BodyInfo, Target, root_of};
use crate::def::DefKind;
use crate::drop_alloc::{Drop, alloc_drops};
use crate::ty::{EffectSet, Ty};
use crate::{Analysis, DefId, Package, module_of_def};

/// The record of the body of `id`: its uses, by their place (the start, then
/// the end), what makes or calls before a drop, then by the expression or
/// the order of the drops (R-459: not by the order of a table).
pub(crate) struct Record<'a> {
    pub id: DefId,
    /// The body (`[0]`), then each anonymous function in it by its start.
    pub scopes: Vec<Scope>,
    pub uses: Vec<Use<'a>>,
}

/// What the uses in it are checked against (§8.1, §10): the body, or an
/// anonymous function, whose uses are its own and not of one around it.
pub(crate) struct Scope {
    /// The anonymous function; none for the body.
    pub closure: Option<ExprId>,
    /// The row of the function, the one given to a `test` (§8.5) and to an
    /// initializer (§6.6), or of the type of the anonymous function (S-1032).
    pub row: EffectSet,
    pub rt: bool,
}

/// A use of an effect (§8.1).
pub(crate) struct Use<'a> {
    /// The expression, or where the value dropped is written (S-783).
    pub at: Span,
    /// Its scope in [`Record::scopes`]: the innermost whose span holds `at`
    /// ([`Closures::around`]).
    pub scope: u32,
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
    Drop { drop: Drop<'a>, points: Vec<Span> },
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
    /// go on from (M12): what it calls, makes or drops, a type as the body
    /// of `def` writes it (R-256). `src` is the text of a span of its file.
    pub(crate) fn describe(&self, a: &Analysis, (ast, def): (&Ast, DefId), src: &dyn Fn(Span) -> String) -> String {
        let at = src(self.at);
        match &self.what {
            What::Call { callee } => format!("this calls `{}`", a.def(*callee).name),
            What::ValueCall => "this calls a function value".into(),
            What::Interp => "this string interpolation creates a `Str`".into(),
            What::Drop { drop, .. } => match drop {
                Drop::Local(_, l) => format!("`{}`, which owns a `{}`, is dropped", l.name, a.display_in(l.ty, def)),
                Drop::Rest { root, .. } => {
                    format!("taking `{at}` out of `{}` drops the rest of it", root.name(ast, src))
                }
                Drop::Temp { .. } => format!("`{at}` is dropped after it is used"),
                Drop::Value { .. } => format!("`{at}` is dropped by an exit before it is used"),
                Drop::Overwrite { .. } => format!("assigning `{at}` drops the value it held"),
                Drop::IterRest { early, .. } => {
                    let what = if *early { "what it has not iterated and its container" } else { "its container" };
                    format!("the `for` that consumes `{at}` drops {what} when it is left")
                }
                Drop::Discard { .. } => format!("what `{at}` binds to no name is dropped"),
            },
        }
    }
}

impl<'a> Record<'a> {
    /// For each scope and each effect its row lacks, the first use of it in
    /// the scope by the order of the record (§8.1, E0601), by the scope: the
    /// one test of whether a use is out of the row, which the rt stage reads
    /// too (it adds no edge of a body with one, §10 rule 5). O(U) for U uses.
    pub(crate) fn lacking(&self, a: &Analysis) -> Vec<(&Scope, DefId, &Use<'a>)> {
        // SPEC-GAP(S-1053): one E0601 for each scope and effect.
        // `Alloc` alone until every effect is checked (W6-03 U7).
        // SPEC-GAP(S-1059): the row as written, `Alloc` too in an `rt` one (E0902).
        let (mut first, mut seen): (Vec<(u32, DefId, &Use<'a>)>, HashSet<_>) = (Vec::new(), HashSet::default());
        for u in &self.uses {
            let row = &self.scopes[u.scope as usize].row;
            for e in a.alloc.into_iter().filter(|&e| !row.has(e) && u.needs(a, e)) {
                if seen.insert((u.scope, e)) {
                    first.push((u.scope, e, u));
                }
            }
        }
        first.sort_by_key(|&(s, ..)| s);
        first.into_iter().map(|(s, e, u)| (&self.scopes[s as usize], e, u)).collect()
    }
}

/// The records of the bodies of the functions, `rt` or not, of the `test`s
/// and of the initializers that the effects stage reads
/// (`Analysis::body_checked`; not of a flow, S-1043), in the order of the defs.
pub(crate) fn records<'a>(pkg: &Package, a: &'a Analysis) -> Vec<Record<'a>> {
    a.new_defs()
        .filter(|&id| root_of(a, id).is_some() && a.body_checked(id, Stage::Effects))
        .filter_map(|id| record(pkg, a, id))
        .collect()
}

/// The row and `rt` of the body of `id`: of a function, and the `Alloc` the
/// runner gives a `test` (§8.5; `Random` in W6-03 U7) and the compiler an
/// initializer (§6.6).
fn body_row(a: &Analysis, id: DefId) -> (EffectSet, bool) {
    match &a.def(id).kind {
        DefKind::Fn(f) => (f.effects.clone(), f.rt),
        _ => {
            let mut row = EffectSet::default();
            a.alloc.into_iter().for_each(|e| row.insert(e));
            (row, false)
        }
    }
}

/// The record of the body of `id`. O(T + E + D + C log C + U (log C + d +
/// log U)) for T targets, E typed expressions, D drop points, C anonymous
/// functions nested d deep and U uses.
fn record<'a>(pkg: &Package, a: &'a Analysis, id: DefId) -> Option<Record<'a>> {
    let _scope = onsa_diag::internal::item_scope(a.def(id).span);
    let ast = &module_of_def(pkg, a, id)?.parsed.ast;
    let body = &a.bodies[&id];
    let closures = Closures::of(ast, body);
    let (row, rt) = body_row(a, id);
    let mut scopes = vec![Scope { closure: None, row, rt }];
    for &(at, e, _) in &closures.0 {
        let Some(Ty::Fn(f)) = body.expr_types.get(&e).map(|&t| a.types.get(t)) else {
            bug(Some(at), "an anonymous function with no function type in a body checked to its end")
        };
        scopes.push(Scope { closure: Some(e), row: f.effects.clone(), rt: f.rt });
    }
    let mut keyed = Vec::new();
    let made = body.targets.keys().filter_map(|&e| call_use(a, ast, body, e).map(|u| (e, u)));
    for (e, u) in made.chain(body.expr_types.keys().filter_map(|&e| interp_use(ast, e).map(|u| (e, u)))) {
        keyed.push(((u.at.start, u.at.end, 0, e.0), u));
    }
    for (n, (drop, points)) in alloc_drops(a, id).into_iter().enumerate() {
        let at = drop.at(ast);
        let u = Use { at, scope: 0, needs: Needs::Alloc, rt: None, what: What::Drop { drop, points } };
        keyed.push(((at.start, at.end, 1, n as u32), u));
    }
    keyed.sort_unstable_by_key(|(k, _)| *k);
    let mut uses: Vec<Use> = keyed.into_iter().map(|(_, u)| u).collect();
    for u in &mut uses {
        u.scope = closures.around(u.at).map_or(0, |i| i as u32 + 1);
    }
    Some(Record { id, scopes, uses })
}

/// The anonymous functions of a body (the names stage makes an entry of
/// `captures` for each), by their start, each with its span and the index of
/// the innermost one around it: the one place that tells the scope of a
/// place (§8.1, §10 rule 5).
pub(crate) struct Closures(Vec<(Span, ExprId, Around)>);

/// The index of the innermost anonymous function around one, in [`Closures`].
type Around = Option<usize>;

impl Closures {
    pub(crate) fn of(ast: &Ast, body: &BodyInfo) -> Closures {
        let mut by_start: Vec<(Span, ExprId)> = body.captures.keys().map(|&e| (ast.expr(e).span, e)).collect();
        by_start.sort_unstable_by_key(|(s, e)| (s.start, std::cmp::Reverse(s.end), e.0));
        let (mut list, mut open): (Vec<(Span, ExprId, Around)>, Vec<usize>) = (Vec::new(), Vec::new());
        for (at, e) in by_start {
            while open.last().is_some_and(|&p| !holds(list[p].0, at)) {
                open.pop();
            }
            list.push((at, e, open.last().copied()));
            open.push(list.len() - 1);
        }
        Closures(list)
    }

    /// The innermost anonymous function whose span holds `at` (its index),
    /// none where it is the body's: the last one that starts at or before
    /// it, or the first around that one that holds it.
    pub(crate) fn around(&self, at: Span) -> Option<usize> {
        let mut i = self.0.partition_point(|(s, ..)| s.start <= at.start).checked_sub(1)?;
        while !holds(self.0[i].0, at) {
            i = self.0[i].2?;
        }
        Some(i)
    }
}

pub(crate) fn holds(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

/// The calls the body itself makes by name of the `rt` functions with a body,
/// by their place: the edges of the rt recursion (§10 rule 5). A call in an
/// anonymous function, `rt` or not, is its own (S-1057). The one collection of
/// them (`crate::rt`, `Analysis::rt_held`).
pub(crate) fn rt_edges(a: &Analysis, ast: &Ast, body: &BodyInfo) -> Vec<(Span, DefId)> {
    let closures = Closures::of(ast, body);
    let edge = |e: ExprId| match call_use(a, ast, body, e)? {
        Use { at, what: What::Call { callee }, .. } if a.rt_with_body(callee) && closures.around(at).is_none() => {
            Some(((at.start, at.end, e.0), (at, callee)))
        }
        _ => None,
    };
    let mut keyed: Vec<_> = body.targets.keys().filter_map(|&e| edge(e)).collect();
    keyed.sort_unstable_by_key(|(k, _)| *k);
    keyed.into_iter().map(|(_, x)| x).collect()
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
    Some(Use { at: expr.span, scope: 0, needs: Needs::Row(row), rt: Some(rt), what })
}

/// The use of the expression `e` when it is a string literal with a hole,
/// which makes a `Str` (§2.4).
pub(crate) fn interp_use<'a>(ast: &Ast, e: ExprId) -> Option<Use<'a>> {
    let expr = ast.expr(e);
    let ExprKind::Lit(Lit::Str(s)) = &expr.kind else { return None };
    let holes = s.segments.iter().any(|seg| matches!(seg, StrSeg::Interp(_)));
    holes.then_some(Use { at: expr.span, scope: 0, needs: Needs::Alloc, rt: None, what: What::Interp })
}
