//! The names of the constant expressions of the types written in a
//! signature or a body (an array length, a const argument; §4.5): walked
//! once, as a body walks the length of `[x; N]` (§15.1), into the records
//! the one reader of the types stage reads (`crate::constarg`, D-15). The
//! locals the type sees (the parameters of a heading, the visible locals of
//! a type of a body) are values there: E0417 of the reader, whatever follows
//! them (§4.5). The walk reports the first error of the names stage of the
//! expression (§18.1); a name it holds as an error has no record.

use onsa_diag::Diagnostic;
use onsa_diag::hash::{HashMap, HashSet};
use onsa_syntax::ast::{Ast, ExprId, Ident, Mode, Path};

use super::paths::Place;
use super::{Binding, BindingId, BindingKind, Fail, Origin, PathRes, Walker};
use crate::Analysis;
use crate::def::{GenericDef, ModId};
use crate::ty::TyId;

/// What the names of a constant expression of a type are read in: the type
/// and const parameters in scope, the type `Self` names (§2.2), whether it is
/// a type of a flow body (§11.1), and the locals the type sees, by name.
#[derive(Clone, Copy)]
pub(crate) struct ConstScope<'s> {
    pub generics: &'s [GenericDef],
    pub self_ty: Option<TyId>,
    pub flow: bool,
    pub locals: &'s HashSet<String>,
}

/// The names of a constant expression of a type, as a body has them: the
/// records of its nodes ([`super::BodyNames::paths`]) and its chains held as
/// an error ([`super::BodyNames::held`]).
pub(crate) type ConstNames = (HashMap<ExprId, PathRes>, HashSet<ExprId>);

/// The names of the constant expression `e` of a type; the error of the
/// names stage is `Err`.
pub(crate) fn const_names(
    a: &Analysis,
    m: ModId,
    (ast, text): (&Ast, &str),
    scope: ConstScope,
    e: ExprId,
) -> Result<ConstNames, Diagnostic> {
    let mut w = Walker::new(a, m, ast, text, (scope.generics, scope.self_ty, e));
    let mut heads = Vec::new();
    super::exprs::expr_heads(ast, e, &mut heads);
    w.outer_locals(scope, heads, ast.expr(e).span);
    let _ = w.const_expr(e);
    match w.failure {
        Some(Fail::Report(d)) => Err(d),
        _ => Ok((w.out.paths, w.out.held)),
    }
}

/// A const argument written as a path (`Ring[F32, N]`, `G[T.BITS]`): the
/// records of its names from its head, one for each name up to the last the
/// names stage resolves ([`Walker::resolve`]), as of [`const_names`];
/// `None` when it is held as an error.
pub(crate) fn const_path_names(
    a: &Analysis,
    m: ModId,
    (ast, text): (&Ast, &str),
    scope: ConstScope,
    path: &Path,
) -> Result<Option<Vec<PathRes>>, Diagnostic> {
    // The root is the place a candidate of a float is found under, which a
    // constant expression has none of (`Walker::float_min`).
    let mut w = Walker::new(a, m, ast, text, (scope.generics, scope.self_ty, ExprId(0)));
    w.outer_locals(scope, path.segments.first().into_iter().collect(), path.span);
    w.in_const = true;
    let segs: Vec<&Ident> = path.segments.iter().collect();
    match w.resolve(&segs, &[], Place::Value) {
        (_, Some(Fail::Report(d))) => Err(d),
        (_, Some(Fail::Held)) => Ok(None),
        (records, _) => Ok(Some(records)),
    }
}

impl Walker<'_> {
    /// Open the scope of the constant expression of a type in `scope`, with
    /// the locals the type sees that it names (`heads`, the first names of
    /// its chains: as a type of a body has them, `Walker::site`) as bindings
    /// of the walk, with no E0304 (the heading and the body report their
    /// own, §5.1); their kind and origin are not read, as only the records of
    /// the names are kept (`span`, the expression's, stands for where they
    /// are bound).
    fn outer_locals(&mut self, scope: ConstScope, heads: Vec<&Ident>, span: onsa_diag::Span) {
        self.flow = scope.flow;
        self.open_scope();
        for name in heads.into_iter().map(|h| &h.name).filter(|&n| scope.locals.contains(n)) {
            if self.outer.contains_key(name) {
                continue;
            }
            let id = BindingId(self.out.bindings.len() as u32);
            self.out.bindings.push(Binding {
                name: name.clone(),
                span,
                kind: BindingKind::Param(Mode::Borrow),
                sites: Vec::new(),
                origin: Origin::Param(id.0),
                scope: super::ScopeId(0),
                reads: 0,
            });
            self.outer.insert(name.clone(), id);
        }
    }
}
