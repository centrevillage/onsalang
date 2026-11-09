//! The constants of type positions: const arguments (`Ring[F32, 4]`) and array
//! lengths (`[F32; N]`, `[e; N]`). Spec §4.5: a constant expression of type
//! `U32`, checked like an ordinary expression with the expected type `U32`;
//! `U32` has no prefix `-` (`-1`, `-0`, E0401, S-228) and a constant of another
//! type is E0401 (R-154). One place for the signature lowering (`sig.rs`),
//! the bodies (`body.rs`) and the flows, which reads the records of the names
//! the names stage made once (`names::body`, D-15); W5-16 U1b replaces the
//! inside with the typing of the whole constant-expression grammar.

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Ast, CallKind, ExprId, ExprKind, ItemKind, Lit, Path};

use crate::def::DefKind;
use crate::names::body::PathRes;
use crate::resolve::{Callee, Entity, NameKind, ResolveError};
use crate::ty::{IntKind, Ty};
use crate::{Analysis, DefId, ModId};

/// The value of a constant expression in a type position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstU32 {
    Value(u32),
    /// The `const` parameter `N` (its index among the generics in scope).
    Param(u32),
}

/// Why a constant expression has no value.
#[derive(Debug)]
pub(crate) enum ConstErr {
    /// A diagnostic for the caller to report.
    Report(Diagnostic),
    /// A constant expression whose value this version does not compute (a
    /// `const` computed by an expression, `I32.BITS`): the diagnostic of the
    /// array lengths, for the caller to report or to say in its own words.
    Uncomputed(Diagnostic),
    /// A constant whose unit failed in the syntax stage (S-59): its value was
    /// not read, and its users get no diagnostic for it (R-71).
    Unknown,
}

impl From<Diagnostic> for ConstErr {
    fn from(d: Diagnostic) -> ConstErr {
        ConstErr::Report(d)
    }
}

/// What a constant expression is read with: the module `m` of `ast`, and the
/// records of the names of the expression, which the names stage made once
/// (a body's, or [`crate::names::body::const_names`]'; §15.1, D-15), with
/// its chains held as an error.
pub(crate) struct ConstCx<'r> {
    pub m: ModId,
    pub ast: &'r Ast,
    pub text: &'r str,
    pub names: &'r HashMap<ExprId, PathRes>,
    pub held: &'r HashSet<ExprId>,
}

/// An array length or a const argument written as an expression (`4`, `-1`, `N`,
/// `SIZE`, `cfg.N`, `I32.BITS`, `Self.N`): the one reader of the forms, for the
/// signatures, the bodies and the flows, from the records of its names.
/// `Ok((value, constant))`: `constant` is the `const` item a name denotes.
/// Of an operation (E0200 until W9-03), a call, a local or a name of no
/// constant in it is the error first (§4.5, S-713 (a)); a name held as an
/// error in it leaves its value unknown, with no diagnostic (§18.1).
pub(crate) fn expr(a: &mut Analysis, cx: &ConstCx, e: ExprId) -> Result<(ConstU32, Option<DefId>), ConstErr> {
    let ast = cx.ast;
    if let Some(r) = literal(ast, cx.text, e) {
        return r.map(|v| (ConstU32::Value(v), None)).map_err(ConstErr::Report);
    }
    let span = ast.expr(e).span;
    if path_of(ast, e).is_some() {
        let head = chain_head(ast, e);
        let ExprKind::Path(first) = &ast.expr(head).kind else {
            onsa_diag::internal::bug(Some(span), "a chain of names starts at a name")
        };
        let records = (cx.names.get(&e), cx.names.get(&head));
        let held = cx.held.contains(&e);
        return read_chain(a, (cx.m, ast, cx.text), (records, held), (&first.segments[0].name, span));
    }
    let found = cx.text[span.start as usize..span.end as usize].to_string();
    if let ExprKind::Call { callee, kind, .. } = &ast.expr(e).kind {
        // A callee held as an error (§18.1).
        if cx.held.contains(callee) && matches!(kind, CallKind::Plain | CallKind::Bang) {
            return Err(ConstErr::Unknown);
        }
        // A constant called with `!` (`K!()`, §5.2), as a body has it.
        let kind_of = |r: &PathRes| match r {
            PathRes::Item { entity, .. } => NameKind::of(*entity, &a.defs),
            PathRes::BoundMember { member, .. } => NameKind::of(Entity::Member(*member), &a.defs),
            PathRes::ConstParam(_) => Some(NameKind::ConstParam),
            _ => None,
        };
        let callee_kind = cx.names.get(callee).and_then(kind_of);
        if callee_kind.is_some_and(|k| k.at_callee(*kind == CallKind::Bang) == Callee::NoFunction) {
            let cspan = ast.expr(*callee).span;
            let shown = cx.text[cspan.start as usize..cspan.end as usize].to_string();
            let msg = format!("`{shown}` is not a function");
            return Err(Diagnostic::new(Stage::Types, Code::E0401, cspan, msg).with_found(shown).into());
        }
        return Err(value_not_constant(found, "a call", span).into());
    }
    let mut leaves = Vec::new();
    operands(ast, e, &mut leaves);
    let (mut wrong, mut held): (Option<Diagnostic>, bool) = (None, false);
    for l in leaves.into_iter().filter(|&l| l != e) {
        match expr(a, cx, l) {
            Err(ConstErr::Report(d)) if d.stage == Stage::Names || d.code == Code::E0417 => {
                if wrong.as_ref().is_none_or(|w| d.unit_order() < w.unit_order()) {
                    wrong = Some(d);
                }
            }
            Err(ConstErr::Unknown) => held = true,
            _ => {}
        }
    }
    match (wrong, held) {
        (Some(d), _) => Err(d.into()),
        (None, true) => Err(ConstErr::Unknown),
        (None, false) => {
            let unsupported = onsa_diag::unsupported::Feature::ArrayLengthExprs.diagnostic(Stage::Types, span, &[]);
            Err(unsupported.with_found(found).into())
        }
    }
}

/// The node of the first name of the chain of names `e` (`a` of `a.b.c`).
fn chain_head(ast: &Ast, e: ExprId) -> ExprId {
    match &ast.expr(e).kind {
        ExprKind::Field { base, .. } => chain_head(ast, *base),
        _ => e,
    }
}

/// A const argument written as a path (`Ring[F32, N]`, `G[T.BITS]`), from
/// the records of its names ([`crate::names::body::const_path_names`]), as
/// [`expr`] reads a chain of names; `None` when it is held as an error.
pub(crate) fn path(
    a: &mut Analysis,
    (m, ast, text): (ModId, &Ast, &str),
    records: Option<&[PathRes]>,
    path: &Path,
) -> Result<(ConstU32, Option<DefId>), ConstErr> {
    let Some(records) = records else { return Err(ConstErr::Unknown) };
    let leaf = records.get(path.segments.len() - 1);
    read_chain(a, (m, ast, text), ((leaf, records.first()), false), (&path.segments[0].name, path.span))
}

/// The chain of names at `span` from the name `first`, by the records at its
/// last name (`leaf`) and at its first (`head`): a const parameter, or a constant
/// ([`of_entity`]); a local, a member of a type parameter and a name of
/// another kind are errors. A chain `held` as an error has no value and no
/// diagnostic (§18.1); one with no record otherwise is one whose names the
/// walk did not read, no constant. The names stage reported a name after a
/// value that is no local.
fn read_chain(
    a: &mut Analysis,
    (m, ast, text): (ModId, &Ast, &str),
    ((leaf, head), held): ((Option<&PathRes>, Option<&PathRes>), bool),
    (first, span): (&str, Span),
) -> Result<(ConstU32, Option<DefId>), ConstErr> {
    let shown = text[span.start as usize..span.end as usize].to_string();
    match (leaf, head) {
        (_, Some(PathRes::Local(_))) => Err(value_not_constant(shown, "a local", span).into()),
        (Some(&PathRes::ConstParam(i)), _) => Ok((ConstU32::Param(i), None)),
        (Some(&PathRes::BoundMember { member, .. }), _) => Err(bound_member(a, member, (first, shown), span)),
        (Some(&PathRes::Item { entity, .. }), _) => {
            let constant = match entity {
                Entity::Def(d) | Entity::Member(d) => Some(d),
                _ => None,
            };
            match of_entity(a, m, ast, text, entity, span)? {
                Some(v) => Ok((ConstU32::Value(v), constant)),
                None => Err(not_constant(NameKind::of_named(entity, &a.defs, span), shown, span)),
            }
        }
        (None, None) if held => Err(ConstErr::Unknown),
        (None, None) => {
            let msg = format!("`{shown}` is not a constant: a constant expression names constants (§4.5)");
            Err(Diagnostic::new(Stage::Types, Code::E0417, span, msg).with_found(shown).into())
        }
        (leaf, _) => onsa_diag::internal::bug(Some(span), format!("a constant expression's name read as {leaf:?}")),
    }
}

/// The error of the member `member` of the type parameter `param` (`T.BITS`, whose
/// bounds give it, `names/body/paths.rs`) in a constant expression: a
/// constant has its value at the instantiation, as a const parameter's in
/// an expression (E0417, §4.5, S-898), and is not read here; a function is
/// no constant ([`not_constant`]).
fn bound_member(a: &Analysis, member: DefId, (param, shown): (&str, String), span: Span) -> ConstErr {
    if !matches!(a.def(member).kind, DefKind::Const(_)) {
        return not_constant(NameKind::of_named(Entity::Member(member), &a.defs, span), shown, span);
    }
    let msg = format!(
        "`{shown}` has no value before `{param}` is instantiated: a constant expression names constants (§4.5)"
    );
    Diagnostic::new(Stage::Types, Code::E0417, span, msg).with_found(shown).into()
}

/// The operands of the arithmetic of `e`, under parentheses, prefix `-` and
/// binary operators; `e` itself when it is none of them.
pub(crate) fn operands(ast: &Ast, e: ExprId, out: &mut Vec<ExprId>) {
    match &ast.expr(e).kind {
        ExprKind::Paren(x) | ExprKind::Unary { expr: x, .. } => operands(ast, *x, out),
        ExprKind::Binary { lhs, rhs, .. } => {
            operands(ast, *lhs, out);
            operands(ast, *rhs, out);
        }
        _ => out.push(e),
    }
}

/// The error of the name `shown` at `span` of a constant expression, of the
/// kind `kind`, which is no constant (§4.5, §15.1, S-713 (a)): a value (a
/// function, a variant) is E0417, as a local is, and what is no value E0308.
pub(crate) fn not_constant(kind: NameKind, shown: String, span: Span) -> ConstErr {
    if !kind.is_value() {
        return ResolveError::Kind { shown, span, kind, want: "a constant" }.into_diagnostic().into();
    }
    value_not_constant(shown, kind.noun(), span).into()
}

/// E0417 for the value `shown` at `span`, which is `noun` (a function, a
/// variant, a local), no constant (§4.5).
pub(crate) fn value_not_constant(shown: String, noun: &str, span: Span) -> Diagnostic {
    let msg = format!("`{shown}` is {noun}, not a constant: a constant expression names constants (§4.5)");
    Diagnostic::new(Stage::Types, Code::E0417, span, msg).with_found(shown)
}

/// `N`, `cfg.N`, `I32.BITS` as a path (a field chain of names is a qualified name here).
pub(crate) fn path_of(ast: &Ast, e: ExprId) -> Option<Path> {
    let expr = ast.expr(e);
    match &expr.kind {
        ExprKind::Path(p) => Some(p.clone()),
        ExprKind::Field { base, name } => {
            let mut p = path_of(ast, *base)?;
            p.segments.push(name.clone());
            p.span = expr.span;
            Some(p)
        }
        _ => None,
    }
}

/// A literal or a negative literal written as the constant (`4`, `-1`, `-(1)`);
/// `None` for any other expression.
pub(crate) fn literal(ast: &Ast, text: &str, e: ExprId) -> Option<Result<u32, Diagnostic>> {
    let expr = ast.expr(e);
    let found = |span: Span| text[span.start as usize..span.end as usize].to_string();
    match &expr.kind {
        ExprKind::Lit(Lit::Int { value, .. }) => Some(match u32::try_from(*value) {
            Ok(v) => Ok(v),
            Err(_) => Err(Diagnostic::new(
                Stage::Types,
                Code::E0408,
                expr.span,
                format!("`{value}` does not fit in `U32`, the type of a constant expression (§4.5)"),
            )
            .with_found(found(expr.span))),
        }),
        _ if ast.negated_literal(e).is_some() => Some(Err(Diagnostic::new(
            Stage::Types,
            Code::E0401,
            expr.span,
            "a constant expression has the type `U32`, which has no prefix `-` (also not `-0`) (§3.4, §4.5)",
        )
        .with_found(found(expr.span)))),
        _ => None,
    }
}

/// The value of the constant `entity` a name at `span` names, of the
/// module `m` of `ast` (`None` when it is no constant).
pub(crate) fn of_entity(
    a: &mut Analysis,
    m: ModId,
    ast: &Ast,
    text: &str,
    entity: Entity,
    span: Span,
) -> Result<Option<u32>, ConstErr> {
    let (Entity::Def(d) | Entity::Member(d)) = entity else { return Ok(None) };
    let found = text[span.start as usize..span.end as usize].to_string();
    let u32_ = a.types.int(IntKind::U32);
    let def = a.def(d).clone();
    let DefKind::Const(c) = &def.kind else { return Ok(None) };
    // A constant of a cycle (E0311, §18.1, S-734).
    if c.int_value.is_none() && a.partly_read(d) || a.decls.cyclic.contains(&d) {
        return Err(ConstErr::Unknown);
    }
    if c.ty != u32_ && !matches!(a.types.get(c.ty), Ty::Error) {
        let shown = a.types.display(c.ty, &|d| a.def(d).name.clone(), &|i| format!("<{i}>"));
        let mut d = Diagnostic::new(
            Stage::Types,
            Code::E0401,
            span,
            format!("a constant expression has the type `U32`; `{}` is `{shown}` (§4.5)", def.name),
        )
        .with_found(found);
        // The candidate makes the type of the constant `U32` when it is
        // declared in this module (§4.5) and its value is a `U32` (an integer
        // literal that fits), so that the candidate leaves no error (S-236).
        if def.module == m
            && c.int_value.is_some_and(|v| u32::try_from(v).is_ok())
            && let Some(item) = def.item
            && let ItemKind::Const(cd) = &ast.item(item).kind
        {
            let tspan = ast.ty(cd.ty).span;
            let want = a.types.display(u32_, &|d| a.def(d).name.clone(), &|i| format!("<{i}>"));
            d = d.with_fix(Fix::replace(format!("make `{}` a `{want}`", def.name), tspan, want));
        }
        return Err(d.into());
    }
    match c.int_value {
        Some(v) => match u32::try_from(v) {
            Ok(v) => Ok(Some(v)),
            Err(_) => Err(Diagnostic::new(
                Stage::Types,
                Code::E0408,
                span,
                format!("the value of `{}` does not fit in `U32` (§4.5)", def.name),
            )
            .with_found(found)
            .into()),
        },
        None => Err(ConstErr::Uncomputed(
            onsa_diag::unsupported::Feature::ComputedArrayLengths.diagnostic(Stage::Types, span, &[]).with_found(found),
        )),
    }
}
