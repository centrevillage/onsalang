//! The constants of type positions: const arguments (`Ring[F32, 4]`) and array
//! lengths (`[F32; N]`, `[e; N]`). Spec §4.5: a constant expression of type
//! `U32`, checked like an ordinary expression with the expected type `U32`;
//! `U32` has no prefix `-` (`-1`, `-0`, E0401, S-228) and a constant of another
//! type is E0401 (R-154). One place for the signature lowering (`sig.rs`),
//! the bodies (`body.rs`) and the flows, which reads the records of the names
//! the names stage made once (`names::body`, D-15): the leaves by their type,
//! the nodes by the grammar (S-966).

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Ast, BinOp, ExprId, ExprKind, Ident, ItemKind, Lit, Path, UnOp};

use crate::def::DefKind;
use crate::names::body::PathRes;
use crate::resolve::{Entity, NameKind, ResolveError};
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

/// An array length or a const argument written as an expression (`4`, `-1`,
/// `N + 1`, `cfg.N`, `(N)`): the one reader of the constant expressions, for
/// the signatures, the bodies and the flows, from the records of their names
/// (§4.5). `Ok((value, constant))`: `constant` is the `const` item that a
/// constant expression of one name (in parentheses too) denotes.
pub(crate) fn expr(a: &mut Analysis, cx: &ConstCx, e: ExprId) -> Result<(ConstU32, Option<DefId>), ConstErr> {
    let got = node(a, cx, e)?;
    finish(got, cx.ast.expr(e).span)
}

/// A const argument written as a path (`Ring[F32, N]`, `G[T.BITS]`), from
/// the records of its names ([`crate::names::body::const_path_names`]; `None`
/// when it is held as an error), as [`expr`] reads a chain of names.
pub(crate) fn path(
    a: &mut Analysis,
    at: (ModId, &Ast, &str),
    records: Option<&[PathRes]>,
    path: &Path,
) -> Result<(ConstU32, Option<DefId>), ConstErr> {
    let Some(records) = records else { return Err(ConstErr::Unknown) };
    let shown = at.2[path.span.start as usize..path.span.end as usize].to_string();
    let got = settle(chain(a, at, records, path.segments.len(), (&path.segments[0].name, shown, path.span)))?;
    finish(got, path.span)
}

/// What a node of a constant expression reads as, when it is no error.
enum Got {
    /// A literal or a constant (in parentheses too), or a const parameter.
    Val(ConstU32, Option<DefId>),
    /// An operation, whose value this version does not compute (K-05).
    Op,
    /// The error type: a name held as an error, a constant of a failed unit
    /// in it (§18.1). The nodes above it report nothing.
    Unknown,
    /// A constant whose value this version does not compute.
    Uncomputed(Diagnostic),
}

/// The value of a whole constant expression at `span`, of what it reads as.
fn finish(got: Got, span: Span) -> Result<(ConstU32, Option<DefId>), ConstErr> {
    match got {
        Got::Val(v, d) => Ok((v, d)),
        Got::Op => Err(ConstErr::Uncomputed(onsa_diag::unsupported::Feature::ArrayLengthExprs.diagnostic(
            Stage::Types,
            span,
            &[],
        ))),
        Got::Unknown => Err(ConstErr::Unknown),
        Got::Uncomputed(d) => Err(ConstErr::Uncomputed(d)),
    }
}

/// [`Got`] of what a leaf reads as (an error to report is `Err`).
fn settle(r: Result<Got, ConstErr>) -> Result<Got, Diagnostic> {
    match r {
        Ok(got) => Ok(got),
        Err(ConstErr::Report(d)) => Err(d),
        Err(ConstErr::Uncomputed(d)) => Ok(Got::Uncomputed(d)),
        Err(ConstErr::Unknown) => Ok(Got::Unknown),
    }
}

/// The node `e`, its operands first (§4.5, §4.7: as an ordinary expression
/// of the expected type `U32`), stopping at the first error. The leaves are
/// read by their type, and the nodes by the grammar (S-966): a node outside
/// it is E0417 whatever is in it, whose names the names stage read (S-968).
fn node(a: &mut Analysis, cx: &ConstCx, e: ExprId) -> Result<Got, Diagnostic> {
    // An integer literal, and a prefix `-` before a literal (S-228).
    if let Some(v) = literal(cx.ast, cx.text, e) {
        return v.map(|v| Got::Val(ConstU32::Value(v), None));
    }
    let expr = cx.ast.expr(e);
    let shown = || cx.text[expr.span.start as usize..expr.span.end as usize].to_string();
    if let Some((nodes, head)) = chain_nodes(cx.ast, e) {
        if cx.held.contains(&e) {
            return Ok(Got::Unknown);
        }
        let records: Vec<PathRes> = nodes.iter().map_while(|n| cx.names.get(n).cloned()).collect();
        return settle(chain(a, (cx.m, cx.ast, cx.text), &records, nodes.len(), (&head.name, shown(), expr.span)));
    }
    match &expr.kind {
        ExprKind::Paren(x) => node(a, cx, *x),
        // `U32` has no prefix `-` (§3.4, S-228), but of the error type.
        ExprKind::Unary { op: UnOp::Neg, expr: x } => match node(a, cx, *x)? {
            Got::Unknown => Ok(Got::Unknown),
            _ => Err(no_negative(shown(), expr.span)),
        },
        ExprKind::Binary { op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem, lhs, rhs, .. } => {
            match (node(a, cx, *lhs)?, node(a, cx, *rhs)?) {
                (Got::Unknown, _) | (_, Got::Unknown) => Ok(Got::Unknown),
                _ => Ok(Got::Op),
            }
        }
        // A literal of another type (§4.5, S-966).
        ExprKind::Lit(lit) => {
            let form = match lit {
                Lit::Float { .. } => "a float literal",
                Lit::Bool(_) => "a `Bool` literal",
                Lit::Str(_) => "a string literal",
                _ => "a character literal",
            };
            let msg = format!("a constant expression has the type `U32`; found {form} (§4.5)");
            Err(Diagnostic::new(Stage::Types, Code::E0401, expr.span, msg).with_found(shown()))
        }
        ExprKind::Error => Ok(Got::Unknown),
        kind => {
            let noun = match kind {
                ExprKind::Call { .. } => "a call",
                ExprKind::Field { .. } | ExprKind::TupleIndex { .. } => "a field of a value",
                ExprKind::Index { .. } => "an element of a value",
                ExprKind::Tuple(_) => "a tuple",
                ExprKind::Array(_) | ExprKind::Repeat { .. } => "an array",
                ExprKind::Struct { .. } => "a struct literal",
                ExprKind::Binary { .. } | ExprKind::Unary { .. } | ExprKind::Cast { .. } => {
                    "an operation other than `+ - * / %` and prefix `-`"
                }
                // SPEC-GAP(S-971): a hole `_` (§18.1, E0421 at an expression) is E0417 here.
                _ => "an expression of another form",
            };
            Err(value_not_constant(shown(), noun, expr.span))
        }
    }
}

/// The nodes of the chain of names `e` (`a.b.c`, from its head `a`) and its
/// first name; none when `e` is no chain (`f().x`, `(K).x`, a literal).
fn chain_nodes(ast: &Ast, e: ExprId) -> Option<(Vec<ExprId>, &Ident)> {
    let mut out = vec![e];
    let mut cur = e;
    loop {
        match &ast.expr(cur).kind {
            ExprKind::Field { base, .. } => cur = *base,
            ExprKind::Path(p) if p.segments.len() == 1 => {
                out.reverse();
                return Some((out, &p.segments[0]));
            }
            _ => return None,
        }
        out.push(cur);
    }
}

/// The chain of `len` names whose records from its head are `records`
/// (`head` its first name, `shown` at `span` the whole), not held as an
/// error: a const parameter, or a constant ([`of_entity`]); what is no
/// constant is E0417 when it is a value (§4.5, S-713 (a)), else E0308. A
/// chain whose records end before its last name ends at a value whose field
/// follows (S-967), or is one whose names the walk did not read.
fn chain(
    a: &mut Analysis,
    (m, ast, text): (ModId, &Ast, &str),
    records: &[PathRes],
    len: usize,
    (head, shown, span): (&str, String, Span),
) -> Result<Got, ConstErr> {
    if records.len() < len {
        let noun = match records.last() {
            Some(PathRes::Local(_)) => "a local",
            Some(_) => "a field of a value",
            None => "a value",
        };
        return Err(value_not_constant(shown, noun, span).into());
    }
    match records[len - 1] {
        PathRes::Local(_) => Err(value_not_constant(shown, "a local", span).into()),
        PathRes::ConstParam(i) => Ok(Got::Val(ConstU32::Param(i), None)),
        // Its value is the instantiation's (S-898); `const_values` is not
        // read, as of the representative type of its row.
        PathRes::BoundMember { member, .. } => match NameKind::of_named(Entity::Member(member), &a.defs, span) {
            NameKind::Constant => {
                let msg = format!(
                    "`{shown}` has no value before `{head}` is instantiated: a constant expression names constants (§4.5)"
                );
                Err(Diagnostic::new(Stage::Types, Code::E0417, span, msg).with_found(shown).into())
            }
            kind => Err(not_constant(kind, shown, span)),
        },
        PathRes::Item { entity, .. } => {
            let d = match entity {
                Entity::Def(d) | Entity::Member(d) => Some(d),
                _ => None,
            };
            match of_entity(a, m, ast, text, entity, span)? {
                Some(v) => Ok(Got::Val(ConstU32::Value(v), d)),
                None => Err(not_constant(NameKind::of_named(entity, &a.defs, span), shown, span)),
            }
        }
        PathRes::TypeParam(_) => Err(not_constant(NameKind::Type, shown, span)),
        PathRes::Namespace(entity) => Err(not_constant(NameKind::of_named(entity, &a.defs, span), shown, span)),
        PathRes::FlowBuiltin(_) => Err(value_not_constant(shown, "a builtin name of a flow", span).into()),
    }
}

/// E0401 for a prefix `-` at `span`: `U32` has none (§3.4, §4.5, S-228).
fn no_negative(shown: String, span: Span) -> Diagnostic {
    let msg = "a constant expression has the type `U32`, which has no prefix `-` (also not `-0`) (§3.4, §4.5)";
    Diagnostic::new(Stage::Types, Code::E0401, span, msg).with_found(shown)
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
        _ if ast.negated_literal(e).is_some() => Some(Err(no_negative(found(expr.span), expr.span))),
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
