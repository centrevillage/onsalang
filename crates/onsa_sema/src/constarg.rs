//! The constants of type positions: const arguments (`Ring[F32, 4]`) and array
//! lengths (`[F32; N]`, `[e; N]`). Spec §4.5: a constant expression of type
//! `U32`, checked like an ordinary expression with the expected type `U32`;
//! `U32` has no prefix `-` (`-1`, `-0`, E0401, S-228) and a constant of another
//! type is E0401 (R-154). One place for the signature lowering (`sig.rs`) and
//! the bodies (`body.rs`); W5-08 replaces the inside with the typing of the
//! whole constant-expression grammar.

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, ItemKind, Lit, Path};

use crate::def::{DefKind, GenericDef, GenericKind};
use crate::resolve::{Builtin, Entity};
use crate::ty::{IntKind, Ty};
use crate::{Analysis, ModId, builtin};

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
    /// A constant whose unit failed in the syntax stage (S-59): its value was
    /// not read, and its users get no diagnostic for it (R-71).
    Unknown,
}

impl From<Diagnostic> for ConstErr {
    fn from(d: Diagnostic) -> ConstErr {
        ConstErr::Report(d)
    }
}

/// An array length or a const argument written as an expression (`4`, `-1`, `N`,
/// `SIZE`, `cfg.N`, `I32.BITS`): the one reader of the forms, for the signatures and
/// the bodies. `Ok((value, constant))`: `constant` is the `const` item a name denotes.
pub(crate) fn expr(
    a: &mut Analysis,
    m: ModId,
    ast: &Ast,
    text: &str,
    generics: &[GenericDef],
    e: ExprId,
) -> Result<(ConstU32, Option<crate::DefId>), ConstErr> {
    if let Some(r) = literal(ast, text, e) {
        return r.map(|v| (ConstU32::Value(v), None)).map_err(ConstErr::Report);
    }
    let expr = ast.expr(e);
    let span = expr.span;
    let found = text[span.start as usize..span.end as usize].to_string();
    let Some(path) = path_of(ast, e) else {
        return Err(onsa_diag::unsupported::Feature::ArrayLengthExprs
            .diagnostic(Stage::Types, span, &[])
            .with_found(found)
            .into());
    };
    if path.segments.len() == 1
        && let Some(i) = generics.iter().position(|g| g.name == path.segments[0].name)
    {
        if matches!(generics[i].kind, GenericKind::Const(_)) {
            return Ok((ConstU32::Param(i as u32), None));
        }
        return Err(Diagnostic::new(
            Stage::Names,
            Code::E0302,
            span,
            "a constant expression names a `const` parameter or a constant, not a type parameter (§4.5)",
        )
        .with_found(found)
        .into());
    }
    match named(a, m, ast, text, &path, span)? {
        Some(v) => {
            let constant = match a.resolve_path(m, &path) {
                Ok(Entity::Def(d) | Entity::Member(d)) => Some(d),
                _ => None,
            };
            Ok((ConstU32::Value(v), constant))
        }
        None => Err(Diagnostic::new(Stage::Names, Code::E0302, span, "array length must be a constant")
            .with_found(found)
            .into()),
    }
}

/// `N`, `cfg.N`, `I32.BITS` as a path (a field chain of names is a qualified name here).
fn path_of(ast: &Ast, e: ExprId) -> Option<Path> {
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

/// A name of a constant (`SIZE`, `cfg.N`, `I32.BITS`) at `span`: its value, when
/// its type is `U32`. `Ok(None)`: the name is not a constant (the caller reports
/// what it is). `ast` is the module `m` the name is written in.
pub(crate) fn named(
    a: &mut Analysis,
    m: ModId,
    ast: &Ast,
    text: &str,
    path: &Path,
    span: Span,
) -> Result<Option<u32>, ConstErr> {
    let found = text[span.start as usize..span.end as usize].to_string();
    let u32_ = a.types.int(IntKind::U32);
    match a.resolve_path(m, path) {
        Ok(Entity::Def(d)) | Ok(Entity::Member(d)) => {
            let def = a.def(d).clone();
            let DefKind::Const(c) = &def.kind else { return Ok(None) };
            if c.int_value.is_none() && a.partly_read(d) {
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
                None => Err(onsa_diag::unsupported::Feature::ComputedArrayLengths
                    .diagnostic(Stage::Types, span, &[])
                    .with_found(found)
                    .into()),
            }
        }
        Ok(_) => Ok(None),
        Err(err) => {
            // `I32.BITS`, `U32.MAX`: an associated constant of a scalar type.
            if path.segments.len() == 2 {
                let prefix = Path { segments: path.segments[..1].to_vec(), span: path.segments[0].span };
                if let Ok(Entity::Builtin(Builtin::Scalar(t))) = a.resolve_path(m, &prefix) {
                    let name = &path.segments[1].name;
                    if let Some(ct) = builtin::assoc_const(&mut a.types, t, name) {
                        if ct != u32_ {
                            let shown = a.types.display(ct, &|d| a.def(d).name.clone(), &|i| format!("<{i}>"));
                            return Err(Diagnostic::new(
                                Stage::Types,
                                Code::E0401,
                                span,
                                format!("a constant expression has the type `U32`; `{found}` is `{shown}` (§4.5)"),
                            )
                            .with_found(found)
                            .into());
                        }
                        // A `U32` associated constant (`I32.BITS`): its value is the
                        // constant evaluator's (W5-08 types the whole grammar).
                        return Err(onsa_diag::unsupported::Feature::ComputedArrayLengths
                            .diagnostic(Stage::Types, span, &[])
                            .with_found(found)
                            .into());
                    }
                }
            }
            Err(err.into_diagnostic().into())
        }
    }
}
