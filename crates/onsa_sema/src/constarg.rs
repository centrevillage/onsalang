//! The constants of type positions: const arguments (`Ring[F32, 4]`) and array
//! lengths (`[F32; N]`, `[e; N]`). Spec §4.5: a constant expression of type
//! `U32`, checked like an ordinary expression with the expected type `U32`;
//! `U32` has no prefix `-` (`-1`, `-0`, E0401, S-228) and a constant of another
//! type is E0401 (R-154). One place for the signature lowering (`sig.rs`),
//! the bodies (`body.rs`) and the flows, which reads the records of the names
//! the names stage made once (`names::body`, D-15): the leaves by their type,
//! the nodes by the grammar (S-966).

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, ItemKind, Lit, Path};
use onsa_syntax::constexpr::ConstForm;

use crate::def::{DefKind, GenericKind};
use crate::names::body::{BodyNames, PathRes};
use crate::resolve::{Entity, NameKind, ResolveError};
use crate::ty::{IntKind, Ty, TyId};
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
    /// An error (`Report`, `Uncomputed`) of a constant of the items `owners`
    /// (`impl`s), or of a node over such constants, which an error of one of
    /// their headings holds back (§18.1, S-304): a signature reports it once
    /// the headings are judged; a body knows them ([`unread`]), and reads the
    /// error itself ([`ConstErr::unheld`]).
    OfOwner(Vec<DefId>, Box<ConstErr>),
}

/// A [`ConstErr`] with no `OfOwner`: the error itself, to a reader that
/// knows the errors of the headings (a body, [`unread`]).
#[derive(Debug)]
pub(crate) enum Unheld {
    Report(Diagnostic),
    Uncomputed(Diagnostic),
    Unknown,
}

impl ConstErr {
    /// The error itself, of a reader that knows the errors of the headings.
    pub(crate) fn unheld(self) -> Unheld {
        match self {
            ConstErr::Report(d) => Unheld::Report(d),
            ConstErr::Uncomputed(d) => Unheld::Uncomputed(d),
            ConstErr::Unknown => Unheld::Unknown,
            ConstErr::OfOwner(_, e) => e.unheld(),
        }
    }
}

impl From<Diagnostic> for ConstErr {
    fn from(d: Diagnostic) -> ConstErr {
        ConstErr::Report(d)
    }
}

/// What a constant expression is read with: the module `m` of `ast`, and the
/// records of the names of the expression, which the names stage made once
/// (a body's, or [`crate::names::body::const_names`]'; §15.1, D-15): of its
/// names, its chains held as an error and its type arguments.
pub(crate) struct ConstCx<'r> {
    pub m: ModId,
    pub ast: &'r Ast,
    pub text: &'r str,
    pub names: &'r BodyNames,
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
    /// An operation, whose value this version does not compute (K-05), over
    /// constants of the items `owners` ([`Got::owners`]).
    Op(Vec<DefId>),
    /// The error type: a name held as an error, a constant of a failed unit
    /// in it (§18.1). The nodes above it report nothing.
    Unknown,
    /// A constant whose value this version does not compute (its error,
    /// held as of its `impl` too).
    Uncomputed(ConstErr),
}

impl Got {
    /// The items of the constants it reads (`impl`s), whose headings hold
    /// back an error of a node over it (S-304), as of the constants' own.
    fn owners(&self, a: &Analysis) -> Vec<DefId> {
        match self {
            Got::Val(_, Some(d)) => a.def(*d).owner.into_iter().collect(),
            Got::Op(os) | Got::Uncomputed(ConstErr::OfOwner(os, _)) => os.clone(),
            _ => Vec::new(),
        }
    }
}

/// The error `e`, held as of the items `owners` (none: not held).
fn held(owners: Vec<DefId>, e: ConstErr) -> ConstErr {
    if owners.is_empty() { e } else { ConstErr::OfOwner(owners, Box::new(e)) }
}

/// The value of a whole constant expression at `span`, of what it reads as.
fn finish(got: Got, span: Span) -> Result<(ConstU32, Option<DefId>), ConstErr> {
    match got {
        Got::Val(v, d) => Ok((v, d)),
        Got::Op(owners) => Err(held(
            owners,
            ConstErr::Uncomputed(onsa_diag::unsupported::Feature::ArrayLengthExprs.diagnostic(Stage::Types, span, &[])),
        )),
        Got::Unknown => Err(ConstErr::Unknown),
        Got::Uncomputed(e) => Err(e),
    }
}

/// [`Got`] of what a leaf reads as (an error to report is `Err`).
fn settle(r: Result<Got, ConstErr>) -> Result<Got, ConstErr> {
    match r {
        Err(e @ ConstErr::Uncomputed(_)) => Ok(Got::Uncomputed(e)),
        Err(ConstErr::OfOwner(o, e)) if matches!(*e, ConstErr::Uncomputed(_)) => {
            Ok(Got::Uncomputed(ConstErr::OfOwner(o, e)))
        }
        Err(ConstErr::Unknown) => Ok(Got::Unknown),
        r => r,
    }
}

/// The node `e`, its operands first (§4.5, §4.7: as an ordinary expression
/// of the expected type `U32`), stopping at the first error. The leaves are
/// read by their type, and the nodes by the grammar (S-966): a node outside
/// it is E0417 whatever is in it, whose names the names stage read (S-968).
/// The grammar is the syntax's ([`Ast::const_form`]).
fn node(a: &mut Analysis, cx: &ConstCx, e: ExprId) -> Result<Got, ConstErr> {
    let expr = cx.ast.expr(e);
    let shown = || cx.text[expr.span.start as usize..expr.span.end as usize].to_string();
    // A prefix `-` before a numeric literal, whatever its value (S-228).
    if cx.ast.negated_literal(e).is_some() {
        return Err(no_negative(shown(), expr.span).into());
    }
    match cx.ast.const_form(e) {
        ConstForm::Chain(c) => {
            if cx.names.held.contains(&e) {
                return Ok(Got::Unknown);
            }
            // Its type arguments (`Pl::[F32].K`, E0412; S-329), before what it names.
            if let Some(d) = cx.names.args_diag(cx.ast, e) {
                return Err(d.clone().into());
            }
            let records: Vec<PathRes> = c.names.iter().map_while(|(n, _)| cx.names.paths.get(n).cloned()).collect();
            let at = (&c.names[0].1.name[..], shown(), expr.span);
            settle(chain(a, (cx.m, cx.ast, cx.text), &records, c.names.len(), at))
        }
        ConstForm::Paren(x) => node(a, cx, x),
        // `U32` has no prefix `-` (§3.4, S-228), but of the error type.
        ConstForm::Neg(x) => match node(a, cx, x)? {
            Got::Unknown => Ok(Got::Unknown),
            x => Err(held(x.owners(a), no_negative(shown(), expr.span).into())),
        },
        ConstForm::Arith(lhs, rhs) => {
            let (l, r) = (node(a, cx, lhs)?, node(a, cx, rhs)?);
            let owners = [l.owners(a), r.owners(a)].concat();
            match (l, r) {
                (Got::Unknown, _) | (_, Got::Unknown) => Ok(Got::Unknown),
                // A const parameter has no value to compute with (§4.5, S-50).
                (Got::Val(ConstU32::Param(_), _), _) | (_, Got::Val(ConstU32::Param(_), _)) => Err(held(
                    owners,
                    value_not_constant(shown(), "an operation on a const parameter", expr.span).into(),
                )),
                _ => Ok(Got::Op(owners)),
            }
        }
        // An integer literal, and a literal of another type (§4.5, S-966).
        ConstForm::Lit(lit) => {
            let form = match lit {
                Lit::Int { value, .. } => return Ok(int_literal(*value, shown(), expr.span)?),
                Lit::Float { .. } => "a float literal",
                Lit::Bool(_) => "a `Bool` literal",
                Lit::Str(_) => "a string literal",
                Lit::Char(_) => "a character literal",
            };
            let msg = format!("a constant expression has the type `U32`; found {form} (§4.5)");
            Err(Diagnostic::new(Stage::Types, Code::E0401, expr.span, msg).with_found(shown()).into())
        }
        ConstForm::Error => Ok(Got::Unknown),
        ConstForm::Outside => {
            let noun = match &expr.kind {
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
            Err(value_not_constant(shown(), noun, expr.span).into())
        }
    }
}

/// The chain of `len` names whose records from its head are `records`
/// (`head` its first name, `shown` at `span` the whole), not held as an
/// error: a const parameter, or a constant ([`of_entity`]); what is no
/// constant is E0417 when it is a value (§4.5, S-713 (a)), else E0308. A
/// chain whose records end before its last name ends at a value whose field
/// follows (S-967), or is one whose names the walk did not read. A type
/// parameter, a namespace and a builtin name of a flow end no chain the
/// names stage passes (its E0308).
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
            NameKind::Constant => Err(uninstantiated(shown, head, span).into()),
            kind => Err(not_constant(kind, shown, span)),
        },
        PathRes::Item { entity, owner } => {
            let d = match entity {
                Entity::Def(d) | Entity::Member(d) => Some(d),
                _ => None,
            };
            match of_entity(a, (m, ast, text), (entity, owner), (head, span))? {
                Some(v) => Ok(Got::Val(ConstU32::Value(v), d)),
                None => Err(not_constant(NameKind::of_named(entity, &a.defs, span), shown, span)),
            }
        }
        PathRes::TypeParam(_) | PathRes::Namespace(_) | PathRes::FlowBuiltin(_) => {
            Err(value_not_constant(shown, "a name of another kind", span).into())
        }
    }
}

/// E0417 for the constant `shown` at `span` of the type parameter or the
/// generic `Self` `head` (`T.BITS`, S-898; `Self.CAP`, S-329): its value is
/// the instantiation's (§4.5).
fn uninstantiated(shown: String, head: &str, span: Span) -> Diagnostic {
    let msg =
        format!("`{shown}` has no value before `{head}` is instantiated: a constant expression names constants (§4.5)");
    Diagnostic::new(Stage::Types, Code::E0417, span, msg).with_found(shown)
}

/// E0401 for a prefix `-` at `span`: `U32` has none (§3.4, §4.5, S-228).
fn no_negative(shown: String, span: Span) -> Diagnostic {
    let msg = "a constant expression has the type `U32`, which has no prefix `-` (also not `-0`) (§3.4, §4.5)";
    Diagnostic::new(Stage::Types, Code::E0401, span, msg).with_found(shown)
}

/// The operands of the arithmetic of `e`, under parentheses, prefix `-` and
/// binary operators; `e` itself when it is none of them. It goes under every
/// unary and binary operator (`!K`, `K < 1`): more than the grammar of
/// [`Ast::const_form`], whose operators are those of `BinOp::in_constant`,
/// so the order of the declarations reads more names than `node` does.
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

/// The integer literal `shown` at `span` of the value `value`: E0408 when
/// it does not fit in `U32`.
fn int_literal(value: u64, shown: String, span: Span) -> Result<Got, Diagnostic> {
    match u32::try_from(value) {
        Ok(v) => Ok(Got::Val(ConstU32::Value(v), None)),
        Err(_) => {
            let msg = format!("`{value}` does not fit in `U32`, the type of a constant expression (§4.5)");
            Err(Diagnostic::new(Stage::Types, Code::E0408, span, msg).with_found(shown))
        }
    }
}

/// The value of the constant `entity` a name at `span` names (`None` when
/// it is no constant), in the module `m` of `ast`: of a generic `impl`, at
/// the arguments the type `owner` an alias or `Self` stands for gives
/// ([`impl_args`]; `head` is the first name).
pub(crate) fn of_entity(
    a: &mut Analysis,
    (m, ast, text): (ModId, &Ast, &str),
    (entity, owner): (Entity, Option<TyId>),
    (head, span): (&str, Span),
) -> Result<Option<u32>, ConstErr> {
    let (Entity::Def(d) | Entity::Member(d)) = entity else { return Ok(None) };
    let found = text[span.start as usize..span.end as usize].to_string();
    let def = a.def(d).clone();
    let DefKind::Const(c) = &def.kind else { return Ok(None) };
    // A constant of a cycle (E0311, §18.1, S-734), and of an `impl` with an
    // error of its heading.
    if c.int_value.is_none() && a.partly_read(d) || a.decls.cyclic.contains(&d) || unread(a, d) {
        return Err(ConstErr::Unknown);
    }
    value_of(a, (m, ast), (d, &def, c), owner, (head, found, span)).map_err(|e| match (e, def.owner) {
        (e @ (ConstErr::Report(_) | ConstErr::Uncomputed(_)), Some(o)) => ConstErr::OfOwner(vec![o], Box::new(e)),
        (e, _) => e,
    })
}

/// `d` is a constant of an `impl` with an error of its heading (`impl[T]
/// N[T]` for `N[T: Num]`), which is read as it is: a read of it decides
/// nothing and reports nothing (§18.1, S-304). Of the record of the
/// failures, which the bodies have from the signatures on (`stages`).
pub(crate) fn unread(a: &Analysis, d: DefId) -> bool {
    let def = a.def(d);
    matches!(def.kind, DefKind::Const(_)) && def.owner.is_some_and(|o| a.failures.failed(o))
}

/// [`of_entity`] of the constant `d` (`def`, `c`), whose value is read.
fn value_of(
    a: &mut Analysis,
    (m, ast): (ModId, &Ast),
    (d, def, c): (DefId, &crate::def::Def, &crate::def::ConstDef),
    owner: Option<TyId>,
    (head, found, span): (&str, String, Span),
) -> Result<Option<u32>, ConstErr> {
    let u32_ = a.types.int(IntKind::U32);
    let args = impl_args(a, d, c.ty, owner, (head, &found, span))?;
    // An argument not decided stays its parameter, shown as `_`.
    let given: Vec<TyId> = (0..).zip(&args).map(|(k, t)| t.unwrap_or_else(|| a.types.intern(Ty::Param(k)))).collect();
    let ty = a.types.subst(c.ty, &given);
    if ty != u32_ && !matches!(a.types.get(ty), Ty::Error) {
        let shown = a.types.display(ty, &|d| a.def(d).name.clone(), &|_| "_".to_string());
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
    judge_args(a, d, &args, (&found, span))?;
    // A constant that is its const parameter reads the argument (S-304).
    let of_param = c.param.and_then(|p| match given.get(p as usize).map(|&t| a.types.get(t)) {
        Some(Ty::ConstVal(v)) => Some(u64::from(*v)),
        _ => None,
    });
    match c.int_value.or(of_param) {
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

/// The arguments of the parameters of the generic `impl` of the constant
/// `d` of the type `ty` (none of another constant; `None`: not decided), of
/// the type `owner` an alias or `Self` stands for (§4.4, S-595): its
/// arguments at the places of the parameters in the type of the `impl`, each
/// there once (§6.2). With no `owner`, a parameter that is the type of `d`
/// is `U32`, the type of a constant expression (S-304). The type of a
/// generic `Self` has none before it is instantiated (E0417, S-329); one
/// with an error, and an `impl` whose type does not have its parameters so
/// (its E0307), read as the error type (§18.1). `(head, found, span)`: the
/// first name, and the whole as written.
fn impl_args(
    a: &mut Analysis,
    d: DefId,
    ty: TyId,
    owner: Option<TyId>,
    (head, found, span): (&str, &str, Span),
) -> Result<Vec<Option<TyId>>, ConstErr> {
    let Some(DefKind::Impl(i)) = a.def(d).owner.map(|o| &a.def(o).kind) else { return Ok(Vec::new()) };
    let (generics, self_ty) = (i.generics.clone(), i.self_ty);
    if generics.is_empty() {
        return Ok(Vec::new());
    }
    let args_of = |t: &Ty| match t {
        Ty::Named(_, args) | Ty::Builtin(_, args) => Some(args.clone()),
        _ => None,
    };
    let Some(target) = args_of(a.types.get(self_ty)) else { return Err(ConstErr::Unknown) };
    // The place of each parameter in the type of the `impl`.
    let mut place = vec![None; generics.len()];
    for (j, &t) in target.iter().enumerate() {
        match a.types.get(t) {
            &Ty::Param(k) if place.get(k as usize) == Some(&None) => place[k as usize] = Some(j),
            _ => return Err(ConstErr::Unknown),
        }
    }
    let Some(place) = place.into_iter().collect::<Option<Vec<usize>>>() else { return Err(ConstErr::Unknown) };
    match owner {
        Some(o) if a.types.open(o) => Err(uninstantiated(found.to_string(), head, span).into()),
        Some(o) => match args_of(a.types.get(o)) {
            Some(given) if given.len() == target.len() && !a.types.has_error(o) => {
                Ok(place.iter().map(|&j| Some(given[j])).collect())
            }
            _ => Err(ConstErr::Unknown),
        },
        None => {
            let (u32_, own) = (a.types.int(IntKind::U32), a.types.get(ty).clone());
            let decided = |k: usize| own == Ty::Param(k as u32) && matches!(generics[k].kind, GenericKind::Type { .. });
            Ok((0..generics.len()).map(|k| decided(k).then_some(u32_)).collect())
        }
    }
}

/// The arguments `args` of the parameters of the generic `impl` of the
/// constant `d` named at `span` (`found` as written), as a use of a value
/// judges them (§4.5, S-304): the decided ones first, as of the statement
/// that decides them, each by the first of its requirements it does not meet
/// ([`crate::body::generics::requirements`]: E0710, or E0416; an unknown
/// bound is met, §18.1); then E0406 for the first one not decided, with no
/// candidate (which arguments is the writer's).
fn judge_args(a: &Analysis, d: DefId, args: &[Option<TyId>], (found, span): (&str, Span)) -> Result<(), ConstErr> {
    use crate::body::generics::{Requirement, alias_way, head_of, parameter, requirements};
    let Some(DefKind::Impl(i)) = a.def(d).owner.map(|o| &a.def(o).kind) else { return Ok(()) };
    let owner = format!("the `impl` of `{}`", head_of(a, i.self_ty).unwrap_or_default());
    let (under, std) = (crate::body::bounds::Bounds { a, generics: &[] }, a.modules.is_std(a.def(d).module));
    let show = |t: TyId| a.types.display(t, &|d| a.def(d).name.clone(), &|i| format!("<{i}>"));
    for (g, &arg) in i.generics.iter().zip(args) {
        let (Some(arg), Some(mut wants)) = (arg, requirements(g, false)) else { continue };
        let Some(q) = wants.find(|&q| match q {
            Requirement::Escape { lifted, .. } => crate::sig::no_kind_argument(&under, arg, lifted),
            Requirement::Bound(b) => !under.meets(arg, b),
        }) else {
            continue;
        };
        let shown = show(arg);
        let e = match q {
            Requirement::Escape { rule, .. } => {
                let msg = crate::deferred::second_class_argument(&shown, &parameter(g, &owner));
                Diagnostic::new(Stage::Types, Code::E0710, span, msg).with_rule(rule)
            }
            Requirement::Bound(b) => {
                let what = crate::deferred::Required::Param { param: g.name.clone(), owner: owner.clone(), std };
                let e = Diagnostic::new(Stage::Types, Code::E0416, span, what.unmet(&shown, b, &mut |t| show(t)));
                match crate::traits::number_traits_note(a.types.get(arg), &shown, b) {
                    Some(note) => e.with_rule(note),
                    None => e,
                }
            }
        };
        return Err(e.with_found(found).into());
    }
    let Some(k) = args.iter().position(Option::is_none) else { return Ok(()) };
    let what = parameter(&i.generics[k], &owner);
    // No function decides it later, nor an annotation (§4.5).
    let msg =
        format!("{what} cannot be determined: a constant expression names a type with its arguments (§4.5, §4.7)");
    let way = alias_way(&head_of(a, i.self_ty).unwrap_or_default(), &a.def(d).name);
    Err(Diagnostic::new(Stage::Types, Code::E0406, span, msg).with_found(found).with_rule(way).into())
}
