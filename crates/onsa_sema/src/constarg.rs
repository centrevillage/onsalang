//! The constants of type positions: const arguments (`Ring[F32, 4]`) and array
//! lengths (`[F32; N]`, `[e; N]`). Spec §4.5: a constant expression of type
//! `U32`, checked like an ordinary expression with the expected type `U32`;
//! `U32` has no prefix `-` (`-1`, `-0`, E0401, S-228) and a constant of another
//! type is E0401 (R-154). One place for the signature lowering (`sig.rs`) and
//! the bodies (`body.rs`); W5-08 replaces the inside with the typing of the
//! whole constant-expression grammar.

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Ast, CallKind, ExprId, ExprKind, ItemKind, Lit, Path};

use crate::def::{DefKind, GenericDef};
use crate::names::body::{method_named, value_called};
use crate::names::{BuiltinMember, PathEnd};
use crate::resolve::{Builtin, Callee, Entity, NameKind, ResolveError};
use crate::ty::{IntKind, Ty, TyId};
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

/// An array length or a const argument written as an expression (`4`, `-1`, `N`,
/// `SIZE`, `cfg.N`, `I32.BITS`, `Self.N`): the one reader of the forms, for the
/// signatures and the bodies, with the type and const parameters in scope and the
/// type `Self` names (§2.2); `local` tells a chain of a body that starts at a
/// local. `Ok((value, constant))`: `constant` is the `const` item a name denotes.
/// Of an operation (E0200 until W9-03), a call, a local or a name of no constant
/// in it is the error first (§4.5, §18.1, S-713 (a)); of a call (E0417), the
/// error of the names stage of its callee and its arguments, as a body has it.
pub(crate) fn expr(
    a: &mut Analysis,
    m: ModId,
    ast: &Ast,
    text: &str,
    (generics, self_ty): (&[GenericDef], Option<TyId>),
    e: ExprId,
    local: &dyn Fn(ExprId) -> bool,
) -> Result<(ConstU32, Option<crate::DefId>), ConstErr> {
    Reader { m, ast, text, generics, self_ty, local }.expr(a, e)
}

/// What [`expr`] reads with: the module `m` of `ast`, the parameters in
/// scope, the type `Self` names and the locals.
struct Reader<'r> {
    m: ModId,
    ast: &'r Ast,
    text: &'r str,
    generics: &'r [GenericDef],
    self_ty: Option<TyId>,
    local: &'r dyn Fn(ExprId) -> bool,
}

impl Reader<'_> {
    fn expr(&self, a: &mut Analysis, e: ExprId) -> Result<(ConstU32, Option<crate::DefId>), ConstErr> {
        let ast = self.ast;
        if let Some(r) = literal(ast, self.text, e) {
            return r.map(|v| (ConstU32::Value(v), None)).map_err(ConstErr::Report);
        }
        let span = ast.expr(e).span;
        let found = self.text[span.start as usize..span.end as usize].to_string();
        if (self.local)(e) {
            return Err(value_not_constant(found, "a local", span).into());
        }
        if let Some(path) = path_of(ast, e) {
            return self.name(a, &path, span);
        }
        if let ExprKind::Call { callee, kind, args } = &ast.expr(e).kind {
            let callee = match kind {
                CallKind::Plain | CallKind::Bang => self.callee(a, *callee),
                CallKind::Value { .. } => self.before(a, *callee, false),
                // The callee of an instance is the flow stage's (W4-12).
                CallKind::Flow => None,
            };
            let mut args = args.iter().map(|x| x.expr);
            return Err(callee
                .or_else(|| args.find_map(|x| self.before(a, x, false)))
                .unwrap_or_else(|| value_not_constant(found, "a call", span).into()));
        }
        let mut leaves = Vec::new();
        operands(ast, e, &mut leaves);
        let wrong = leaves.into_iter().filter(|&l| l != e).filter_map(|l| match self.before(a, l, true) {
            Some(ConstErr::Report(d)) => Some(d),
            _ => None,
        });
        if let Some(d) = wrong.min_by(|x, y| x.unit_order().cmp(&y.unit_order())) {
            return Err(d.into());
        }
        let unsupported = onsa_diag::unsupported::Feature::ArrayLengthExprs.diagnostic(Stage::Types, span, &[]);
        Err(unsupported.with_found(found).into())
    }

    /// The error of the part `l` that comes before the error of what holds
    /// it: one of the names stage (§18.1), or an E0417 when `e0417`.
    fn before(&self, a: &mut Analysis, l: ExprId, e0417: bool) -> Option<ConstErr> {
        match self.expr(a, l) {
            Err(ConstErr::Report(d)) if d.stage == Stage::Names || (e0417 && d.code == Code::E0417) => Some(d.into()),
            _ => None,
        }
    }

    /// The error of the names stage of the callee `c` of `c(...)`, as a body
    /// has it (§15.1, §6.1): what is not found, a method named through its
    /// type, a constant called (E0020) and what is no value; a local and the
    /// members of a value (`K.x()`) are the types stage's.
    fn callee(&self, a: &mut Analysis, c: ExprId) -> Option<ConstErr> {
        let Some(path) = path_of(self.ast, c).filter(|_| !(self.local)(c)) else { return self.before(a, c, false) };
        let span = self.ast.expr(c).span;
        let shown = self.text[span.start as usize..span.end as usize].to_string();
        let kind = match generic(a, self.generics, &path) {
            Some((_, kind)) => kind,
            None => match path_end(a, self.m, &path, self.self_ty) {
                Ok(end) if end.method(a).is_some() => {
                    return Some(method_named(shown, &path.segments[path.segments.len() - 1].name, span).into());
                }
                Ok(end) => end.kind(a, span),
                Err(ResolveError::Failed) => return Some(ConstErr::Unknown),
                // A member of a value (`K.x()`) is the types stage's; a method
                // named through its type is no value whatever follows it.
                Err(ResolveError::NotANamespace { kind: Some(k), span: at, .. }) if k.is_value() => {
                    return self.method_before(a, &path, at);
                }
                Err(err) => return Some(err.into_diagnostic().into()),
            },
        };
        let want = "a function";
        match kind.at_callee() {
            // A flow is U3's E0821 (W4-12).
            Callee::Called | Callee::Flow => None,
            Callee::Value => Some(value_called(self.text, span).into()),
            Callee::NoValue => Some(ResolveError::Kind { shown, span, kind, want }.into_diagnostic().into()),
        }
    }

    /// E0308 for the method named through its type (`P.get` of
    /// `P.get.zz()`) before the name at `at` of `path`, as a body has it
    /// (§15.1, S-205); none for another name.
    fn method_before(&self, a: &Analysis, path: &Path, at: Span) -> Option<ConstErr> {
        let i = path.segments.iter().position(|s| s.span == at)?;
        let last = &path.segments[i.checked_sub(1)?];
        let span = Span::new(path.span.file, path.span.start, last.span.end);
        let before = Path { segments: path.segments[..i].to_vec(), span };
        // `before` resolved on the way to `at`.
        let Ok(end) = path_end(a, self.m, &before, self.self_ty) else { return None };
        end.method(a)?;
        let shown = self.text[span.start as usize..span.end as usize].to_string();
        Some(method_named(shown, &last.name, span).into())
    }

    /// The name `path` at `span`: a const parameter, or a constant
    /// ([`named_def`]); a parameter of another kind is an error
    /// ([`not_constant`]).
    fn name(&self, a: &mut Analysis, path: &Path, span: Span) -> Result<(ConstU32, Option<crate::DefId>), ConstErr> {
        match generic(a, self.generics, path) {
            Some((i, NameKind::ConstParam)) => Ok((ConstU32::Param(i), None)),
            Some((_, kind)) => Err(not_constant(kind, path.segments[0].name.clone(), span)),
            None => {
                let (v, constant) = named_def(a, self.m, (self.ast, self.text), path, self.self_ty, span)?;
                Ok((ConstU32::Value(v), constant))
            }
        }
    }
}

/// The parameter of `generics` a path of one name names, with its kind
/// (§15.1): the one question of the constants of a body and a signature.
pub(crate) fn generic(a: &Analysis, generics: &[GenericDef], path: &Path) -> Option<(u32, NameKind)> {
    let [seg] = &path.segments[..] else { return None };
    let i = generics.iter().position(|g| g.name == seg.name)?;
    a.note_use(generics[i].span, seg.span);
    Some((i as u32, NameKind::of_generic(&generics[i].kind)))
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

/// A name of a constant (`SIZE`, `cfg.N`, `I32.BITS`, `Self.N`, `Al.N` of an
/// alias, §4.4) at `span`: its value, when its type is `U32`; a name of
/// another kind is an error ([`not_constant`]). `ast` is the module `m` the
/// name is written in, and `self_ty` the type `Self` names. A body reads the
/// entity its record has ([`of_entity`], [`of_builtin`]).
pub(crate) fn named(
    a: &mut Analysis,
    m: ModId,
    (ast, text): (&Ast, &str),
    path: &Path,
    self_ty: Option<TyId>,
    span: Span,
) -> Result<u32, ConstErr> {
    Ok(named_def(a, m, (ast, text), path, self_ty, span)?.0)
}

/// [`named`], with the `const` item the name denotes.
fn named_def(
    a: &mut Analysis,
    m: ModId,
    (ast, text): (&Ast, &str),
    path: &Path,
    self_ty: Option<TyId>,
    span: Span,
) -> Result<(u32, Option<crate::DefId>), ConstErr> {
    let shown = text[span.start as usize..span.end as usize].to_string();
    match path_end(a, m, path, self_ty) {
        // A method named through its type, no value (§15.1, S-205).
        Ok(end) if end.method(a).is_some() => {
            Err(method_named(shown, &path.segments[path.segments.len() - 1].name, span).into())
        }
        Ok(PathEnd::Entity(entity)) => {
            let constant = match entity {
                Entity::Def(d) | Entity::Member(d) => Some(d),
                _ => None,
            };
            match of_entity(a, m, ast, text, entity, span)? {
                Some(v) => Ok((v, constant)),
                None => Err(not_constant(NameKind::of_named(entity, &a.defs, span), shown, span)),
            }
        }
        // `I32.BITS`, `U32.MAX`, `Sample.PI`: an associated constant of a
        // scalar type, the last name.
        Ok(PathEnd::Builtin { of: Entity::Builtin(Builtin::Scalar(t)), member: BuiltinMember::Constant }) => {
            let name = &path.segments[path.segments.len() - 1].name;
            match of_builtin(a, t, name, text, span) {
                Some(Ok(Some(v))) => Ok((v, None)),
                Some(Err(e)) => Err(e),
                _ => onsa_diag::internal::bug(Some(span), "an associated constant of no scalar's table"),
            }
        }
        Ok(PathEnd::Builtin { member, .. }) => Err(not_constant(member.kind(), shown, span)),
        // A name held as an error (§18.1, S-462, S-675): no diagnostic, and
        // the check goes on (S-689).
        Err(ResolveError::Failed) => Err(ConstErr::Unknown),
        Err(err) => Err(err.into_diagnostic().into()),
    }
}

/// What `path` names ([`Analysis::path_end`]); an alias of the error type
/// stands for a failed name, as at the head of a value path (§18.1, S-728).
fn path_end(a: &Analysis, m: ModId, path: &Path, self_ty: Option<TyId>) -> Result<PathEnd, ResolveError> {
    match a.path_end(m, path, self_ty)? {
        PathEnd::Entity(e) if a.alias_type(e).is_err() => Err(ResolveError::Failed),
        end => Ok(end),
    }
}

/// The value of the constant `entity` a name at `span` names (as [`named`]).
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

/// The associated constant `name` of the scalar type `t` at `span` (`I32.BITS`,
/// `U32.MAX`), as [`named`] reads it; none when the compiler's table has none.
pub(crate) fn of_builtin(
    a: &mut Analysis,
    t: crate::ty::TyId,
    name: &str,
    text: &str,
    span: Span,
) -> Option<Result<Option<u32>, ConstErr>> {
    let found = text[span.start as usize..span.end as usize].to_string();
    let u32_ = a.types.int(IntKind::U32);
    let ct = builtin::assoc_const(&mut a.types, t, name)?;
    if ct != u32_ {
        let shown = a.types.display(ct, &|d| a.def(d).name.clone(), &|i| format!("<{i}>"));
        return Some(Err(Diagnostic::new(
            Stage::Types,
            Code::E0401,
            span,
            format!("a constant expression has the type `U32`; `{found}` is `{shown}` (§4.5)"),
        )
        .with_found(found)
        .into()));
    }
    // A `U32` associated constant (`I32.BITS`): its value is the constant
    // evaluator's (W5-08 types the whole grammar).
    Some(Err(ConstErr::Uncomputed(
        onsa_diag::unsupported::Feature::ComputedArrayLengths.diagnostic(Stage::Types, span, &[]).with_found(found),
    )))
}
