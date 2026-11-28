//! The default values of the types (§6.3) and the bodies of what a derive
//! makes (§6.4). All are the forms of Core a body lowers to: a `default()` is
//! the row of the values of its fields, no opaque operation (S-697), and no
//! later stage knows of them. A body is one function for each instance of its
//! type, of the size of the type: `from_ordinal` is one `If` for each variant.

use onsa_diag::Span;
use onsa_sema::DefId;
use onsa_sema::def::{DefKind, DerivedFn, FieldDef, Fields, FnDef as SFnDef};
use onsa_sema::ty::Ty as STy;

use super::build::{cmp, stmt, tag_of, u32_lit};
use super::{GenericArg, Lowerer, R, core_mode, internal};
use crate::ir::*;

/// The default of `ty` when it comes of its structure, with no declaration to
/// call (§6.3), the one judgment of that: the element of an array is one
/// value, evaluated once and copied.
pub(super) fn structural_default(lw: &mut Lowerer, ty: CTy, span: Span) -> Option<R<Expr>> {
    let kind = match lw.m.tys.kind(ty).clone() {
        TyKind::Unit => Ok(ExprKind::Lit(Lit::Unit)),
        TyKind::Tuple(ts) => ts.iter().map(|&t| default_value(lw, t, span)).collect::<R<_>>().map(ExprKind::Tuple),
        TyKind::Array(elem, n) => default_value(lw, elem, span).map(|e| ExprKind::Repeat { elem: Box::new(e), n }),
        _ => return None,
    };
    Some(kind.map(|kind| Expr::new(ty, span, kind)))
}

/// The default value of `ty` (§6.3): the one path of a field, of an
/// element and of the omitted `init` of a delay (§11.4). It recurs on the
/// structure of the type, and a struct is a call: its fields are lowered
/// once, for its function.
pub(super) fn default_value(lw: &mut Lowerer, ty: CTy, span: Span) -> R<Expr> {
    if let Some(value) = structural_default(lw, ty, span) {
        return value;
    }
    let (member, args) = lw.member_of(ty, DerivedFn::Default.name(), span)?;
    Ok(Expr::new(ty, span, ExprKind::Call { fn_: lw.fn_id(member, args, span)?, args: Vec::new() }))
}

/// The read of the default `d` of a field of the type `ty` of a struct at
/// `args` (§4.4): the constant of the instance, burnt in once (S-918).
fn declared_default(lw: &mut Lowerer, d: DefId, ty: CTy, args: &[GenericArg], span: Span) -> R<Expr> {
    Ok(Expr::new(ty, span, ExprKind::Const(lw.const_id(d, args.to_vec(), span)?)))
}

/// The value of the field `name` of the struct `id` that a struct literal
/// leaves to its last `...` ([`Unwritten::Literal`]).
pub(super) fn filled_field(lw: &mut Lowerer, id: TypeId, name: &str, span: Span) -> R<Expr> {
    let (fields, args) = named_fields(lw, id, span)?;
    let Some(f) = fields.iter().find(|f| f.name == name) else { return Err(internal(span, "missing field")) };
    field_default(lw, f, &args, span, Unwritten::Literal)
}

/// The named fields of the struct `id` and the generic arguments of its declaration.
fn named_fields<'a>(lw: &Lowerer<'a>, id: TypeId, span: Span) -> R<(&'a [FieldDef], Vec<GenericArg>)> {
    let (d, args) = lw.type_decl(id, span)?;
    match lw.a.def(d).as_struct().map(|s| &s.fields) {
        Some(Fields::Named(fields)) => Ok((fields, args)),
        _ => Err(internal(span, "a struct of no named fields")),
    }
}

/// What gives the value of a field the source does not write.
enum Unwritten {
    /// A struct literal's last `...`: the default the field declares at the
    /// arguments of the type of the literal (§4.4, S-918), with no
    /// `default()` (a hand-written `impl Default` is not called). The checks
    /// left no other.
    Literal,
    /// A derived `default()`: the default the field declares, else the
    /// default of its type (§6.4).
    Derived,
}

/// The value of the field `f` the source does not write, given by `by`.
// SPEC-GAP(S-173): the default of a field that reads a constant made by this
// `default()` (`struct P: Default { x: U32 = A.x }`, `const A: P = P.default()`)
// is no E0312: `const_id` follows no call, so it stops, and the evaluation
// panics at the cycle (`const_cycle`), as for `const A: U32 = f()` through a
// function.
fn field_default(lw: &mut Lowerer, f: &FieldDef, args: &[GenericArg], span: Span, by: Unwritten) -> R<Expr> {
    let ty = lw.core_ty(f.ty, args, span)?;
    match (f.default, by) {
        (Some(d), _) => declared_default(lw, d, ty, args, span),
        (None, Unwritten::Derived) => default_value(lw, ty, span),
        (None, Unwritten::Literal) => Err(internal(span, "missing field")),
    }
}

/// A block of the value `e` alone.
fn valued(e: Expr) -> Block {
    Block { stmts: Vec::new(), value: Some(Box::new(e)) }
}

/// The body of `default()` of the struct `id`.
fn default_body(lw: &mut Lowerer, id: TypeId, span: Span) -> R<Block> {
    let (fields, args) = named_fields(lw, id, span)?;
    let fields = (0..)
        .zip(fields)
        .map(|(k, f)| Ok((k, field_default(lw, f, &args, span, Unwritten::Derived)?)))
        .collect::<R<_>>()?;
    Ok(valued(Expr::new(lw.ty(TyKind::Struct(id)), span, ExprKind::Struct { ty: id, fields })))
}

/// The body of `ordinal()`: the tag is the place of the variant in the
/// declaration, from 0 (§6.4).
fn ordinal_body(lw: &Lowerer, this: Expr, span: Span) -> R<Block> {
    let tag = tag_of(lw, this)?;
    Ok(valued(if tag.ty == Types::U32 { tag } else { Expr::new(Types::U32, span, ExprKind::Cast(Box::new(tag))) }))
}

/// The body of `from_ordinal(n)` of the enum `id`, of the type `Option[Self]`
/// `option`: one test for each variant, and `None` beyond the last (§6.4).
fn from_ordinal_body(lw: &mut Lowerer, n: Expr, id: TypeId, option: TypeId, span: Span) -> R<Block> {
    let (d, _) = lw.type_decl(option, span)?;
    let Some(row) = lw.a.modules.lang.of(d) else {
        return Err(internal(span, "`from_ordinal` of a type that is not `Option`"));
    };
    let (option_ty, id_ty) = (lw.ty(TyKind::Enum(option)), lw.ty(TyKind::Enum(id)));
    let wrapped =
        |tag: u32, fields: Vec<Expr>| Expr::new(option_ty, span, ExprKind::Variant { ty: option, tag, fields });
    let mut stmts = Vec::new();
    for tag in 0..lw.enum_variants(id).len() as u32 {
        let variant = Expr::new(id_ty, span, ExprKind::Variant { ty: id, tag, fields: Vec::new() });
        let found = vec![stmt(span, StmtKind::Return(Some(wrapped(row.keep, vec![variant]))))];
        let test = cmp(CmpOp::Eq, n.clone(), u32_lit(span, tag));
        stmts.push(stmt(span, StmtKind::If(test, Block { stmts: found, value: None }, Block::default())));
    }
    Ok(Block { stmts, value: Some(Box::new(wrapped(row.exit, Vec::new()))) })
}

impl Lowerer<'_> {
    /// The declaration of the struct or the enum `id` and its generic arguments.
    fn type_decl(&self, id: TypeId, span: Span) -> R<(DefId, Vec<GenericArg>)> {
        self.type_defs.get(&id).cloned().ok_or_else(|| internal(span, "a type of no declaration"))
    }

    /// The member `name` of the type `ty` and the generic arguments of its
    /// `impl`: what a use of a member of a type parameter is at the type the
    /// parameter is instantiated at (§6.3). A type a member is asked of has
    /// it, by the bounds the types stage judged; `Str` and `Bytes` do not come
    /// here, stopped by `core_ty` (E0200).
    pub(super) fn member_of(&self, ty: CTy, name: &str, span: Span) -> R<(DefId, Vec<GenericArg>)> {
        let key = match *self.m.tys.kind(ty) {
            TyKind::Struct(id) | TyKind::Enum(id) => {
                let (d, args) = self.type_decl(id, span)?;
                let member = self.a.modules.assoc.get(&d).and_then(|t| t.get(name));
                let of = |&m: &DefId| (m, self.impl_args(m, args));
                return member.map(of).ok_or_else(|| internal(span, "a member its type does not have"));
            }
            TyKind::Int(k) => STy::Int(k),
            TyKind::Float(k) => STy::Float(k),
            TyKind::Bool => STy::Bool,
            _ => return Err(internal(span, "a member of a type with no declaration")),
        };
        let table = self.a.types.find(&key).and_then(|k| self.a.modules.assoc_builtin.get(&k));
        let member = table.and_then(|t| t.get(name));
        member.map(|&m| (m, Vec::new())).ok_or_else(|| internal(span, "a member std does not declare"))
    }

    /// The generic arguments of the `impl` of the member `m`, of the arguments
    /// `args` of its type: its heading names its parameters in any order (§6.2).
    fn impl_args(&self, m: DefId, args: Vec<GenericArg>) -> Vec<GenericArg> {
        let types = &self.a.types;
        let imp = self.a.def(m).owner.and_then(|o| self.a.def(o).as_impl());
        let Some((imp, STy::Named(_, written))) = imp.map(|i| (i, types.get(i.self_ty))) else { return args };
        let at = |k: usize| written.iter().position(|&w| matches!(types.get(w), STy::Param(p) if *p as usize == k));
        (0..imp.generics.len()).filter_map(at).map(|k| args[k].clone()).collect()
    }

    /// Fill the function `fid` of `d`, the member `made` a derive makes, at
    /// `args`. Its name is the one of a member written (`dsp.P.default`).
    pub(super) fn lower_derived(
        &mut self,
        d: DefId,
        f: &SFnDef,
        made: DerivedFn,
        args: &[GenericArg],
        fid: FnId,
    ) -> R<()> {
        let a = self.a;
        let def = a.def(d);
        let span = def.span;
        let Some(DefKind::Impl(imp)) = def.owner.map(|o| &a.def(o).kind) else {
            return Err(internal(span, "a derived member out of its `impl`"));
        };
        let this = self.core_ty(imp.self_ty, args, span)?;
        let ret = self.core_ty(f.ret, args, span)?;
        let mut params = Vec::new();
        let mut locals = Vec::new();
        let mut bind = |name: &str, mode, ty: CTy| {
            params.push(Param { local: LocalId(locals.len() as u32), mode: core_mode(mode), ty });
            locals.push(Local::value(name, ty));
        };
        if let Some(mode) = f.self_mode {
            bind("self", mode, this);
        }
        for p in &f.params {
            bind(&p.name, p.mode, self.core_ty(p.ty, args, p.span)?);
        }
        // A body has at most one parameter: `self`, or the number.
        let param = params.first().map(|p| Expr::new(p.ty, span, ExprKind::Local(p.local)));
        let block = match (made, self.m.tys.kind(this).clone(), self.m.tys.kind(ret).clone(), param) {
            (DerivedFn::Default, TyKind::Struct(id), ..) => default_body(self, id, span)?,
            (DerivedFn::Ordinal, TyKind::Enum(_), _, Some(this)) => ordinal_body(self, this, span)?,
            (DerivedFn::FromOrdinal, TyKind::Enum(id), TyKind::Enum(option), Some(n)) => {
                from_ordinal_body(self, n, id, option, span)?
            }
            _ => return Err(internal(span, "a derived member of another form of type")),
        };
        self.fill_fn(fid, params, ret, f.rt, locals, Some(block));
        Ok(())
    }
}
