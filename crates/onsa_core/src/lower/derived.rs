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
pub(super) fn structural_default(lw: &mut Lowerer, ty: &Ty, span: Span) -> Option<R<Expr>> {
    let kind = match ty {
        Ty::Unit => Ok(ExprKind::Lit(Lit::Unit)),
        Ty::Tuple(ts) => ts.iter().map(|t| default_value(lw, t, span)).collect::<R<_>>().map(ExprKind::Tuple),
        Ty::Array(elem, n) => default_value(lw, elem, span).map(|e| ExprKind::Repeat { elem: Box::new(e), n: *n }),
        _ => return None,
    };
    Some(kind.map(|kind| Expr::new(ty.clone(), span, kind)))
}

/// The default value of `ty` (§6.3): the one path of a field and of an
/// element. It recurs on the structure of the type, and a struct is a call:
/// its fields are lowered once, for its function.
fn default_value(lw: &mut Lowerer, ty: &Ty, span: Span) -> R<Expr> {
    if let Some(value) = structural_default(lw, ty, span) {
        return value;
    }
    let (member, args) = lw.member_of(ty, DerivedFn::Default.name(), span)?;
    Ok(Expr::new(ty.clone(), span, ExprKind::Call { fn_: lw.fn_id(member, args), args: Vec::new() }))
}

/// The read of the default `d` of a field of the type `ty` of a struct at
/// `args` (§4.4): the constant of the instance, burnt in once (S-918).
fn declared_default(lw: &mut Lowerer, d: DefId, ty: Ty, args: &[GenericArg], span: Span) -> R<Expr> {
    Ok(Expr::new(ty, span, ExprKind::Const(lw.const_id(d, args.to_vec())?)))
}

/// The value of the field `f` in a `default()`: the default it declares, else
/// the default of its type (§6.4).
// SPEC-GAP(S-173): the default of a field that reads a constant made by this
// `default()` (`struct P: Default { x: U32 = A.x }`, `const A: P = P.default()`)
// is no E0312: `const_id` follows no call, so it stops, and the evaluation
// panics at the cycle (`const_cycle`), as for `const A: U32 = f()` through a
// function.
fn field_default(lw: &mut Lowerer, f: &FieldDef, args: &[GenericArg], span: Span) -> R<Expr> {
    let ty = lw.core_ty(f.ty, args, span)?;
    match f.default {
        Some(d) => declared_default(lw, d, ty, args, span),
        None => default_value(lw, &ty, span),
    }
}

/// A block of the value `e` alone.
fn valued(e: Expr) -> Block {
    Block { stmts: Vec::new(), value: Some(Box::new(e)) }
}

/// The body of `default()` of the struct `id`.
fn default_body(lw: &mut Lowerer, id: TypeId, span: Span) -> R<Block> {
    let (d, args) = lw.type_decl(id, span)?;
    let a = lw.a;
    let Some(Fields::Named(fields)) = a.def(d).as_struct().map(|s| &s.fields) else {
        return Err(internal(span, "a derived `default` of a type of no fields"));
    };
    let fields = fields.iter().map(|f| field_default(lw, f, &args, span)).collect::<R<_>>()?;
    Ok(valued(Expr::new(Ty::Struct(id), span, ExprKind::Struct { ty: id, fields })))
}

/// The body of `ordinal()`: the tag is the place of the variant in the
/// declaration, from 0 (§6.4).
fn ordinal_body(lw: &Lowerer, this: Expr, span: Span) -> R<Block> {
    let tag = tag_of(lw, this)?;
    Ok(valued(if tag.ty == Ty::u32() { tag } else { Expr::new(Ty::u32(), span, ExprKind::Cast(Box::new(tag))) }))
}

/// The body of `from_ordinal(n)` of the enum `id`, of the type `Option[Self]`
/// `option`: one test for each variant, and `None` beyond the last (§6.4).
fn from_ordinal_body(lw: &mut Lowerer, n: Expr, id: TypeId, option: TypeId, span: Span) -> R<Block> {
    let (d, _) = lw.type_decl(option, span)?;
    let Some(row) = lw.a.modules.lang.of(d) else {
        return Err(internal(span, "`from_ordinal` of a type that is not `Option`"));
    };
    let wrapped =
        |tag: u32, fields: Vec<Expr>| Expr::new(Ty::Enum(option), span, ExprKind::Variant { ty: option, tag, fields });
    let mut stmts = Vec::new();
    for tag in 0..lw.enum_variants(id).len() as u32 {
        let variant = Expr::new(Ty::Enum(id), span, ExprKind::Variant { ty: id, tag, fields: Vec::new() });
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
    pub(super) fn member_of(&self, ty: &Ty, name: &str, span: Span) -> R<(DefId, Vec<GenericArg>)> {
        let key = match ty {
            Ty::Struct(id) | Ty::Enum(id) => {
                let (d, args) = self.type_decl(*id, span)?;
                let member = self.a.modules.assoc.get(&d).and_then(|t| t.get(name));
                let of = |&m: &DefId| (m, self.impl_args(m, args));
                return member.map(of).ok_or_else(|| internal(span, "a member its type does not have"));
            }
            Ty::Int(k) => STy::Int(*k),
            Ty::Float(k) => STy::Float(*k),
            Ty::Bool => STy::Bool,
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
        let mut bind = |name: &str, mode, ty: Ty| {
            params.push(Param { local: LocalId(locals.len() as u32), mode: core_mode(mode), ty: ty.clone() });
            locals.push(Local { name: name.to_string(), ty });
        };
        if let Some(mode) = f.self_mode {
            bind("self", mode, this.clone());
        }
        for p in &f.params {
            bind(&p.name, p.mode, self.core_ty(p.ty, args, p.span)?);
        }
        // A body has at most one parameter: `self`, or the number.
        let param = params.first().map(|p| Expr::new(p.ty.clone(), span, ExprKind::Local(p.local)));
        let block = match (made, &this, &ret, param) {
            (DerivedFn::Default, Ty::Struct(id), ..) => default_body(self, *id, span)?,
            (DerivedFn::Ordinal, Ty::Enum(_), _, Some(this)) => ordinal_body(self, this, span)?,
            (DerivedFn::FromOrdinal, Ty::Enum(id), Ty::Enum(option), Some(n)) => {
                from_ordinal_body(self, n, *id, *option, span)?
            }
            _ => return Err(internal(span, "a derived member of another form of type")),
        };
        let fd = &mut self.m.fns[fid.0 as usize];
        fd.params = params;
        fd.sret = ret.is_aggregate();
        fd.ret = ret;
        fd.rt = f.rt;
        fd.locals = locals;
        fd.body = Some(block);
        Ok(())
    }
}
