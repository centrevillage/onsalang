//! Small builders of Core expressions, statements and arguments, shared by
//! the lowering of bodies ([`super::body`]) and of flows ([`super::flow`]).

use onsa_diag::Span;

use super::body::FnCx;
use super::{Lowerer, R, internal};
use crate::ir::*;

pub(super) fn local_expr(cx: &FnCx, l: LocalId, span: Span) -> Expr {
    Expr::new(cx.locals[l.0 as usize].ty.clone(), span, ExprKind::Local(l))
}

pub(super) fn lit(ty: Ty, span: Span, l: Lit) -> Expr {
    Expr::new(ty, span, ExprKind::Lit(l))
}

pub(super) fn u32_lit(span: Span, n: u32) -> Expr {
    lit(Ty::u32(), span, Lit::Int(n as i128))
}

pub(super) fn bool_lit(span: Span, b: bool) -> Expr {
    lit(Ty::Bool, span, Lit::Bool(b))
}

pub(super) fn stmt(span: Span, kind: StmtKind) -> Stmt {
    Stmt { span, kind }
}

pub(super) fn tag_ty(lw: &Lowerer, id: TypeId) -> Ty {
    Ty::Int(onsa_sema::layout::tag_kind(lw.enum_variants(id).len()))
}

pub(super) fn tag_of(lw: &Lowerer, e: Expr) -> R<Expr> {
    let Ty::Enum(id) = &e.ty else { return Err(internal(e.span, "tag of a non-enum")) };
    let ty = tag_ty(lw, *id);
    let span = e.span;
    Ok(Expr::new(ty, span, ExprKind::Tag(Box::new(e))))
}

pub(super) fn payload(lw: &Lowerer, base: Expr, tag: u32, index: u32) -> R<Expr> {
    let Ty::Enum(id) = &base.ty else { return Err(internal(base.span, "payload of a non-enum")) };
    let ty = lw.enum_variants(*id).get(tag as usize).and_then(|(_, f)| f.get(index as usize).cloned());
    let Some(ty) = ty else { return Err(internal(base.span, "payload index out of range")) };
    let span = base.span;
    Ok(Expr::new(ty, span, ExprKind::Payload { base: Box::new(base), tag, index }))
}

pub(super) fn field(lw: &Lowerer, base: Expr, index: u32) -> R<Expr> {
    let ty = match &base.ty {
        Ty::Struct(id) => lw.struct_fields(*id).get(index as usize).map(|(_, t)| t.clone()),
        Ty::Tuple(ts) => ts.get(index as usize).cloned(),
        _ => None,
    };
    let Some(ty) = ty else { return Err(internal(base.span, "field index out of range")) };
    let span = base.span;
    Ok(Expr::new(ty, span, ExprKind::Field { base: Box::new(base), index }))
}

pub(super) fn field_by_name(lw: &Lowerer, base: Expr, name: &str, span: Span) -> R<Expr> {
    let Ty::Struct(id) = &base.ty else { return Err(internal(span, format!("field `{name}` of a non-struct"))) };
    let idx = lw.struct_fields(*id).iter().position(|(n, _)| n == name);
    let Some(idx) = idx else { return Err(internal(span, format!("no field `{name}`"))) };
    field(lw, base, idx as u32)
}

pub(super) fn index(base: Expr, idx: Expr) -> R<Expr> {
    let ty = match &base.ty {
        Ty::Array(e, _) | Ty::Span(e) | Ty::Buf(e) => (**e).clone(),
        _ => return Err(internal(base.span, "index of a non-sequence")),
    };
    let span = base.span;
    Ok(Expr::new(ty, span, ExprKind::Index { base: Box::new(base), index: Box::new(idx) }))
}

/// Statements that evaluate `e` once into a temporary, unless it is a place.
pub(super) fn materialize(cx: &mut FnCx, e: Expr, stmts: &mut Vec<Stmt>, name: &str) -> Expr {
    if e.as_place().is_some() {
        return e;
    }
    let span = e.span;
    let t = cx.temp(name, e.ty.clone());
    stmts.push(stmt(span, StmtKind::Let(t, e)));
    local_expr(cx, t, span)
}

pub(super) fn float_lit(ty: &Ty, v: f64, span: Span) -> R<Expr> {
    match ty {
        Ty::Float(FloatKind::F32) => Ok(lit(ty.clone(), span, Lit::F32(v as f32))),
        Ty::Float(FloatKind::F64) => Ok(lit(ty.clone(), span, Lit::F64(v))),
        Ty::Int(_) => Ok(lit(ty.clone(), span, Lit::Int(v as i128))),
        _ => Err(internal(span, "numeric literal of a non-numeric type")),
    }
}

pub(super) fn checked_binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    let (ty, span) = (lhs.ty.clone(), lhs.span);
    Expr::new(ty, span, ExprKind::Binary { op, overflow: Overflow::Checked, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

pub(super) fn cmp(op: CmpOp, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span;
    Expr::new(Ty::Bool, span, ExprKind::Cmp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

pub(super) fn place_of(e: &Expr) -> R<Place> {
    e.as_place().ok_or_else(|| internal(e.span, "expected a place"))
}

pub(super) fn assign(out: &mut Vec<Stmt>, target: &Expr, value: Expr) -> R<()> {
    let span = target.span;
    out.push(stmt(span, StmtKind::Assign(place_of(target)?, value)));
    Ok(())
}

pub(super) fn expr_stmt(out: &mut Vec<Stmt>, e: Expr) {
    let span = e.span;
    out.push(stmt(span, StmtKind::Expr(e)));
}

pub(super) fn call(fid: FnId, ret: Ty, span: Span, args: Vec<Arg>) -> Expr {
    Expr::new(ret, span, ExprKind::Call { fn_: fid, args })
}

pub(super) fn borrow(e: Expr) -> Arg {
    Arg { mode: Mode::Borrow, expr: e }
}

pub(super) fn inout(e: Expr) -> Arg {
    Arg { mode: Mode::Inout, expr: e }
}
