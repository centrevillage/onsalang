//! Small builders of Core expressions, statements and arguments, shared by
//! the lowering of bodies ([`super::body`]) and of flows ([`super::flow`]).

use onsa_diag::Span;

use super::body::FnCx;
use super::{Lowerer, R, internal};
use crate::effects::repeatable;
use crate::ir::*;

pub(super) fn local_expr(cx: &FnCx, l: LocalId, span: Span) -> Expr {
    Expr::new(cx.locals[l.0 as usize].ty, span, ExprKind::Local(l))
}

pub(super) fn lit(ty: CTy, span: Span, l: Lit) -> Expr {
    Expr::new(ty, span, ExprKind::Lit(l))
}

pub(super) fn u32_lit(span: Span, n: u32) -> Expr {
    lit(Types::U32, span, Lit::Int(n as i128))
}

pub(super) fn bool_lit(span: Span, b: bool) -> Expr {
    lit(Types::BOOL, span, Lit::Bool(b))
}

pub(super) fn stmt(span: Span, kind: StmtKind) -> Stmt {
    Stmt { span, kind }
}

pub(super) fn tag_ty(lw: &Lowerer, id: TypeId) -> CTy {
    Types::int(onsa_sema::layout::tag_kind(lw.enum_variants(id).len()))
}

pub(super) fn tag_of(lw: &Lowerer, e: Expr) -> R<Expr> {
    let TyKind::Enum(id) = *lw.m.tys.kind(e.ty) else { return Err(internal(e.span, "tag of a non-enum")) };
    let ty = tag_ty(lw, id);
    let span = e.span;
    Ok(Expr::new(ty, span, ExprKind::Tag(Box::new(e))))
}

pub(super) fn payload(lw: &Lowerer, base: Expr, tag: u32, index: u32) -> R<Expr> {
    let TyKind::Enum(id) = *lw.m.tys.kind(base.ty) else { return Err(internal(base.span, "payload of a non-enum")) };
    let ty = lw.enum_variants(id).get(tag as usize).and_then(|(_, f)| f.get(index as usize).copied());
    let Some(ty) = ty else { return Err(internal(base.span, "payload index out of range")) };
    let span = base.span;
    Ok(Expr::new(ty, span, ExprKind::Payload { base: Box::new(base), tag, index }))
}

/// The fields of the Core struct `id`, borrowed: a field is reached with no
/// copy of the others (R-498).
fn fields_of<'l>(lw: &'l Lowerer, id: TypeId) -> &'l [(String, CTy)] {
    match &lw.m.ty(id).kind {
        TypeDefKind::Struct { fields } => fields,
        _ => &[],
    }
}

pub(super) fn field(lw: &Lowerer, base: Expr, index: u32) -> R<Expr> {
    let ty = match lw.m.tys.kind(base.ty) {
        TyKind::Struct(id) => fields_of(lw, *id).get(index as usize).map(|&(_, t)| t),
        TyKind::Tuple(ts) => ts.get(index as usize).copied(),
        _ => None,
    };
    let Some(ty) = ty else { return Err(internal(base.span, "field index out of range")) };
    let span = base.span;
    Ok(Expr::new(ty, span, ExprKind::Field { base: Box::new(base), index }))
}

pub(super) fn field_by_name(lw: &Lowerer, base: Expr, name: &str, span: Span) -> R<Expr> {
    let TyKind::Struct(id) = *lw.m.tys.kind(base.ty) else {
        return Err(internal(span, format!("field `{name}` of a non-struct")));
    };
    let idx = fields_of(lw, id).iter().position(|(n, _)| n == name);
    let Some(idx) = idx else { return Err(internal(span, format!("no field `{name}`"))) };
    field(lw, base, idx as u32)
}

/// `base[idx]`, checked against the length of `base` (§18.1).
/// (`tys`: the types of the module, last so that the other arguments may
/// borrow the lowering.)
pub(super) fn index(base: Expr, idx: Expr, tys: &Types) -> R<Expr> {
    index_as(base, idx, Bounds::Checked, tys)
}

pub(super) fn index_as(base: Expr, idx: Expr, bounds: Bounds, tys: &Types) -> R<Expr> {
    let ty = match tys.kind(base.ty) {
        TyKind::Array(e, _) | TyKind::Span(e) | TyKind::Buf(e) => *e,
        _ => return Err(internal(base.span, "index of a non-sequence")),
    };
    let span = base.span;
    Ok(Expr::new(ty, span, ExprKind::Index { base: Box::new(base), index: Box::new(idx), bounds }))
}

/// Statements that evaluate `e` once, for an expression used more than once
/// (§3.5): a place stays one, not copied, with each of its indices that is
/// not [`repeatable`] bound to a temporary first (the base before its index,
/// R-433); another expression is bound to a temporary. (`tys`: the types of
/// the module, last as in [`index`].)
pub(super) fn materialize(cx: &mut FnCx, mut e: Expr, stmts: &mut Vec<Stmt>, name: &str, tys: &Types) -> Expr {
    let place = unrepeated(&mut e, tys, &mut |i| {
        let x = Expr::new(i.ty, i.span, std::mem::replace(&mut i.kind, ExprKind::Lit(Lit::Unit)));
        *i = materialize(cx, x, stmts, "__index", tys);
    });
    if place {
        return e;
    }
    let span = e.span;
    let t = cx.temp(name, e.ty);
    stmts.push(stmt(span, StmtKind::Let(t, e)));
    local_expr(cx, t, span)
}

/// Whether [`materialize`] binds nothing of `e`: a place whose indices are
/// all [`repeatable`]. (`&mut` as [`unrepeated`], the one walk of both, D-15,
/// changes nothing here.)
pub(super) fn stays(e: &mut Expr, tys: &Types) -> bool {
    let mut all = true;
    unrepeated(e, tys, &mut |_| all = false) && all
}

/// Whether `e` is a place ([`Expr::as_place`]); of one, each index that is
/// not [`repeatable`] given to `f`, the base before its index (R-433).
fn unrepeated(e: &mut Expr, tys: &Types, f: &mut dyn FnMut(&mut Expr)) -> bool {
    match &mut e.kind {
        ExprKind::Local(_) => true,
        ExprKind::Field { base, .. } => unrepeated(base, tys, f),
        ExprKind::Index { base, index, .. } => {
            let place = unrepeated(base, tys, f);
            if place && !repeatable(index, tys) {
                f(index);
            }
            place
        }
        _ => false,
    }
}

/// `value` after the statements `stmts` (of [`materialize`]), a block when
/// there are some.
pub(super) fn after(stmts: Vec<Stmt>, value: Expr) -> Expr {
    match stmts.is_empty() {
        true => value,
        false => Expr::new(value.ty, value.span, ExprKind::Block(Block { stmts, value: Some(Box::new(value)) })),
    }
}

/// The one conversion of a float literal's `text` (§2.4, R-20): its value
/// rounded once to `k` (for `F32`, `float_value` gives a value that is an
/// `F32` already, so `as f32` is exact). The types stage reported one out of
/// its range (E0408).
pub(super) fn float_text(text: &str, k: FloatKind, span: Span) -> R<Lit> {
    let v = onsa_syntax::float_value(text, k.width()).map_err(|_| internal(span, "float literal out of range"))?;
    Ok(match k {
        FloatKind::F32 => Lit::F32(v as f32),
        FloatKind::F64 => Lit::F64(v),
    })
}

pub(super) fn float_lit(ty: CTy, v: f64, span: Span, tys: &Types) -> R<Expr> {
    match tys.kind(ty) {
        TyKind::Float(FloatKind::F32) => Ok(lit(ty, span, Lit::F32(v as f32))),
        TyKind::Float(FloatKind::F64) => Ok(lit(ty, span, Lit::F64(v))),
        TyKind::Int(_) => Ok(lit(ty, span, Lit::Int(v as i128))),
        _ => Err(internal(span, "numeric literal of a non-numeric type")),
    }
}

pub(super) fn checked_binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    let (ty, span) = (lhs.ty, lhs.span);
    Expr::new(ty, span, ExprKind::Binary { op, overflow: Overflow::Checked, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

pub(super) fn cmp(op: CmpOp, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span;
    Expr::new(Types::BOOL, span, ExprKind::Cmp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

/// The parts `xs` joined by the short-circuit `op` in a balanced tree (none
/// of none), ⌈n/2⌉ of them on the left: up to three it is the chain
/// `(a op b) op c`. Of any tree the parts are evaluated from the left and
/// stop at the same one, so the value and the panics are those of the
/// chain, and the depth is ⌈log2 n⌉ (V-22). For a list the lowering joins;
/// a chain the source writes stays as written (§2.5 counts its depth).
pub(super) fn balanced(op: LogicOp, xs: Vec<Expr>, span: Span) -> Option<Expr> {
    fn join(op: LogicOp, xs: &mut std::vec::IntoIter<Expr>, n: usize, span: Span) -> Option<Expr> {
        if n <= 1 {
            return xs.next();
        }
        let lhs = Box::new(join(op, xs, n.div_ceil(2), span)?);
        let rhs = Box::new(join(op, xs, n / 2, span)?);
        Some(Expr::new(Types::BOOL, span, ExprKind::Logic { op, lhs, rhs }))
    }
    let n = xs.len();
    join(op, &mut xs.into_iter(), n, span)
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

pub(super) fn call(fid: FnId, ret: CTy, span: Span, args: Vec<Arg>) -> Expr {
    Expr::new(ret, span, ExprKind::Call { fn_: fid, args })
}

pub(super) fn borrow(e: Expr) -> Arg {
    Arg { mode: Mode::Borrow, expr: e }
}

pub(super) fn inout(e: Expr) -> Arg {
    Arg { mode: Mode::Inout, expr: e }
}
