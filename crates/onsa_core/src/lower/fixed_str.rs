//! The type `FixedStr[N]` of `std.text` (§4.2, S-614): the value of a
//! string literal of it (the struct of its bytes, 0 after them to the
//! capacity, and the length used; the types stage judged the length and the
//! characters), and its view as a `Span[U8]` of the used part.

use onsa_diag::Span;
use onsa_sema::lang::LangFixedStr;
use onsa_syntax::ast::StrLit;

use super::body::FnCx;
use super::build::{after, field, lit, local_expr, materialize, stmt, u32_lit};
use super::{Lowerer, R, internal};
use crate::ir::*;
use crate::prim::Prim;

/// The row of the lang item of the struct `id`, which the types stage gave
/// a `FixedStr[N]` alone.
fn row(lw: &Lowerer, id: TypeId, span: Span) -> R<LangFixedStr> {
    let row = lw.type_defs.get(&id).and_then(|(d, _)| lw.a.modules.lang.fixed_str(*d));
    row.ok_or_else(|| internal(span, "a `FixedStr` of another struct type"))
}

/// The value `e` of a `FixedStr[N]` passed as a `Span[U8]` (§4.2, §5.3):
/// the partial view `slice(span(e.bytes), 0, e.len)` of a place (R-31),
/// evaluated once ([`materialize`]). The types stage took no `inout`
/// parameter.
pub(super) fn view(lw: &Lowerer, cx: &mut FnCx, e: Expr) -> R<Expr> {
    let span = e.span;
    let Ty::Struct(id) = e.ty else { return Err(internal(span, "a view of a non-struct")) };
    let row = row(lw, id, span)?;
    let mut stmts = Vec::new();
    let base = materialize(cx, e, &mut stmts, "__fixed_str");
    let (bytes, len) = (field(lw, base.clone(), row.bytes)?, field(lw, base, row.len)?);
    let Ty::Array(el, _) = &bytes.ty else { return Err(internal(span, "the bytes of a `FixedStr`")) };
    let ty = Ty::Span(el.clone());
    let whole = Expr::new(ty.clone(), span, ExprKind::SpanOf(Box::new(bytes)));
    let args = [whole, u32_lit(span, 0), len].map(|expr| Arg { mode: Mode::Borrow, expr }).into();
    Ok(after(stmts, Expr::new(ty, span, ExprKind::Prim { prim: Prim::Slice, args })))
}

/// The value of the literal `text` of the type of the struct `id`, which the
/// types stage gave a literal of a `FixedStr[N]` alone. In a body its nodes
/// are of the length of the literal, not of `N`: the bytes are a `[0; N]`
/// with the bytes of the text written in it. A `const` has no local to write
/// in, and its value is of `N` bytes in any case: the array of them.
pub(super) fn value(lw: &Lowerer, cx: &mut FnCx, text: &StrLit, id: TypeId, span: Span) -> R<ExprKind> {
    let row = row(lw, id, span)?;
    // The value of a literal with no interpolation (the types stage).
    let text = text.value().ok_or_else(|| internal(span, "an interpolation of a `FixedStr`"))?;
    let fields = lw.struct_fields(id);
    let (Some((_, bytes)), Some((_, len))) = (fields.get(row.bytes as usize), fields.get(row.len as usize)) else {
        return Err(internal(span, "the fields of a `FixedStr`"));
    };
    let Ty::Array(el, n) = bytes else { return Err(internal(span, "the bytes of a `FixedStr`")) };
    if text.len() > *n as usize || fields.len() != 2 {
        return Err(internal(span, "a `FixedStr` literal over its capacity"));
    }
    let byte = |b: u8| lit((**el).clone(), span, Lit::Int(i128::from(b)));
    let zeros = Expr::new(bytes.clone(), span, ExprKind::Repeat { elem: Box::new(byte(0)), n: *n });
    let array = if text.is_empty() {
        zeros
    } else if cx.constant {
        let mut elems: Vec<Expr> = text.bytes().map(byte).collect();
        elems.resize(*n as usize, byte(0));
        Expr::new(bytes.clone(), span, ExprKind::Array(elems))
    } else {
        let tmp = cx.temp("__fixed_str", bytes.clone());
        let mut stmts = vec![stmt(span, StmtKind::Let(tmp, zeros))];
        for (i, b) in (0..).zip(text.bytes()) {
            let place = Place::Index(Box::new(Place::Local(tmp)), Box::new(u32_lit(span, i)), span);
            stmts.push(stmt(span, StmtKind::Assign(place, byte(b))));
        }
        let value = Some(Box::new(local_expr(cx, tmp, span)));
        Expr::new(bytes.clone(), span, ExprKind::Block(Block { stmts, value }))
    };
    let mut out = vec![lit(len.clone(), span, Lit::Int(text.len() as i128))];
    // The two fields in the order of the declaration.
    out.insert(row.bytes as usize, array);
    Ok(ExprKind::Struct { ty: id, fields: out })
}
