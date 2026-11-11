//! The value of a string literal of the type `FixedStr[N]` of `std.text`
//! (§4.2, S-614): the struct of its bytes, 0 after them to the capacity, and
//! the length used. The types stage judged the length and the characters.

use onsa_diag::Span;
use onsa_syntax::ast::StrLit;

use super::body::FnCx;
use super::build::{lit, local_expr, stmt, u32_lit};
use super::{Lowerer, R, internal};
use crate::ir::*;

/// The value of the literal `text` of the type of the struct `id`, which the
/// types stage gave a literal of a `FixedStr[N]` alone. In a body its nodes
/// are of the length of the literal, not of `N`: the bytes are a `[0; N]`
/// with the bytes of the text written in it. A `const` has no local to write
/// in, and its value is of `N` bytes in any case: the array of them.
pub(super) fn value(lw: &Lowerer, cx: &mut FnCx, text: &StrLit, id: TypeId, span: Span) -> R<ExprKind> {
    let Some(row) = lw.type_defs.get(&id).and_then(|(d, _)| lw.a.modules.lang.fixed_str(*d)) else {
        return Err(internal(span, "a string literal of a struct type"));
    };
    // The value of a literal with no interpolation (the types stage).
    let text = onsa_syntax::test_name::value(text).ok_or_else(|| internal(span, "an interpolation of a `FixedStr`"))?;
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
