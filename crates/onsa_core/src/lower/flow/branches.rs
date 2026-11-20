//! `if~` in `tick` (§11.5, S-110, R-14, S-1094): every branch evaluated,
//! one chosen. Its parts of a slower stage are written by [`super::hoist`].

use onsa_sema::flow::chain;

use super::super::body::{drop_value, lower_block_expr, push_expr_stmt};
use super::*;

/// The `if~` chain `e` of the type `ty`, in one block: the conditions from
/// the first to the one that holds (S-1094), giving the number of its link
/// (the number of links of none); every branch in the order of the text,
/// each in a temporary (R-14: the state in each goes on); the branch of
/// that number. One loop over the chain.
pub(crate) fn tilde_if(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, ty: Ty) -> R<Expr> {
    let span = cx.ast.expr(e).span;
    let chain = chain(cx.ast, e);
    let Some(last) = chain.last else { return Err(internal(span, "an `if~` with no `else`")) };
    let value = |v: Expr| Block { stmts: Vec::new(), value: Some(Box::new(v)) };
    let mut conds = Vec::with_capacity(chain.links.len());
    for l in &chain.links {
        conds.push(lower_expr(lw, cx, l.cond)?);
    }
    let mut taken = u32_lit(span, conds.len() as u32);
    for (k, c) in conds.into_iter().enumerate().rev() {
        let then = value(u32_lit(span, k as u32));
        taken = Expr::new(Ty::u32(), span, ExprKind::IfExpr { cond: Box::new(c), then, else_: value(taken) });
    }
    let mut stmts = Vec::new();
    let taken = materialize(cx, taken, &mut stmts, "__taken");
    let mut values = Vec::with_capacity(chain.links.len() + 1);
    for x in chain.links.iter().map(|l| l.then).chain([last]) {
        let b = lower_block_expr(lw, cx, x)?;
        if ty == Ty::Unit {
            push_expr_stmt(Expr::new(Ty::Unit, span, ExprKind::Block(drop_value(b))), &mut stmts);
            continue;
        }
        let Some(t) = b.value.as_ref().map(|v| v.ty.clone()) else {
            return Err(internal(cx.ast.expr(x).span, "a branch of an `if~` with no value"));
        };
        values.push(materialize(cx, Expr::new(t, span, ExprKind::Block(b)), &mut stmts, "__branch"));
    }
    let mut chosen = values.pop();
    for (k, v) in values.into_iter().enumerate().rev() {
        let cond = Box::new(cmp(CmpOp::Eq, taken.clone(), u32_lit(span, k as u32)));
        let else_ = chosen.map(value).unwrap_or_default();
        chosen = Some(Expr::new(ty.clone(), span, ExprKind::IfExpr { cond, then: value(v), else_ }));
    }
    Ok(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: chosen.map(Box::new) })))
}
