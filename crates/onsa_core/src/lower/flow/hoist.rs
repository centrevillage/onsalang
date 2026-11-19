//! The stores of the hoisted fields of a flow (§11.3, `FlowInfo::hoists`):
//! the function of a stage writes the fields of its stage, found in the
//! `let`s of the faster stages and in the output, and the functions of the
//! later stages read them ([`super::lower_flow_expr`]). The plan chose and
//! ordered them; the lowering finds them by `FlowInfo::hoist_of` and
//! judges nothing (D-15).

use onsa_syntax::ast::{BinOp, ExprKind as AK};

use super::*;

#[cfg(test)]
mod tests;

/// Writes into `out` the fields of the stage `s` hoisted in `e`, of the
/// struct `state`, in the order of the text: of a field of `s`, its value;
/// of one of a slower stage, nothing (its stage wrote it); else those of
/// the parts of `e`. None is in a branch, a guard, the right of `&&` / `||`
/// or the body of a `par~`, whose parts are not walked: W7-05 U2 writes
/// those under their conditions, U3 those of each replica.
pub(super) fn writes(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    e: ExprId,
    s: ClockStage,
    state: &Expr,
    out: &mut Vec<Stmt>,
) -> R<()> {
    if let Some(h) = info.hoist_of(e) {
        let x = info.hoist(h);
        if x.stage == s {
            let v = lower_expr(lw, cx, e)?;
            let f = sfield(lw, info, state, FieldOf::Hoist(h), x.span)?;
            return assign(out, &f, v);
        }
        if x.stage < s {
            return Ok(());
        }
    }
    let ast = cx.ast;
    let parts = match &ast.expr(e).kind {
        AK::If { cond, .. } => vec![*cond],
        AK::Match { scrutinee, .. } => vec![*scrutinee],
        AK::Binary { op: BinOp::And | BinOp::Or, lhs, .. } => vec![*lhs],
        AK::Par { .. } => Vec::new(),
        _ => ast.sub_exprs(e),
    };
    for x in parts {
        writes(lw, cx, info, x, s, state, out)?;
    }
    Ok(())
}
