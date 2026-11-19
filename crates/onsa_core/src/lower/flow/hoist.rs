//! The stores of the hoisted fields of a flow (§11.3, `FlowInfo::hoists`):
//! the function of a stage writes the fields of its stage, found in the
//! `let`s of the faster stages and in the output, and the functions of the
//! later stages read them ([`super::lower_flow_expr`]); a guarded one is
//! written under its conditions (S-1157). The plan chose and ordered them;
//! the lowering finds them by `FlowInfo::hoist_of` and judges nothing (D-15).

use onsa_sema::flow::strip;
use onsa_syntax::ast::{Ast, BinOp, ExprKind as AK};

use super::super::body::{lower_match_with, push_expr_stmt};
use super::*;

#[cfg(test)]
mod tests;

/// Writes into `out` the fields of the stage `s` hoisted in `e`, of the
/// struct `state`, in the order of the text: of a field of `s`, its value;
/// of one of a slower stage, nothing (its stage wrote it); else those of
/// the parts of `e`, the guarded ones (S-1157) under the conditions on
/// their paths: an `if` or `Switch` of the condition read at `s`, holding
/// the bindings of an arm (§11.3). The constant expressions checked at `s`
/// are evaluated there for their panic (S-888 (c′)). None is in the body of
/// a `par~`, whose parts are not walked: W7-05 U3 writes those of each
/// replica.
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
    if let Some(c) = info.check_of(e) {
        if c == s {
            push_expr_stmt(lower_expr(lw, cx, e)?, out);
        }
        return Ok(());
    }
    let under = |lw: &mut Lowerer, cx: &mut FnCx, x: ExprId| {
        let mut b = Vec::new();
        writes(lw, cx, info, x, s, state, &mut b).map(|()| Block { stmts: b, value: None })
    };
    let ast = cx.ast;
    let span = ast.expr(e).span;
    match &ast.expr(e).kind {
        AK::If { cond, then, else_, tilde: None } => {
            writes(lw, cx, info, *cond, s, state, out)?;
            let t = under(lw, cx, *then)?;
            let f = match else_ {
                Some(x) => under(lw, cx, *x)?,
                None => Block::default(),
            };
            if !t.stmts.is_empty() || !f.stmts.is_empty() {
                let c = cond_value(lw, cx, info, *cond, s, state)?;
                out.push(stmt(span, StmtKind::If(c, t, f)));
            }
        }
        AK::Binary { op: op @ (BinOp::And | BinOp::Or), lhs, rhs, .. } => {
            writes(lw, cx, info, *lhs, s, state, out)?;
            let r = under(lw, cx, *rhs)?;
            if !r.stmts.is_empty() {
                let mut c = cond_value(lw, cx, info, *lhs, s, state)?;
                if *op == BinOp::Or {
                    c = Expr::new(Ty::Bool, span, ExprKind::Unary(UnOp::Not, Box::new(c)));
                }
                out.push(stmt(span, StmtKind::If(c, r, Block::default())));
            }
        }
        AK::Match { scrutinee, arms, tilde: None } => {
            writes(lw, cx, info, *scrutinee, s, state, out)?;
            if !arms.iter().any(|a| a.guard.into_iter().chain([a.body]).any(|x| has_writes(info, ast, x, s))) {
                return Ok(());
            }
            // The arms with a guard take the general path of a `match`,
            // which gives no value (W8-06): the reading stage is E0200 too.
            if arms.iter().any(|a| a.guard.is_some()) {
                return Err(unsupported(span, Feature::ValueMatch, &[]));
            }
            let v = cond_value(lw, cx, info, *scrutinee, s, state)?;
            let m = lower_match_with(lw, cx, e, v, arms, Ty::Unit, &mut |lw, cx, i| under(lw, cx, arms[i].body))?;
            push_expr_stmt(m, out);
        }
        AK::If { cond: x, .. } | AK::Match { scrutinee: x, .. } => writes(lw, cx, info, *x, s, state, out)?,
        AK::Par { .. } => {}
        _ => {
            for x in ast.sub_exprs(e) {
                writes(lw, cx, info, x, s, state, out)?;
            }
        }
    }
    Ok(())
}

/// Whether `e` holds a field or a check of the stage `s`.
fn has_writes(info: &FlowInfo, ast: &Ast, e: ExprId, s: ClockStage) -> bool {
    let here = info.hoist_of(e).map(|h| info.hoist(h).stage).or(info.check_of(e));
    here == Some(s) || ast.sub_exprs(e).into_iter().any(|x| has_writes(info, ast, x, s))
}

/// The value at the stage `s` of the condition `c` that guards fields of
/// `s`: its field, which [`writes`] wrote before, when it is one of `s`;
/// else lowered, an earlier field read ([`super::lower_flow_expr`]). The
/// plan guards a field of `s` with conditions decided by `s` only (D-15).
fn cond_value(lw: &mut Lowerer, cx: &mut FnCx, info: &FlowInfo, c: ExprId, s: ClockStage, state: &Expr) -> R<Expr> {
    let x = strip(cx.ast, c);
    let span = cx.ast.expr(c).span;
    let late = |k: Clock| k.stage().is_some_and(|k| k > s);
    if info.clocks.exprs.get(&x).copied().is_some_and(late) {
        return Err(internal(span, "a field guarded by a condition decided after its stage"));
    }
    match info.hoist_of(x).filter(|&h| info.hoist(h).stage == s) {
        Some(h) => sfield(lw, info, state, FieldOf::Hoist(h), span),
        None => lower_expr(lw, cx, c),
    }
}
