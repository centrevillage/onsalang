//! Generated structural equality (`==` on aggregates): one `__eq.<type>`
//! function per type, so backends only compare scalars.

use onsa_diag::Span;
use onsa_diag::unsupported::Feature;

use super::body::push_expr_stmt;
use super::{Lowerer, R, internal, unsupported};
use crate::ir::*;

pub(crate) fn eq_fn(lw: &mut Lowerer, ty: &Ty, span: Span) -> R<FnId> {
    if let Some(&id) = lw.eq_fns.get(ty) {
        return Ok(id);
    }
    let id = FnId(lw.m.fns.len() as u32);
    let name = format!("__eq.{}", lw.mangle(ty));
    lw.m.fns.push(FnDef {
        name,
        params: Vec::new(),
        ret: Ty::Bool,
        sret: false,
        rt: true,
        locals: Vec::new(),
        body: None,
        span,
        fp_relaxed: false,
        test: None,
        decl: None,
    });
    lw.eq_fns.insert(ty.clone(), id);
    let mut locals = vec![Local { name: "a".into(), ty: ty.clone() }, Local { name: "b".into(), ty: ty.clone() }];
    let (a, b) = (LocalId(0), LocalId(1));
    let la = Expr::new(ty.clone(), span, ExprKind::Local(a));
    let lb = Expr::new(ty.clone(), span, ExprKind::Local(b));
    let body = eq_body(lw, &mut locals, ty, la, lb, span)?;
    let f = &mut lw.m.fns[id.0 as usize];
    f.params = vec![
        Param { local: a, mode: Mode::Borrow, ty: ty.clone() },
        Param { local: b, mode: Mode::Borrow, ty: ty.clone() },
    ];
    f.locals = locals;
    f.body = Some(body);
    Ok(id)
}

/// Whether [`compare`] takes values of `ty`: the scalars and `()`; an
/// aggregate is compared by its eq fn.
pub(crate) fn compared_directly(ty: &Ty) -> bool {
    ty.is_scalar() || *ty == Ty::Unit
}

/// `l op r` of values that [`compared_directly`] takes. The one value of
/// `()` equals itself: its operands are evaluated, the left one first, and
/// the result is a constant, so the backends compare scalars only (§6.4,
/// §3.5, R-415).
pub(crate) fn compare(op: CmpOp, l: Expr, r: Expr, span: Span) -> R<Expr> {
    if l.ty != Ty::Unit {
        return Ok(Expr::new(Ty::Bool, span, ExprKind::Cmp { op, lhs: Box::new(l), rhs: Box::new(r) }));
    }
    let equal = match op {
        CmpOp::Eq => true,
        CmpOp::Ne => false,
        _ => return Err(internal(span, "ordering on ()")),
    };
    let mut stmts = Vec::new();
    push_expr_stmt(l, &mut stmts);
    push_expr_stmt(r, &mut stmts);
    let value = Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(equal)));
    Ok(Expr::new(Ty::Bool, span, ExprKind::Block(Block { stmts, value: Some(Box::new(value)) })))
}

/// `a == b` as an expression (scalars compare, aggregates call their eq fn),
/// at `span`; `at`: where the eq fn of the type is asked for (the operator).
pub(super) fn eq_expr(lw: &mut Lowerer, a: Expr, b: Expr, span: Span, at: Span) -> R<Expr> {
    if compared_directly(&a.ty) {
        return compare(CmpOp::Eq, a, b, span);
    }
    let f = eq_fn(lw, &a.ty, at)?;
    Ok(Expr::new(
        Ty::Bool,
        span,
        ExprKind::Call { fn_: f, args: vec![Arg { mode: Mode::Borrow, expr: a }, Arg { mode: Mode::Borrow, expr: b }] },
    ))
}

fn and_all(mut xs: Vec<Expr>, span: Span) -> Expr {
    if xs.is_empty() {
        return Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(true)));
    }
    let mut acc = xs.remove(0);
    for x in xs {
        acc = Expr::new(Ty::Bool, span, ExprKind::Logic { op: LogicOp::And, lhs: Box::new(acc), rhs: Box::new(x) });
    }
    acc
}

fn eq_body(lw: &mut Lowerer, locals: &mut Vec<Local>, ty: &Ty, a: Expr, b: Expr, span: Span) -> R<Block> {
    let field = |base: &Expr, i: u32, t: &Ty| {
        Expr::new(t.clone(), span, ExprKind::Field { base: Box::new(base.clone()), index: i })
    };
    match ty {
        Ty::Struct(id) => {
            let fields = lw.struct_fields(*id);
            let mut parts = Vec::new();
            for (i, (_, t)) in fields.iter().enumerate() {
                parts.push(eq_expr(lw, field(&a, i as u32, t), field(&b, i as u32, t), span, span)?);
            }
            Ok(Block { stmts: Vec::new(), value: Some(Box::new(and_all(parts, span))) })
        }
        Ty::Tuple(ts) => {
            let mut parts = Vec::new();
            for (i, t) in ts.iter().enumerate() {
                parts.push(eq_expr(lw, field(&a, i as u32, t), field(&b, i as u32, t), span, span)?);
            }
            Ok(Block { stmts: Vec::new(), value: Some(Box::new(and_all(parts, span))) })
        }
        Ty::Array(elem, n) => {
            let i = LocalId(locals.len() as u32);
            locals.push(Local { name: "i".into(), ty: Ty::u32() });
            let li = Expr::new(Ty::u32(), span, ExprKind::Local(i));
            let ea =
                Expr::new((**elem).clone(), span, ExprKind::Index { base: Box::new(a), index: Box::new(li.clone()) });
            let eb = Expr::new((**elem).clone(), span, ExprKind::Index { base: Box::new(b), index: Box::new(li) });
            let test = eq_expr(lw, ea, eb, span, span)?;
            let not = Expr::new(Ty::Bool, span, ExprKind::Unary(UnOp::Not, Box::new(test)));
            let ret_false = Block {
                stmts: vec![Stmt {
                    span,
                    kind: StmtKind::Return(Some(Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(false))))),
                }],
                value: None,
            };
            let body =
                Block { stmts: vec![Stmt { span, kind: StmtKind::If(not, ret_false, Block::default()) }], value: None };
            let lo = Expr::new(Ty::u32(), span, ExprKind::Lit(Lit::Int(0)));
            let hi = Expr::new(Ty::u32(), span, ExprKind::Lit(Lit::Int(*n as i128)));
            Ok(Block {
                stmts: vec![Stmt { span, kind: StmtKind::ForRange(i, lo, hi, body) }],
                value: Some(Box::new(Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(true))))),
            })
        }
        Ty::Enum(id) => {
            let variants = lw.enum_variants(*id);
            let tag_ty = Ty::Int(onsa_sema::layout::tag_kind(variants.len()));
            let ta = Expr::new(tag_ty.clone(), span, ExprKind::Tag(Box::new(a.clone())));
            let tb = Expr::new(tag_ty, span, ExprKind::Tag(Box::new(b.clone())));
            let tags_differ =
                Expr::new(Ty::Bool, span, ExprKind::Cmp { op: CmpOp::Ne, lhs: Box::new(ta), rhs: Box::new(tb) });
            let ret_false = Block {
                stmts: vec![Stmt {
                    span,
                    kind: StmtKind::Return(Some(Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(false))))),
                }],
                value: None,
            };
            let mut arms = Vec::new();
            for (tag, (_, fields)) in variants.iter().enumerate() {
                let mut parts = Vec::new();
                for (i, t) in fields.iter().enumerate() {
                    let pa = Expr::new(
                        t.clone(),
                        span,
                        ExprKind::Payload { base: Box::new(a.clone()), tag: tag as u32, index: i as u32 },
                    );
                    let pb = Expr::new(
                        t.clone(),
                        span,
                        ExprKind::Payload { base: Box::new(b.clone()), tag: tag as u32, index: i as u32 },
                    );
                    parts.push(eq_expr(lw, pa, pb, span, span)?);
                }
                arms.push((tag as u32, Block { stmts: Vec::new(), value: Some(Box::new(and_all(parts, span))) }));
            }
            let sw = Expr::new(Ty::Bool, span, ExprKind::Switch { scrutinee: Box::new(a), arms, default: None });
            Ok(Block {
                stmts: vec![Stmt { span, kind: StmtKind::If(tags_differ, ret_false, Block::default()) }],
                value: Some(Box::new(sw)),
            })
        }
        _ => Err(unsupported(span, Feature::Equality, &[])),
    }
}
