//! Lowering of function bodies: expressions, statements, patterns (T3-3).
//!
//! This module holds the context of a body ([`FnCx`]), the function bodies
//! and the statements; [`pat`] the patterns and `match`, [`expr`] the
//! expressions, [`call`] the calls and the builtin methods.

use onsa_diag::Span;
use onsa_diag::unsupported::Feature;
use onsa_sema::body::{BodyInfo, Target};
use onsa_sema::def::{DefKind, FnDef as SFnDef};
use onsa_sema::resolve::Builtin;
use onsa_sema::ty::TyId;
use onsa_sema::{DefId, ModId};
use onsa_syntax::ast::{
    self, Ast, BinOp as ABinOp, ExprId, ExprKind as AK, Lit as ALit, OpGroup, PatId, PatKind, RangeEnd, StmtId,
    StmtKind as AS, UnOp as AUnOp,
};

use super::build::{
    bool_lit, field, field_by_name, index, lit, local_expr, materialize, payload, stmt, tag_of, u32_lit,
};
use super::{FailKind, GenericArg, Hole, Lowerer, R, at_hole, core_mode, internal, unsupported};
use crate::ir::*;
use crate::prim::{CheckedOp, MathFn, Prim};

mod call;
mod expr;
mod pat;

use super::{eq, flow};
pub(super) use call::coerce;
use call::lower_call;
pub(super) use expr::lower_expr;
use expr::placeholder_ty;
pub(super) use pat::bind_irrefutable;
use pat::{lower_match, tag_test};

pub(crate) struct FnCx<'b> {
    pub args: Vec<GenericArg>,
    pub info: &'b BodyInfo,
    pub ast: &'b Ast,
    pub text: &'b str,
    pub module: ModId,
    pub locals: Vec<Local>,
    pub ret: Ty,
    /// Depth of inlined closure bodies (`return` and `?` inside them are
    /// unsupported until W8-09: they leave the closure, S-192).
    pub inline_depth: u32,
    /// Set while lowering a flow body (T3-5): overrides for state-resident
    /// locals and for the stateful node expressions.
    pub flow: Option<super::flow::FlowLowerCx<'b>>,
}

impl<'b> FnCx<'b> {
    pub(crate) fn new(
        lw: &mut Lowerer<'b>,
        def: DefId,
        args: Vec<GenericArg>,
        info: &'b BodyInfo,
        ret: Ty,
    ) -> R<FnCx<'b>> {
        let d = lw.a.def(def);
        let module = d.module;
        let Some(m) = lw.a.ast(lw.pkg, module) else { return Err(internal(d.span, "module source not found")) };
        let mut locals = Vec::new();
        for l in &info.locals {
            // A local of a type lowering does not support: the expressions
            // that give it a value report the type (S-67), as placeholders.
            let (ty, _) = placeholder_ty(lw, l.ty, &args, l.span)?;
            locals.push(Local { name: l.name.clone(), ty });
        }
        Ok(FnCx { args, info, ast: &m.parsed.ast, text: &m.text, module, locals, ret, inline_depth: 0, flow: None })
    }

    pub(crate) fn temp(&mut self, name: &str, ty: Ty) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(Local { name: name.to_string(), ty });
        id
    }

    fn src(&self, span: Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    fn expr(&self, e: ExprId) -> &'b ast::Expr {
        self.ast.expr(e)
    }

    fn sema_ty(&self, e: ExprId) -> R<TyId> {
        self.info.expr_types.get(&e).copied().ok_or_else(|| internal(self.expr(e).span, "untyped expression"))
    }

    /// Sema local declared with this name span (`var`, closure parameters).
    fn local_by_span(&self, span: Span) -> R<LocalId> {
        self.info
            .locals
            .iter()
            .position(|l| l.span == span)
            .map(|i| LocalId(i as u32))
            .ok_or_else(|| internal(span, "binding without a local"))
    }

    fn pat_local(&self, p: PatId) -> R<LocalId> {
        self.info
            .pat_locals
            .get(&p)
            .map(|l| LocalId(l.0))
            .ok_or_else(|| internal(self.ast.pat(p).span, "pattern without a local"))
    }
}

// ---------------------------------------------------------------- functions

pub(crate) fn bind_params(lw: &mut Lowerer, cx: &mut FnCx, d: DefId, f: &SFnDef) -> R<Vec<Param>> {
    let def = lw.a.def(d);
    let span = def.span;
    let ast_params: Vec<ast::Param> = match def.item.map(|i| &cx.ast.item(i).kind) {
        Some(ast::ItemKind::Fn(fd)) => fd.params.clone(),
        Some(ast::ItemKind::Target(inner)) => match inner.as_ref() {
            ast::ItemKind::Fn(fd) => fd.params.clone(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    let mut params = Vec::new();
    // Sema declares parameter locals first, in order, skipping `_`.
    let mut next_local = 0usize;
    let mut sig = f.params.iter();
    for p in &ast_params {
        match &p.name {
            ast::ParamName::SelfParam(_) => {
                let l = LocalId(next_local as u32);
                next_local += 1;
                let Some(local) = cx.locals.get(l.0 as usize) else { return Err(internal(span, "missing self local")) };
                let mode = core_mode(f.self_mode.unwrap_or(ast::Mode::Borrow));
                params.push(Param { local: l, mode, ty: local.ty.clone() });
            }
            ast::ParamName::Ident(_) => {
                let Some(ps) = sig.next() else { return Err(internal(span, "parameter count")) };
                let l = LocalId(next_local as u32);
                next_local += 1;
                let Some(local) = cx.locals.get(l.0 as usize) else {
                    return Err(internal(span, "missing param local"));
                };
                params.push(Param { local: l, mode: core_mode(ps.mode), ty: local.ty.clone() });
            }
            ast::ParamName::Wild(_) => {
                let Some(ps) = sig.next() else { return Err(internal(span, "parameter count")) };
                let ty = lw.core_ty(ps.ty, &cx.args, ps.span)?;
                let l = cx.temp("_", ty.clone());
                params.push(Param { local: l, mode: core_mode(ps.mode), ty });
            }
        }
    }
    Ok(params)
}

pub(crate) fn lower_fn_body(lw: &mut Lowerer, cx: &mut FnCx, body: ExprId) -> R<Block> {
    let AK::Block(b) = &cx.expr(body).kind else {
        return Err(internal(cx.expr(body).span, "function body is not a block"));
    };
    let want = cx.ret != Ty::Unit;
    lower_block(lw, cx, b, want)
}

/// Lower a block; `want_value` keeps the tail expression as the block value.
fn lower_block(lw: &mut Lowerer, cx: &mut FnCx, b: &ast::Block, want_value: bool) -> R<Block> {
    let mut stmts = Vec::new();
    for &s in &b.stmts {
        lower_stmt(lw, cx, s, &mut stmts)?;
    }
    let value = match b.tail {
        Some(t) if want_value => Some(Box::new(lower_expr(lw, cx, t)?)),
        Some(t) => {
            lower_expr_stmt(lw, cx, t, &mut stmts)?;
            None
        }
        None => None,
    };
    Ok(Block { stmts, value })
}

/// A block expression in value position: its sema type decides whether it has a value.
pub(super) fn lower_block_expr(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Block> {
    let ty = lw.core_ty(cx.sema_ty(e)?, &cx.args, cx.expr(e).span)?;
    match &cx.expr(e).kind {
        AK::Block(b) => lower_block(lw, cx, b, ty != Ty::Unit),
        _ => {
            let v = lower_expr(lw, cx, e)?;
            if ty == Ty::Unit {
                let mut stmts = Vec::new();
                push_expr_stmt(v, &mut stmts);
                Ok(Block { stmts, value: None })
            } else {
                Ok(Block { stmts: Vec::new(), value: Some(Box::new(v)) })
            }
        }
    }
}

fn push_expr_stmt(e: Expr, stmts: &mut Vec<Stmt>) {
    match e.kind {
        ExprKind::Block(b) => {
            stmts.extend(b.stmts);
            if let Some(v) = b.value {
                push_expr_stmt(*v, stmts);
            }
        }
        ExprKind::Lit(_) | ExprKind::Local(_) => {}
        _ => stmts.push(stmt(e.span, StmtKind::Expr(e))),
    }
}

// ---------------------------------------------------------------- statements

fn lower_stmt(lw: &mut Lowerer, cx: &mut FnCx, s: StmtId, out: &mut Vec<Stmt>) -> R<()> {
    let st = cx.ast.stmt(s);
    let span = st.span;
    match &st.kind {
        AS::Let { pat, init, .. } => {
            let v = lower_expr(lw, cx, *init)?;
            bind_irrefutable(lw, cx, *pat, v, out)
        }
        AS::Var { name, init, .. } => {
            let v = lower_expr(lw, cx, *init)?;
            let l = cx.local_by_span(name.span)?;
            out.push(stmt(span, StmtKind::Let(l, v)));
            Ok(())
        }
        AS::Assign { target, value } => {
            let t = lower_expr(lw, cx, *target)?;
            let Some(place) = t.as_place() else { return Err(internal(span, "assignment target is not a place")) };
            let v = lower_expr(lw, cx, *value)?;
            // The position of an assignment is its target (`xs[i]` of `xs[i] =
            // v`): where its write panics, an index out of range (§18.1,
            // R-185). The value's panics have the value's own positions.
            out.push(stmt(cx.expr(*target).span, StmtKind::Assign(place, v)));
            Ok(())
        }
        AS::For { pat, iter, body, .. } => lower_for(lw, cx, *pat, *iter, *body, span, out),
        AS::While { cond, body } => {
            let c = lower_expr(lw, cx, *cond)?;
            let b = lower_block_expr(lw, cx, *body)?;
            out.push(stmt(span, StmtKind::While(c, b)));
            Ok(())
        }
        AS::Break => {
            out.push(stmt(span, StmtKind::Break));
            Ok(())
        }
        AS::Continue => {
            out.push(stmt(span, StmtKind::Continue));
            Ok(())
        }
        AS::Return(v) => {
            let e = match v {
                Some(v) => Some(lower_expr(lw, cx, *v)?),
                None => None,
            };
            // `return` leaves the innermost function (S-192): in an anonymous
            // function that `from_fn` expands in place, that is not the
            // function being lowered (R-08, W8-09).
            if cx.inline_depth > 0 {
                return Err(unsupported(span, Feature::ReturnInFromFn, &[]));
            }
            match e {
                // `return e` with `e: ()` evaluates `e`, then leaves (R-07):
                // the value is nothing, the effects are not.
                Some(e) if e.ty == Ty::Unit => {
                    push_expr_stmt(e, out);
                    out.push(stmt(span, StmtKind::Return(None)));
                }
                e => out.push(stmt(span, StmtKind::Return(e))),
            }
            Ok(())
        }
        AS::Assert(e) => {
            let c = lower_expr(lw, cx, *e)?;
            // The message of a failed `assert` (§11.8, §18.1): `assert <source
            // of the expression>`, made here only (R-183); the interpreter,
            // `onsa test` and C's `panic_messages` all show it as it is. The
            // source of an expression on several lines is as written, its
            // line breaks made LF (a CR LF is one line break, §2.5, as `onsa
            // fmt` makes it; S-284). A lone CR is E0001 (§2.5) only from
            // W3-04; until then one can stay in the message as written.
            let src = cx.src(cx.expr(*e).span).replace("\r\n", "\n");
            let msg = lw.msg(&format!("assert {src}"));
            let not = Expr::new(Ty::Bool, span, ExprKind::Unary(UnOp::Not, Box::new(c)));
            let then = Block {
                stmts: vec![stmt(
                    span,
                    StmtKind::Expr(Expr::new(Ty::Unit, span, ExprKind::Panic { msg, origin: PanicOrigin::Assert })),
                )],
                value: None,
            };
            out.push(stmt(span, StmtKind::If(not, then, Block::default())));
            Ok(())
        }
        AS::Expr(e) => lower_expr_stmt(lw, cx, *e, out),
    }
}

/// An expression in statement position: `if` / blocks become statements.
fn lower_expr_stmt(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, out: &mut Vec<Stmt>) -> R<()> {
    let span = cx.expr(e).span;
    match &cx.expr(e).kind {
        AK::If { cond, then, else_, .. } => {
            let c = lower_expr(lw, cx, *cond)?;
            let t = lower_block_expr(lw, cx, *then)?;
            let el = match else_ {
                Some(el) => lower_block_expr(lw, cx, *el)?,
                None => Block::default(),
            };
            out.push(stmt(span, StmtKind::If(c, drop_value(t), drop_value(el))));
            Ok(())
        }
        AK::Block(b) => {
            let blk = lower_block(lw, cx, b, false)?;
            out.extend(blk.stmts);
            Ok(())
        }
        AK::Paren(inner) => lower_expr_stmt(lw, cx, *inner, out),
        _ => {
            let v = lower_expr(lw, cx, e)?;
            push_expr_stmt(v, out);
            Ok(())
        }
    }
}

pub(super) fn drop_value(mut b: Block) -> Block {
    if let Some(v) = b.value.take() {
        push_expr_stmt(*v, &mut b.stmts);
    }
    b
}

fn lower_for(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    pat: PatId,
    iter: ExprId,
    body: ExprId,
    span: Span,
    out: &mut Vec<Stmt>,
) -> R<()> {
    if let AK::Range(r) = &cx.expr(iter).kind {
        let r = *r;
        if r.end != RangeEnd::Excluded {
            // The checker gives E0200 until W8-03 (S-224); never as `..<` (R-81).
            return Err(internal(span, "a `for` over `a..=b` reached the lowering"));
        }
        let lo = lower_expr(lw, cx, r.lo)?;
        let hi = lower_expr(lw, cx, r.hi)?;
        let var = match &cx.ast.pat(pat).kind {
            PatKind::Bind(_) => cx.pat_local(pat)?,
            PatKind::Wild => cx.temp("_", lo.ty.clone()),
            _ => return Err(internal(span, "range loop pattern")),
        };
        let b = lower_block_expr(lw, cx, body)?;
        out.push(stmt(span, StmtKind::ForRange(var, lo, hi, drop_value(b))));
        return Ok(());
    }
    // Sequence: index loop over a place (or a temporary holding the value).
    let seq = lower_expr(lw, cx, iter)?;
    let seq = materialize(cx, seq, out, "__seq");
    let len = match &seq.ty {
        Ty::Array(_, n) => u32_lit(span, *n),
        Ty::Span(_) | Ty::Buf(_) => Expr::new(
            Ty::u32(),
            span,
            ExprKind::Prim { prim: Prim::Len, args: vec![Arg { mode: Mode::Borrow, expr: seq.clone() }] },
        ),
        _ => return Err(unsupported(span, Feature::Iteration, &[])),
    };
    let i = cx.temp("__i", Ty::u32());
    let mut stmts = Vec::new();
    let elem = index(seq, local_expr(cx, i, span))?;
    bind_irrefutable(lw, cx, pat, elem, &mut stmts)?;
    let b = lower_block_expr(lw, cx, body)?;
    let b = drop_value(b);
    stmts.extend(b.stmts);
    out.push(stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), len, Block { stmts, value: None })));
    Ok(())
}
