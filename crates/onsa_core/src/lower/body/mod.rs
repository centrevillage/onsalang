//! Lowering of function bodies: expressions, statements, patterns (T3-3).
//!
//! This module holds the context of a body ([`FnCx`]), the function bodies
//! and the statements; [`pat`] the patterns and `match`, [`expr`] the
//! expressions, [`call`] the calls.

use onsa_diag::Span;
use onsa_diag::unsupported::Feature;
use onsa_sema::body::{BodyInfo, Dropped, InstId, Target, TryArms};
use onsa_sema::def::{DefKind, FnDef as SFnDef};
use onsa_sema::ty::TyId;
use onsa_sema::{DefId, ModId};
use onsa_syntax::ast::{
    self, Ast, BinOp as ABinOp, ExprId, ExprKind as AK, Lit as ALit, OpGroup, PatId, PatKind, RangeEnd, StmtId,
    StmtKind as AS, UnOp as AUnOp,
};

use super::build::{
    after, balanced, bool_lit, field, field_by_name, float_text, index, lit, local_expr, materialize, payload, stmt,
    tag_of, u32_lit,
};
use super::{FailKind, GenericArg, Hole, Lowerer, R, at_hole, core_mode, internal, stopped, unsupported};
use crate::effects::repeatable;
use crate::ir::*;
use crate::prim::{MathFn, Prim, PrimRow, Scalar, row_self};

mod call;
mod expr;
mod pat;

use super::{derived, eq, flow};
use call::lower_call;
pub(super) use call::{of_type, span_of};
pub(super) use expr::lower_expr;
use pat::lower_match;
pub(super) use pat::{arm_test, bind_irrefutable, lower_match_with, pat_bind};

pub(crate) struct FnCx<'b> {
    pub args: Vec<GenericArg>,
    pub info: &'b BodyInfo,
    pub ast: &'b Ast,
    pub text: &'b str,
    pub module: ModId,
    pub locals: Vec<Local>,
    pub ret: CTy,
    /// Of each parameter but `self`, in order, the Core type of a `_` (no
    /// local), from the binding stage: [`bind_params`] reads it.
    pub wild: Vec<Option<CTy>>,
    /// Depth of inlined closure bodies (`return` and `?` inside them are
    /// unsupported until W8-09: they leave the closure, S-192).
    pub inline_depth: u32,
    /// Set while lowering a flow body (T3-5): overrides for state-resident
    /// locals and for the stateful node expressions.
    pub flow: Option<super::flow::FlowLowerCx<'b>>,
    /// Lowering the initializer of a `const`, which has no local of its own
    /// (`Feature::ConstBindings`).
    pub constant: bool,
    /// Whether this body lowered a placeholder (S-67), whatever the unit
    /// that lowers it.
    pub placeholder: bool,
}

/// A binding of a unit: its type, where it is converted (the limits of
/// §4.4 are judged there) and where it is declared (its E0200, §18.1).
#[derive(Debug, Clone, Copy)]
pub(crate) struct Binding {
    pub ty: TyId,
    pub at: Span,
    pub decl: Span,
}

/// The result of a body: a binding of the unit, or made by its caller.
pub(crate) enum Ret {
    Of(Binding),
    Made(CTy),
}

/// The binding stage of a unit (§18.1, S-67): the Core types of `binds`,
/// in order. A type lowering does not lower stops the unit, as Stopped: one
/// E0200 for each unsupported part (`BadTy`: its feature, its detail and the
/// field it is written in), at the binding of it declared first, so that
/// the body is not lowered. O(the bindings).
pub(crate) fn bind_tys(
    lw: &mut Lowerer,
    binds: impl IntoIterator<Item = Binding>,
    args: &[GenericArg],
    span: Span,
) -> R<Vec<CTy>> {
    // In the order found, each at its binding declared first.
    let (mut tys, mut first, mut index) = (Vec::new(), Vec::<(_, Span)>::new(), std::collections::HashMap::new());
    for b in binds {
        match lw.core_ty(b.ty, args, b.at) {
            Ok(t) => tys.push(t),
            Err(f) => {
                let FailKind::UnsupportedType(bad) = f.kind else { return Err(f) };
                let i = *index.entry(bad).or_insert_with(|| {
                    first.push((bad, b.decl));
                    first.len() - 1
                });
                first[i].1 = std::cmp::min_by_key(first[i].1, b.decl, |s: &Span| s.start);
            }
        }
    }
    if first.is_empty() {
        return Ok(tys);
    }
    for (bad, at) in first {
        if let Some(d) = bad.fail(lw, at).report {
            lw.unsupported.push(*d);
        }
    }
    Err(stopped(span))
}

impl<'b> FnCx<'b> {
    /// The body of `def` at `args`, after the binding stage ([`bind_tys`]):
    /// the result, the parameters `_` (no locals), then every local.
    pub(crate) fn new(
        lw: &mut Lowerer<'b>,
        def: DefId,
        args: Vec<GenericArg>,
        info: &'b BodyInfo,
        ret: Ret,
    ) -> R<FnCx<'b>> {
        let d = lw.a.def(def);
        let (module, span) = (d.module, d.span);
        let Some(m) = lw.a.ast(lw.pkg, module) else { return Err(internal(span, "module source not found")) };
        let (head, made) = match ret {
            Ret::Of(b) => (Some(b), None),
            Ret::Made(t) => (None, Some(t)),
        };
        let params = d.as_fn().map(|f| &f.params[..]).unwrap_or_default();
        // Sema names a parameter `_` only when it is one, and declares no local of it.
        let is_wild: Vec<bool> = params.iter().map(|p| p.name == "_").collect();
        let wild = params.iter().zip(&is_wild).filter(|(_, w)| **w);
        let wild = wild.map(|(p, _)| Binding { ty: p.ty, at: p.span, decl: p.name_span });
        let named = info.locals.iter().map(|l| Binding { ty: l.ty, at: l.span, decl: l.span });
        let head: Vec<_> = head.into_iter().chain(wild).collect();
        let n = head.len();
        let mut tys = bind_tys(lw, head.into_iter().chain(named), &args, span)?;
        let locals = tys.split_off(n).into_iter().zip(&info.locals);
        let locals = locals.map(|(ty, l)| Local { name: l.name.clone(), ty }).collect();
        let mut head = tys.into_iter();
        let ret = match made {
            Some(t) => t,
            None => head.next().ok_or_else(|| internal(span, "a body of no result"))?,
        };
        let wild = is_wild.into_iter().map(|w| if w { head.next() } else { None }).collect();
        let (ast, text) = (&m.parsed.ast, &m.text[..]);
        Ok(FnCx {
            args,
            info,
            ast,
            text,
            module,
            locals,
            ret,
            wild,
            inline_depth: 0,
            flow: None,
            constant: false,
            placeholder: false,
        })
    }

    pub(crate) fn temp(&mut self, name: &str, ty: CTy) -> LocalId {
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

    /// The type of the value of `e`: of a node above the tails at a view,
    /// the view's (its tails are converted to it, [`onsa_sema::body::View`]).
    fn value_ty(&self, e: ExprId) -> R<TyId> {
        match self.info.views.get(&e) {
            Some(v) if !v.tail => Ok(v.to),
            _ => self.sema_ty(e),
        }
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

impl Lowerer<'_> {
    /// The declaration a use of `def` is of, and its type arguments in the
    /// body of `cx`: of a member of the type parameter `of`, the member of the
    /// same name of the type it is instantiated at, from where the use reads
    /// as one of that type ([`Target::Method`]).
    fn instance_target(
        &mut self,
        def: DefId,
        of: Option<TyId>,
        inst: Option<InstId>,
        cx: &FnCx,
        span: Span,
    ) -> R<(DefId, Vec<GenericArg>)> {
        let args = match inst {
            Some(i) => self.generic_args(&cx.info.instances[i.0 as usize].args, &cx.args, span)?,
            None => Vec::new(),
        };
        let Some(of) = of else { return Ok((def, args)) };
        let ty = self.core_ty(of, &cx.args, span)?;
        // The arguments of its `impl`, then its own.
        let (member, mut gargs) = self.member_of(ty, &self.a.def(def).name, span)?;
        gargs.extend(args);
        Ok((member, gargs))
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
    let wild = cx.wild.clone();
    let mut sig = f.params.iter().zip(wild);
    for p in &ast_params {
        match &p.name {
            ast::ParamName::SelfParam(_) => {
                let l = LocalId(next_local as u32);
                next_local += 1;
                let Some(local) = cx.locals.get(l.0 as usize) else { return Err(internal(span, "missing self local")) };
                let mode = core_mode(f.self_mode.unwrap_or(ast::Mode::Borrow));
                params.push(Param { local: l, mode, ty: local.ty });
            }
            ast::ParamName::Ident(_) | ast::ParamName::Wild(_) => {
                let Some((ps, wild)) = sig.next() else { return Err(internal(span, "parameter count")) };
                let l = match wild {
                    Some(ty) => cx.temp("_", ty),
                    None => {
                        let l = LocalId(next_local as u32);
                        next_local += 1;
                        l
                    }
                };
                let Some(local) = cx.locals.get(l.0 as usize) else {
                    return Err(internal(span, "missing param local"));
                };
                params.push(Param { local: l, mode: core_mode(ps.mode), ty: local.ty });
            }
        }
    }
    Ok(params)
}

pub(crate) fn lower_fn_body(lw: &mut Lowerer, cx: &mut FnCx, body: ExprId) -> R<Block> {
    // S-85, X-8: the rest is dropped over the whole body, so it stops whole (W8-04).
    if let Some(t) = cx.info.drops.iter().find(|d| matches!(d.what, Dropped::Rest(_))) {
        return Err(unsupported(t.at, Feature::TakenFields, &[]));
    }
    let AK::Block(b) = &cx.expr(body).kind else {
        return Err(internal(cx.expr(body).span, "function body is not a block"));
    };
    let want = cx.ret;
    lower_block(lw, cx, b, want)
}

/// Lower a block of the type `want`; a type other than `()` keeps the tail
/// expression as the block value. A block that wants one and ends in a
/// diverging statement that Core does not see as one ([`Block::diverges`]: a
/// `while` of §7) has a value no path reaches, so that Core has one form.
fn lower_block(lw: &mut Lowerer, cx: &mut FnCx, b: &ast::Block, want: CTy) -> R<Block> {
    let want_value = want != Types::UNIT;
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
    let block = Block { stmts, value };
    let last = b.stmts.last().filter(|&&s| want_value && cx.info.diverging.stmt(cx.ast, s));
    match last {
        Some(&s) if b.tail.is_none() && !block.diverges() => {
            let msg = lw.msg("unreachable");
            let panic = ExprKind::Panic { msg, origin: PanicOrigin::Panic, shown: Vec::new() };
            let value = Some(Box::new(Expr::new(want, cx.ast.stmt(s).span, panic)));
            Ok(Block { value, ..block })
        }
        _ => Ok(block),
    }
}

/// A block expression in value position: its sema type decides whether it has a value.
pub(super) fn lower_block_expr(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Block> {
    let ty = lw.core_ty(cx.value_ty(e)?, &cx.args, cx.expr(e).span)?;
    match &cx.expr(e).kind {
        AK::Block(b) => lower_block(lw, cx, b, ty),
        _ => {
            let v = lower_expr(lw, cx, e)?;
            if ty == Types::UNIT {
                let mut stmts = Vec::new();
                push_expr_stmt(v, &mut stmts);
                Ok(Block { stmts, value: None })
            } else {
                Ok(Block { stmts: Vec::new(), value: Some(Box::new(v)) })
            }
        }
    }
}

pub(crate) fn push_expr_stmt(e: Expr, stmts: &mut Vec<Stmt>) {
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
                Some(e) if e.ty == Types::UNIT => {
                    push_expr_stmt(e, out);
                    out.push(stmt(span, StmtKind::Return(None)));
                }
                e => out.push(stmt(span, StmtKind::Return(e))),
            }
            Ok(())
        }
        AS::Assert(e) => {
            let shown = cx.info.shown_asserts.get(e).filter(|&&c| !lw.holes.contains(&Hole::Expr(cx.module, c)));
            let (c, shown) = match shown {
                Some(&cmp) => assert_comparison(lw, cx, cmp, out)?,
                None => (lower_expr(lw, cx, *e)?, Vec::new()),
            };
            // The message of a failed `assert` (§11.8, §18.1): `assert <source
            // of the expression>`, made here only (R-183); the interpreter,
            // `onsa test` and C's `panic_messages` all show it as it is. The
            // source of an expression on several lines is as written, its
            // line breaks made LF (a CR LF is one line break, §2.5, as `onsa
            // fmt` makes it; S-284). A lone CR is E0001 (§2.5) only from
            // W3-04; until then one can stay in the message as written.
            let src = cx.src(cx.expr(*e).span).replace("\r\n", "\n");
            let msg = lw.msg(&format!("assert {src}"));
            let not = Expr::new(Types::BOOL, span, ExprKind::Unary(UnOp::Not, Box::new(c)));
            let then = Block {
                stmts: vec![stmt(
                    span,
                    StmtKind::Expr(Expr::new(
                        Types::UNIT,
                        span,
                        ExprKind::Panic { msg, origin: PanicOrigin::Assert, shown },
                    )),
                )],
                value: None,
            };
            out.push(stmt(span, StmtKind::If(not, then, Block::default())));
            Ok(())
        }
        AS::Expr(e) => lower_expr_stmt(lw, cx, *e, out),
    }
}

/// The comparison `cmp` of an `assert` that shows its values (§18.1,
/// S-1261), and the two values: each operand lowered and evaluated once, in
/// order (§3.5). When one is not [`repeatable`] (has an effect), the left is put in a temporary first
/// (the right may change what it reads), and so is the right with one; an
/// operand without an effect is read again when the `assert` fails, to the
/// same value, as the comparison passed it without a panic.
fn assert_comparison(lw: &mut Lowerer, cx: &mut FnCx, cmp: ExprId, out: &mut Vec<Stmt>) -> R<(Expr, Vec<Expr>)> {
    let &AK::Binary { op, op_span, lhs, rhs } = &cx.expr(cmp).kind else {
        return Err(internal(cx.expr(cmp).span, "a shown `assert` of no comparison"));
    };
    let mut l = lower_expr(lw, cx, lhs)?;
    let mut r = lower_expr(lw, cx, rhs)?;
    let effect = (!repeatable(&l, &lw.m.tys), !repeatable(&r, &lw.m.tys));
    // SPEC-GAP(S-1263): a `const` has no temporary of its own (`Feature::ConstBindings`): the
    // `assert` of its initializer with an operand of an effect shows no values.
    let shows = !(cx.constant && (effect.0 || effect.1));
    let mut bind = |cx: &mut FnCx, x: Expr| {
        let (span, t) = (x.span, cx.temp("__shown", x.ty));
        out.push(stmt(span, StmtKind::Let(t, x)));
        local_expr(cx, t, span)
    };
    if shows && (effect.0 || effect.1) {
        l = bind(cx, l);
    }
    if shows && effect.1 {
        r = bind(cx, r);
    }
    let shown = if shows { vec![l.clone(), r.clone()] } else { Vec::new() };
    let sp = cx.expr(cmp).span;
    let c = expr::comparison(lw, (op, op_span), l, r, sp).map_err(|f| at_hole(f, Hole::Expr(cx.module, cmp)))?;
    Ok((c, shown))
}

/// An expression in statement position: `if` / blocks become statements
/// (an `if~` is lowered as a value, [`super::flow::tilde_if`]).
fn lower_expr_stmt(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, out: &mut Vec<Stmt>) -> R<()> {
    let span = cx.expr(e).span;
    match &cx.expr(e).kind {
        AK::If { cond, then, else_, tilde: None } => {
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
            let blk = lower_block(lw, cx, b, Types::UNIT)?;
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
            PatKind::Wild => cx.temp("_", lo.ty),
            _ => return Err(internal(span, "range loop pattern")),
        };
        let b = lower_block_expr(lw, cx, body)?;
        out.push(stmt(span, StmtKind::ForRange(var, lo, hi, drop_value(b))));
        return Ok(());
    }
    // Sequence: index loop over a place (or a temporary holding the value).
    let seq = lower_expr(lw, cx, iter)?;
    let seq = materialize(cx, seq, out, "__seq", &lw.m.tys);
    let len = match *lw.m.tys.kind(seq.ty) {
        TyKind::Array(_, n) => u32_lit(span, n),
        TyKind::Span(_) | TyKind::Buf(_) => Expr::new(
            Types::U32,
            span,
            ExprKind::Prim { prim: Prim::Len, args: vec![Arg { mode: Mode::Borrow, expr: seq.clone() }] },
        ),
        // The checks stop the others (E0200 `Iteration`), and a type lowering
        // does not lower stops the unit first.
        _ => return Err(internal(span, "iteration over a type of no array")),
    };
    let i = cx.temp("__i", Types::U32);
    let mut stmts = Vec::new();
    let elem = index(seq, local_expr(cx, i, span), &lw.m.tys)?;
    bind_irrefutable(lw, cx, pat, elem, &mut stmts)?;
    let b = lower_block_expr(lw, cx, body)?;
    let b = drop_value(b);
    stmts.extend(b.stmts);
    out.push(stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), len, Block { stmts, value: None })));
    Ok(())
}
