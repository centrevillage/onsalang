//! Lowering of function bodies: expressions, statements, patterns (T3-3).

use onsa_diag::Span;
use onsa_diag::unsupported::{Feature, FlowForm};
use onsa_sema::body::{BodyInfo, Target};
use onsa_sema::def::{DefKind, FnDef as SFnDef};
use onsa_sema::resolve::{Builtin, Entity};
use onsa_sema::ty::TyId;
use onsa_sema::{DefId, ModId};
use onsa_syntax::ast::{
    self, Ast, BinOp as ABinOp, ExprId, ExprKind as AK, Lit as ALit, OpGroup, PatId, PatKind, RangeEnd, StmtId,
    StmtKind as AS, UnOp as AUnOp,
};

use super::{FailKind, GenericArg, Hole, Lowerer, R, at_hole, core_mode, flow_form, internal, unsupported};
use crate::ir::*;
use crate::prim::{CheckedOp, MathFn, Prim};

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

fn tag_ty(lw: &Lowerer, id: TypeId) -> Ty {
    Ty::Int(onsa_sema::layout::tag_kind(lw.enum_variants(id).len()))
}

fn tag_of(lw: &Lowerer, e: Expr) -> R<Expr> {
    let Ty::Enum(id) = &e.ty else { return Err(internal(e.span, "tag of a non-enum")) };
    let ty = tag_ty(lw, *id);
    let span = e.span;
    Ok(Expr::new(ty, span, ExprKind::Tag(Box::new(e))))
}

fn payload(lw: &Lowerer, base: Expr, tag: u32, index: u32) -> R<Expr> {
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
                stmts: vec![stmt(span, StmtKind::Expr(Expr::new(Ty::Unit, span, ExprKind::Panic(msg))))],
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

// ---------------------------------------------------------------- patterns

/// Bind an irrefutable pattern (`let`, `for`, switch arms) to `value`.
pub(super) fn bind_irrefutable(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, value: Expr, out: &mut Vec<Stmt>) -> R<()> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    match &p.kind {
        PatKind::Bind(_) => {
            let l = cx.pat_local(pat)?;
            out.push(stmt(span, StmtKind::Let(l, value)));
            Ok(())
        }
        PatKind::Wild => {
            push_expr_stmt(value, out);
            Ok(())
        }
        PatKind::Tuple(elems) => {
            let base = materialize(cx, value, out, "__tuple");
            for (i, &el) in elems.iter().enumerate() {
                let f = field(lw, base.clone(), i as u32)?;
                bind_irrefutable(lw, cx, el, f, out)?;
            }
            Ok(())
        }
        PatKind::Struct { fields, .. } => {
            let base = materialize(cx, value, out, "__struct");
            for (name, fp) in fields {
                let f = field_by_name(lw, base.clone(), &name.name, name.span)?;
                bind_irrefutable(lw, cx, *fp, f, out)?;
            }
            Ok(())
        }
        PatKind::TupleStruct { path, elems } => {
            let (tag, _) = ctor_of(lw, cx, path, &value.ty)?;
            let base = materialize(cx, value, out, "__variant");
            for (i, &el) in elems.iter().enumerate() {
                let f = payload(lw, base.clone(), tag, i as u32)?;
                bind_irrefutable(lw, cx, el, f, out)?;
            }
            Ok(())
        }
        PatKind::Path(_) => {
            push_expr_stmt(value, out);
            Ok(())
        }
        PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Or(_) => {
            Err(internal(span, "refutable pattern in an irrefutable position"))
        }
    }
}

/// Constructor tag (and arity) of a ctor pattern path against an enum type.
fn ctor_of(lw: &mut Lowerer, cx: &FnCx, path: &ast::Path, ty: &Ty) -> R<(u32, usize)> {
    // Sema resolved the path already: a failure here is lowering's own.
    let entity = lw.a.resolve_path(cx.module, path).map_err(|e| {
        let d = e.into_diagnostic();
        internal(d.span, format!("pattern path does not resolve ({}: {})", d.code.as_str(), d.message))
    })?;
    let tag = match entity {
        Entity::Builtin(Builtin::None) | Entity::Builtin(Builtin::Ok) => 0,
        Entity::Builtin(Builtin::Some) | Entity::Builtin(Builtin::Err) => 1,
        Entity::Variant(_, i) => i,
        _ => return Err(internal(path.span, "pattern path is not a constructor")),
    };
    let Ty::Enum(id) = ty else { return Err(internal(path.span, "constructor pattern on a non-enum")) };
    let arity = lw.enum_variants(*id).get(tag as usize).map(|(_, f)| f.len()).unwrap_or(0);
    Ok((tag, arity))
}

fn is_irrefutable(cx: &FnCx, pat: PatId) -> bool {
    match &cx.ast.pat(pat).kind {
        PatKind::Wild | PatKind::Bind(_) => true,
        PatKind::Tuple(es) => es.iter().all(|&e| is_irrefutable(cx, e)),
        PatKind::Struct { fields, .. } => fields.iter().all(|(_, p)| is_irrefutable(cx, *p)),
        _ => false,
    }
}

fn pat_binds(cx: &FnCx, pat: PatId) -> bool {
    match &cx.ast.pat(pat).kind {
        PatKind::Bind(_) => true,
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => false,
        PatKind::Tuple(es) | PatKind::TupleStruct { elems: es, .. } | PatKind::Or(es) => {
            es.iter().any(|&e| pat_binds(cx, e))
        }
        PatKind::Struct { fields, .. } => fields.iter().any(|(_, p)| pat_binds(cx, *p)),
    }
}

/// Test of a refutable pattern against a place; `None` means "always matches".
fn pat_test(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr) -> R<Option<Expr>> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    let and = |a: Option<Expr>, b: Option<Expr>| match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) => {
            Some(Expr::new(Ty::Bool, span, ExprKind::Logic { op: LogicOp::And, lhs: Box::new(a), rhs: Box::new(b) }))
        }
    };
    match &p.kind {
        PatKind::Wild | PatKind::Bind(_) => Ok(None),
        PatKind::Lit(l) | PatKind::Neg(l) => {
            let neg = matches!(p.kind, PatKind::Neg(_));
            let v = match (l, &place.ty) {
                (ALit::Int { value, .. }, Ty::Int(_)) => Lit::Int(if neg { -(*value as i128) } else { *value as i128 }),
                (ALit::Char(c), Ty::Char) => Lit::Char(*c),
                (ALit::Bool(b), Ty::Bool) => Lit::Bool(*b),
                (ALit::Str(_), _) => return Err(unsupported(span, Feature::StrPatterns, &[])),
                _ => return Err(internal(span, "literal pattern type")),
            };
            let rhs = lit(place.ty.clone(), span, v);
            Ok(Some(Expr::new(
                Ty::Bool,
                span,
                ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(place.clone()), rhs: Box::new(rhs) },
            )))
        }
        PatKind::Path(path) => {
            let (tag, _) = ctor_of(lw, cx, path, &place.ty)?;
            Ok(Some(tag_test(lw, place, tag)?))
        }
        PatKind::TupleStruct { path, elems } => {
            let (tag, _) = ctor_of(lw, cx, path, &place.ty)?;
            let mut t = Some(tag_test(lw, place, tag)?);
            for (i, &el) in elems.iter().enumerate() {
                let sub = payload(lw, place.clone(), tag, i as u32)?;
                let st = pat_test(lw, cx, el, &sub)?;
                t = and(t, st);
            }
            Ok(t)
        }
        PatKind::Tuple(elems) => {
            let mut t = None;
            for (i, &el) in elems.iter().enumerate() {
                let sub = field(lw, place.clone(), i as u32)?;
                let st = pat_test(lw, cx, el, &sub)?;
                t = and(t, st);
            }
            Ok(t)
        }
        PatKind::Struct { fields, .. } => {
            let mut t = None;
            for (name, fp) in fields {
                let sub = field_by_name(lw, place.clone(), &name.name, name.span)?;
                let st = pat_test(lw, cx, *fp, &sub)?;
                t = and(t, st);
            }
            Ok(t)
        }
        PatKind::Or(alts) => {
            if alts.iter().any(|&a| pat_binds(cx, a)) {
                return Err(unsupported(span, Feature::OrPatternBindings, &[]));
            }
            let mut t: Option<Expr> = None;
            for &alt in alts {
                let st = pat_test(lw, cx, alt, place)?.unwrap_or_else(|| bool_lit(span, true));
                t = Some(match t {
                    None => st,
                    Some(prev) => Expr::new(
                        Ty::Bool,
                        span,
                        ExprKind::Logic { op: LogicOp::Or, lhs: Box::new(prev), rhs: Box::new(st) },
                    ),
                });
            }
            Ok(t)
        }
    }
}

fn tag_test(lw: &Lowerer, place: &Expr, tag: u32) -> R<Expr> {
    let t = tag_of(lw, place.clone())?;
    let span = place.span;
    let rhs = lit(t.ty.clone(), span, Lit::Int(tag as i128));
    Ok(Expr::new(Ty::Bool, span, ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(t), rhs: Box::new(rhs) }))
}

/// Bindings of a (possibly refutable) pattern once it is known to match.
fn pat_bind(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr, out: &mut Vec<Stmt>) -> R<()> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    match &p.kind {
        PatKind::Bind(_) => {
            let l = cx.pat_local(pat)?;
            out.push(stmt(span, StmtKind::Let(l, place.clone())));
            Ok(())
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::Or(_) => Ok(()),
        PatKind::TupleStruct { path, elems } => {
            let (tag, _) = ctor_of(lw, cx, path, &place.ty)?;
            for (i, &el) in elems.iter().enumerate() {
                let sub = payload(lw, place.clone(), tag, i as u32)?;
                pat_bind(lw, cx, el, &sub, out)?;
            }
            Ok(())
        }
        PatKind::Tuple(elems) => {
            for (i, &el) in elems.iter().enumerate() {
                let sub = field(lw, place.clone(), i as u32)?;
                pat_bind(lw, cx, el, &sub, out)?;
            }
            Ok(())
        }
        PatKind::Struct { fields, .. } => {
            for (name, fp) in fields {
                let sub = field_by_name(lw, place.clone(), &name.name, name.span)?;
                pat_bind(lw, cx, *fp, &sub, out)?;
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------- match

fn lower_match(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    scrutinee: ExprId,
    arms: &[ast::MatchArm],
    ty: Ty,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let scrut_ast = match &cx.expr(scrutinee).kind {
        AK::Move(inner) => *inner,
        _ => scrutinee,
    };
    let s = lower_expr(lw, cx, scrut_ast)?;
    let mut stmts = Vec::new();
    let place = materialize(cx, s, &mut stmts, "__match");
    let want = ty != Ty::Unit;
    // Fast path: every arm is a constructor (or a final catch-all) with
    // irrefutable sub-patterns and no guard -> `Switch`.
    let simple = matches!(place.ty, Ty::Enum(_))
        && arms.iter().all(|a| a.guard.is_none())
        && arms.iter().enumerate().all(|(i, a)| match &cx.ast.pat(a.pat).kind {
            PatKind::Path(_) => true,
            PatKind::TupleStruct { elems, .. } => elems.iter().all(|&p| is_irrefutable(cx, p)),
            PatKind::Wild | PatKind::Bind(_) => i == arms.len() - 1,
            _ => false,
        });
    if simple {
        let mut sw_arms = Vec::new();
        let mut default = None;
        for arm in arms {
            let mut b = Vec::new();
            match &cx.ast.pat(arm.pat).kind {
                PatKind::Wild | PatKind::Bind(_) => {
                    pat_bind(lw, cx, arm.pat, &place, &mut b)?;
                    let body = lower_block_expr(lw, cx, arm.body)?;
                    b.extend(body.stmts);
                    default = Some(Block { stmts: b, value: if want { body.value } else { None } });
                }
                _ => {
                    let path = match &cx.ast.pat(arm.pat).kind {
                        PatKind::Path(p) | PatKind::TupleStruct { path: p, .. } => p.clone(),
                        _ => unreachable!(),
                    };
                    let (tag, _) = ctor_of(lw, cx, &path, &place.ty)?;
                    pat_bind(lw, cx, arm.pat, &place, &mut b)?;
                    let body = lower_block_expr(lw, cx, arm.body)?;
                    b.extend(body.stmts);
                    let blk = Block { stmts: b, value: if want { body.value } else { None } };
                    if sw_arms.iter().any(|(t, _)| *t == tag) {
                        // A later arm for the same tag is unreachable; keep the first.
                        continue;
                    }
                    sw_arms.push((tag, blk));
                }
            }
        }
        let sw = Expr::new(ty.clone(), span, ExprKind::Switch { scrutinee: Box::new(place), arms: sw_arms, default });
        return Ok(if stmts.is_empty() {
            sw
        } else {
            Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(sw)) }))
        });
    }
    // General path: `if` chain with a `done` flag (guards may fall through).
    let done = cx.temp("__done", Ty::Bool);
    stmts.push(stmt(span, StmtKind::Let(done, bool_lit(span, false))));
    let result = if want { Some(cx.temp("__result", ty.clone())) } else { None };
    for arm in arms {
        let not_done = Expr::new(Ty::Bool, span, ExprKind::Unary(UnOp::Not, Box::new(local_expr(cx, done, span))));
        // A pattern that uses an unsupported feature (S-67): the arm never
        // matches and binds nothing, so lowering reaches its guard and body.
        let pat_hole = Hole::Pat(cx.module, arm.pat);
        let placeholder = lw.holes.contains(&pat_hole);
        let test = if placeholder {
            let pat_span = cx.ast.pat(arm.pat).span;
            lw.hole_spans.push(pat_span);
            Some(bool_lit(pat_span, false))
        } else {
            pat_test(lw, cx, arm.pat, &place).map_err(|f| at_hole(f, pat_hole))?
        };
        let cond = match test {
            None => not_done,
            Some(t) => Expr::new(
                Ty::Bool,
                span,
                ExprKind::Logic { op: LogicOp::And, lhs: Box::new(not_done), rhs: Box::new(t) },
            ),
        };
        let mut inner = Vec::new();
        if !placeholder {
            pat_bind(lw, cx, arm.pat, &place, &mut inner)?;
        }
        let mut body_stmts = vec![stmt(span, StmtKind::Assign(Place::Local(done), bool_lit(span, true)))];
        let body = lower_block_expr(lw, cx, arm.body)?;
        let diverges = body.diverges();
        body_stmts.extend(body.stmts);
        match (result, body.value) {
            (Some(r), Some(v)) => body_stmts.push(stmt(span, StmtKind::Assign(Place::Local(r), *v))),
            (Some(_), None) if !diverges => return Err(internal(span, "match arm without a value")),
            (_, Some(v)) => push_expr_stmt(*v, &mut body_stmts),
            _ => {}
        }
        let body_block = Block { stmts: body_stmts, value: None };
        match arm.guard {
            Some(g) => {
                let gc = lower_expr(lw, cx, g)?;
                inner.push(stmt(span, StmtKind::If(gc, body_block, Block::default())));
            }
            None => inner.extend(body_block.stmts),
        }
        stmts.push(stmt(span, StmtKind::If(cond, Block { stmts: inner, value: None }, Block::default())));
    }
    // The general path gives no value yet (R-06): its result is assigned in
    // the arms but never declared. A `match` whose value is not used (a
    // statement, a `()` match) keeps this path; W8-06 lowers the value.
    if result.is_some() {
        return Err(unsupported(span, Feature::ValueMatch, &[]));
    }
    Ok(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: None })))
}

// ---------------------------------------------------------------- expressions

pub(crate) fn lower_expr(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Expr> {
    let hole = Hole::Expr(cx.module, e);
    if lw.holes.contains(&hole) {
        // An expression that uses an unsupported feature (S-67): a fresh
        // local of its type stands for it, so lowering reaches the next one.
        // A type lowering does not support has `()` in its place (its uses
        // are placeholders too). The Core is dropped (`lower_with`).
        let span = cx.expr(e).span;
        let (ty, stand_in) = placeholder_ty(lw, cx.sema_ty(e)?, &cx.args, span)?;
        lw.hole_spans.push(span);
        if stand_in {
            lw.stand_in_spans.push(span);
        }
        let l = cx.temp("__unsupported", ty);
        return Ok(local_expr(cx, l, span));
    }
    lower_expr_at(lw, cx, e).map_err(|f| at_hole(f, hole))
}

/// The Core type of a placeholder, and whether it stands in for a type
/// lowering does not support (then it is `()`).
fn placeholder_ty(lw: &mut Lowerer, t: TyId, args: &[GenericArg], span: Span) -> R<(Ty, bool)> {
    match lw.core_ty(t, args, span) {
        Err(f) if f.kind == FailKind::Unsupported => Ok((Ty::Unit, true)),
        r => r.map(|t| (t, false)),
    }
}

fn lower_expr_at(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Expr> {
    let span = cx.expr(e).span;
    // Flow bodies (T3-5): stateful nodes, `sample_rate()` and `par` are
    // lowered by the flow lowering, not by the rules below.
    if cx.flow.is_some()
        && let Some(v) = super::flow::lower_flow_expr(lw, cx, e)?
    {
        return Ok(v);
    }
    let ty = lw.core_ty(cx.sema_ty(e)?, &cx.args, span)?;
    // Resolved names first (locals, consts, variants, builtin constants).
    if let Some(t) = cx.info.targets.get(&e).cloned()
        && !matches!(cx.expr(e).kind, AK::Call { .. })
    {
        return lower_target_value(lw, cx, e, t, ty);
    }
    let kind = match &cx.expr(e).kind {
        AK::Lit(l) => match l {
            ALit::Int { value, .. } => ExprKind::Lit(Lit::Int(*value as i128)),
            ALit::Float { text } => {
                let t = text.replace('_', "");
                match ty {
                    Ty::Float(FloatKind::F32) => {
                        ExprKind::Lit(Lit::F32(t.parse().map_err(|_| internal(span, "float literal"))?))
                    }
                    Ty::Float(FloatKind::F64) => {
                        ExprKind::Lit(Lit::F64(t.parse().map_err(|_| internal(span, "float literal"))?))
                    }
                    _ => return Err(internal(span, "float literal type")),
                }
            }
            ALit::Char(c) => ExprKind::Lit(Lit::Char(*c)),
            ALit::Bool(b) => ExprKind::Lit(Lit::Bool(*b)),
            ALit::Str(_) => return Err(unsupported(span, Feature::StrValues, &[])),
        },
        AK::Path(_) => return Err(internal(span, "unresolved path")),
        AK::Hole => return Err(internal(span, "typed hole")),
        // The names stage stops a `::[…]` with E0200 until W4-13.
        AK::TypeArgs { .. } => return Err(internal(span, "type arguments in an expression")),
        // Lowering runs only on a package without diagnostics, and a failed
        // item has a syntax diagnostic (S-59).
        AK::Error => onsa_diag::internal::bug(Some(span), "lowering met a body a syntax error left unread"),
        AK::Paren(inner) | AK::Move(inner) => return lower_expr(lw, cx, *inner),
        AK::Tuple(elems) => {
            if elems.is_empty() {
                ExprKind::Lit(Lit::Unit)
            } else {
                let mut out = Vec::new();
                for &x in elems {
                    out.push(lower_expr(lw, cx, x)?);
                }
                ExprKind::Tuple(out)
            }
        }
        AK::Array(elems) => {
            let mut out = Vec::new();
            for &x in elems {
                out.push(lower_expr(lw, cx, x)?);
            }
            ExprKind::Array(out)
        }
        AK::Repeat { elem, .. } => {
            let Ty::Array(_, n) = &ty else { return Err(internal(span, "repeat type")) };
            let n = *n;
            ExprKind::Repeat { elem: Box::new(lower_expr(lw, cx, *elem)?), n }
        }
        AK::Struct { fields, .. } => {
            let Ty::Struct(id) = &ty else { return Err(internal(span, "struct literal type")) };
            let id = *id;
            let defs = lw.struct_fields(id);
            let mut out = Vec::new();
            for (name, _) in &defs {
                let Some((_, v)) = fields.iter().find(|(n, _)| n.name == *name) else {
                    return Err(internal(span, "missing field"));
                };
                out.push(lower_expr(lw, cx, *v)?);
            }
            ExprKind::Struct { ty: id, fields: out }
        }
        AK::Block(b) => {
            let blk = lower_block(lw, cx, b, ty != Ty::Unit)?;
            if ty == Ty::Unit && blk.stmts.is_empty() { ExprKind::Lit(Lit::Unit) } else { ExprKind::Block(blk) }
        }
        AK::If { cond, then, else_, .. } => {
            let c = lower_expr(lw, cx, *cond)?;
            let t = lower_block_expr(lw, cx, *then)?;
            let el = match else_ {
                Some(el) => lower_block_expr(lw, cx, *el)?,
                None => Block::default(),
            };
            if ty == Ty::Unit {
                let s = stmt(span, StmtKind::If(c, drop_value(t), drop_value(el)));
                ExprKind::Block(Block { stmts: vec![s], value: None })
            } else {
                ExprKind::IfExpr { cond: Box::new(c), then: t, else_: el }
            }
        }
        AK::Match { scrutinee, arms, .. } => return lower_match(lw, cx, e, *scrutinee, arms, ty),
        AK::Closure { .. } => return Err(unsupported(span, Feature::Closures, &[])),
        // The checks stop at the flow syntax (W3-09); never reached.
        AK::At { .. } => return Err(flow_form(span, FlowForm::Clock)),
        AK::Feedback(_) => return Err(flow_form(span, FlowForm::Feedback)),
        AK::Handle { .. } => return Err(unsupported(span, Feature::EffectHandlers, &[])),
        AK::Unsafe(_) => return Err(unsupported(span, Feature::Unsafe, &[])),
        // Sema rejects `par` outside a flow body: lowering never sees one.
        AK::Par { .. } => return Err(internal(span, "`par` outside a flow")),
        &AK::Binary { op, op_span, lhs, rhs } => return lower_binary(lw, cx, e, (op, op_span), lhs, rhs, ty),
        AK::Cast { expr: inner, .. } => {
            let x = lower_expr(lw, cx, *inner)?;
            if x.ty == ty {
                return Ok(x);
            }
            ExprKind::Cast(Box::new(x))
        }
        AK::Unary { op, expr: inner } => {
            let x = lower_expr(lw, cx, *inner)?;
            match op {
                // A negative literal is a literal (`-128` fits `I8`; no run-time negation).
                // Sema decided which `-` belong to a literal (§4.7, S-227); every other
                // `-` negates a value and panics at `MIN` (`-(I32.MIN)`, `-(-2147483648)`, R-03).
                AUnOp::Neg if cx.info.neg_literals.contains(&e) => match &x.kind {
                    ExprKind::Lit(Lit::Int(v)) => ExprKind::Lit(Lit::Int(-v)),
                    ExprKind::Lit(Lit::F32(v)) => ExprKind::Lit(Lit::F32(-v)),
                    ExprKind::Lit(Lit::F64(v)) => ExprKind::Lit(Lit::F64(-v)),
                    _ => return Err(internal(span, "a negative literal whose operand did not lower to a literal")),
                },
                AUnOp::Neg => ExprKind::Unary(UnOp::Neg, Box::new(x)),
                AUnOp::Not => ExprKind::Unary(UnOp::Not, Box::new(x)),
            }
        }
        AK::Call { callee, args, .. } => return lower_call(lw, cx, e, *callee, args, ty),
        AK::Field { base, name } => {
            let b = lower_expr(lw, cx, *base)?;
            return field_by_name(lw, b, &name.name, span);
        }
        AK::TupleIndex { base, index, .. } => {
            let b = lower_expr(lw, cx, *base)?;
            return field(lw, b, *index);
        }
        AK::Index { base, index: i } => {
            let b = lower_expr(lw, cx, *base)?;
            let i = lower_expr(lw, cx, *i)?;
            // The whole `xs[i]`, not its base: the position of its panic
            // (§18.1, S-233).
            let mut x = index(b, i)?;
            x.span = span;
            return Ok(x);
        }
        AK::Try(inner) => return lower_try(lw, cx, *inner, ty, span),
        AK::Range(_) => return Err(internal(span, "range outside a loop head")),
    };
    Ok(Expr::new(ty, span, kind))
}

fn lower_target_value(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, t: Target, ty: Ty) -> R<Expr> {
    let span = cx.expr(e).span;
    if let Target::Local(l) = t
        && let Some(f) = &cx.flow
        && let Some(v) = f.local_override.get(&l.0)
    {
        return Ok(v.clone());
    }
    let kind = match t {
        Target::Local(l) => ExprKind::Local(LocalId(l.0)),
        Target::ConstParam(i) => match cx.args.get(i as usize) {
            Some(GenericArg::Const(n)) => ExprKind::Lit(Lit::Int(*n as i128)),
            _ => return Err(internal(span, "unbound const parameter")),
        },
        Target::Const(d) => ExprKind::Const(lw.const_id(d)?),
        Target::Variant { index, .. } => {
            let Ty::Enum(id) = &ty else { return Err(unsupported(span, Feature::VariantCtorValues, &[])) };
            ExprKind::Variant { ty: *id, tag: index, fields: Vec::new() }
        }
        Target::Prelude(Builtin::None) => {
            let Ty::Enum(id) = &ty else { return Err(internal(span, "None type")) };
            ExprKind::Variant { ty: *id, tag: 0, fields: Vec::new() }
        }
        Target::BuiltinConst { name, .. } => builtin_const(&ty, &name, span)?,
        Target::Fn { .. } | Target::Prelude(_) => return Err(unsupported(span, Feature::FnValues, &[])),
        Target::Method { .. } | Target::BuiltinMethod { .. } | Target::Value => {
            return Err(internal(span, "call target on a non-call"));
        }
    };
    Ok(Expr::new(ty, span, kind))
}

fn builtin_const(ty: &Ty, name: &str, span: Span) -> R<ExprKind> {
    Ok(match ty {
        Ty::Float(FloatKind::F32) => ExprKind::Lit(Lit::F32(match name {
            "PI" => std::f32::consts::PI,
            "MIN" => f32::MIN,
            "MAX" => f32::MAX,
            "EPSILON" => f32::EPSILON,
            "INFINITY" => f32::INFINITY,
            "NAN" => f32::NAN,
            _ => return Err(internal(span, "builtin constant")),
        })),
        Ty::Float(FloatKind::F64) => ExprKind::Lit(Lit::F64(match name {
            "PI" => std::f64::consts::PI,
            "MIN" => f64::MIN,
            "MAX" => f64::MAX,
            "EPSILON" => f64::EPSILON,
            "INFINITY" => f64::INFINITY,
            "NAN" => f64::NAN,
            _ => return Err(internal(span, "builtin constant")),
        })),
        Ty::Int(k) => {
            let (lo, hi) = k.range();
            ExprKind::Lit(Lit::Int(match name {
                "MIN" => lo,
                "MAX" => hi,
                "BITS" => k.bits() as i128,
                _ => return Err(internal(span, "builtin constant")),
            }))
        }
        _ => return Err(internal(span, "builtin constant type")),
    })
}

fn lower_binary(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    (op, op_span): (ABinOp, Span),
    lhs: ExprId,
    rhs: ExprId,
    ty: Ty,
) -> R<Expr> {
    let sp = cx.expr(e).span;
    let l = lower_expr(lw, cx, lhs)?;
    let r = lower_expr(lw, cx, rhs)?;
    let out = match op.group() {
        OpGroup::And | OpGroup::Or => {
            let lop = if op.group() == OpGroup::And { LogicOp::And } else { LogicOp::Or };
            Expr::new(Ty::Bool, sp, ExprKind::Logic { op: lop, lhs: Box::new(l), rhs: Box::new(r) })
        }
        OpGroup::Comparison => {
            let cop = match op {
                ABinOp::Eq => CmpOp::Eq,
                ABinOp::Ne => CmpOp::Ne,
                ABinOp::Lt => CmpOp::Lt,
                ABinOp::Le => CmpOp::Le,
                ABinOp::Gt => CmpOp::Gt,
                _ => CmpOp::Ge,
            };
            if l.ty.is_scalar() {
                Expr::new(Ty::Bool, sp, ExprKind::Cmp { op: cop, lhs: Box::new(l), rhs: Box::new(r) })
            } else if matches!(cop, CmpOp::Eq | CmpOp::Ne) {
                let f = super::eq::eq_fn(lw, &l.ty, op_span)?;
                let call = Expr::new(
                    Ty::Bool,
                    sp,
                    ExprKind::Call {
                        fn_: f,
                        args: vec![Arg { mode: Mode::Borrow, expr: l }, Arg { mode: Mode::Borrow, expr: r }],
                    },
                );
                if cop == CmpOp::Eq {
                    call
                } else {
                    Expr::new(Ty::Bool, sp, ExprKind::Unary(UnOp::Not, Box::new(call)))
                }
            } else {
                return Err(unsupported(op_span, Feature::OrderingAggregates, &[]));
            }
        }
        OpGroup::Additive | OpGroup::Multiplicative | OpGroup::Remainder | OpGroup::Bitwise => {
            let (bop, overflow) = match op {
                ABinOp::Add => (BinOp::Add, Overflow::Checked),
                ABinOp::Sub => (BinOp::Sub, Overflow::Checked),
                ABinOp::Mul => (BinOp::Mul, Overflow::Checked),
                ABinOp::Div => (BinOp::Div, Overflow::Checked),
                ABinOp::Rem => (BinOp::Rem, Overflow::Checked),
                ABinOp::WrapAdd => (BinOp::Add, Overflow::Wrap),
                ABinOp::WrapSub => (BinOp::Sub, Overflow::Wrap),
                ABinOp::WrapMul => (BinOp::Mul, Overflow::Wrap),
                ABinOp::SatAdd => (BinOp::Add, Overflow::Sat),
                ABinOp::SatSub => (BinOp::Sub, Overflow::Sat),
                ABinOp::SatMul => (BinOp::Mul, Overflow::Sat),
                ABinOp::BitAnd => (BinOp::BitAnd, Overflow::Checked),
                ABinOp::BitOr => (BinOp::BitOr, Overflow::Checked),
                ABinOp::BitXor => (BinOp::BitXor, Overflow::Checked),
                ABinOp::Shl => (BinOp::Shl, Overflow::Checked),
                ABinOp::Shr => (BinOp::Shr, Overflow::Checked),
                _ => unreachable!(),
            };
            let t = l.ty.clone();
            if bop == BinOp::Rem && t.is_float() {
                let Ty::Float(k) = t else { unreachable!() };
                Expr::new(
                    Ty::Float(k),
                    sp,
                    ExprKind::Prim {
                        prim: Prim::Math(MathFn::Fmod, k),
                        args: vec![Arg { mode: Mode::Borrow, expr: l }, Arg { mode: Mode::Borrow, expr: r }],
                    },
                )
            } else {
                Expr::new(t, sp, ExprKind::Binary { op: bop, overflow, lhs: Box::new(l), rhs: Box::new(r) })
            }
        }
    };
    if out.ty != ty {
        return Err(internal(sp, "binary operator type"));
    }
    Ok(out)
}

fn lower_try(lw: &mut Lowerer, cx: &mut FnCx, inner: ExprId, ty: Ty, span: Span) -> R<Expr> {
    let v = lower_expr(lw, cx, inner)?;
    // `?` leaves the innermost function (S-192), as `return` does.
    if cx.inline_depth > 0 {
        return Err(unsupported(span, Feature::TryInFromFn, &[]));
    }
    let Ty::Enum(id) = v.ty.clone() else { return Err(internal(span, "`?` on a non-enum")) };
    let variants = lw.enum_variants(id);
    let is_option = variants.first().is_some_and(|(n, _)| n == "None");
    let Ty::Enum(ret_id) = cx.ret.clone() else {
        return Err(internal(span, "`?` in a function without Option / Result"));
    };
    let mut stmts = Vec::new();
    let tmp = materialize(cx, v, &mut stmts, "__try");
    // Option: None -> return None; Some(x) -> x.   Result: Err(e) -> return Err(e); Ok(x) -> x.
    let (good, bad) = if is_option { (1, 0) } else { (0, 1) };
    let early = if is_option {
        Expr::new(cx.ret.clone(), span, ExprKind::Variant { ty: ret_id, tag: 0, fields: Vec::new() })
    } else {
        let err = payload(lw, tmp.clone(), 1, 0)?;
        Expr::new(cx.ret.clone(), span, ExprKind::Variant { ty: ret_id, tag: 1, fields: vec![err] })
    };
    let bad_block = Block { stmts: vec![stmt(span, StmtKind::Return(Some(early)))], value: None };
    let good_block = Block { stmts: Vec::new(), value: Some(Box::new(payload(lw, tmp.clone(), good, 0)?)) };
    let mut arms = vec![(good, good_block), (bad, bad_block)];
    arms.sort_by_key(|(t, _)| *t);
    let sw = Expr::new(ty.clone(), span, ExprKind::Switch { scrutinee: Box::new(tmp), arms, default: None });
    Ok(if stmts.is_empty() {
        sw
    } else {
        Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(sw)) }))
    })
}

// ---------------------------------------------------------------- calls

/// Lower call arguments against parameter types, coercing arrays / `Buf` to
/// `Span` (§5.3) and planar `[Span[T]; N]` arguments.
fn lower_args(lw: &mut Lowerer, cx: &mut FnCx, args: &[ast::Arg], params: &[(Mode, Ty)]) -> R<Vec<Arg>> {
    let mut out = Vec::new();
    for (a, (pm, pt)) in args.iter().zip(params) {
        let e = lower_expr(lw, cx, a.expr)?;
        let e = coerce(lw, cx, e, pt, *pm)?;
        out.push(Arg { mode: *pm, expr: e });
    }
    Ok(out)
}

pub(super) fn coerce(lw: &mut Lowerer, cx: &mut FnCx, e: Expr, want: &Ty, mode: Mode) -> R<Expr> {
    if e.ty == *want {
        return Ok(e);
    }
    let span = e.span;
    match (want, &e.ty) {
        (Ty::Span(_), Ty::Array(..) | Ty::Buf(_)) => span_of(cx, e, mode),
        (Ty::Array(elem, n), Ty::Array(from, m)) if matches!(**elem, Ty::Span(_)) && n == m => {
            let n = *n;
            // Planar: `[a, b]` written in the argument, or an array of arrays / Bufs.
            if let ExprKind::Array(items) = e.kind {
                let mut out = Vec::new();
                for it in items {
                    out.push(coerce(lw, cx, it, elem, mode)?);
                }
                return Ok(Expr::new(want.clone(), span, ExprKind::Array(out)));
            }
            let _ = from;
            let base =
                if e.as_place().is_some() { e } else { return Err(unsupported(span, Feature::PlanarTemporary, &[])) };
            let mut out = Vec::new();
            for i in 0..n {
                let el = index(base.clone(), u32_lit(span, i))?;
                out.push(coerce(lw, cx, el, elem, mode)?);
            }
            Ok(Expr::new(want.clone(), span, ExprKind::Array(out)))
        }
        _ => Err(internal(
            span,
            format!(
                "cannot coerce `{}` to `{}`",
                crate::dump::type_name(&lw.m, &e.ty),
                crate::dump::type_name(&lw.m, want)
            ),
        )),
    }
}

pub(super) fn span_of(cx: &mut FnCx, e: Expr, mode: Mode) -> R<Expr> {
    let span = e.span;
    let elem = match &e.ty {
        Ty::Array(t, _) | Ty::Buf(t) => (**t).clone(),
        Ty::Span(_) => return Ok(e),
        _ => return Err(internal(span, "span of a non-sequence")),
    };
    let base = if e.as_place().is_some() {
        e
    } else {
        if mode == Mode::Inout {
            return Err(internal(span, "inout span of a temporary"));
        }
        // A temporary: bind it so the span has a place to point at.
        let t = cx.temp("__arr", e.ty.clone());
        let let_ = stmt(span, StmtKind::Let(t, e));
        let local = local_expr(cx, t, span);
        let sp = Expr::new(Ty::Span(Box::new(elem)), span, ExprKind::SpanOf(Box::new(local)));
        return Ok(Expr::new(
            sp.ty.clone(),
            span,
            ExprKind::Block(Block { stmts: vec![let_], value: Some(Box::new(sp)) }),
        ));
    };
    Ok(Expr::new(Ty::Span(Box::new(elem)), span, ExprKind::SpanOf(Box::new(base))))
}

fn lower_call(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, callee: ExprId, args: &[ast::Arg], ty: Ty) -> R<Expr> {
    let span = cx.expr(e).span;
    let Some(target) = cx.info.targets.get(&e).cloned() else { return Err(internal(span, "call without a target")) };
    match target {
        Target::Fn { def, inst } => {
            let gargs = match inst {
                Some(i) => {
                    let inst = &cx.info.instances[i.0 as usize];
                    lw.generic_args(&inst.args, &cx.args, span)?
                }
                None => Vec::new(),
            };
            let d = lw.a.def(def).clone();
            let DefKind::Fn(f) = &d.kind else { return Err(internal(span, "call to a non-fn")) };
            if f.target {
                return lower_target_call(lw, cx, e, def, f, &gargs, args, ty);
            }
            let params = sig_params(lw, cx, f, &gargs, span)?;
            let cargs = lower_args(lw, cx, args, &params)?;
            let fid = lw.fn_id(def, gargs);
            Ok(Expr::new(ty, span, ExprKind::Call { fn_: fid, args: cargs }))
        }
        Target::Method { def, inst } => {
            let gargs = match inst {
                Some(i) => {
                    let inst = &cx.info.instances[i.0 as usize];
                    lw.generic_args(&inst.args, &cx.args, span)?
                }
                None => Vec::new(),
            };
            let d = lw.a.def(def).clone();
            let DefKind::Fn(f) = &d.kind else { return Err(internal(span, "method target")) };
            let AK::Field { base, .. } = &cx.expr(callee).kind else { return Err(internal(span, "method call shape")) };
            let recv = lower_expr(lw, cx, *base)?;
            let self_mode = core_mode(f.self_mode.unwrap_or(ast::Mode::Borrow));
            let params = sig_params(lw, cx, f, &gargs, span)?;
            let mut cargs = vec![Arg { mode: self_mode, expr: recv }];
            cargs.extend(lower_args(lw, cx, args, &params)?);
            let fid = lw.fn_id(def, gargs);
            Ok(Expr::new(ty, span, ExprKind::Call { fn_: fid, args: cargs }))
        }
        Target::BuiltinMethod { name, .. } => lower_builtin_method(lw, cx, e, callee, &name, args, ty),
        Target::Variant { index, .. } => {
            let Ty::Enum(id) = &ty else { return Err(internal(span, "variant call type")) };
            let id = *id;
            let fields = lw.enum_variants(id)[index as usize].1.clone();
            let params: Vec<(Mode, Ty)> = fields.into_iter().map(|t| (Mode::Borrow, t)).collect();
            let cargs = lower_args(lw, cx, args, &params)?;
            Ok(Expr::new(
                ty,
                span,
                ExprKind::Variant { ty: id, tag: index, fields: cargs.into_iter().map(|a| a.expr).collect() },
            ))
        }
        Target::Prelude(b) => {
            let Ty::Enum(id) = &ty else { return Err(internal(span, "prelude call type")) };
            let id = *id;
            let tag = match b {
                Builtin::Some | Builtin::Err => 1,
                Builtin::Ok => 0,
                _ => return Err(internal(span, "prelude call")),
            };
            let fields = lw.enum_variants(id)[tag as usize].1.clone();
            let params: Vec<(Mode, Ty)> = fields.into_iter().map(|t| (Mode::Borrow, t)).collect();
            let cargs = lower_args(lw, cx, args, &params)?;
            Ok(Expr::new(
                ty,
                span,
                ExprKind::Variant { ty: id, tag, fields: cargs.into_iter().map(|a| a.expr).collect() },
            ))
        }
        Target::Value => Err(unsupported(span, Feature::CallsThroughFnValues, &[])),
        _ => Err(internal(span, "call target")),
    }
}

fn sig_params(lw: &mut Lowerer, cx: &FnCx, f: &SFnDef, gargs: &[GenericArg], span: Span) -> R<Vec<(Mode, Ty)>> {
    let _ = cx;
    let mut out = Vec::new();
    for p in &f.params {
        out.push((core_mode(p.mode), lw.core_ty(p.ty, gargs, span)?));
    }
    Ok(out)
}

/// A call to a `target fn` of `std` (D-07): math primitives, `array.from_fn`
/// (inlined), or a named primitive the interpreter provides.
#[allow(clippy::too_many_arguments)]
fn lower_target_call(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    def: DefId,
    f: &SFnDef,
    gargs: &[GenericArg],
    args: &[ast::Arg],
    ty: Ty,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let d = lw.a.def(def);
    if !lw.is_std_def(def) {
        // Sema stops a `target` declaration outside `std` (`UserTargets` of
        // the list of S-224): lowering never sees a call to one.
        return Err(internal(span, "a call to a `target` declaration outside `std`"));
    }
    let module = lw.a.modules.get(d.module).path.clone();
    let name = d.name.clone();
    let params = sig_params(lw, cx, f, gargs, span)?;
    match (module.as_str(), name.as_str()) {
        ("math", n) => {
            let Some(mf) = MathFn::parse(n) else { return Err(internal(span, "unknown std.math function")) };
            let cargs = lower_args(lw, cx, args, &params)?;
            let prim = match &ty {
                Ty::Float(k) => Prim::Math(mf, *k),
                Ty::Int(k) => match mf {
                    MathFn::Abs => Prim::IntAbs(*k),
                    MathFn::Min => Prim::IntMin(*k),
                    MathFn::Max => Prim::IntMax(*k),
                    _ => return Err(internal(span, "math function on an integer")),
                },
                _ => return Err(internal(span, "math function type")),
            };
            Ok(Expr::new(ty, span, ExprKind::Prim { prim, args: cargs }))
        }
        ("array", "from_fn") => lower_from_fn(lw, cx, args, ty, span),
        _ => {
            let cargs = lower_args(lw, cx, args, &params)?;
            Ok(Expr::new(ty, span, ExprKind::Prim { prim: Prim::Std(format!("std.{module}.{name}")), args: cargs }))
        }
    }
}

/// `array.from_fn(f)`: an array local filled by a loop; a closure argument is
/// inlined with its parameter bound to the index, a function item is called.
fn lower_from_fn(lw: &mut Lowerer, cx: &mut FnCx, args: &[ast::Arg], ty: Ty, span: Span) -> R<Expr> {
    let Ty::Array(elem, n) = &ty else { return Err(internal(span, "from_fn type")) };
    let (elem, n) = ((**elem).clone(), *n);
    let [farg] = args else { return Err(internal(span, "from_fn arity")) };
    let arr = cx.temp("__arr", ty.clone());
    let i = cx.temp("__i", Ty::u32());
    let mut body = Vec::new();
    let value = match &cx.expr(farg.expr).kind {
        AK::Closure { params, body: cbody, .. } => {
            let [p] = params.as_slice() else { return Err(internal(span, "from_fn closure arity")) };
            if let ast::ParamName::Ident(id) = &p.name {
                let l = cx.local_by_span(id.span)?;
                body.push(stmt(span, StmtKind::Let(l, local_expr(cx, i, span))));
            }
            cx.inline_depth += 1;
            let r = lower_block_expr(lw, cx, *cbody);
            cx.inline_depth -= 1;
            let blk = r?;
            body.extend(blk.stmts);
            match blk.value {
                Some(v) => *v,
                None => return Err(internal(span, "from_fn closure without a value")),
            }
        }
        _ => {
            let Some(Target::Fn { def, inst }) = cx.info.targets.get(&farg.expr).cloned() else {
                return Err(unsupported(span, Feature::FromFnValue, &[]));
            };
            let gargs = match inst {
                Some(ix) => lw.generic_args(&cx.info.instances[ix.0 as usize].args.clone(), &cx.args, span)?,
                None => Vec::new(),
            };
            let fid = lw.fn_id(def, gargs);
            Expr::new(
                elem.clone(),
                span,
                ExprKind::Call { fn_: fid, args: vec![Arg { mode: Mode::Borrow, expr: local_expr(cx, i, span) }] },
            )
        }
    };
    body.push(stmt(
        span,
        StmtKind::Assign(Place::Index(Box::new(Place::Local(arr)), Box::new(local_expr(cx, i, span)), span), value),
    ));
    let stmts = vec![
        stmt(span, StmtKind::Let(arr, Expr::new(ty.clone(), span, ExprKind::Zeroed))),
        stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), u32_lit(span, n), Block { stmts: body, value: None })),
    ];
    Ok(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(local_expr(cx, arr, span))) })))
}

fn lower_builtin_method(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    callee: ExprId,
    name: &str,
    args: &[ast::Arg],
    ty: Ty,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let assoc = matches!(name, "zeroed" | "from_bits");
    let AK::Field { base, .. } = &cx.expr(callee).kind else { return Err(internal(span, "builtin method shape")) };
    let base = *base;
    let mut lowered_args = Vec::new();
    for a in args {
        lowered_args.push(lower_expr(lw, cx, a.expr)?);
    }
    let borrow = |e: Expr| Arg { mode: Mode::Borrow, expr: e };
    if assoc {
        let prim = match name {
            "zeroed" => Prim::BufZeroed,
            _ => match &ty {
                Ty::Float(k) => Prim::FromBits(*k),
                _ => return Err(internal(span, "from_bits type")),
            },
        };
        return Ok(Expr::new(ty, span, ExprKind::Prim { prim, args: lowered_args.into_iter().map(borrow).collect() }));
    }
    let recv = lower_expr(lw, cx, base)?;
    let rty = recv.ty.clone();
    let prim_call = |prim: Prim, recv: Expr, rest: Vec<Expr>| {
        let mut a = vec![borrow(recv)];
        a.extend(rest.into_iter().map(borrow));
        ExprKind::Prim { prim, args: a }
    };
    let kind = match (&rty, name) {
        (Ty::Int(k), n) if n.starts_with("narrow_") => {
            let to = IntKind::parse(&n[7..].to_uppercase()).ok_or_else(|| internal(span, "narrow target"))?;
            prim_call(Prim::Narrow { from: *k, to }, recv, lowered_args)
        }
        (Ty::Int(k), "round_f32") => prim_call(Prim::IntToFloat { from: *k, to: FloatKind::F32 }, recv, lowered_args),
        (Ty::Int(k), "round_f64") => prim_call(Prim::IntToFloat { from: *k, to: FloatKind::F64 }, recv, lowered_args),
        (Ty::Int(k), "abs") => prim_call(Prim::IntAbs(*k), recv, lowered_args),
        (Ty::Int(k), "min") => prim_call(Prim::IntMin(*k), recv, lowered_args),
        (Ty::Int(k), "max") => prim_call(Prim::IntMax(*k), recv, lowered_args),
        (Ty::Int(k), "checked_add") => prim_call(Prim::Checked(CheckedOp::Add, *k), recv, lowered_args),
        (Ty::Int(k), "checked_sub") => prim_call(Prim::Checked(CheckedOp::Sub, *k), recv, lowered_args),
        (Ty::Int(k), "checked_mul") => prim_call(Prim::Checked(CheckedOp::Mul, *k), recv, lowered_args),
        (Ty::Int(k), "checked_div") => prim_call(Prim::Checked(CheckedOp::Div, *k), recv, lowered_args),
        (Ty::Int(k), "div_euclid") => prim_call(Prim::DivEuclid(*k), recv, lowered_args),
        (Ty::Int(k), "rem_euclid") => prim_call(Prim::RemEuclid(*k), recv, lowered_args),
        (Ty::Float(k), n) if n.starts_with("trunc_") => {
            let sat = n.ends_with("_sat");
            let mid = n.trim_start_matches("trunc_").trim_end_matches("_sat");
            let to = IntKind::parse(&mid.to_uppercase()).ok_or_else(|| internal(span, "trunc target"))?;
            prim_call(Prim::TruncToInt { from: *k, to, sat }, recv, lowered_args)
        }
        (Ty::Float(k), "round_f32") => {
            prim_call(Prim::FloatToFloat { from: *k, to: FloatKind::F32 }, recv, lowered_args)
        }
        (Ty::Float(k), "round_f64") => {
            prim_call(Prim::FloatToFloat { from: *k, to: FloatKind::F64 }, recv, lowered_args)
        }
        (Ty::Float(k), "to_bits") => prim_call(Prim::ToBits(*k), recv, lowered_args),
        (Ty::Float(k), "is_nan") => prim_call(Prim::IsNan(*k), recv, lowered_args),
        (Ty::Float(k), "is_finite") => prim_call(Prim::IsFinite(*k), recv, lowered_args),
        (Ty::Float(k), n) => {
            let Some(mf) = MathFn::parse(n) else {
                return Err(unsupported(span, Feature::Methods, &[n, &crate::dump::type_name(&lw.m, &rty)]));
            };
            prim_call(Prim::Math(mf, *k), recv, lowered_args)
        }
        (Ty::Array(..) | Ty::Span(_) | Ty::Buf(_), n) => {
            return lower_seq_method(lw, cx, recv, n, lowered_args, ty, span);
        }
        (Ty::Enum(id), n) => return lower_enum_method(lw, cx, *id, recv, n, lowered_args, ty, span),
        _ => return Err(unsupported(span, Feature::Methods, &[name, &crate::dump::type_name(&lw.m, &rty)])),
    };
    Ok(Expr::new(ty, span, kind))
}

fn lower_seq_method(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    recv: Expr,
    name: &str,
    args: Vec<Expr>,
    ty: Ty,
    span: Span,
) -> R<Expr> {
    let seq_ty = crate::dump::type_name(&lw.m, &recv.ty);
    let borrow = |e: Expr| Arg { mode: Mode::Borrow, expr: e };
    let len_of = |cx: &mut FnCx, recv: Expr| -> R<Expr> {
        match &recv.ty {
            Ty::Array(_, n) => Ok(u32_lit(span, *n)),
            _ => {
                let s = span_of(cx, recv, Mode::Borrow)?;
                Ok(Expr::new(Ty::u32(), span, ExprKind::Prim { prim: Prim::Len, args: vec![borrow(s)] }))
            }
        }
    };
    let kind = match name {
        "len" => return len_of(cx, recv),
        "is_empty" => {
            let l = len_of(cx, recv)?;
            ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(l), rhs: Box::new(u32_lit(span, 0)) }
        }
        "slice" => {
            let s = span_of(cx, recv, Mode::Borrow)?;
            let mut a = vec![borrow(s)];
            a.extend(args.into_iter().map(borrow));
            ExprKind::Prim { prim: Prim::Slice, args: a }
        }
        "get" => {
            let s = span_of(cx, recv, Mode::Borrow)?;
            let mut a = vec![borrow(s)];
            a.extend(args.into_iter().map(borrow));
            ExprKind::Prim { prim: Prim::Get, args: a }
        }
        "fill" | "add_from" | "copy_from" => {
            let s = span_of(cx, recv, Mode::Inout)?;
            let mut a = vec![Arg { mode: Mode::Inout, expr: s }];
            for x in args {
                let x = match name {
                    "fill" => x,
                    _ => span_of(cx, x, Mode::Borrow)?,
                };
                a.push(borrow(x));
            }
            let prim = match name {
                "fill" => Prim::Fill,
                "add_from" => Prim::AddFrom,
                _ => Prim::CopyFrom,
            };
            ExprKind::Prim { prim, args: a }
        }
        _ => return Err(unsupported(span, Feature::Methods, &[name, &seq_ty])),
    };
    Ok(Expr::new(ty, span, kind))
}

#[allow(clippy::too_many_arguments)]
fn lower_enum_method(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    id: TypeId,
    recv: Expr,
    name: &str,
    args: Vec<Expr>,
    ty: Ty,
    span: Span,
) -> R<Expr> {
    let variants = lw.enum_variants(id);
    let is_option = variants.first().is_some_and(|(n, _)| n == "None");
    let (good, bad) = if is_option { (1u32, 0u32) } else { (0, 1) };
    let mut stmts = Vec::new();
    let tmp = materialize(cx, recv, &mut stmts, "__opt");
    let wrap = |stmts: Vec<Stmt>, e: Expr| -> Expr {
        if stmts.is_empty() {
            e
        } else {
            Expr::new(e.ty.clone(), span, ExprKind::Block(Block { stmts, value: Some(Box::new(e)) }))
        }
    };
    let kind = match name {
        "is_some" | "is_ok" | "is_none" | "is_err" => {
            let want = if matches!(name, "is_some" | "is_ok") { good } else { bad };
            return Ok(wrap(stmts, tag_test(lw, &tmp, want)?));
        }
        "unwrap" => {
            let msg = lw.msg(if is_option { "called `unwrap()` on `None`" } else { "called `unwrap()` on `Err`" });
            let good_block = Block { stmts: Vec::new(), value: Some(Box::new(payload(lw, tmp.clone(), good, 0)?)) };
            let bad_block =
                Block { stmts: Vec::new(), value: Some(Box::new(Expr::new(ty.clone(), span, ExprKind::Panic(msg)))) };
            let mut arms = vec![(good, good_block), (bad, bad_block)];
            arms.sort_by_key(|(t, _)| *t);
            ExprKind::Switch { scrutinee: Box::new(tmp), arms, default: None }
        }
        "unwrap_or" => {
            let [d] = args.as_slice() else { return Err(internal(span, "unwrap_or arity")) };
            let good_block = Block { stmts: Vec::new(), value: Some(Box::new(payload(lw, tmp.clone(), good, 0)?)) };
            let bad_block = Block { stmts: Vec::new(), value: Some(Box::new(d.clone())) };
            let mut arms = vec![(good, good_block), (bad, bad_block)];
            arms.sort_by_key(|(t, _)| *t);
            ExprKind::Switch { scrutinee: Box::new(tmp), arms, default: None }
        }
        _ => return Err(unsupported(span, Feature::Methods, &[name, &crate::dump::type_name(&lw.m, &Ty::Enum(id))])),
    };
    Ok(wrap(stmts, Expr::new(ty, span, kind)))
}
