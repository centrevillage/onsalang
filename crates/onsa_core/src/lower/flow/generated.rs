//! The generated functions of a flow: the small helpers and the builder of
//! one generated function ([`Gen`]).

use super::*;

// ---------------------------------------------------------------- small helpers

/// `state.<name>` (dotted node field names are plain field names).
pub(super) fn sfield(lw: &Lowerer, state: &Expr, name: &str, span: Span) -> R<Expr> {
    field_by_name(lw, state.clone(), name, span)
}

/// Parameters of a generated member as declared by sema (§11.6).
pub(super) fn member_params(lw: &mut Lowerer, fd: &FlowDef, name: &str, span: Span) -> R<Vec<(String, Mode, Ty)>> {
    let d = member(fd, name).ok_or_else(|| internal(span, format!("flow without `{name}`")))?;
    let def = lw.a.def(d).clone();
    let DefKind::Fn(f) = &def.kind else { return Err(internal(span, "member is not a function")) };
    let mut out = Vec::new();
    for p in &f.params {
        out.push((p.name.clone(), core_mode(p.mode), lw.core_ty(p.ty, &[], p.span)?));
    }
    Ok(out)
}

/// A node's `init` value: a constant literal, or the `Init`-rate expression
/// (lowered in `init`; `reset` reads the stored copy).
pub(super) fn init_value(lw: &mut Lowerer, cx: &mut FnCx, init: &InitArg, ty: &Ty, span: Span) -> R<Expr> {
    match init {
        InitArg::Const(v) => lw.const_value_expr(v, ty, span),
        InitArg::Init(e) => lower_expr(lw, cx, *e),
    }
}

fn sub_inputs(lw: &Lowerer, callee: DefId) -> Vec<onsa_sema::def::FlowInput> {
    lw.a.def(callee).as_flow().map(|f| f.inputs.clone()).unwrap_or_default()
}

/// Arguments of an instance call for the callee inputs of `rate`, lowered
/// in the current function and coerced to the input value types.
pub(super) fn instance_args(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    callee: DefId,
    args: &[ExprId],
    rate: Rate,
) -> R<Vec<Expr>> {
    let inputs = sub_inputs(lw, callee);
    let mut out = Vec::new();
    for (arg, input) in args.iter().zip(&inputs) {
        if input.rate != rate {
            continue;
        }
        let want = lw.core_ty(input.ty, &[], input.span)?;
        let e = lower_expr(lw, cx, *arg)?;
        out.push(coerce(lw, cx, e, &want, Mode::Borrow)?);
    }
    Ok(out)
}

/// The replica index of a `par` loop variable (`var - from`).
pub(super) fn replica_index(cx: &FnCx, var: onsa_sema::LocalId, from: u32, span: Span) -> Expr {
    let v = local_expr(cx, LocalId(var.0), span);
    if from == 0 { v } else { checked_binary(BinOp::Sub, v, u32_lit(span, from)) }
}

// ---------------------------------------------------------------- generated functions

/// A generated function under construction.
pub(super) struct Gen<'b> {
    pub(super) cx: FnCx<'b>,
    params: Vec<Param>,
    pub(super) stmts: Vec<Stmt>,
    pub(super) span: Span,
}

impl<'b> Gen<'b> {
    pub(super) fn new(
        lw: &mut Lowerer<'b>,
        shape: &FlowShape,
        info: &'b FlowInfo,
        phase: Phase,
        ret: Ty,
    ) -> R<Gen<'b>> {
        let mut cx = FnCx::new(lw, shape.def, Vec::new(), &info.body, ret)?;
        cx.flow = Some(FlowLowerCx {
            local_override: HashMap::new(),
            expr_override: HashMap::new(),
            info,
            phase,
            node_by_expr: flat_nodes(&info.nodes),
            sample_rate: lit(Ty::Float(FloatKind::F32), shape.span, Lit::F32(0.0)),
            scopes: Vec::new(),
        });
        Ok(Gen { cx, params: Vec::new(), stmts: Vec::new(), span: shape.span })
    }

    pub(super) fn flow(&mut self) -> &mut FlowLowerCx<'b> {
        self.cx.flow.as_mut().expect("flow context")
    }

    pub(super) fn param(&mut self, name: &str, mode: Mode, ty: Ty) -> Expr {
        let l = self.cx.temp(name, ty.clone());
        self.params.push(Param { local: l, mode, ty });
        local_expr(&self.cx, l, self.span)
    }

    /// Bind a sema local as a parameter (its Core local already exists).
    pub(super) fn param_local(&mut self, l: LocalId, mode: Mode) {
        let ty = self.cx.locals[l.0 as usize].ty.clone();
        self.params.push(Param { local: l, mode, ty });
    }

    /// Parameters as declared by sema for a member (§11.6), as expressions by name.
    pub(super) fn member_params(
        &mut self,
        lw: &mut Lowerer,
        shape: &FlowShape,
        name: &str,
    ) -> R<HashMap<String, Expr>> {
        let mut out = HashMap::new();
        for (n, mode, ty) in member_params(lw, &shape.flow, name, self.span)? {
            let e = self.param(&n, mode, ty);
            out.insert(n, e);
        }
        Ok(out)
    }

    pub(super) fn temp(&mut self, name: &str, ty: Ty) -> Expr {
        let l = self.cx.temp(name, ty);
        local_expr(&self.cx, l, self.span)
    }

    pub(super) fn let_(&mut self, name: &str, value: Expr) -> Expr {
        let l = self.cx.temp(name, value.ty.clone());
        self.stmts.push(stmt(self.span, StmtKind::Let(l, value)));
        local_expr(&self.cx, l, self.span)
    }

    /// Overrides for locals that live in the state and are read in this
    /// phase at a rate above their own, and for `sample_rate()`.
    pub(super) fn state_overrides(
        &mut self,
        lw: &mut Lowerer,
        shape: &FlowShape,
        info: &FlowInfo,
        state: &Expr,
    ) -> R<()> {
        let phase = self.flow().phase;
        for (&l, name) in &shape.state_locals {
            let own = info.local_rates.get(&onsa_sema::LocalId(l)).copied().unwrap_or(FlowRate::Sig);
            if Phase::of(own) != phase {
                let f = sfield(lw, state, name, self.span)?;
                self.flow().local_override.insert(l, f);
            }
        }
        if shape.sample_rate_field && phase != Phase::Init {
            let f = sfield(lw, state, "sample_rate", self.span)?;
            self.flow().sample_rate = f;
        }
        Ok(())
    }

    /// `Const`-rate `let`s read in this phase, recomputed as locals.
    pub(super) fn const_lets(&mut self, lw: &mut Lowerer, shape: &FlowShape, info: &FlowInfo) -> R<()> {
        let phase = self.flow().phase;
        let Some(ks) = shape.const_lets.get(&phase) else { return Ok(()) };
        for &k in ks {
            let l = &info.lets[k];
            let v = lower_expr(lw, &mut self.cx, l.init)?;
            bind_irrefutable(lw, &mut self.cx, l.pat, v, &mut self.stmts)?;
        }
        Ok(())
    }

    /// The `let`s of `rate` in order; state ones are also stored.
    pub(super) fn rate_lets(
        &mut self,
        lw: &mut Lowerer,
        shape: &FlowShape,
        info: &FlowInfo,
        rate: FlowRate,
        state: &Expr,
    ) -> R<()> {
        for l in info.lets.iter().filter(|l| l.rate == rate) {
            let v = lower_expr(lw, &mut self.cx, l.init)?;
            bind_irrefutable(lw, &mut self.cx, l.pat, v, &mut self.stmts)?;
            for loc in &l.locals {
                if let Some(name) = shape.state_locals.get(&loc.0) {
                    let f = sfield(lw, state, name, l.span)?;
                    let v = local_expr(&self.cx, LocalId(loc.0), l.span);
                    assign(&mut self.stmts, &f, v)?;
                }
            }
        }
        Ok(())
    }

    pub(super) fn finish(self, lw: &mut Lowerer, fid: FnId, ret: Ty, rt: bool, value: Option<Expr>) {
        let fd = &mut lw.m.fns[fid.0 as usize];
        fd.params = self.params;
        fd.sret = ret.is_aggregate();
        fd.ret = ret;
        fd.rt = rt;
        fd.locals = self.cx.locals;
        fd.body = Some(Block { stmts: self.stmts, value: value.map(Box::new) });
    }
}
