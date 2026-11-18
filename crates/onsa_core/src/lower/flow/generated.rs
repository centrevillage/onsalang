//! The generated functions of a flow: the small helpers and the builder of
//! one generated function ([`Gen`]).

use super::*;

// ---------------------------------------------------------------- small helpers

/// The field of `state` that holds `of`, at the place the plan gives it
/// (S-06; the Core struct has the plan's fields in their order). One the
/// plan has not is an internal error.
pub(super) fn sfield(lw: &Lowerer, info: &FlowInfo, state: &Expr, of: FieldOf, span: Span) -> R<Expr> {
    let at = info.field_at(of).ok_or_else(|| internal(span, format!("no state field of {of:?}")))?;
    field(lw, state.clone(), at)
}

/// Parameters of a generated member as declared by sema (§11.6), with
/// those Core keeps ([`implicit_params`]).
pub(super) fn member_params(lw: &mut Lowerer, fd: &FlowDef, f: FlowFn, span: Span) -> R<Vec<(String, Mode, Ty)>> {
    let d = generated_fn(lw.a, fd, f).ok_or_else(|| internal(span, format!("flow without {f:?}")))?;
    let def = lw.a.def(d).clone();
    let DefKind::Fn(f) = &def.kind else { return Err(internal(span, "member is not a function")) };
    let mut out = Vec::new();
    for p in &f.params {
        out.push((p.name.clone(), core_mode(p.mode), lw.core_ty(p.ty, &[], p.span)?));
    }
    for (at, name, ty) in implicit_params(lw, d, span)? {
        out.insert(at, (name.to_string(), Mode::Borrow, Ty::Struct(ty)));
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

/// Arguments of an instance call for the callee inputs of the stage of
/// `phase`, in their places, lowered in the current function: of the input
/// value types, which are no views (§11.3), so with no conversion.
pub(super) fn instance_args(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    callee: DefId,
    args: &[ExprId],
    phase: Phase,
    span: Span,
) -> R<Vec<Expr>> {
    let a = lw.a;
    let (Some(info), Some(fd)) = (a.flows.get(&callee), a.def(callee).as_flow()) else {
        return Err(internal(span, "an instance of no checked flow"));
    };
    let mut out = Vec::new();
    for (arg, input) in args.iter().zip(inputs(info, fd, span)?) {
        if input.phase != phase {
            continue;
        }
        let want = lw.core_ty(input.decl.ty, &[], input.decl.span)?;
        let e = lower_expr(lw, cx, *arg)?;
        out.push(of_type(e, &want)?);
    }
    Ok(out)
}

/// The length of the ring of a `delay~` (`N`) or a `vdelay~` (`MAX + 1`,
/// §11.4): the one place of it. Of another node, an internal error.
pub(super) fn ring_len(kind: &PlanKind, span: Span) -> R<u32> {
    match kind {
        PlanKind::Delay { n, .. } => Ok(*n),
        PlanKind::Vdelay { max, .. } => Ok(max + 1),
        _ => Err(internal(span, "the ring of no delay")),
    }
}

/// The replicas of a `par~` (§11.5): its variable and its range as the
/// plan gives them, read in this one place.
pub(super) struct Replicas {
    var: onsa_sema::LocalId,
    from: u32,
    to: u32,
}

/// The replicas of the `par~` of `kind`; of another node, an internal error.
pub(super) fn replicas(kind: &PlanKind, span: Span) -> R<Replicas> {
    match kind {
        &PlanKind::Par { var, from, to, .. } => Ok(Replicas { var, from, to }),
        _ => Err(internal(span, "the replicas of no `par~`")),
    }
}

impl Replicas {
    /// Their number: the length of the array of their states.
    pub(super) fn count(&self) -> u32 {
        self.to - self.from
    }

    /// The index of the replica of the iteration (`var - from`).
    pub(super) fn index(&self, cx: &FnCx, span: Span) -> Expr {
        let v = local_expr(cx, LocalId(self.var.0), span);
        if self.from == 0 { v } else { checked_binary(BinOp::Sub, v, u32_lit(span, self.from)) }
    }

    /// The loop over them, of the variable of the `par~`, with the body `stmts`.
    pub(super) fn each(&self, span: Span, stmts: Vec<Stmt>) -> Stmt {
        let (from, to) = (u32_lit(span, self.from), u32_lit(span, self.to));
        stmt(span, StmtKind::ForRange(LocalId(self.var.0), from, to, Block { stmts, value: None }))
    }
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
            sample_rate: lit(Ty::Float(FloatKind::F32), shape.span, Lit::F32(0.0)),
            sample_rate_calls: info.sample_rate_calls.iter().copied().collect(),
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

    /// Parameters as declared by sema for a member (§11.6), as expressions
    /// in their order.
    pub(super) fn member_params(&mut self, lw: &mut Lowerer, shape: &FlowShape, f: FlowFn) -> R<Vec<Expr>> {
        let ps = member_params(lw, &shape.flow, f, self.span)?;
        Ok(ps.into_iter().map(|(n, mode, ty)| self.param(&n, mode, ty)).collect())
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

    /// The inputs of the stage of the function, read from `from` (`cfg` of
    /// `init`, `p` of `ctl`) at their places; those the state keeps are
    /// also stored.
    pub(super) fn inputs_from(
        &mut self,
        lw: &mut Lowerer,
        shape: &FlowShape,
        info: &FlowInfo,
        from: &Expr,
        state: &Expr,
    ) -> R<()> {
        let phase = self.flow().phase;
        for i in shape.inputs.iter().filter(|i| i.phase == phase) {
            let v = field(lw, from.clone(), i.at)?;
            self.flow().local_override.insert(i.local.0, v.clone());
            if let Some(of) = info.kept_field(i.local) {
                let f = sfield(lw, info, state, of, i.decl.span)?;
                assign(&mut self.stmts, &f, v)?;
            }
        }
        Ok(())
    }

    /// Overrides for the locals this phase reads from the state, and for
    /// `sample_rate()` (S-05, [`FlowInfo::from_state`]).
    pub(super) fn state_overrides(&mut self, lw: &mut Lowerer, info: &FlowInfo, state: &Expr) -> R<()> {
        let stage = self.flow().phase.stage();
        for of in info.fields.iter().map(|f| f.of) {
            if let FieldOf::Input(l) | FieldOf::Let(l) = of
                && info.from_state(Kept::Local(l), stage)
            {
                let f = sfield(lw, info, state, of, self.span)?;
                self.flow().local_override.insert(l.0, f);
            }
        }
        if info.from_state(Kept::SampleRate, stage) {
            let f = sfield(lw, info, state, FieldOf::SampleRate, self.span)?;
            self.flow().sample_rate = f;
        }
        Ok(())
    }

    /// The `let`s of a constant this phase reads, recomputed as locals (§11.3).
    pub(super) fn const_lets(&mut self, lw: &mut Lowerer, info: &FlowInfo) -> R<()> {
        let stage = self.flow().phase.stage();
        for l in info.consts_at(stage) {
            let v = lower_expr(lw, &mut self.cx, l.init)?;
            bind_irrefutable(lw, &mut self.cx, l.pat, v, &mut self.stmts)?;
        }
        Ok(())
    }

    /// The `let`s of the stage of this phase in order; those the state keeps
    /// are also stored.
    pub(super) fn rate_lets(&mut self, lw: &mut Lowerer, info: &FlowInfo, state: &Expr) -> R<()> {
        let stage = self.flow().phase.stage();
        for l in info.lets_at(stage) {
            let v = lower_expr(lw, &mut self.cx, l.init)?;
            bind_irrefutable(lw, &mut self.cx, l.pat, v, &mut self.stmts)?;
            for &loc in &l.locals {
                if let Some(of) = info.kept_field(loc) {
                    let f = sfield(lw, info, state, of, l.span)?;
                    let v = local_expr(&self.cx, LocalId(loc.0), l.span);
                    assign(&mut self.stmts, &f, v)?;
                }
            }
        }
        Ok(())
    }

    pub(super) fn finish(self, lw: &mut Lowerer, fid: FnId, ret: Ty, rt: bool, value: Option<Expr>) {
        let body = Block { stmts: self.stmts, value: value.map(Box::new) };
        lw.fill_fn(fid, self.params, ret, rt, self.cx.locals, Some(body));
    }
}
