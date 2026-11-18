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
/// §11.4): the one place of it. A length past `U32` (a `MAX` of `U32`'s
/// largest value) is an E0200 (R-501). Of another node, an internal error.
pub(super) fn ring_len(kind: &PlanKind, span: Span) -> R<u32> {
    match kind {
        PlanKind::Delay { n, .. } => Ok(*n),
        PlanKind::Vdelay { max, .. } => max.checked_add(1).ok_or_else(|| unsupported(span, Feature::HugeRing, &[])),
        _ => Err(internal(span, "the ring of no delay")),
    }
}

/// The replicas of a `par~` (§11.5): its variable, its first value and
/// their number as the plan gives them, read in this one place. The loop
/// over them is of the variable, `from..<from + count`, when that end fits
/// in `U32`; past it (a last of `U32`'s maximum, S-257) it counts them with
/// a local `k` of its own from 0 and binds the variable to `from + k`, and
/// no end past the last is made.
pub(super) struct Replicas {
    var: onsa_sema::LocalId,
    from: u32,
    count: u32,
    /// The counter of the loop when `from + count` is past `U32`.
    k: Option<LocalId>,
}

/// The replicas of the `par~` of `kind`, with the locals of a loop over
/// them in `cx`; of another node, an internal error.
pub(super) fn replica_loop(cx: &mut FnCx, kind: &PlanKind, span: Span) -> R<Replicas> {
    let &PlanKind::Par { var, from, count, .. } = kind else {
        return Err(internal(span, "the replicas of no `par~`"));
    };
    let k = from.checked_add(count).is_none().then(|| cx.temp("k", Ty::u32()));
    Ok(Replicas { var, from, count, k })
}

impl Replicas {
    /// The index of the replica of the iteration (`var - from`, or `k`).
    pub(super) fn index(&self, cx: &FnCx, span: Span) -> Expr {
        if let Some(k) = self.k {
            return local_expr(cx, k, span);
        }
        let v = local_expr(cx, LocalId(self.var.0), span);
        if self.from == 0 { v } else { checked_binary(BinOp::Sub, v, u32_lit(span, self.from)) }
    }

    /// The loop over them, of the variable of the `par~`, with the body `stmts`.
    pub(super) fn each(&self, span: Span, mut stmts: Vec<Stmt>) -> Stmt {
        let var = LocalId(self.var.0);
        // With no `k`, `from + count` fits in `U32` ([`replica_loop`], the one maker).
        let Some(k) = self.k else {
            let (from, to) = (u32_lit(span, self.from), u32_lit(span, self.from + self.count));
            return stmt(span, StmtKind::ForRange(var, from, to, Block { stmts, value: None }));
        };
        let at = checked_binary(BinOp::Add, u32_lit(span, self.from), Expr::new(Ty::u32(), span, ExprKind::Local(k)));
        stmts.insert(0, stmt(span, StmtKind::Let(var, at)));
        let (zero, count) = (u32_lit(span, 0), u32_lit(span, self.count));
        stmt(span, StmtKind::ForRange(k, zero, count, Block { stmts, value: None }))
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
