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

/// A node's `init` value: a constant literal, the default of its type
/// (§11.4, made again at `reset`: it has no effect), or what `of` gives of
/// the `Init`-rate expression (lowered in `init`; `reset` reads the stored
/// copy).
pub(super) fn init_value(
    lw: &mut Lowerer,
    init: &InitArg,
    ty: &Ty,
    span: Span,
    of: impl FnOnce(&mut Lowerer, ExprId) -> R<Expr>,
) -> R<Expr> {
    match init {
        InitArg::Const(v) => lw.const_value_expr(v, ty, span),
        InitArg::Default => crate::lower::derived::default_value(lw, ty, span),
        InitArg::Init(e) => of(lw, *e),
    }
}

/// The Core type of a value of the clock `c` and the value type `ty` in a
/// flow body: `[ty; N]` of a burst of the caller (§11.9,
/// [`Clock::burst_len`]), else `ty`. The one place of it: the locals, the
/// expressions and the arguments of a port of a burst.
pub(crate) fn burst_ty(c: Option<Clock>, ty: Ty) -> Ty {
    match c.and_then(Clock::burst_len) {
        Some(n) => Ty::Array(Box::new(ty), n),
        None => ty,
    }
}

/// The value `v` of the argument `arg` of a port at the clock `port` in
/// the frame of the call: of a port of a burst and an argument at a clock
/// of none (of `block`, `init`, a constant), its N copies, each element the
/// value read (§11.9, S-1214 (3)); else `v`. The one place of it: the
/// inputs of a head and the rings of a chain.
pub(super) fn spread(cx: &FnCx, arg: ExprId, port: Clock, v: Expr) -> Expr {
    let clocks = &cx.flow.as_ref().expect("flow context").info.clocks;
    match (port.burst_len(), clocks.exprs.get(&arg).copied().and_then(Clock::burst_len)) {
        (Some(n), None) => {
            Expr::new(burst_ty(Some(port), v.ty.clone()), v.span, ExprKind::Repeat { elem: Box::new(v), n })
        }
        _ => v,
    }
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
/// no end past the last is made. Of one the function is of a replica of
/// ([`StageCx::pinned`]), that replica alone, with no loop.
pub(super) struct Replicas {
    var: onsa_sema::LocalId,
    from: u32,
    count: u32,
    /// The counter of the loop when `from + count` is past `U32`.
    k: Option<LocalId>,
    pinned: bool,
}

/// The variable of the `par~` `id`, its first value and the number of its replicas.
pub(super) fn range(info: &FlowInfo, id: NodeId, span: Span) -> R<(onsa_sema::LocalId, u32, u32)> {
    match info.node(id).kind {
        PlanKind::Par { var, from, count, .. } => Ok((var, from, count)),
        _ => Err(internal(span, "the replicas of no `par~`")),
    }
}

/// The replicas of the `par~` `id`, with the locals of a loop over them in
/// `cx`, and the state of the one of the iteration in `state` (or it, of none).
pub(super) fn replicas(lw: &Lowerer, cx: &mut FnCx, id: NodeId, state: &Expr, span: Span) -> R<(Replicas, Expr)> {
    let f = cx.flow.as_ref().expect("flow context");
    let (info, pinned) = (f.info, f.now.pinned.contains(&id));
    let (var, from, count) = range(info, id, span)?;
    let k = (!pinned && from.checked_add(count).is_none()).then(|| cx.temp("k", Ty::u32()));
    let r = Replicas { var, from, count, k, pinned };
    let own = FieldOf::Node(id, Part::Own);
    let elem = match info.field_at(own) {
        Some(_) => index(sfield(lw, info, state, own, span)?, r.index(cx, span))?,
        None => state.clone(),
    };
    Ok((r, elem))
}

/// The place of a replica in a local `name` at the head of the function,
/// `Zeroed` in `out`, of an element `ty` for each of the replicas of `pars`
/// (the outermost first) that is not pinned.
pub(super) fn replicas_place(
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    name: &str,
    ty: Ty,
    pars: &[NodeId],
    span: Span,
) -> R<Expr> {
    let f = cx.flow.as_ref().expect("flow context");
    let pars = pars.iter().filter(|p| !f.now.pinned.contains(p));
    let each = pars.map(|&p| range(f.info, p, span)).collect::<R<Vec<_>>>()?;
    let ty = each.iter().rev().fold(ty, |t, &(_, _, n)| Ty::Array(Box::new(t), n));
    let l = cx.temp(name, ty.clone());
    out.push(stmt(span, StmtKind::Let(l, Expr::new(ty, span, ExprKind::Zeroed))));
    let mut place = local_expr(cx, l, span);
    for (var, from, _) in each {
        place = index(place, var_index(cx, var, from, span))?;
    }
    Ok(place)
}

/// The index of the replica of the variable `var` of a `par~` from `from`
/// (`var - from`): in a loop over them ([`Replicas::each`]) or pinned.
fn var_index(cx: &FnCx, var: onsa_sema::LocalId, from: u32, span: Span) -> Expr {
    let v = local_expr(cx, LocalId(var.0), span);
    if from == 0 { v } else { checked_binary(BinOp::Sub, v, u32_lit(span, from)) }
}

impl Replicas {
    /// The index of the replica of the iteration (`var - from`, or `k`).
    pub(super) fn index(&self, cx: &FnCx, span: Span) -> Expr {
        match self.k {
            Some(k) => local_expr(cx, k, span),
            None => var_index(cx, self.var, self.from, span),
        }
    }

    /// The body `stmts` in a loop over them, of the variable of the `par~`,
    /// into `out`; of the one of the function, as it is.
    pub(super) fn each(&self, cx: &FnCx, out: &mut Vec<Stmt>, span: Span, mut stmts: Vec<Stmt>) {
        if self.pinned {
            return out.append(&mut stmts);
        }
        let var = LocalId(self.var.0);
        // With no `k`, `from + count` fits in `U32` ([`replicas`], the one maker).
        let Some(k) = self.k else {
            let (from, to) = (u32_lit(span, self.from), u32_lit(span, self.from + self.count));
            return out.push(stmt(span, StmtKind::ForRange(var, from, to, Block { stmts, value: None })));
        };
        let at = checked_binary(BinOp::Add, u32_lit(span, self.from), self.index(cx, span));
        stmts.insert(0, stmt(span, StmtKind::Let(var, at)));
        let (zero, count) = (u32_lit(span, 0), u32_lit(span, self.count));
        out.push(stmt(span, StmtKind::ForRange(k, zero, count, Block { stmts, value: None })));
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
        stage: ClockStage,
        ret: Ty,
    ) -> R<Gen<'b>> {
        Gen::of(lw, (shape.def, shape.span), info, stage, ret)
    }

    /// [`Gen::new`] of the flow `def` declared at `span`, with no shape.
    pub(super) fn of(
        lw: &mut Lowerer<'b>,
        (def, span): (DefId, Span),
        info: &'b FlowInfo,
        stage: ClockStage,
        ret: Ty,
    ) -> R<Gen<'b>> {
        let mut cx = FnCx::new(lw, def, Vec::new(), &info.body, ret)?;
        for (l, &c) in &info.clocks.locals {
            let local = cx.locals.get_mut(l.0 as usize).ok_or_else(|| internal(span, "a clock of no local"))?;
            local.ty = burst_ty(Some(c), local.ty.clone());
        }
        cx.flow = Some(FlowLowerCx {
            info,
            sample_rate_calls: info.sample_rate_calls.iter().copied().collect(),
            sample_tick_calls: info.sample_tick_calls.iter().copied().collect(),
            events: Vec::new(),
            now: StageCx {
                stage,
                local_override: HashMap::new(),
                expr_override: HashMap::new(),
                done: HashMap::new(),
                saving: false,
                guards: None,
                heads: Vec::new(),
                sample_rate: lit(Ty::Float(FloatKind::F32), span, Lit::F32(0.0)),
                source: None,
                pinned: Vec::new(),
                gave: None,
                time: Vec::new(),
                scopes: Vec::new(),
            },
        });
        Ok(Gen { cx, params: Vec::new(), stmts: Vec::new(), span })
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
        let stage = self.flow().now.stage;
        for i in shape.inputs.iter().filter(|i| i.stage == stage) {
            let v = field(lw, from.clone(), i.at)?;
            self.flow().now.local_override.insert(i.local.0, v.clone());
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
        let stage = self.flow().now.stage;
        for of in info.fields.iter().map(|f| f.of) {
            if let FieldOf::Input(l) | FieldOf::Let(l) = of
                && info.from_state(Kept::Local(l), stage)
            {
                let f = sfield(lw, info, state, of, self.span)?;
                self.flow().now.local_override.insert(l.0, f);
            }
        }
        if info.from_state(Kept::SampleRate, stage) {
            let f = sfield(lw, info, state, FieldOf::SampleRate, self.span)?;
            self.flow().now.sample_rate = f;
        }
        Ok(())
    }

    /// The place of each binding of an arm of `match~` this phase reads
    /// (§11.5, S-1131), a local of the function, which a read of the
    /// binding reads and [`super::branches::choose`] writes: of one the end
    /// of `tick` reads (`FlowInfo::store_bindings`), an element for each
    /// replica of the `par~`s around it.
    pub(super) fn slots(&mut self, info: &FlowInfo) -> R<()> {
        let (stage, span) = (self.flow().now.stage, self.span);
        for t in info.tilde_matches.values() {
            let here = |b: &&onsa_sema::LocalId| {
                info.bound_at.get(b).is_some_and(|r| r.iter().any(|&s| info.run_stage(s) == stage))
            };
            for &b in t.arms.iter().flatten().filter(here) {
                let pars = if info.store_bindings.contains(&b) { info.around(t.owner) } else { Vec::new() };
                let local = &self.cx.locals[b.0 as usize];
                let (name, ty) = (format!("__bind.{}", local.name), local.ty.clone());
                let place = replicas_place(&mut self.cx, &mut self.stmts, &name, ty, &pars, span)?;
                self.flow().now.local_override.insert(b.0, place);
            }
        }
        Ok(())
    }

    /// The `let`s of a constant this phase reads, recomputed as locals (§11.3).
    pub(super) fn const_lets(&mut self, lw: &mut Lowerer, info: &FlowInfo) -> R<()> {
        let stage = self.flow().now.stage;
        for l in info.consts_at(stage) {
            let v = lower_expr(lw, &mut self.cx, l.init)?;
            bind_irrefutable(lw, &mut self.cx, l.pat, v, &mut self.stmts)?;
        }
        Ok(())
    }

    /// The `let`s of the stage of this phase in order, those the state
    /// keeps also stored, and the work of this stage in the others and in
    /// the output last, at their places (§11.3, S-1233; [`super::hoist::work`]):
    /// in each that holds some (`FlowInfo::work_in`).
    pub(super) fn stage_lets(&mut self, lw: &mut Lowerer, info: &FlowInfo, state: &Expr) -> R<()> {
        let stage = self.flow().now.stage;
        for (k, l) in info.lets.iter().enumerate() {
            let Some(at) = l.stage.stage() else { continue };
            if info.run_stage(at) != stage {
                if info.work_in(k, stage) {
                    super::hoist::work(lw, &mut self.cx, info, l.init, stage, state, &mut self.stmts)?;
                }
                continue;
            }
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
        if let Some(out) = info.output.filter(|_| info.work_in(info.lets.len(), stage)) {
            super::hoist::work(lw, &mut self.cx, info, out, stage, state, &mut self.stmts)?;
        }
        Ok(())
    }

    pub(super) fn finish(self, lw: &mut Lowerer, fid: FnId, ret: Ty, rt: bool, value: Option<Expr>) {
        let body = Block { stmts: self.stmts, value: value.map(Box::new) };
        lw.fill_fn(fid, self.params, ret, rt, self.cx.locals, Some(body));
    }
}
