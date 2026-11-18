//! The rate pass (§11.3): after type checking, the rate of every
//! expression, the flow rules and the stateful nodes.

use super::nodes::NodeBuilder;
use super::*;

// ---------------------------------------------------------------- rate pass

/// After type checking: assign rates, check the flow rules, collect nodes.
pub(crate) fn finish_flow(a: &mut Analysis, module: &Module, id: DefId, body: BodyInfo, fcx: FlowCx) {
    let _flow = onsa_diag::timing::phase(onsa_diag::timing::Phase::Flow);
    let mut info = FlowInfo {
        inputs: fcx.inputs.iter().map(|(l, _)| *l).collect(),
        sample_rate_calls: fcx.sample_rate_calls.clone(),
        output: fcx.output,
        complete: false,
        ..Default::default()
    };
    if !body.complete {
        info.body = body;
        a.flows.insert(id, info);
        return;
    }
    let mut r = Rater {
        a,
        ast: &module.parsed.ast,
        text: &module.text,
        body: &body,
        fcx: &fcx,
        final_pass: false,
        rates: HashMap::default(),
        local_rates: HashMap::default(),
        let_rates: vec![FlowRate::Const; fcx.pending.len()],
        lets: Vec::new(),
        diag: None,
        inout_call: None,
        nodes: NodeBuilder::new(&fcx.pending),
        sample_rate_at: None,
        read_at: HashMap::default(),
        call_of_expr: HashMap::default(),
        branch: 0,
    };
    for (i, c) in fcx.calls.iter().enumerate() {
        r.call_of_expr.insert(c.expr, i);
    }
    // Fixpoint on the `let` rates: a look-back (`prev~(^y)` before `let y`)
    // reads a rate that is only known after its `let` is rated. Rates only go
    // up, and the lattice has four levels, so this converges quickly.
    for _ in 0..6 {
        r.pass();
        let mut changed = false;
        for (i, l) in r.lets.iter().enumerate() {
            changed |= r.let_rates[i] != l.clock;
            r.let_rates[i] = l.clock;
        }
        if !changed {
            break;
        }
    }
    r.final_pass = true;
    r.pass();
    if r.diag.is_none() {
        r.mark_all();
    }
    // The stage of the modes comes after the flow checks (§18.1).
    let diag = r.diag.take().or(r.inout_call.take());
    info.complete = diag.is_none();
    // The rates of the pass, as the clocks and the stages of the tables.
    let exprs = r.rates.into_iter().map(|(e, r)| (e, r.to_clock())).collect();
    let locals = r.local_rates.into_iter().map(|(l, r)| (l, r.to_clock())).collect();
    info.clocks = ClockInfo { exprs, locals };
    info.lets = r.lets.into_iter().map(|l| l.map_clock(FlowRate::to_clock)).collect();
    (info.nodes, info.node_of_expr) = r.nodes.finish();
    info.sample_rate_at = r.sample_rate_at.map(FlowRate::read_stage);
    let stages = |rs: BTreeSet<FlowRate>| rs.into_iter().map(FlowRate::read_stage).collect();
    info.read_at = r.read_at.into_iter().map(|(l, rs)| (l, stages(rs))).collect();
    info.body = body;
    if let Some(d) = diag {
        a.diagnostics.push(d);
    }
    a.flows.insert(id, info);
}

pub(super) struct RStop;
type RR<T> = Result<T, RStop>;

pub(super) struct Rater<'a> {
    pub(super) a: &'a mut Analysis,
    pub(super) ast: &'a onsa_syntax::ast::Ast,
    pub(super) text: &'a str,
    pub(super) body: &'a BodyInfo,
    pub(super) fcx: &'a FlowCx,
    /// Diagnostics and nodes are produced in the final pass only.
    pub(super) final_pass: bool,
    pub(super) rates: HashMap<ExprId, FlowRate>,
    pub(super) local_rates: HashMap<LocalId, FlowRate>,
    /// Rates of the `let`s from the previous pass (read by look-backs).
    pub(super) let_rates: Vec<FlowRate>,
    pub(super) lets: Vec<FlowLet<FlowRate>>,
    pub(super) diag: Option<Diagnostic>,
    /// The first call of an `inout self` method (E0713, §5.2), reported
    /// when the flow checks find no error: the modes stage, which reads no
    /// flow body, would come after them (§18.1).
    pub(super) inout_call: Option<Diagnostic>,
    pub(super) nodes: NodeBuilder,
    pub(super) sample_rate_at: Option<FlowRate>,
    /// The rates each local is read at (the state marking).
    pub(super) read_at: HashMap<LocalId, BTreeSet<FlowRate>>,
    pub(super) call_of_expr: HashMap<ExprId, usize>,
    /// Nonzero inside a branch, a guard or the right side of `&&` / `||` (K-08).
    pub(super) branch: u32,
}

impl<'a> Rater<'a> {
    pub(super) fn src(&self, span: Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    pub(super) fn fail(&mut self, d: Diagnostic) -> RStop {
        if self.final_pass && self.diag.is_none() {
            self.diag = Some(d);
        }
        RStop
    }

    pub(super) fn err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> RStop {
        let found = self.src(span);
        self.fail(Diagnostic::new(Stage::Flow, code, span, msg).with_found(found))
    }

    pub(super) fn expr(&self, e: ExprId) -> &'a onsa_syntax::ast::Expr {
        self.ast.expr(e)
    }

    pub(super) fn display(&self, t: TyId) -> String {
        self.a.display_type(t)
    }

    fn pass(&mut self) {
        self.rates.clear();
        self.local_rates.clear();
        self.lets.clear();
        self.nodes.reset();
        self.sample_rate_at = None;
        self.branch = 0;
        for &(l, r) in &self.fcx.inputs {
            self.local_rates.insert(l, r);
        }
        let _ = self.pass_inner();
    }

    fn pass_inner(&mut self) -> RR<()> {
        for k in 0..self.fcx.pending.len() {
            let p = self.fcx.pending[k].clone();
            let rate = self.rate(p.init)?;
            // §11.3: the value type of a signal must be Copy.
            let ty = self.body.expr_types.get(&p.init).copied().unwrap_or_else(|| self.a.types.error());
            if self.final_pass
                && let Some(k) = crate::kind::facts_of(self.a, ty, &[]).not_copy()
            {
                let shown = self.display(ty);
                return Err(self.err(
                    Code::E0810,
                    p.span,
                    format!("the value type of a signal must be Copy; `{shown}` is {k} (§11.3)"),
                ));
            }
            for &l in &p.locals {
                self.local_rates.insert(l, rate);
            }
            self.lets.push(FlowLet {
                pat: p.pat,
                locals: p.locals.clone(),
                name: p.name.clone(),
                ty,
                clock: rate,
                init: p.init,
                span: p.span,
                state: false,
            });
        }
        for &(span, call) in &self.fcx.float_checks {
            let t = self.body.expr_types.get(&call).map(|&t| self.a.types.get(t).clone()).unwrap_or(Ty::Error);
            if self.final_pass && !matches!(t, Ty::Float(_) | Ty::Error) {
                return Err(self.err(
                    Code::E0401,
                    span,
                    "`vdelay~` interpolates and needs a float signal (`F32` / `F64`, §11.4)",
                ));
            }
        }
        if let Some(out) = self.fcx.output {
            self.rate(out)?;
        }
        Ok(())
    }

    fn set(&mut self, e: ExprId, r: FlowRate) -> RR<FlowRate> {
        self.rates.insert(e, r);
        Ok(r)
    }

    fn rate_of_local(&mut self, id: LocalId) -> FlowRate {
        if let Some(&r) = self.local_rates.get(&id) {
            return r;
        }
        // A look-back to a later `let`: its rate from the previous pass.
        match self.fcx.let_of_local.get(&id) {
            Some(&k) => self.let_rates[k],
            None => FlowRate::Const,
        }
    }

    fn rate_target(&mut self, e: ExprId, t: &Target) -> RR<Option<FlowRate>> {
        Ok(Some(match t {
            Target::Local(id) => self.rate_of_local(*id),
            Target::Const { .. } | Target::ConstParam(_) | Target::Variant { .. } => FlowRate::Const,
            Target::Panic => FlowRate::Const,
            // The names stage reported a function value (E0806, S-195).
            Target::Fn { .. } | Target::Method { .. } | Target::Value => {
                onsa_diag::internal::bug(Some(self.expr(e).span), "a function value the names stage passed")
            }
        }))
    }

    /// The rate of an expression (§11.3): the maximum of its operands;
    /// the delays and instances are `Sig`.
    pub(super) fn rate(&mut self, e: ExprId) -> RR<FlowRate> {
        let expr = self.expr(e);
        let span = expr.span;
        let r = match &expr.kind {
            ExprKind::Lit(_) | ExprKind::Hole | ExprKind::Error | ExprKind::Range(_) => FlowRate::Const,
            ExprKind::Path(_) | ExprKind::Feedback(_) => match self.body.targets.get(&e).cloned() {
                Some(t) => self.rate_target(e, &t)?.unwrap_or(FlowRate::Const),
                None => FlowRate::Const,
            },
            ExprKind::Field { base, .. } => match self.body.targets.get(&e).cloned() {
                Some(t) => match self.rate_target(e, &t)? {
                    Some(r) => r,
                    None => self.rate(*base)?,
                },
                None => self.rate(*base)?,
            },
            ExprKind::Paren(inner) | ExprKind::Cast { expr: inner, .. } | ExprKind::Unary { expr: inner, .. } => {
                self.rate(*inner)?
            }
            ExprKind::At { expr: inner, .. } => self.rate_at(e, *inner)?,
            ExprKind::Move(inner) | ExprKind::Try(inner) | ExprKind::Unsafe(inner) => self.rate(*inner)?,
            ExprKind::Tuple(elems) | ExprKind::Array(elems) => {
                let mut r = FlowRate::Const;
                for &x in elems {
                    r = r.max(self.rate(x)?);
                }
                r
            }
            ExprKind::Repeat { elem, .. } => self.rate(*elem)?,
            ExprKind::Struct { fields, .. } => {
                let mut r = FlowRate::Const;
                for (_, x) in fields {
                    r = r.max(self.rate(*x)?);
                }
                r
            }
            ExprKind::Block(b) => match b.tail {
                Some(t) => self.rate(t)?,
                None => FlowRate::Const,
            },
            ExprKind::If { tilde: Some(t), .. } => return Err(self.tilde_branches(*t, "if~")),
            ExprKind::Match { tilde: Some(t), .. } => return Err(self.tilde_branches(*t, "match~")),
            ExprKind::If { cond, then, else_, tilde: None } => {
                let mut r = self.rate(*cond)?;
                self.branch += 1;
                let b = (|| -> RR<FlowRate> {
                    let mut r = self.rate(*then)?;
                    if let Some(el) = else_ {
                        r = r.max(self.rate(*el)?);
                    }
                    Ok(r)
                })();
                self.branch -= 1;
                r = r.max(b?);
                r
            }
            ExprKind::Match { scrutinee, arms, tilde: None } => {
                let sr = self.rate(*scrutinee)?;
                let mut r = sr;
                self.branch += 1;
                let b = (|| -> RR<FlowRate> {
                    let mut r = FlowRate::Const;
                    for arm in arms {
                        self.bind_pat_rates(arm.pat, sr);
                        if let Some(g) = arm.guard {
                            r = r.max(self.rate(g)?);
                        }
                        r = r.max(self.rate(arm.body)?);
                    }
                    Ok(r)
                })();
                self.branch -= 1;
                r = r.max(b?);
                r
            }
            ExprKind::Closure { .. } | ExprKind::Handle { .. } => FlowRate::Const,
            ExprKind::Binary { op, lhs, rhs, .. } => {
                let l = self.rate(*lhs)?;
                let short = Self::short_circuits(*op);
                self.branch += short as u32;
                let r = self.rate(*rhs);
                self.branch -= short as u32;
                l.max(r?)
            }
            ExprKind::TupleIndex { base, .. } | ExprKind::TypeArgs { base, .. } => self.rate(*base)?,
            ExprKind::Index { base, index } => self.rate(*base)?.max(self.rate(*index)?),
            ExprKind::Par { body, .. } => self.rate_par(e, *body)?,
            ExprKind::Call { callee, args, .. } => {
                if let Some(&i) = self.call_of_expr.get(&e) {
                    self.rate_node(e, i)?
                } else if self.fcx.sample_rate_calls.contains(&e) {
                    FlowRate::Init
                } else {
                    self.rate_call(e, *callee, args, span)?
                }
            }
        };
        self.set(e, r)
    }

    fn bind_pat_rates(&mut self, pat: PatId, r: FlowRate) {
        if let Some(&l) = self.body.pat_locals.get(&pat) {
            self.local_rates.insert(l, r);
        }
        match &self.ast.pat(pat).kind {
            PatKind::Tuple(elems) | PatKind::TupleStruct { elems, .. } | PatKind::Or(elems) => {
                for &x in elems {
                    self.bind_pat_rates(x, r);
                }
            }
            PatKind::Struct { fields, .. } => {
                for (_, p) in fields {
                    self.bind_pat_rates(*p, r);
                }
            }
            _ => {}
        }
    }

    /// Ordinary calls (§11.5 table): `rt` effect-free functions apply point-wise;
    /// a non-`rt` function runs at `init` and takes `Init`-or-constant arguments.
    fn rate_call(&mut self, e: ExprId, callee: ExprId, args: &[Arg], span: Span) -> RR<FlowRate> {
        let mut r = FlowRate::Const;
        // Receiver of a method call.
        if let Some(base) = crate::names::body::receiver(self.ast, callee)
            && self.body.expr_types.contains_key(&base)
            && !matches!(self.body.targets.get(&e), Some(Target::Fn { .. }))
        {
            r = r.max(self.rate(base)?);
        }
        r = args.iter().try_fold(r, |r, a| Ok(r.max(self.rate(a.expr)?)))?;
        let target = self.body.targets.get(&e).cloned();
        match target {
            Some(Target::Fn { def, .. }) | Some(Target::Method { def, .. }) => {
                let f = self.a.def(def).as_fn().cloned();
                let name = self.a.def(def).name.clone();
                if let Some(f) = f {
                    // The E0713 of §5.2, with no candidate: the `!` it writes is
                    // an E0806 (§11.2, S-811).
                    if self.final_pass && f.takes_inout_self() && self.inout_call.is_none() {
                        let msg = format!("`{name}` takes `inout self`, and a flow body cannot call it (§5.2, §11.2)");
                        let d = Diagnostic::new(Stage::Flow, Code::E0713, span, msg).with_found(self.src(span));
                        self.inout_call = Some(d);
                    }
                    // A name of no effect (`uses {I32}`, E0308) is no effect (§8.1, §18.1).
                    if self.final_pass && !f.effects.effects().is_empty() {
                        return Err(self.err(
                            Code::E0805,
                            span,
                            format!("`{name}` has effects; a flow calls effect-free functions only (§11.5)"),
                        ));
                    }
                    if self.final_pass && !f.rt && r > FlowRate::Init {
                        return Err(self.err(
                            Code::E0805,
                            span,
                            format!(
                                "`{name}` is not `rt` and takes arguments at the clock `init` or constants only; mark it `rt` or pass values at `init` (§11.5)"
                            ),
                        ));
                    }
                }
                Ok(r.max(FlowRate::Init))
            }
            Some(Target::Variant { .. }) | Some(Target::Panic) => Ok(r),
            // `.(` is the names stage's E0806 (§11.2, S-811).
            Some(Target::Value) => onsa_diag::internal::bug(Some(span), "a call of a value the names stage passed"),
            _ => Ok(r.max(FlowRate::Init)),
        }
    }

    /// The delays and instance calls (§11.4, §11.5, S-04, S-06).
    fn rate_node(&mut self, e: ExprId, i: usize) -> RR<FlowRate> {
        let call = self.fcx.calls[i].clone();
        let span = self.expr(e).span;
        self.stateful_here(span)?;
        match call.kind {
            NodeKind::Instance(callee) => {
                let inputs = self.a.def(callee).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
                let callee_name = self.a.def(callee).name.clone();
                for (arg, input) in call.args.iter().zip(&inputs) {
                    let ra = self.rate(*arg)?;
                    let ri = FlowRate::of_clock(input.api_clock(), input.span);
                    if self.final_pass && ra > ri {
                        let aspan = self.expr(*arg).span;
                        return Err(self.err(
                            Code::E0815,
                            aspan,
                            format!(
                                "this argument is at the clock `{}` but the input `{}` of `{callee_name}` is at `{}`; a value is never made slower (§11.3)",
                                ra.name(),
                                input.name,
                                ri.name()
                            ),
                        ));
                    }
                }
            }
            NodeKind::Delay(delay, _) => {
                let what = delay.name();
                let arg = call.args[0];
                let ra = self.rate(arg)?;
                if self.final_pass && ra != FlowRate::Sig {
                    let aspan = self.expr(arg).span;
                    let mut d = Diagnostic::new(
                        Stage::Flow,
                        Code::E0813,
                        aspan,
                        match ra {
                            FlowRate::Const => {
                                format!("the first argument of `{what}~` must be at the clock `sample`; this one is a constant (§11.4)")
                            }
                            _ => format!(
                                "the first argument of `{what}~` must be at the clock `sample`; this one is at `{}` (§11.4)",
                                ra.name()
                            ),
                        },
                    )
                    .with_found(self.src(aspan));
                    // The form to write is `prev~(p at sample)` (§11.4), where
                    // this version holds the promotion (`rate_at`).
                    if ra == FlowRate::Ctl && self.promotes_as_written(arg) {
                        let src = self.src(aspan);
                        d = d.with_note(aspan, format!("write `{what}~({src} at sample)` to delay it per sample"));
                    }
                    return Err(self.fail(d));
                }
                if delay == Delay::Variable {
                    self.rate(call.args[1])?;
                }
                if let Some(init_e) = call.init_expr {
                    let ri = self.rate(init_e)?;
                    if self.final_pass && ri > FlowRate::Init {
                        let ispan = self.expr(init_e).span;
                        // The clock of a value is faster than its position (S-147).
                        return Err(self.err(
                            Code::E0815,
                            ispan,
                            format!(
                                "the `init` of `{what}~` must be at the clock `init` or a constant; this one is at `{}` (§11.4)",
                                ri.name()
                            ),
                        ));
                    }
                }
            }
        }
        // The node, after the checks of its clocks (`NodeBuilder`).
        if self.final_pass
            && let Err(d) = self.nodes.node(self.a, self.body, e, &call, span)
        {
            let found = self.src(span);
            return Err(self.fail(d.with_found(found)));
        }
        Ok(FlowRate::Sig)
    }

    /// `par~ i in a..<b { e }` (§11.5): nodes of the body are nested in the `Par` node.
    fn rate_par(&mut self, e: ExprId, body: ExprId) -> RR<FlowRate> {
        self.stateful_here(self.expr(e).span)?;
        let (var, from, to) = self.fcx.pars[&e];
        self.local_rates.insert(var, FlowRate::Init);
        self.nodes.enter_par();
        let r = self.rate(body);
        let nodes = self.nodes.leave_par();
        let r = r?;
        if self.final_pass {
            self.nodes.par(e, var, from, to, body, nodes);
        }
        Ok(r.max(FlowRate::Init))
    }
}
