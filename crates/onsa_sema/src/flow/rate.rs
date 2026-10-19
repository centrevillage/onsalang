//! The rate pass (§11.3): after type checking, the rate of every
//! expression, the flow rules and the stateful nodes.

use super::*;

// ---------------------------------------------------------------- rate pass

/// After type checking: assign rates, check the flow rules, collect nodes.
pub(crate) fn finish_flow(a: &mut Analysis, module: &Module, id: DefId, body: BodyInfo, fcx: FlowCx) {
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
        rates: HashMap::new(),
        local_rates: HashMap::new(),
        let_rates: vec![FlowRate::Const; fcx.pending.len()],
        lets: Vec::new(),
        diag: None,
        node_lists: Vec::new(),
        node_of_expr: HashMap::new(),
        counters: HashMap::new(),
        sample_rate_at: None,
        read_at: HashMap::new(),
        let_names: HashMap::new(),
        call_of_expr: HashMap::new(),
        branch: 0,
    };
    for (i, c) in fcx.calls.iter().enumerate() {
        r.call_of_expr.insert(c.expr, i);
    }
    for p in &fcx.pending {
        if let Some(n) = &p.name {
            r.let_names.insert(p.init, n.clone());
        }
    }
    // Fixpoint on the `let` rates: a look-back (`prev~(^y)` before `let y`)
    // reads a rate that is only known after its `let` is rated. Rates only go
    // up, and the lattice has four levels, so this converges quickly.
    for _ in 0..6 {
        r.pass();
        let mut changed = false;
        for (i, l) in r.lets.iter().enumerate() {
            changed |= r.let_rates[i] != l.rate;
            r.let_rates[i] = l.rate;
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
    let diag = r.diag.take();
    info.complete = diag.is_none();
    info.expr_rates = r.rates;
    info.local_rates = r.local_rates;
    info.lets = r.lets;
    info.nodes = r.node_lists.pop().unwrap_or_default();
    info.node_of_expr = r.node_of_expr;
    info.sample_rate_at = r.sample_rate_at;
    info.read_at = r.read_at;
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
    pub(super) lets: Vec<FlowLet>,
    pub(super) diag: Option<Diagnostic>,
    pub(super) node_lists: Vec<Vec<Node>>,
    pub(super) node_of_expr: HashMap<ExprId, usize>,
    pub(super) counters: HashMap<String, u32>,
    pub(super) sample_rate_at: Option<FlowRate>,
    /// The highest rate each local is read at (the state marking).
    pub(super) read_at: HashMap<LocalId, FlowRate>,
    pub(super) let_names: HashMap<ExprId, String>,
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
        self.node_lists = vec![Vec::new()];
        self.node_of_expr.clear();
        self.counters.clear();
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
                && let Some(k) = self.a.kind_of(ty)
                && k != Kind::Copy
            {
                let shown = self.display(ty);
                return Err(self.err(
                    Code::E0810,
                    p.span,
                    format!("the value type of a signal must be Copy; `{shown}` is {} (§11.3)", k.name()),
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
                rate,
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
            Target::Const(_) | Target::BuiltinConst { .. } | Target::ConstParam(_) | Target::Variant { .. } => {
                FlowRate::Const
            }
            Target::Prelude(_) => FlowRate::Const,
            Target::Fn { .. } | Target::Method { .. } | Target::Value => {
                let span = self.expr(e).span;
                return Err(self.err(
                    Code::E0806,
                    span,
                    "a flow body cannot contain function values; call the function directly (§11.2)",
                ));
            }
            Target::BuiltinMethod { .. } => return Ok(None),
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
            ExprKind::If { tilde: Some(t), .. } => return Err(self.tilde_branches(*t, FlowForm::IfTilde)),
            ExprKind::Match { tilde: Some(t), .. } => return Err(self.tilde_branches(*t, FlowForm::MatchTilde)),
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
        if let ExprKind::Field { base, .. } = &self.expr(callee).kind
            && self.body.expr_types.contains_key(base)
            && !matches!(self.body.targets.get(&e), Some(Target::Fn { .. }))
        {
            r = r.max(self.rate(*base)?);
        }
        // The arguments a builtin evaluates on some paths only are a branch
        // (`o.unwrap_or(d)`, K-08).
        let lazy = matches!(self.body.targets.get(&e), Some(Target::BuiltinMethod { lazy_args: true, .. }));
        self.branch += lazy as u32;
        let rated = args.iter().try_fold(r, |r, a| Ok(r.max(self.rate(a.expr)?)));
        self.branch -= lazy as u32;
        r = rated?;
        let target = self.body.targets.get(&e).cloned();
        match target {
            Some(Target::Fn { def, .. }) | Some(Target::Method { def, .. }) => {
                let f = self.a.def(def).as_fn().cloned();
                let name = self.a.def(def).name.clone();
                if let Some(f) = f {
                    if self.final_pass && !f.effects.is_empty() {
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
            Some(Target::BuiltinMethod { .. }) => Ok(r.max(FlowRate::Init)),
            Some(Target::Variant { .. }) | Some(Target::Prelude(_)) => Ok(r),
            Some(Target::Value) => Err(self.err(
                Code::E0806,
                span,
                "a flow body cannot contain function values; call the function directly (§11.2)",
            )),
            _ => Ok(r.max(FlowRate::Init)),
        }
    }

    fn next_name(&mut self, kind: &str) -> String {
        let n = self.counters.entry(kind.to_string()).or_insert(0);
        let name = format!("{kind}_{n}");
        *n += 1;
        name
    }

    fn push_node(&mut self, node: Node) {
        let list = self.node_lists.last_mut().expect("node list");
        let idx = list.len();
        self.node_of_expr.insert(node.expr(), idx);
        list.push(node);
    }

    fn node_name(&mut self, e: ExprId, kind: &str) -> String {
        match self.let_names.get(&e) {
            Some(n) => n.clone(),
            None => self.next_name(kind),
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
                    let ri = FlowRate::from_rate(input.rate);
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
                if self.final_pass {
                    let name = self.node_name(e, &callee_name);
                    self.push_node(Node::Instance { name, expr: e, callee, args: call.args.clone(), span });
                }
                Ok(FlowRate::Sig)
            }
            NodeKind::Delay(delay, len) => {
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
                let d_e = (delay == Delay::Variable).then(|| call.args[1]);
                if let Some(d) = d_e {
                    self.rate(d)?;
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
                if self.final_pass {
                    let ty = self.body.expr_types.get(&e).copied().unwrap_or(call.ty);
                    let init = match (&call.init, call.init_expr) {
                        (Some(init), _) => init.clone(),
                        (None, Some(init_e)) => InitArg::Init(init_e),
                        (None, None) => self.default_init(ty, span)?,
                    };
                    let name = self.node_name(e, what);
                    let node = match (delay, d_e) {
                        (Delay::Prev, _) => Node::Prev { name, expr: e, arg, init, ty },
                        (Delay::Fixed, _) => Node::Delay { name, expr: e, arg, n: len, init, ty },
                        (Delay::Variable, Some(d)) => Node::Vdelay { name, expr: e, arg, d, max: len, init, ty },
                        (Delay::Variable, None) => onsa_diag::internal::bug(Some(span), "a `vdelay~` without its `d`"),
                    };
                    self.push_node(node);
                }
                Ok(FlowRate::Sig)
            }
        }
    }

    /// `par i in a..<b { e }` (§11.5): nodes of the body are nested in the `Par` node.
    fn rate_par(&mut self, e: ExprId, body: ExprId) -> RR<FlowRate> {
        self.stateful_here(self.expr(e).span)?;
        let (var, from, to) = self.fcx.pars[&e];
        self.local_rates.insert(var, FlowRate::Init);
        self.node_lists.push(Vec::new());
        let r = self.rate(body);
        let nodes = self.node_lists.pop().unwrap_or_default();
        let r = r?;
        if self.final_pass {
            let name = self.node_name(e, "par");
            self.push_node(Node::Par { name, expr: e, var, from, to, body, nodes });
        }
        Ok(r.max(FlowRate::Init))
    }
}
