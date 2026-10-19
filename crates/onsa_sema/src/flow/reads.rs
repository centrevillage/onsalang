//! The state marking (S-05): the highest rate at which each local is read
//! (`FlowInfo::read_at`), the `let`s read at a higher rate than their own,
//! and the rate at which `sample_rate()` is read. The lowering reads these
//! and does not walk the body again (R-91 (1), D-15).

use super::*;

impl<'a> Rater<'a> {
    // ------------------------------------------------------------ state marking

    /// The rate each local is read at, the `let`s read at a higher rate than
    /// their own (S-05), and the rate at which `sample_rate()` is read.
    pub(super) fn mark_all(&mut self) {
        for k in 0..self.lets.len() {
            let (init, rate) = (self.lets[k].init, self.lets[k].rate);
            self.mark(init, rate);
        }
        if let Some(out) = self.fcx.output {
            self.mark(out, FlowRate::Sig);
        }
        for l in &mut self.lets {
            l.state =
                l.rate >= FlowRate::Init && l.locals.iter().any(|id| self.read_at.get(id).is_some_and(|&r| r > l.rate));
        }
    }

    fn mark(&mut self, e: ExprId, ctx: FlowRate) {
        let expr = self.expr(e);
        match &expr.kind {
            ExprKind::Path(_) | ExprKind::Feedback(_) | ExprKind::Field { .. } => {
                if let Some(Target::Local(id)) = self.body.targets.get(&e) {
                    let r = self.read_at.entry(*id).or_insert(ctx);
                    *r = (*r).max(ctx);
                }
                if let ExprKind::Field { base, .. } = &expr.kind
                    && !self.body.targets.contains_key(&e)
                {
                    self.mark(*base, ctx);
                }
            }
            ExprKind::Call { callee, args, .. } => {
                if let Some(&i) = self.call_of_expr.get(&e) {
                    let call = self.fcx.calls[i].clone();
                    match call.kind {
                        NodeKind::Instance(callee_def) => {
                            let inputs = self.a.def(callee_def).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
                            for (arg, input) in call.args.iter().zip(&inputs) {
                                self.mark(*arg, FlowRate::from_rate(input.rate));
                            }
                        }
                        NodeKind::Delay(delay, _) => {
                            self.mark(call.args[0], FlowRate::Sig);
                            if delay == Delay::Variable {
                                self.mark(call.args[1], FlowRate::Sig);
                            }
                            if let Some(i) = call.init_expr {
                                self.mark(i, FlowRate::Init);
                            }
                        }
                    }
                } else if self.fcx.sample_rate_calls.contains(&e) {
                    self.sample_rate_at = Some(self.sample_rate_at.map_or(ctx, |r| r.max(ctx)));
                } else {
                    self.non_rt_here(e, ctx);
                    if let ExprKind::Field { base, .. } = &self.expr(*callee).kind
                        && self.body.expr_types.contains_key(base)
                    {
                        self.mark(*base, ctx);
                    }
                    for a in args {
                        self.mark(a.expr, ctx);
                    }
                }
            }
            ExprKind::Par { body, .. } => self.mark(*body, ctx),
            _ => {
                for child in children(expr) {
                    self.mark(child, ctx);
                }
            }
        }
    }
}

/// Direct sub-expressions of an expression (for the marking walk).
fn children(expr: &onsa_syntax::ast::Expr) -> Vec<ExprId> {
    match &expr.kind {
        ExprKind::Paren(x) | ExprKind::Move(x) | ExprKind::Try(x) | ExprKind::Unsafe(x) => vec![*x],
        ExprKind::Cast { expr, .. } | ExprKind::Unary { expr, .. } | ExprKind::At { expr, .. } => vec![*expr],
        ExprKind::Tuple(xs) | ExprKind::Array(xs) => xs.clone(),
        ExprKind::Repeat { elem, .. } => vec![*elem],
        ExprKind::Struct { fields, .. } => fields.iter().map(|(_, x)| *x).collect(),
        ExprKind::Block(b) => b.tail.into_iter().collect(),
        ExprKind::If { cond, then, else_, .. } => {
            let mut v = vec![*cond, *then];
            v.extend(*else_);
            v
        }
        ExprKind::Match { scrutinee, arms, .. } => {
            let mut v = vec![*scrutinee];
            for arm in arms {
                v.extend(arm.guard);
                v.push(arm.body);
            }
            v
        }
        ExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
        ExprKind::TupleIndex { base, .. } | ExprKind::TypeArgs { base, .. } => vec![*base],
        ExprKind::Index { base, index } => vec![*base, *index],
        ExprKind::Call { args, .. } => args.iter().map(|a| a.expr).collect(),
        ExprKind::Range(r) => vec![r.lo, r.hi],
        ExprKind::Par { body, .. } => vec![*body],
        ExprKind::Lit(_)
        | ExprKind::Path(_)
        | ExprKind::Feedback(_)
        | ExprKind::Hole
        | ExprKind::Error
        | ExprKind::Field { .. }
        | ExprKind::Closure { .. }
        | ExprKind::Handle { .. } => Vec::new(),
    }
}
