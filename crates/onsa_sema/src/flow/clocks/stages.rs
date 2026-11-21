//! The stages of the expressions of a flow body (§11.3, S-1196, S-1161,
//! S-1166): made once of the clocks the walk recorded, the one place of the
//! judgement (D-15). An expression decided by values of the parameter kinds
//! alone (constants, `init`, `block`, through `at` and parentheses, names
//! and bindings of them) is of the stage of its values whatever clock an
//! `at` gives it; one that reads a tick is of the stage of its clock. A
//! condition, a scrutinee and a guard count by their clocks, `at` counted
//! (the stage they are decided at). The marking ([`crate::flow::hoist`]) and
//! the plan read them ([`ClockInfo::stage`], [`FlowLet::stage`]).

use super::*;

#[cfg(test)]
mod tests;

/// Of a clock of the parameter kinds, its place in their order (§11.3).
fn param(c: Clock) -> Option<u8> {
    match c {
        Clock::Const => Some(0),
        Clock::Init => Some(1),
        Clock::Block => Some(2),
        _ => None,
    }
}

struct Stages<'w, 'a> {
    w: &'w Walk<'a>,
    memo: HashMap<ExprId, Clock>,
    /// The stages of the `let`s made, in their order: a name reads an
    /// earlier one, with no recursion through the chain of the `let`s (one
    /// not made yet, read only in error, E0801, is of its clock).
    lets: Vec<Clock>,
}

/// The stages of the expressions and the locals the walk `w` recorded,
/// those that differ from their clocks ([`ClockInfo::stages`]), and of its
/// `let`s in their order. Each expression is made once (memoized), of the
/// stages of its parts: linear in the body.
pub(super) fn of_walk(w: &Walk) -> (HashMap<ExprId, Clock>, HashMap<LocalId, Clock>, Vec<Clock>) {
    let mut s = Stages { w, memo: HashMap::default(), lets: Vec::with_capacity(w.cx.pending.len()) };
    for k in 0..w.cx.pending.len() {
        let c = s.of_let(k);
        s.lets.push(c);
    }
    for &e in w.out.exprs.keys() {
        s.of(e);
    }
    let lets = std::mem::take(&mut s.lets);
    s.memo.retain(|e, c| w.out.exprs.get(e) != Some(c));
    let locals = w.cx.pending.iter().zip(&lets).flat_map(|(p, &c)| p.locals.iter().map(move |&l| (l, c)));
    let locals = locals.filter(|(l, c)| w.out.locals.get(l) != Some(c)).collect();
    (s.memo, locals, lets)
}

impl Stages<'_, '_> {
    /// The stage of `e`, as a clock; none of one the walk did not record.
    fn of(&mut self, e: ExprId) -> Option<Clock> {
        let c = *self.w.out.exprs.get(&e)?;
        if let Some(&s) = self.memo.get(&e) {
            return Some(s);
        }
        let s = if param(c).is_some() || matches!(c, Clock::Tick(_)) { self.rule(e, c) } else { c };
        self.memo.insert(e, s);
        Some(s)
    }

    /// The stage of the `let` k: of its initializer, of its clock when that
    /// reads a tick.
    fn of_let(&mut self, k: usize) -> Clock {
        let own = self.w.checked[k].or(self.w.lets[k]).unwrap_or(Clock::Const);
        self.of(self.w.cx.pending[k].init).filter(|&s| param(s).is_some()).unwrap_or(own)
    }

    /// The stage of `e` of the clock `c` (§11.3): of its parts, its
    /// conditions by their clocks; `c` when one reads a tick.
    fn rule(&mut self, e: ExprId, c: Clock) -> Clock {
        let (w, ast) = (self.w, self.w.ast);
        let (mut conds, mut parts, mut init) = (Vec::new(), Vec::new(), false);
        match &ast.expr(e).kind {
            ExprKind::Path(_) | ExprKind::Feedback(_) => return self.name(e, c),
            ExprKind::Field { .. } if w.body.targets.contains_key(&e) => return self.name(e, c),
            ExprKind::At { expr, .. } => return self.of(*expr).filter(|&s| param(s).is_some()).unwrap_or(c),
            // A node, `sample_rate()` and `sample_tick()` have the clock of what they make.
            ExprKind::Call { .. } if w.calls.contains_key(&e) || w.time.contains_key(&e) => return c,
            ExprKind::Call { callee, args, .. } => {
                parts.extend(crate::names::body::receiver(ast, *callee));
                parts.extend(args.iter().map(|x| x.expr));
                // A call of constants is at `init` (provisional, as its clock in `clocks.rs`; W9-03 drops both).
                init = !matches!(w.body.targets.get(&e), Some(Target::Variant { .. } | Target::Panic));
            }
            ExprKind::If { .. } => {
                let chain = crate::flow::branching::chain(ast, e);
                conds.extend(chain.links.iter().map(|l| l.cond));
                parts.extend(chain.links.iter().map(|l| l.then).chain(chain.last));
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                conds.extend(std::iter::once(*scrutinee).chain(arms.iter().filter_map(|a| a.guard)));
                parts.extend(arms.iter().map(|a| a.body));
            }
            ExprKind::Binary { op: BinOp::And | BinOp::Or, lhs, rhs, .. } => (conds, parts) = (vec![*lhs], vec![*rhs]),
            ExprKind::Par { body, .. } => (parts, init) = (vec![*body], true),
            _ => parts = ast.sub_exprs(e),
        }
        let conds = conds.into_iter().filter_map(|x| w.out.exprs.get(&x).copied());
        let parts: Vec<Clock> = parts.into_iter().filter_map(|x| self.of(x)).collect();
        let mut s = if init { Clock::Init } else { Clock::Const };
        for k in conds.chain(parts) {
            match (param(k), param(s)) {
                (None, _) => return c,
                (Some(a), Some(b)) if a > b => s = k,
                _ => {}
            }
        }
        s
    }

    /// A name: of an earlier `let`, the stage of the `let`; of an
    /// input, a binding of an arm (whose stage is the clock its choice is
    /// decided by) and the index of a `par`, its clock. `^y` is in the first
    /// argument of a delay, of the clock of the delay.
    // SPEC-GAP(S-1199): a binding of an arm is of its clock, not of the stage of its value.
    // SPEC-GAP(S-1200): a name a `let` destructures is of the stage of the whole `let`.
    fn name(&mut self, e: ExprId, c: Clock) -> Clock {
        let Some(Target::Local(id)) = self.w.body.targets.get(&e) else { return c };
        match self.w.cx.let_of_local.get(id) {
            Some(&k) if !matches!(self.w.ast.expr(e).kind, ExprKind::Feedback(_)) => {
                self.lets.get(k).copied().filter(|&s| param(s).is_some()).unwrap_or(c)
            }
            _ => c,
        }
    }
}
