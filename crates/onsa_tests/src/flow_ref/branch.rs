//! The forms that make several of one thing or take one of several, of a flow body (§11.5): `par~` makes a replica of its
//! body for each value of its index, with the state of each its own (a node of the state is by the call and the replica
//! of each `par~` around it), and `if~` and `match~` evaluate every branch, so that what has state in each moves, and take
//! the value of one. The bindings a replica or an arm makes are kept in the `scope` of the run while it is evaluated,
//! so that what a delay saves in it (read in the second phase of the tick, after it) is read under them.

use onsa_diag::Span;
use onsa_syntax::ast::{ExprId, ExprKind, RangeEnd};

use super::expr::{Eval, Frame, Stop};
use super::scalar::Fault::{Internal, Unavailable};
use super::value::{IntKind, Value};

impl<'a> Frame<'a> {
    /// `go` for each replica of the `par~` `par` (the range evaluated here, `i` bound to its value, the index of the replica
    /// and the binding kept in the run while `go` goes); the results in the order of the index.
    pub(super) fn replicate<R>(
        &mut self,
        par: ExprId,
        mut go: impl FnMut(&mut Self) -> Result<R, Stop>,
    ) -> Result<Vec<R>, Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(par).span);
        let here = |fault| Stop { fault, at };
        let ExprKind::Par { var, range, .. } = &ast.expr(par).kind else { return Err(here(Internal("not a `par~`"))) };
        let var = self.body.par_var(var.span).map_err(here)?;
        let bound = |f: &mut Self, e| match f.eval(e)? {
            Value::Int(_, n, _) => Ok(n),
            _ => Err(here(Internal("a range of a `par~` that is not of integers"))),
        };
        let (lo, hi) = (bound(self, range.lo)?, bound(self, range.hi)?);
        let n = hi - lo + i128::from(range.end == RangeEnd::Included);
        let n = usize::try_from(n).ok().filter(|n| *n > 0).ok_or(here(Internal("an empty range of a `par~`")))?;
        if n > self.limits.most {
            return Err(here(Unavailable("a `par~` of more replicas than the evaluator holds")));
        }
        let mut out = Vec::with_capacity(n);
        for k in 0..n {
            let i = Value::int(IntKind::U32, lo + k as i128);
            self.locals.insert(var, i.clone());
            let run = self.run.as_mut().ok_or(here(Unavailable("a `par~` outside an instance of a flow")))?;
            run.replicas.push(k as u32);
            run.scope.push((var, i));
            let value = go(self);
            if let Some(run) = self.run.as_mut() {
                run.replicas.pop();
                run.scope.pop();
            }
            out.push(value?);
        }
        Ok(out)
    }

    /// `par~ i in a ..< b { e }`: the array of the values of `e` for each `i` (§11.5).
    #[inline(never)]
    pub(super) fn par(&mut self, e: ExprId) -> Eval {
        let ExprKind::Par { body, .. } = &self.body.ast.expr(e).kind else {
            return Err(Stop { fault: Internal("not a `par~`"), at: self.body.ast.expr(e).span });
        };
        Ok(Value::Array(self.replicate(e, |f| f.eval(*body))?))
    }

    /// `if~` (§11.5): each condition and each branch is evaluated, in the order written (the nested `if`s of an `else if`
    /// are part of the chain), and the value is that of the first branch whose condition is true, else the `else`.
    // The condition of an `else if` is evaluated even when an earlier branch is taken: the `~` is on the whole chain, and
    // the parts with no state are all evaluated too (§11.5).
    #[inline(never)]
    pub(super) fn all_branches(&mut self, e: ExprId, at: Span) -> Eval {
        let (ast, mut taken, mut chain) = (self.body.ast, None, e);
        loop {
            let ExprKind::If { cond, then, else_, .. } = &ast.expr(chain).kind else {
                return Err(Stop { fault: Internal("not an `if~`"), at });
            };
            let (hit, value) = (self.truth(*cond, at)?, self.eval(*then)?);
            taken = taken.or(hit.then_some(value));
            let Some(rest) = *else_ else { return Err(Stop { fault: Internal("an `if~` with no `else`"), at }) };
            if !matches!(ast.expr(rest).kind, ExprKind::If { .. }) {
                let last = self.eval(rest)?;
                return Ok(taken.unwrap_or(last));
            }
            chain = rest;
        }
    }

    /// `match~` (§11.5): the arm taken is chosen as `match` does (the pattern and the guard, from the top), then the body of
    /// every arm is evaluated in the order written, an arm not taken with the locals of its pattern at `T.default()`.
    // SPEC-GAP(S-1094): the guards of the arms after the one taken are not evaluated, as in a `match`; the other reading
    // evaluates all of them, which shows when a guard panics (`d if 100 / d > 1`).
    #[inline(never)]
    pub(super) fn select_all(&mut self, e: ExprId, at: Span) -> Eval {
        let (ast, here) = (self.body.ast, |fault| Stop { fault, at });
        let ExprKind::Match { scrutinee, arms, .. } = &ast.expr(e).kind else {
            return Err(here(Internal("not a match~")));
        };
        let (v, ty) = (self.eval(*scrutinee)?, self.body.ty(*scrutinee).map_err(here)?);
        let mut taken = None;
        for (n, arm) in arms.iter().enumerate() {
            if taken.is_none() && self.arm(arm.pat, &v, ty, arm.guard, at)? {
                taken = Some(n);
            }
        }
        let mut value = None;
        for (n, arm) in arms.iter().enumerate() {
            let locals = self.body.pat_locals(arm.pat).map_err(here)?;
            for l in locals.iter().filter(|_| Some(n) != taken) {
                let ty = self.body.local_ty(*l).map_err(here)?;
                let default = self.shape(ty, at)?.default_value();
                self.locals.insert(*l, default.ok_or(here(Unavailable("a binding of a type with no default")))?);
            }
            let bound: Vec<_> = locals.iter().filter_map(|l| Some((*l, self.locals.get(l)?.clone()))).collect();
            let kept = self.run.as_ref().map_or(0, |r| r.scope.len());
            if let Some(run) = self.run.as_mut() {
                run.scope.extend(bound);
            }
            let result = self.eval(arm.body);
            if let Some(run) = self.run.as_mut() {
                run.scope.truncate(kept);
            }
            let result = result?;
            if Some(n) == taken {
                value = Some(result);
            }
        }
        value.ok_or(here(Internal("no arm of a match~ is taken")))
    }
}
