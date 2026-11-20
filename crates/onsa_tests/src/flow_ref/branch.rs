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
        places: impl Fn(&R) -> usize,
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
        self.run.as_ref().ok_or(here(Unavailable("a `par~` outside an instance of a flow")))?;
        let mut out = Vec::with_capacity(n.min(1024));
        for k in 0..n {
            let i = Value::int(IntKind::U32, lo + k as i128);
            let value = self.with_bindings(&[k as u32], vec![(var, i)], |f| go(f))?;
            // The values of all the replicas are as many places as the first has, n times (as `[e; N]` is held, `aggregate.rs`):
            // the nest of `par~`s is stopped at its first row, before the product is made.
            if k == 0 && n.saturating_mul(places(&value)) > self.limits.most {
                return Err(here(Unavailable("the values of a `par~` are more places than the evaluator holds")));
            }
            out.push(value);
        }
        Ok(out)
    }

    /// `par~ i in a ..< b { e }`: the array of the values of `e` for each `i` (§11.5).
    #[inline(never)]
    pub(super) fn par(&mut self, e: ExprId) -> Eval {
        let ExprKind::Par { body, .. } = &self.body.ast.expr(e).kind else {
            return Err(Stop { fault: Internal("not a `par~`"), at: self.body.ast.expr(e).span });
        };
        Ok(Value::Array(self.replicate(e, Value::places, |f| f.eval(*body))?))
    }

    /// `if~` (§11.5): the side that selects goes first: the conditions of the chain from the top, up to the first that is true (the
    /// nested `if`s of an `else if` are part of the chain, and the conditions after it are not evaluated), then every branch in the
    /// order written, and the value is that of the branch whose condition was the first true, else the `else` (S-1094 (1)).
    // The condition of an `else { if~ … }` is in a branch, so it is evaluated whatever the conditions before it are; the `~` is on
    // the whole chain, and the parts with no state of every branch are all evaluated too (§11.5).
    #[inline(never)]
    pub(super) fn all_branches(&mut self, e: ExprId, at: Span) -> Eval {
        let (ast, mut chain, mut links) = (self.body.ast, e, Vec::new());
        let last = loop {
            let ExprKind::If { cond, then, else_, .. } = &ast.expr(chain).kind else {
                return Err(Stop { fault: Internal("not an `if~`"), at });
            };
            links.push((*cond, *then));
            let Some(rest) = *else_ else { return Err(Stop { fault: Internal("an `if~` with no `else`"), at }) };
            if !matches!(ast.expr(rest).kind, ExprKind::If { .. }) {
                break rest;
            }
            chain = rest;
        };
        let mut chosen = links.len();
        for (n, (cond, _)) in links.iter().enumerate() {
            if self.truth(*cond, at)? {
                chosen = n;
                break;
            }
        }
        let mut taken = None;
        for (n, (_, then)) in links.iter().enumerate() {
            let value = self.eval(*then)?;
            if n == chosen {
                taken = Some(value);
            }
        }
        let rest = self.eval(last)?;
        Ok(taken.unwrap_or(rest))
    }

    /// `match~` (§11.5): the arm taken is chosen as `match` does (the pattern and the guard, from the top), then the body of
    /// every arm is evaluated in the order written, an arm not taken with the locals of its pattern at `T.default()`.
    // The guards of the arms after the one taken are not evaluated, as in a `match` (S-1094 (1): the side that selects stops
    // at the first arm that matches); the bodies of all the arms come after it.
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
            let mut bound = Vec::new();
            for l in self.body.pat_locals(arm.pat).map_err(here)? {
                if Some(n) == taken {
                    bound.extend(self.locals.get(&l).map(|v| (l, v.clone())));
                    continue;
                }
                let default = self.shape(self.body.local_ty(l).map_err(here)?, at)?.default_value();
                bound.push((l, default.ok_or(here(Unavailable("a binding of a type with no default")))?));
            }
            let result = self.with_bindings(&[], bound, |f| f.eval(arm.body))?;
            if Some(n) == taken {
                value = Some(result);
            }
        }
        value.ok_or(here(Internal("no arm of a match~ is taken")))
    }
}
