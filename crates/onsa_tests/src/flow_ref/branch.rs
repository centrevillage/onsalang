//! The forms that make several of one thing or take one of several, of a flow body (§11.5): `par~` makes a replica of its
//! body for each value of its index, with the state of each its own (a node of the state is by the call and the replica
//! of each `par~` around it), and `if~` and `match~` evaluate every branch, so that what has state in each moves, and take
//! the value of one. The bindings a replica or an arm makes are kept in the `scope` of the run while it is evaluated,
//! so that what a delay saves in it (read in the second phase of the tick, after it) is read under them.

use onsa_diag::Span;
use onsa_sema::{LocalId, Target};
use onsa_syntax::ast::{ExprId, ExprKind, PatId, RangeEnd};

use super::expr::{Eval, Frame, Stop};
use super::scalar::Fault::{self, Internal, Unavailable};
use super::sema_view::Body;
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
            let bound = if Some(n) == taken { self.pat_values(arm.pat)? } else { self.default_values(arm.pat, at)? };
            let result = self.with_bindings(&[], bound, |f| f.eval(arm.body))?;
            if Some(n) == taken {
                value = Some(result);
            }
        }
        value.ok_or(here(Internal("no arm of a match~ is taken")))
    }

    /// The values the locals of the pattern `pat` have now (the arm it is of has just matched).
    pub(super) fn pat_values(&self, pat: PatId) -> Result<Vec<(LocalId, Value)>, Stop> {
        let at = self.body.ast.pat(pat).span;
        let locals = self.body.pat_locals(pat).map_err(|fault| Stop { fault, at })?;
        Ok(locals.into_iter().filter_map(|l| self.locals.get(&l).map(|v| (l, v.clone()))).collect())
    }

    /// The locals of the pattern `pat` at `T.default()` of their types, as those of an arm that is not taken have them (§11.5).
    pub(super) fn default_values(&mut self, pat: PatId, at: Span) -> Result<Vec<(LocalId, Value)>, Stop> {
        let here = |fault| Stop { fault, at };
        let mut out = Vec::new();
        for l in self.body.pat_locals(pat).map_err(here)? {
            let default = self.shape(self.body.local_ty(l).map_err(here)?, at)?.default_value();
            out.push((l, default.ok_or(here(Unavailable("a binding of a type with no default")))?));
        }
        Ok(out)
    }

    /// The bindings of the arm `arm` of the `match~` `m` at the stage this evaluation is of (`init` or `block`): the parts of the object where the
    /// arm is the first that the pattern and the guard choose, `T.default()` where it is not (S-1131). The object and the guards of the arms
    /// up to it are evaluated from the top, and the arms after it are not.
    fn arm_values(&mut self, m: ExprId, arm: usize) -> Result<Vec<(LocalId, Value)>, Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(m).span);
        let here = |fault| Stop { fault, at };
        let ExprKind::Match { scrutinee, arms, .. } = &ast.expr(m).kind else {
            return Err(here(Internal("not a match~")));
        };
        let (v, ty) = (self.eval(*scrutinee)?, self.body.ty(*scrutinee).map_err(here)?);
        for (n, a) in arms.iter().enumerate().take(arm + 1) {
            if self.arm(a.pat, &v, ty, a.guard, at)? {
                return if n == arm { self.pat_values(a.pat) } else { self.default_values(arms[arm].pat, at) };
            }
        }
        self.default_values(arms[arm].pat, at)
    }

    /// `go` with the bindings of the arms (outermost first) that hold the call as the stage gives them.
    fn with_arms<R>(
        &mut self,
        arms: &[(ExprId, usize)],
        go: impl FnOnce(&mut Self) -> Result<R, Stop>,
    ) -> Result<R, Stop> {
        match arms.split_first() {
            None => go(self),
            Some((&(m, arm), rest)) => {
                let binds = self.arm_values(m, arm)?;
                self.with_bindings(&[], binds, |f| f.with_arms(rest, go))
            }
        }
    }

    /// The argument `arg` of the call `call`, evaluated for the stage `stage` of the input it is for: at `init` and `block` a binding of an
    /// arm that it reads has the value that stage gives it (`with_arms`), whether the arm is taken or not (S-1131); at `sample` it is live.
    pub(super) fn eval_staged(
        &mut self,
        call: ExprId,
        arg: ExprId,
        stage: super::sema_view::Stage,
    ) -> Result<Value, Stop> {
        if stage == super::sema_view::Stage::Sample || !self.body.reads_arm_binding(arg, arg) {
            return self.eval(arg);
        }
        let at = self.body.ast.expr(call).span;
        let arms = arms_of(&self.body, call).map_err(|fault| Stop { fault, at })?;
        // Only the arms whose bindings `arg` reads give them here: an arm that binds a name it does not read (or none) may have a guard or an
        // object of `sample`, which this stage cannot evaluate (a binding of that clock is not read at this stage, S-1131).
        let mut read = Vec::new();
        for (m, n) in arms {
            let ExprKind::Match { arms: all, .. } = &self.body.ast.expr(m).kind else { continue };
            let locals = self.body.pat_locals(all[n].pat).map_err(|fault| Stop { fault, at })?;
            if locals.iter().any(|l| reads_local(&self.body, arg, *l)) {
                read.push((m, n));
            }
        }
        self.with_arms(&read, |f| f.eval(arg))
    }
}

/// Does `e` read the local `l`?
fn reads_local(body: &Body, e: ExprId, l: LocalId) -> bool {
    matches!(body.target(e), Ok(Target::Local(x)) if *x == l)
        || body.ast.sub_exprs(e).into_iter().any(|x| reads_local(body, x, l))
}

/// The arms of the `match~`s that hold `call`, outermost first, with the number of each arm: the bindings its arguments may read.
pub(super) fn arms_of(body: &Body, call: ExprId) -> Result<Vec<(ExprId, usize)>, Fault> {
    fn find(body: &Body, e: ExprId, call: ExprId, path: &mut Vec<(ExprId, usize)>) -> bool {
        if e == call {
            return true;
        }
        if let ExprKind::Match { scrutinee, arms, tilde: Some(_) } = &body.ast.expr(e).kind {
            if find(body, *scrutinee, call, path) {
                return true;
            }
            for (n, arm) in arms.iter().enumerate() {
                path.push((e, n));
                if find(body, arm.body, call, path) {
                    return true;
                }
                path.pop();
            }
            return false;
        }
        body.ast.sub_exprs(e).into_iter().any(|x| find(body, x, call, path))
    }
    let root = body.view.flow(body.def)?.body;
    let mut path = Vec::new();
    find(body, root, call, &mut path).then_some(path).ok_or(Internal("a call that is not in the body of its flow"))
}
