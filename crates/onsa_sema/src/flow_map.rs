//! The flow syntax of version 0.3 written in the terms of this version's
//! flow checks (W3-10, K-02 (a)): the clocks `at` (S-102, S-359), the
//! feedback references `^name` and the built-in delays `prev~` / `delay~` /
//! `vdelay~` with their optional `init` (S-44, S-29), and `if~` / `match~`
//! (S-110). The checks keep their representation (`Rate`, [`FlowRate`], the
//! nodes of [`super::Node`] and [`InitArg`]); this module holds the reading
//! of the new forms into it, and W7-02 removes it with the clock analysis
//! and the flow plan. The names of the clocks and of the delays stay
//! (`crate::flow_names`, [`crate::ty::Rate::clock`]).
//!
//! What the representation cannot hold is E0200 here, never read in another
//! meaning (plan §8.2): a computed expression made faster with `at`, `if~` /
//! `match~`, the omitted `init` of a value type that is no number, a `^`
//! inside a `par` (R-03), a call of a function that is not `rt` above `init`
//! (R-17). So are the forms that the representation reads wrongly until W7
//! (K-08): a delay inside the first argument of a delay (R-13, W7-07), a
//! stateful node in a branch, a guard, the right side of `&&` / `||` or an
//! argument a builtin evaluates on some paths only (S-110, W7-06).
//!
//! W7-02 also removes or rewrites, outside this file, what serves it:
//! - `flow.rs`: the fields `delay_arg`, `par_depth` and `ats` of `FlowCx`
//!   and their counting (`check_delay`, `check_par`); the save of `lookback`
//!   around the arguments in `check_instance`; the arms of `At` and
//!   `Feedback` in `check_flow_expr`, `rate`, `mark` and `children`; the
//!   field `branch` of the rate pass and its counting in `rate` (`If`,
//!   `Match`, `Binary`) and `rate_call`.
//! - `sig.rs`: the rates of the inputs and the output from their clocks
//!   (`lower_flow`); `Ty::Rate` is gone already.
//! - `body.rs`: the arms of `tilde` of `If` / `Match` (typed as plain in a
//!   flow, E0200 outside).
//! - `onsa_diag/src/unsupported.rs`: the features of the E0200 here and of
//!   `NestedDelays` (the works named on each).
//! - `modes.rs`, `onsa_core` (`lower/body.rs` `At`, `lower/flow.rs`
//!   `children`) and `onsa_driver/graph.rs`: the arms of `At` / `Feedback`.
//!
//! The optional `init` of a delay (`NodeCall.init_expr`) stays: W7-07 gives
//! the omitted one its value `T.default()`. The arguments a builtin evaluates
//! lazily (`builtin.rs`, `lazy_args`) go with `unwrap_or` in W5-03.

use onsa_diag::unsupported::{Feature, FlowForm};
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{BinOp, Clock, ExprId, ExprKind, Ident, Path};

use super::{FlowRate, InitArg, Rater};
use crate::body::{Checker, R, Target};
use crate::consteval::ConstValue;
use crate::flow_names::clock_rate;
use crate::ty::{Ty, TyId};

impl Checker<'_> {
    /// `e at k` in a flow body (§11.3): the type of `e`; the clock is the
    /// rate pass's ([`Rater::rate_at`]).
    pub(super) fn check_at(&mut self, e: ExprId, inner: ExprId, clock: &Clock, expected: Option<TyId>) -> R<TyId> {
        let rate = clock_rate(clock).map_err(|d| self.diag(d))?;
        let t = self.check_expr(inner, expected)?;
        self.fcx().ats.insert(e, FlowRate::from_rate(rate));
        Ok(t)
    }

    /// `^name` in a flow body (§11.2): a later `let` of the body, read in the
    /// first argument of a delay (outside it E0801, inside a `par` E0200).
    pub(super) fn check_feedback(&mut self, e: ExprId, name: &Ident) -> R<TyId> {
        let span = self.expr(e).span;
        let local = self.lookup_local(&name.name);
        let later = local.and_then(|id| {
            let f = self.fcx();
            let k = *f.let_of_local.get(&id)?;
            (!f.defined.contains(&id)).then_some((id, k))
        });
        match (local, later) {
            (_, Some((id, k))) => {
                if self.fcx().lookback == 0 {
                    let def_span = self.fcx().pending[k].span;
                    return Err(self.diag(
                        Diagnostic::new(
                            Stage::Flow,
                            Code::E0801,
                            span,
                            format!(
                                "`^{0}` reads the later `{0}`, which only the first argument of `prev~` / `delay~` / `vdelay~` may do (§11.2)",
                                name.name
                            ),
                        )
                        .with_found(self.src(span))
                        .with_note(def_span, "defined here"),
                    ));
                }
                // R-03: the replicas store before the later `let` (W7-04).
                if self.fcx().par_depth > 0 {
                    return Err(self.unsupported_in(Stage::Flow, span, Feature::FeedbackInPar, &[]));
                }
                self.info.targets.insert(e, Target::Local(id));
                Ok(self.local_ty(id))
            }
            (Some(_), None) => Err(self.unsupported_in(Stage::Flow, span, Feature::CaretOnVisible, &[])),
            (None, None) => {
                let path = Path { segments: vec![name.clone()], span: name.span };
                match self.a.resolve_path(self.m, &path) {
                    Ok(_) => Err(self.unsupported_in(Stage::Flow, span, Feature::CaretOnVisible, &[])),
                    Err(err) => Err(self.resolve_error(&path, err)),
                }
            }
        }
    }
}

impl Rater<'_> {
    /// The rate of `e at k` (§11.3): `k`. A slower `k` than the rate of the
    /// expression is E0815; a faster one is a promotion, which this
    /// representation holds for a name or a literal only (the `let` of a
    /// computed one would be evaluated at `k`, not at its own clock, K-02).
    pub(super) fn rate_at(&mut self, e: ExprId, inner: ExprId) -> Result<FlowRate, super::RStop> {
        let r = self.rate(inner)?;
        let Some(&k) = self.fcx.ats.get(&e) else {
            let span = self.expr(e).span;
            onsa_diag::internal::bug(Some(span), "the rate pass met an `at` the checker did not read")
        };
        if self.final_pass && r > k {
            let span = self.expr(e).span;
            return Err(self.err(
                Code::E0815,
                span,
                format!(
                    "this expression is at the clock `{}`, faster than `{}`; `at` cannot make a value slower (§11.3)",
                    r.name(),
                    k.name()
                ),
            ));
        }
        // A constant goes to every clock (§11.3).
        let held = r == FlowRate::Const || self.promotes_as_written(inner);
        if self.final_pass && r < k && !held {
            let span = self.expr(e).span;
            return Err(self.unsupported(span, Feature::ClockPromotion, &[]));
        }
        Ok(k)
    }

    /// Whether `e at k` with a faster `k` is held by this representation
    /// whatever the clock of `e`: a name or a literal, in parentheses or not,
    /// has its place, and nothing is computed at `k` (K-02). The E0813 note
    /// suggests `prev~(e at sample)` on the same ground.
    pub(super) fn promotes_as_written(&self, e: ExprId) -> bool {
        let mut x = e;
        while let ExprKind::Paren(i) = &self.expr(x).kind {
            x = *i;
        }
        matches!(self.expr(x).kind, ExprKind::Path(_) | ExprKind::Lit(_))
    }

    /// The omitted `init` of a delay (§11.4, S-29): `T.default()`, which this
    /// representation holds for a number (`0`, `+0.0`) only (K-02).
    pub(super) fn default_init(&mut self, ty: TyId, span: Span) -> Result<InitArg, super::RStop> {
        match self.a.types.get(ty) {
            Ty::Int(_) => Ok(InitArg::Const(ConstValue::Int(0))),
            Ty::Float(_) => Ok(InitArg::Const(ConstValue::Float(0.0))),
            _ => {
                let shown = self.display(ty);
                Err(self.unsupported(span, Feature::DefaultInit, &[&shown]))
            }
        }
    }

    /// `if~` / `match~` (§11.5): E0200 at the `~` (W7-06).
    pub(super) fn tilde_branches(&mut self, tilde: Span, form: FlowForm) -> super::RStop {
        self.unsupported(tilde, Feature::TildeBranches, &[&form.label()])
    }

    /// A stateful node at `span` (an instance, a delay, a `par`): E0200 in a
    /// branch, a guard, the right side of `&&` / `||` or a lazily evaluated
    /// argument of a builtin (K-08, W7-06).
    pub(super) fn stateful_here(&mut self, span: Span) -> Result<(), super::RStop> {
        if self.final_pass && self.branch > 0 {
            return Err(self.unsupported(span, Feature::StatefulInBranch, &[]));
        }
        Ok(())
    }

    /// Whether the right side of `op` is evaluated only for some values of
    /// the left (`&&`, `||`).
    pub(super) fn short_circuits(op: BinOp) -> bool {
        matches!(op, BinOp::And | BinOp::Or)
    }

    /// A call of a function that is not `rt`, read at `ctx` (the walk of
    /// S-05): the lowering evaluates the expression that holds it at `ctx`,
    /// in `process`. Hoisting computes the call at `init` (R-17, S-33,
    /// W7-05); until then it is E0200 above `init`.
    pub(super) fn non_rt_here(&mut self, e: ExprId, ctx: FlowRate) {
        if ctx <= FlowRate::Init {
            return;
        }
        let (Some(Target::Fn { def, .. }) | Some(Target::Method { def, .. })) = self.body.targets.get(&e) else {
            return;
        };
        if self.a.def(*def).as_fn().is_some_and(|f| !f.rt) {
            let span = self.expr(e).span;
            let _ = self.unsupported(span, Feature::NonRtCallAtClock, &[ctx.name()]);
        }
    }

    fn unsupported(&mut self, span: Span, feature: Feature, details: &[&str]) -> super::RStop {
        let found = self.src(span);
        self.fail(feature.diagnostic(Stage::Flow, span, details).with_found(found))
    }
}
