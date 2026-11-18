//! The flow syntax of version 0.3 written in the terms of this version's
//! flow checks (W3-10, K-02 (a)): the clocks `at` (S-102, S-359), the
//! feedback references `^name` and the built-in delays `prev~` / `delay~` /
//! `vdelay~` with their optional `init` (S-44, S-29), and `if~` / `match~`
//! (S-110). The checks keep their representation (the nodes of
//! [`super::Node`] and [`super::InitArg`]); this module holds the typing of
//! `at` and `^name`, which W7-02 U3 moves to `flow/check.rs`. The names of
//! the clocks and of the delays stay (`crate::flow_names`,
//! [`crate::clock::ClockName::name`]).
//!
//! What the representation cannot hold is E0200, never read in another
//! meaning (plan §8.2), in the walk of the clocks (`flow/clocks.rs`): a
//! computed expression made faster with `at` (W7-05), `if~` / `match~`
//! (W7-06); a call of a function that is not `rt` above `init` (R-17) is the
//! state marking's (`flow/reads.rs`, W7-05); the omitted `init` of a value
//! type that is no number is the nodes' (`flow/nodes.rs`, W7-07), and a `^`
//! inside a `par` (R-03) is the names stage's (`names/body/flow_order.rs`).
//! So are the forms that the representation reads wrongly until W7 (K-08):
//! a delay inside the first argument of a delay (R-13, W7-07), a stateful
//! node in a branch, a guard, the right side of `&&` / `||` or an argument a
//! builtin evaluates on some paths only (S-110, W7-06).
//!
//! What serves them outside this file, and goes with their works:
//! - `flow.rs`: the field `delay_arg` of `FlowCx`, and its counting in
//!   `flow/check.rs` (`check_delay`), with the arms of `At` and `Feedback`
//!   in `check_flow_expr`. `flow/clocks.rs`: the depth of the branches of
//!   the walk (`If`, `Match`, `Binary`). `flow/reads.rs`: the arm of
//!   `Feedback` in `mark`.
//! - `body.rs`: the arms of `tilde` of `If` / `Match` (typed as plain in a
//!   flow, E0200 outside).
//! - `onsa_diag/src/unsupported.rs`: the features of the E0200 of the flow
//!   checks and of `NestedDelays` (the works named on each).
//! - `onsa_core` (`lower/body/expr.rs` `At`): the arms of `At` / `Feedback`.
//!   The modes stage (`modes/walk.rs`), `mark` and `onsa_driver/graph.rs` have
//!   no arm of `At`: they reach its operand through `onsa_syntax`'s `Ast::sub_exprs`, the one
//!   plain enumeration of the children, which keeps its arms while the AST has
//!   the forms.
//!
//! The optional `init` of a delay (`NodeCall.init_expr`) stays: W7-07 gives
//! the omitted one its value `T.default()`.

use onsa_syntax::ast::ExprId;

use crate::body::{Checker, LocalId, R, Target};
use crate::names::body::PathRes;
use crate::ty::TyId;

impl Checker<'_> {
    /// `e at k` in a flow body (§11.3): the type of `e`; the clock is the
    /// names stage's record ([`crate::names::body::BodyNames::clocks`]), which
    /// the walk of the clocks reads.
    pub(super) fn check_at(&mut self, e: ExprId, inner: ExprId, expected: Option<TyId>) -> R<TyId> {
        let t = self.check_expr_as(inner, expected, self.joining)?;
        self.names_record(e, self.names.clocks.get(&e).copied())?;
        Ok(t)
    }

    /// `^name` in a flow body (§11.2): a later `let` of the body, read in the
    /// first argument of a delay, as the names stage recorded it (its E0801,
    /// E0020 and the E0200 in a `par`, `names/body/flow_order.rs`).
    pub(super) fn check_feedback(&mut self, e: ExprId) -> R<TyId> {
        let record = match self.names.paths.get(&e) {
            Some(&PathRes::Local(b)) => Some(LocalId(b.0)),
            _ => None,
        };
        let id = self.names_record(e, record)?;
        self.info.targets.insert(e, Target::Local(id));
        Ok(self.local_ty(id))
    }

    /// The record `r` of the names stage at the node `e` of a flow body: none
    /// where it stopped before it with no diagnostic (§18.1, S-692).
    fn names_record<T>(&mut self, e: ExprId, r: Option<T>) -> R<T> {
        match r {
            Some(r) => Ok(r),
            None if !self.names.complete => Err(self.held_stop()),
            None => onsa_diag::internal::bug(
                Some(self.expr(e).span),
                "a node of a flow body the names stage did not record",
            ),
        }
    }
}
