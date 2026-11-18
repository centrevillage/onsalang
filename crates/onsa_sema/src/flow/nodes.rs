//! The record of the stateful nodes of a flow body (§11.4, §11.5, S-06):
//! their names, their owners and the nesting of `par~`, apart from the
//! clocks. The walk of the clocks records a node where it meets its call,
//! before its arguments; the plan ([`super::plan::build`]) makes the table
//! of the record.

use onsa_syntax::ast::Ast;

use super::plan::{NodeId, Owner, PlanKind, names};
use super::*;
use crate::flow_names::PAR;

/// A node the walk recorded: a [`super::PlanNode`] before its clock, in the
/// order of its [`NodeId`].
#[derive(Debug, Clone)]
pub(super) struct Recorded {
    pub(super) expr: ExprId,
    pub(super) span: Span,
    pub(super) kind: PlanKind,
    pub(super) owner: Owner,
    pub(super) name: String,
    pub(super) path: String,
    pub(super) whole: bool,
}

/// The record of the nodes of a flow body while a walk goes through it. It
/// knows no clock.
///
/// The walk of the clocks calls it at stage 2 in the order of the source:
/// - [`NodeBuilder::owner`] before each `let` and the output;
/// - [`NodeBuilder::node`] at a delay or an instance call, before the walk
///   of its arguments;
/// - at `par~`, [`NodeBuilder::enter_par`] before the body and
///   [`NodeBuilder::leave_par`] after it, even when the body stopped;
/// - [`NodeBuilder::finish`] at the end, for the plan.
///
/// So the nodes come in the order the names of their calls come in the
/// text (the outer call first), which numbers them (§11.6, [`names`]).
pub(super) struct NodeBuilder {
    nodes: Vec<Recorded>,
    /// The owner of the nodes recorded now: the `let` or the output walked,
    /// then each `par~` entered.
    owners: Vec<Owner>,
    namer: names::Namer,
}

impl NodeBuilder {
    pub(super) fn new(pending: &[PendingLet], ast: &Ast, body: &BodyInfo) -> NodeBuilder {
        NodeBuilder { nodes: Vec::new(), owners: Vec::new(), namer: names::Namer::new(pending, ast, body) }
    }

    /// The nodes of the body, in the order of their [`NodeId`]s.
    pub(super) fn finish(self) -> Vec<Recorded> {
        self.nodes
    }

    /// The nodes recorded next are of `owner`, a `let` or the output.
    pub(super) fn owner(&mut self, owner: Owner) {
        self.owners = vec![owner];
    }

    /// The node `e` of `kind` at `span`, its name and its path (§11.6).
    fn push(&mut self, e: ExprId, span: Span, kind: PlanKind, of: &str) -> NodeId {
        let Some(&owner) = self.owners.last() else { onsa_diag::internal::bug(Some(span), "a node of no owner") };
        let par = match owner {
            Owner::Par(p) => self.nodes.get(p.0 as usize).map(|n| n.path.as_str()),
            Owner::Let(_) | Owner::Output => None,
        };
        let Some((name, path)) = self.namer.name(e, owner, of, par) else {
            onsa_diag::internal::bug(Some(span), "a node of a part the body has not")
        };
        let id = NodeId(self.nodes.len() as u32);
        let whole = self.namer.whole(e);
        self.nodes.push(Recorded { expr: e, span, kind, owner, name, path, whole });
        id
    }

    /// The node of the delay or the instance call `e` at `span`. The `init`
    /// of a delay is the written one, else the [`default_init`] of its type,
    /// whose E0200 is the error.
    pub(super) fn node(
        &mut self,
        a: &Analysis,
        body: &BodyInfo,
        e: ExprId,
        call: &NodeCall,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let kind = match call.kind {
            NodeKind::Instance(callee) => PlanKind::Instance { callee, args: call.args.clone(), span },
            NodeKind::Delay(delay, len) => {
                let (arg, d_e, init_e) = call.delay_parts();
                let ty = body.expr_types.get(&e).copied().unwrap_or(call.ty);
                let init = match (&call.init, init_e) {
                    (Some(init), _) => init.clone(),
                    (None, Some(init_e)) => InitArg::Init(init_e),
                    (None, None) => default_init(a, ty, span)?,
                };
                match (delay, d_e) {
                    (Delay::Prev, _) => PlanKind::Prev { arg, init, ty },
                    (Delay::Fixed, _) => PlanKind::Delay { arg, n: len, init, ty },
                    (Delay::Variable, Some(d)) => PlanKind::Vdelay { arg, d, max: len, init, ty },
                    (Delay::Variable, None) => onsa_diag::internal::bug(Some(span), "a `vdelay~` without its `d`"),
                }
            }
        };
        let of = names::kind(a, &kind).to_string();
        self.push(e, span, kind, &of);
        Ok(())
    }

    /// `par~ var in from..<to { body }` (§11.5) at `e` and `span`: its node,
    /// and the nodes recorded next are of its body.
    pub(super) fn enter_par(&mut self, e: ExprId, span: Span, var: LocalId, from: u32, to: u32, body: ExprId) {
        let kind = PlanKind::Par { var, from, to, body, children: Vec::new(), fields: Vec::new() };
        let id = self.push(e, span, kind, PAR);
        self.owners.push(Owner::Par(id));
    }

    /// The end of the body of the `par~` `e` entered last.
    pub(super) fn leave_par(&mut self, e: ExprId, span: Span) {
        if !self.owners.pop().is_some_and(|o| matches!(o, Owner::Par(p) if self.nodes[p.0 as usize].expr == e)) {
            onsa_diag::internal::bug(Some(span), "a `par~` left that was not entered")
        }
    }
}

/// The omitted `init` of a delay (§11.4, S-29): `T.default()`, which this
/// representation holds for a number (`0`, `+0.0`) only (K-02, W7-07). A
/// value of the error type is not known, so no diagnostic (§18.1, R-271).
pub(super) fn default_init(a: &Analysis, ty: TyId, span: Span) -> Result<InitArg, Diagnostic> {
    match a.types.get(ty) {
        Ty::Int(_) | Ty::Error => Ok(InitArg::Const(ConstValue::Int(0))),
        Ty::Float(_) => Ok(InitArg::Const(ConstValue::Float(0.0))),
        _ => {
            let shown = a.display_type(ty);
            Err(Feature::DefaultInit.diagnostic(Stage::Flow, span, &[&shown]))
        }
    }
}
