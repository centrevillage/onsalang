//! The record of the stateful nodes of a flow body (§11.4, §11.5, S-06):
//! their names, their owners and the nesting of `par~`, apart from the
//! clocks. The walk of the clocks checks a node first and then records it
//! here; the plan ([`super::plan::build`]) makes the table of the record.

use super::plan::{NodeId, Owner, PlanKind};
use super::*;

/// A node the walk recorded: a [`super::PlanNode`] before its clock, in the
/// order of its [`NodeId`].
#[derive(Debug, Clone)]
pub(super) struct Recorded {
    pub(super) expr: ExprId,
    pub(super) span: Span,
    pub(super) kind: PlanKind,
    pub(super) owner: Owner,
    pub(super) name: String,
}

/// The record of the nodes of a flow body while a walk goes through it. It
/// knows no clock.
///
/// The walk of the clocks calls it at stage 2 in the order of the source:
/// - [`NodeBuilder::owner`] before each `let` and the output;
/// - [`NodeBuilder::node`] at a delay or an instance call, after the checks
///   of its clocks;
/// - at `par~`, [`NodeBuilder::enter_par`] before the body, which takes the
///   slot of the `par~` before the nodes of its body, and
///   [`NodeBuilder::leave_par`] after it, even when the body stopped;
/// - [`NodeBuilder::finish`] at the end, for the plan.
///
/// The names are numbered per kind in the order the nodes are finished (a
/// `par~` after its body, S-06).
pub(super) struct NodeBuilder {
    nodes: Vec<Recorded>,
    /// The owner of the nodes recorded now: the `let` or the output walked,
    /// then each `par~` entered.
    owners: Vec<Owner>,
    counters: HashMap<String, u32>,
    let_names: HashMap<ExprId, String>,
}

impl NodeBuilder {
    /// The node of the whole initializer of a `let` of a single name takes
    /// that name (S-06).
    pub(super) fn new(pending: &[PendingLet]) -> NodeBuilder {
        let let_names = pending.iter().filter_map(|p| Some((p.init, p.name.clone()?))).collect();
        NodeBuilder { nodes: Vec::new(), owners: Vec::new(), counters: HashMap::default(), let_names }
    }

    /// The nodes of the body, in the order of their [`NodeId`]s.
    pub(super) fn finish(self) -> Vec<Recorded> {
        self.nodes
    }

    /// The nodes recorded next are of `owner`, a `let` or the output.
    pub(super) fn owner(&mut self, owner: Owner) {
        self.owners = vec![owner];
    }

    fn next_name(&mut self, kind: &str) -> String {
        let n = self.counters.entry(kind.to_string()).or_insert(0);
        let name = format!("{kind}_{n}");
        *n += 1;
        name
    }

    fn push(&mut self, expr: ExprId, span: Span, kind: PlanKind, name: String) -> NodeId {
        let Some(&owner) = self.owners.last() else { onsa_diag::internal::bug(Some(span), "a node of no owner") };
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(Recorded { expr, span, kind, owner, name });
        id
    }

    fn node_name(&mut self, e: ExprId, kind: &str) -> String {
        match self.let_names.get(&e) {
            Some(n) => n.clone(),
            None => self.next_name(kind),
        }
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
        let (kind, name) = match call.kind {
            NodeKind::Instance(callee) => {
                let name = self.node_name(e, &a.def(callee).name);
                (PlanKind::Instance { callee, args: call.args.clone(), span }, name)
            }
            NodeKind::Delay(delay, len) => {
                let arg = call.args[0];
                let d_e = call.d();
                let ty = body.expr_types.get(&e).copied().unwrap_or(call.ty);
                let init = match (&call.init, call.init_expr) {
                    (Some(init), _) => init.clone(),
                    (None, Some(init_e)) => InitArg::Init(init_e),
                    (None, None) => default_init(a, ty, span)?,
                };
                let name = self.node_name(e, delay.name());
                let kind = match (delay, d_e) {
                    (Delay::Prev, _) => PlanKind::Prev { arg, init, ty },
                    (Delay::Fixed, _) => PlanKind::Delay { arg, n: len, init, ty },
                    (Delay::Variable, Some(d)) => PlanKind::Vdelay { arg, d, max: len, init, ty },
                    (Delay::Variable, None) => onsa_diag::internal::bug(Some(span), "a `vdelay~` without its `d`"),
                };
                (kind, name)
            }
        };
        self.push(e, span, kind, name);
        Ok(())
    }

    /// `par~ var in from..<to { body }` (§11.5) at `e` and `span`: its slot,
    /// and the nodes recorded next are of its body.
    pub(super) fn enter_par(&mut self, e: ExprId, span: Span, var: LocalId, from: u32, to: u32, body: ExprId) {
        let kind = PlanKind::Par { var, from, to, body, children: Vec::new(), fields: Vec::new() };
        let id = self.push(e, span, kind, String::new());
        self.owners.push(Owner::Par(id));
    }

    /// The end of the body of the `par~` `e` entered last, which takes its
    /// name.
    pub(super) fn leave_par(&mut self, e: ExprId, span: Span) {
        let Some(Owner::Par(id)) =
            self.owners.pop().filter(|o| matches!(o, Owner::Par(p) if self.nodes[p.0 as usize].expr == e))
        else {
            onsa_diag::internal::bug(Some(span), "a `par~` left that was not entered")
        };
        let name = self.node_name(e, "par");
        self.nodes[id.0 as usize].name = name;
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
