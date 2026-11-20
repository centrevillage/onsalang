//! The record of the stateful nodes of a flow body (§11.4, §11.5, S-06):
//! their names, their owners and the nesting of `par~`, apart from the
//! clocks, and who reads what (the edges of the plan). The walk of the
//! clocks records a node where it meets its call, before its arguments; the
//! plan ([`super::plan::build`]) makes the table of the record.

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::Ast;

use super::plan::{Edge, NodeId, Owner, PlanKind, Vertex, names};
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
    pub(super) arms: Vec<(ExprId, u32)>,
}

/// The record of the nodes of a flow body while a walk goes through it. It
/// knows no clock.
///
/// The walk of the clocks calls it at stage 2 in the order of the source:
/// - [`NodeBuilder::owner`] before each `let` and the output;
/// - [`NodeBuilder::node`] at a delay or an instance call, before the walk
///   of its arguments, and [`NodeBuilder::leave_node`] after it;
/// - at `par~`, [`NodeBuilder::enter_par`] before the body and
///   [`NodeBuilder::leave_par`] after it, even when the body stopped;
/// - [`NodeBuilder::read`] at each read of a local, and
///   [`NodeBuilder::lookback`] around the first argument of a delay;
/// - [`NodeBuilder::enter_arm`] before the body of an arm of `match~` and
///   [`NodeBuilder::leave_arm`] after it;
/// - [`NodeBuilder::finish`] at the end, for the plan.
///
/// So the nodes come in the order the names of their calls come in the
/// text (the outer call first), which numbers them (§11.6, [`names`]), and
/// the edges in the order of the reads, a node's before its arguments'.
pub(super) struct NodeBuilder {
    nodes: Vec<Recorded>,
    /// The owner of the nodes recorded now: the `let` or the output walked,
    /// then each `par~` entered.
    owners: Vec<Owner>,
    namer: names::Namer,
    /// The vertices around the place walked now, the innermost last, each
    /// with whether what it reads is read a tick later.
    readers: Vec<(Vertex, bool)>,
    edges: Vec<Edge>,
    seen: HashSet<Edge>,
    /// The arms of the `match~`s around the place walked now.
    arms: Vec<(ExprId, u32)>,
}

impl NodeBuilder {
    pub(super) fn new(pending: &[PendingLet], ast: &Ast, body: &BodyInfo) -> NodeBuilder {
        let namer = names::Namer::new(pending, ast, body);
        let (readers, edges, seen) = (Vec::new(), Vec::new(), HashSet::default());
        NodeBuilder { nodes: Vec::new(), owners: Vec::new(), namer, readers, edges, seen, arms: Vec::new() }
    }

    /// [`names::Namer::apart`].
    pub(super) fn apart(&mut self, init: ExprId) {
        self.namer.apart(init);
    }

    /// The `par~`s around the place walked now, the outermost first.
    pub(super) fn pars(&self) -> Vec<NodeId> {
        self.owners.iter().filter_map(|o| if let Owner::Par(p) = o { Some(*p) } else { None }).collect()
    }

    /// The nodes recorded next are in the arm `arm` of the `match~` `m`,
    /// until [`NodeBuilder::leave_arm`].
    pub(super) fn enter_arm(&mut self, m: ExprId, arm: u32) {
        self.arms.push((m, arm));
    }

    pub(super) fn leave_arm(&mut self) {
        self.arms.pop();
    }

    /// The nodes of the body, in the order of their [`NodeId`]s, and the
    /// edges in the order of the text.
    pub(super) fn finish(self) -> (Vec<Recorded>, Vec<Edge>) {
        (self.nodes, self.edges)
    }

    /// The nodes recorded next are of `owner`, a `let` or the output, which
    /// reads what is walked next.
    pub(super) fn owner(&mut self, owner: Owner) {
        let reader = match owner {
            Owner::Let(k) => Vertex::Let(k),
            Owner::Output => Vertex::Output,
            Owner::Par(_) => onsa_diag::internal::bug(None, "a `par~` as the owner of a `let`"),
        };
        self.owners = vec![owner];
        self.readers = vec![(reader, false)];
    }

    /// `from` is read by the innermost reader around, once.
    fn edge(&mut self, from: Vertex, span: Option<Span>) {
        let Some(&(to, lookback)) = self.readers.last() else {
            onsa_diag::internal::bug(span, "a read outside a `let` and the output")
        };
        let edge = Edge { from, to, lookback };
        if self.seen.insert(edge) {
            self.edges.push(edge);
        }
    }

    /// The local `l` read at `span`.
    pub(super) fn read(&mut self, l: LocalId, span: Span) {
        self.edge(Vertex::Local(l), Some(span));
    }

    /// What is read next is read a tick later (`on`), in the first argument
    /// of a delay (§11.4), or no longer.
    pub(super) fn lookback(&mut self, on: bool) {
        if let Some(r) = self.readers.last_mut() {
            r.1 = on;
        }
    }

    /// The node `id` reads what is walked next; a node not the whole value
    /// of its `let` is read by the reader around it.
    fn enter(&mut self, id: NodeId, whole: bool, span: Span) {
        if !whole {
            self.edge(Vertex::Node(id), Some(span));
        }
        self.readers.push((Vertex::Node(id), false));
    }

    /// The end of the arguments of the node recorded last that is not left.
    pub(super) fn leave_node(&mut self) {
        self.readers.pop();
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
        let arms = self.arms.clone();
        self.nodes.push(Recorded { expr: e, span, kind, owner, name, path, whole, arms });
        self.enter(id, whole, span);
        id
    }

    /// The node of the delay or the instance call `e` at `span`. The `init`
    /// of a delay is the written one, else the [`default_init`] of its type,
    /// whose E0816 is the error.
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
                    (None, None) => default_init(a, ty, span, delay)?,
                };
                // A length the check does not compute (held) is read by no plan.
                let len = len.unwrap_or_default();
                match (delay, d_e) {
                    (Delay::Prev, _) => PlanKind::Prev { arg, init, ty },
                    (Delay::Fixed, _) => PlanKind::Delay { arg, n: len, init, ty },
                    (Delay::Variable, Some(d)) => PlanKind::Vdelay { arg, d, max: len, init, ty },
                    (Delay::Variable, None) => onsa_diag::internal::bug(Some(span), "a `vdelay~` without its `d`"),
                }
            }
        };
        let of = names::kind(a, &call.kind).to_string();
        self.push(e, span, kind, &of);
        Ok(())
    }

    /// The `par~` of `count` replicas of `var` from `from`, of a range with
    /// `end` (§11.5), at `e` and `span`, whose `body` holds state if `state`
    /// ([`holds_state`]): its node, and the nodes recorded next are of its
    /// body.
    pub(super) fn enter_par(
        &mut self,
        e: ExprId,
        span: Span,
        var: LocalId,
        (from, count, end): (u32, u32, RangeEnd),
        (body, state): (ExprId, bool),
    ) {
        let (children, fields) = (Vec::new(), Vec::new());
        let kind = PlanKind::Par { var, from, count, end, body, state, children, fields };
        let id = self.push(e, span, kind, PAR);
        self.owners.push(Owner::Par(id));
    }

    /// The end of the body of the `par~` `e` entered last.
    pub(super) fn leave_par(&mut self, e: ExprId, span: Span) {
        if !self.owners.pop().is_some_and(|o| matches!(o, Owner::Par(p) if self.nodes[p.0 as usize].expr == e)) {
            onsa_diag::internal::bug(Some(span), "a `par~` left that was not entered")
        }
        self.leave_node();
    }
}

/// Whether `e` holds state in its text (§11.5, S-1177): a call with `~`, an
/// instance (a modifier too) or a built-in delay, in a replication in it
/// too, whatever the `~` written on it. The one predicate of whether a
/// replication is a `par~` or a `par`, and of its name ([`names::Namer`]).
/// Linear in `e`.
pub(in crate::flow) fn holds_state(ast: &Ast, e: ExprId) -> bool {
    let mut todo = vec![e];
    while let Some(x) = todo.pop() {
        if let ExprKind::Call { kind: CallKind::Flow, .. } = ast.expr(x).kind {
            return true;
        }
        todo.extend(ast.sub_exprs(x));
    }
    false
}

/// The omitted `init` of the delay `of` (§11.4, S-29): `T.default()`, a
/// literal for a number (`0`, `+0.0`), else made of the type in Core, and
/// the E0816 of a type that does not satisfy `Default`
/// ([`crate::signal::no_default_signal`]). A value of the error type is not
/// known, so no diagnostic (§18.1, R-271).
pub(super) fn default_init(a: &Analysis, ty: TyId, span: Span, of: Delay) -> Result<InitArg, Diagnostic> {
    match a.types.get(ty) {
        Ty::Int(_) | Ty::Error => Ok(InitArg::Const(ConstValue::Int(0))),
        Ty::Float(_) => Ok(InitArg::Const(ConstValue::Float(0.0))),
        _ => match crate::signal::no_default_signal(
            a,
            ty,
            span,
            &format!("the omitted `init` of `{}~`", of.name()),
            "§11.4",
        ) {
            Some(d) => Err(d),
            None => Ok(InitArg::Default),
        },
    }
}
