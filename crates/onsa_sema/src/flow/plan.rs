//! The plan of a flow (R-91 (1)): its stateful nodes in one flat table
//! ([`FlowInfo::nodes`]), each with the part of the body that holds it
//! ([`Owner`], by the tree of the body), its clock and the clocks its
//! arguments are read at. The walk of the clocks records the nodes and
//! their owners ([`super::nodes::NodeBuilder`]); [`build`] makes the table
//! of a walk with no diagnostic.

use super::clocks::Walked;
use super::nodes::Recorded;
use super::*;

mod fields;
pub(super) mod names;
mod stage;

pub use fields::{Field, FieldOf, Part};

/// The index of a node in [`FlowInfo::nodes`]: the one index of a node
/// outside the walk of the clocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NodeId(pub u32);

/// The part of the body that holds a node, by the tree of the body: the
/// initializer of the `let` k of [`FlowInfo::lets`], the output, or the
/// body of a `par~`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Owner {
    Let(u32),
    Output,
    Par(NodeId),
}

/// A vertex of the edges of the plan ([`FlowInfo::edges`]): a local read (an
/// input, a local of a `let`, the index of a `par~`, a binding of an arm), a
/// node, the initializer of the `let` k of [`FlowInfo::lets`], or the output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Vertex {
    Local(LocalId),
    Node(NodeId),
    Let(u32),
    Output,
}

/// An edge of the plan: `from` is read by `to`, the innermost node, `let`
/// or output that reads it (a node by the one that holds its call).
/// `lookback`: read a tick later, in the first argument of a delay (§11.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Edge {
    pub from: Vertex,
    pub to: Vertex,
    pub lookback: bool,
}

/// What a stateful node is (§11.4, §11.5).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PlanKind {
    Prev {
        arg: ExprId,
        init: InitArg,
        ty: TyId,
    },
    Delay {
        arg: ExprId,
        n: u32,
        init: InitArg,
        ty: TyId,
    },
    Vdelay {
        arg: ExprId,
        d: ExprId,
        max: u32,
        init: InitArg,
        ty: TyId,
    },
    Instance {
        callee: DefId,
        args: Vec<ExprId>,
        span: Span,
    },
    /// `par~ var in a..<b { body }` or `a..=b` (`end`, as written):
    /// `count` (one or more) replicas whose `var` is `from` (`a`) and up,
    /// with no end past the last (S-257, a last of `U32`'s maximum);
    /// `children` are the nodes its body holds, in the order of the table,
    /// and `fields` the fields of its replica (none: it has no state).
    Par {
        var: LocalId,
        from: u32,
        count: u32,
        end: RangeEnd,
        body: ExprId,
        children: Vec<NodeId>,
        fields: Vec<Field>,
    },
}

impl PlanKind {
    /// The built-in delay of the node, if it is one.
    pub fn delay(&self) -> Option<Delay> {
        match self {
            PlanKind::Prev { .. } => Some(Delay::Prev),
            PlanKind::Delay { .. } => Some(Delay::Fixed),
            PlanKind::Vdelay { .. } => Some(Delay::Variable),
            PlanKind::Instance { .. } | PlanKind::Par { .. } => None,
        }
    }
}

/// A stateful node of a flow body.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlanNode {
    /// The call or the `par~` expression.
    pub expr: ExprId,
    pub kind: PlanKind,
    pub owner: Owner,
    /// The clock of the node: of a delay its output, of an instance the
    /// output of the callee in the frame of the call, of a `par~` its
    /// expression's.
    pub clock: Clock,
    /// The arguments and the clocks they are read at (none of a `par~`).
    pub args: Vec<ArgRead>,
    /// The name in the part of the body that holds it (§11.6): the name of
    /// the `let` of a single name whose whole value it is, else `<kind>_<n>`
    /// (`prev_0`), numbered per kind in that part in the order of the text.
    pub name: String,
    /// The name shown (§11.6, spec/tools.md §1.1): the name after the
    /// scope of that part (`a.prev_0`, `_out.lp_0`, `m.par_0.lp_0`), or the
    /// name of the `let` whose whole value it is.
    pub path: String,
    /// It is the whole value of the `let` that holds it and has its name
    /// ([`FlowInfo::whole`]).
    pub whole: bool,
    pub span: Span,
    /// The place of its first field in the struct that holds it
    /// ([`FlowInfo::fields_of`]); none of a `par~` with no state.
    pub field: Option<u32>,
}

/// A value of the body the state may keep beside its nodes (S-05).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kept {
    Local(LocalId),
    /// The value of `sample_rate()`, of the stage `init`.
    SampleRate,
}

/// The nodes each `let` and the output hold, in the order of the table:
/// made once with the table ([`build`]), with the `children` of each `par~`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct Roots {
    lets: Vec<Vec<NodeId>>,
    output: Vec<NodeId>,
}

impl FlowInfo {
    /// Whether the state keeps `v` (S-05, §11.3): it is read at a stage
    /// that is not its own (the `let`s of a constant have none and are
    /// defined in each phase that reads them). The one place of the
    /// judgement: [`FlowLet::state`] and the fields of the plan read it.
    pub fn stored(&self, v: Kept) -> bool {
        match v {
            Kept::Local(l) => {
                let own = self.clocks.locals.get(&l).and_then(|c| c.stage());
                let reads = self.read_at.get(&l).into_iter().flatten();
                own.is_some_and(|own| reads.into_iter().any(|&s| s != own))
            }
            Kept::SampleRate => self.sample_rate_at.is_some_and(|s| s != ClockStage::Init),
        }
    }

    pub fn node(&self, id: NodeId) -> &PlanNode {
        &self.nodes[id.0 as usize]
    }

    /// The nodes `owner` holds itself (not those of a `par~` in it), in the
    /// order of the table.
    pub fn roots(&self, owner: Owner) -> &[NodeId] {
        match owner {
            Owner::Let(k) => self.roots.lets.get(k as usize).map_or(&[], Vec::as_slice),
            Owner::Output => &self.roots.output,
            Owner::Par(p) => match &self.node(p).kind {
                PlanKind::Par { children, .. } => children,
                _ => &[],
            },
        }
    }

    /// The node that is the whole value of the `let` k and has its name
    /// (S-148, §11.6): of a `let` of a single name, through parentheses.
    pub fn whole(&self, k: u32) -> Option<NodeId> {
        self.roots(Owner::Let(k)).iter().copied().find(|&id| self.node(id).whole)
    }

    /// The scope of each `let` (§11.6, S-1136): its first name, or `_<m>`
    /// when it binds none. Of its nodes and its hoisted fields, and its
    /// vertex in `onsa graph` (S-1169).
    pub fn let_scopes(&self) -> Vec<String> {
        names::scopes(self.lets.iter().map(|l| l.locals.as_slice()), &self.body)
    }

    /// The nodes no `par~` holds: of each `let` in their order, then of the
    /// output.
    pub fn top(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.roots.lets.iter().flatten().chain(&self.roots.output).copied()
    }
}

/// The table of the nodes of `info` from the nodes the walk `w` recorded,
/// in the order of their [`NodeId`]s, with the clocks the walk gave them;
/// the table of the subexpressions the marking hoisted (`hoisted`, of the
/// module of `ast`); and the fields of the state.
pub(super) fn build(
    info: &mut FlowInfo,
    recorded: Vec<Recorded>,
    w: &Walked,
    ast: &onsa_syntax::ast::Ast,
    hoisted: Vec<(ExprId, ClockStage, Owner, bool)>,
) {
    let mut roots = Roots { lets: vec![Vec::new(); info.lets.len()], output: Vec::new() };
    let mut children = vec![Vec::new(); recorded.len()];
    for (i, r) in recorded.iter().enumerate() {
        let id = NodeId(i as u32);
        let list = match r.owner {
            Owner::Let(k) => roots.lets.get_mut(k as usize),
            Owner::Output => Some(&mut roots.output),
            Owner::Par(p) => children.get_mut(p.0 as usize),
        };
        let Some(list) = list else { onsa_diag::internal::bug(Some(r.span), "a node of an owner the flow has not") };
        list.push(id);
    }
    let nodes = recorded.into_iter().zip(children).map(|(r, ch)| {
        let (clock, args) = match (w.node_of.get(&r.expr), info.clocks.exprs.get(&r.expr)) {
            (Some(&k), _) => (w.nodes[k].clock, w.nodes[k].args.clone()),
            (None, Some(&c)) => (c, Vec::new()),
            (None, None) => onsa_diag::internal::bug(Some(r.span), "a node the walk gave no clock"),
        };
        let kind = match r.kind {
            PlanKind::Par { var, from, count, end, body, fields, .. } => {
                PlanKind::Par { var, from, count, end, body, children: ch, fields }
            }
            kind => kind,
        };
        PlanNode {
            expr: r.expr,
            kind,
            owner: r.owner,
            clock,
            args,
            name: r.name,
            path: r.path,
            whole: r.whole,
            span: r.span,
            field: None,
        }
    });
    info.nodes = nodes.collect();
    info.node_of = info.nodes.iter().enumerate().map(|(i, n)| (n.expr, NodeId(i as u32))).collect();
    info.roots = roots;
    super::hoist::table(info, ast, hoisted);
    fields::build(info);
}

#[cfg(test)]
mod tests;
