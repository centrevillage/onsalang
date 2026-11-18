//! The plan of a flow (R-91 (1)): its stateful nodes in one flat table
//! ([`FlowInfo::nodes`]), each with the part of the body that holds it
//! ([`Owner`], by the tree of the body), its clock and the clocks its
//! arguments are read at. The walk of the clocks records the nodes and
//! their owners ([`super::nodes::NodeBuilder`]); [`build`] makes the table
//! of a walk with no diagnostic.

use super::clocks::Walked;
use super::nodes::Recorded;
use super::*;

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
    /// `par~ var in from..<to { body }`; `children` are the nodes its body
    /// holds, in the order of the table.
    Par {
        var: LocalId,
        from: u32,
        to: u32,
        body: ExprId,
        children: Vec<NodeId>,
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
    /// The S-06 name: the `let` name when the node is the whole initializer,
    /// otherwise `<kind>_<n>`, numbered per kind over the whole body in the
    /// order the walk finishes the nodes.
    pub name: String,
}

/// The nodes each `let` and the output hold, in the order of the table:
/// made once with the table ([`build`]), with the `children` of each `par~`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct Roots {
    lets: Vec<Vec<NodeId>>,
    output: Vec<NodeId>,
}

impl FlowInfo {
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

    /// The nodes no `par~` holds: of each `let` in their order, then of the
    /// output.
    pub fn top(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.roots.lets.iter().flatten().chain(&self.roots.output).copied()
    }
}

/// The table of the nodes of `info` from the nodes the walk `w` recorded,
/// in the order of their [`NodeId`]s, with the clocks the walk gave them.
pub(super) fn build(info: &mut FlowInfo, recorded: Vec<Recorded>, w: &Walked) {
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
        let (clock, args) = match (w.node_of.get(&r.expr), w.info.exprs.get(&r.expr)) {
            (Some(&k), _) => (w.nodes[k].clock, w.nodes[k].args.clone()),
            (None, Some(&c)) => (c, Vec::new()),
            (None, None) => onsa_diag::internal::bug(Some(r.span), "a node the walk gave no clock"),
        };
        let kind = match r.kind {
            PlanKind::Par { var, from, to, body, .. } => PlanKind::Par { var, from, to, body, children: ch },
            kind => kind,
        };
        PlanNode { expr: r.expr, kind, owner: r.owner, clock, args, name: r.name }
    });
    info.nodes = nodes.collect();
    info.node_of = info.nodes.iter().enumerate().map(|(i, n)| (n.expr, NodeId(i as u32))).collect();
    info.roots = roots;
}

#[cfg(test)]
mod tests;
