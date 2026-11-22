//! The plan of a flow (R-91 (1)): its stateful nodes in one flat table
//! ([`FlowInfo::nodes`]), each with the part of the body that holds it
//! ([`Owner`], by the tree of the body), its clock and the clocks its
//! arguments are read at. The walk of the clocks records the nodes and
//! their owners ([`super::nodes::NodeBuilder`]); [`build`] makes the table
//! of a walk with no diagnostic.

use super::clocks::Walked;
use super::nodes::Recorded;
use super::*;
use crate::clock::Ratio;
use crate::flow_names::Modifier;

pub(super) mod bounds;
pub(crate) mod entries;
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
    /// `state`: its body holds state (a `par~`, §11.5, S-1177), the one
    /// judgement of it; the replicas of a `par` have no node to set, reset
    /// or run.
    Par {
        var: LocalId,
        from: u32,
        count: u32,
        end: RangeEnd,
        body: ExprId,
        state: bool,
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
    /// The arms of the `match~`s around it, the outermost first (S-1131).
    pub arms: Vec<(ExprId, u32)>,
    /// The ratio of the ports of its callee as this flow reads them over
    /// the `sample` of the body (§11.9): of the head of a chain, the sum of
    /// the ratios of the chain, else 0: the frame the walk read the clocks
    /// of its arguments and its output in. Not the stages it runs in nor
    /// its time, which are of each boundary ([`PlanNode::bounds`],
    /// [`PlanNode::runs`]; S-1207).
    pub frame: Ratio,
    /// The modifiers after its call, in the order they are written (§11.9,
    /// §11.10): its chain, none of a node with no modifier.
    pub chain: Vec<PlanModifier>,
    /// The sum of the exponents of the N of its chain, either way (§11.9,
    /// S-1089), counted once by the check of the chain.
    pub size: u32,
    /// The boundaries of its chain, inner first (§11.9, S-1207): one of
    /// each `.down~(N)` and `.up~(N)` of `chain`; none of a chain with an N
    /// in error.
    pub bounds: Vec<PlanBound>,
    /// Of an instance, the runs of the stages of the body of its callee
    /// (§11.9, S-1088), its stages slowest first, then `sample`; none of
    /// another node, and of an instance whose callee has no table (in
    /// error, in a loop of calls). Made by the walk of the table
    /// ([`entries`]). Of a chain, only the stage of this flow each stage of
    /// its head runs in: how many times and at which time are of its
    /// `bounds`.
    pub runs: Vec<Run>,
    /// Of an instance, its callee reads the time ([`FlowInfo::reads_time`]),
    /// recorded by the walk of the table ([`entries`]) for the gate of a
    /// chain ([`PlanNode::lowered_chain`]); U6a3 of W7-16 lifts it (S-1217).
    pub timed: bool,
}

/// A boundary of a chain (§11.9, §11.10, S-1207): a `.down~(N)` or an
/// `.up~(N)` of it, which runs the part it wraps (the head and the
/// modifiers inside it) as one part in the frame of its own caller, and
/// gathers and deals at the ports of that part. Its ports are of the
/// record ([`bounds::bounds`]), its stages of the walk of the table
/// ([`entries`]): the fields and the Core read them, not the ratios.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlanBound {
    /// Its modifier, by its place in the `chain` of the node (its ratio is
    /// `chain[at].ratio`).
    pub at: u32,
    /// The exponent of each input of the part it wraps, in the frame that
    /// part is called in (`sample * 2^k`); none of a parameter kind.
    pub ins: Vec<Option<Ratio>>,
    /// The exponent of the output of that part.
    pub out: Option<Ratio>,
    /// The inputs it gathers (a `.down~` of an input of the part faster than
    /// its `sample`), each by its index with the stage of its caller that
    /// writes its ring.
    pub gathers: Vec<(u32, ClockStage)>,
    /// It deals the output of the part (a `.down~` of an output faster than
    /// its `sample`), at its own tick.
    pub deals: bool,
    /// Each stage of the caller of the part (slowest first) with the stage
    /// of its own caller that runs it ([`bounds::step`]).
    pub maps: Vec<(ClockStage, ClockStage)>,
    /// The stages of its caller, slowest first: those of `maps`, those of
    /// its rings and its tick if it deals.
    pub stages: Vec<ClockStage>,
    /// The stage of its caller that makes its output: its tick if it deals,
    /// else that of the part moved as `maps`. None, and no `maps` and
    /// `stages`, of a callee with no table.
    pub made: Option<ClockStage>,
}

/// A run of an instance (§11.9, S-1088): the stage `body` of the body of
/// its callee runs in the function of the stage `caller` of this flow
/// (the stage x of the body moved out of each boundary, [`bounds::step`]);
/// `at_read`: that stage makes the output of the instance (the `made` of
/// its outermost boundary), so it runs where the call is read.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Run {
    pub body: ClockStage,
    pub caller: ClockStage,
    pub at_read: bool,
}

/// The most of the exponents of the N on a path of `.down~(N)` and
/// `.up~(N)` from an outermost body (§11.9: 2^24, S-1089).
pub const MOST_N_EXP: u32 = 24;

/// The `.down~(N)` and `.up~(N)` of `chain` as written (`.down~(4096).up~(2)`),
/// for the notes of the E0808 of S-1089.
pub(super) fn shown<'a>(chain: impl IntoIterator<Item = &'a PlanModifier>) -> String {
    let n = |m: &PlanModifier| m.ratio.map(|r| format!(".{}~({})", m.modifier.name(), 1u64 << r.0.unsigned_abs()));
    chain.into_iter().filter_map(n).collect()
}

/// The modifier of `chain` past which, multiplied in the order they are
/// written from the exponent `from` (of the path in the callee), the N are
/// past 2^24 ([`MOST_N_EXP`]): the place of the E0808 of S-1089, of a
/// chain alone (`from` 0) and of a path through flows. The one test of it
/// (D-15).
pub(super) fn past<'a>(chain: impl IntoIterator<Item = &'a PlanModifier>, from: u32) -> Option<&'a PlanModifier> {
    let mut size = from;
    chain.into_iter().find(|m| {
        size = size.saturating_add(m.ratio.map_or(0, |r| r.0.unsigned_abs()));
        size > MOST_N_EXP
    })
}

/// A modifier of the chain of a node (§11.10).
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct PlanModifier {
    pub modifier: Modifier,
    /// The ratio of `.down~(N)` and `.up~(N)` (S-1077), none of `.when~`
    /// and `.reset_if~`.
    pub ratio: Option<Ratio>,
    /// The name of the modifier (`down`).
    pub name: Span,
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
    /// "Read at a stage not its own" is "read at a later stage": a value is
    /// never read at a slower stage (E0815; ticks at the same ratio only).
    pub fn stored(&self, v: Kept) -> bool {
        match v {
            Kept::Local(l) => {
                let reads = self.read_at.get(&l).into_iter().flatten();
                self.own_stage(l).is_some_and(|own| reads.into_iter().any(|&s| s != own))
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
/// module of `ast`); and its own slow stages. The walk of the table
/// ([`entries`]) adds those of its callees and makes the fields of the
/// state after.
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
            PlanKind::Par { var, from, count, end, body, state, fields, .. } => {
                PlanKind::Par { var, from, count, end, body, state, children: ch, fields }
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
            arms: r.arms,
            frame: r.frame,
            chain: r.chain,
            size: r.size,
            bounds: r.bounds,
            runs: Vec::new(),
            timed: false,
        }
    });
    info.nodes = nodes.collect();
    info.node_of = info.nodes.iter().enumerate().map(|(i, n)| (n.expr, NodeId(i as u32))).collect();
    info.roots = roots;
    super::hoist::table(info, ast, hoisted);
    info.stages = stage::slow_stages(info);
}

#[cfg(test)]
mod tests;
