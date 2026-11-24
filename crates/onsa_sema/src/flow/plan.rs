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
mod steps;

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
    /// [`PlanNode::entries`]; S-1207).
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
    /// The guards of its chain, inner first (§11.10, S-1209): one of each
    /// `.when~` of `chain`, of the same walk as `bounds`.
    pub guards: Vec<PlanGuard>,
    /// Of an instance, its work in each stage of this flow (§11.9, S-1088,
    /// S-1207), one entry of a stage, slowest first; none of another node,
    /// and of an instance whose callee has no table (in error, in a loop of
    /// calls). Made by the walk of the table ([`entries`], [`steps`]).
    pub entries: Vec<Entry>,
    /// How this flow reads its value (§11.9).
    pub read: Read,
}

/// The work of an instance in the function of the stage `caller` of this
/// flow (§11.9, S-1088, S-1207): its `ops`, in the order of §11.9 (the
/// slow ticks, then the ticks of `sample`), which the Core lowers as they
/// are. `read`: this flow reads the instance in that function and they
/// write what it reads (a [`Op::Run`] of [`Out::Value`], a [`Op::Deal`] to
/// [`To::Value`], or one of either into the array of its [`Read::Array`]),
/// so they are lowered where the call is read, before it is; else in the
/// walk of the runs of that function (the review of U6b, its high 1).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Entry {
    pub caller: ClockStage,
    pub read: bool,
    pub ops: Vec<Op>,
}

/// A step of the work of an instance ([`Entry`]). A list of them and the
/// groups of an [`Op::Each`] are in the order of §11.9 (the slow ticks,
/// then the ticks of `sample`), which the Core lowers as it is.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op {
    /// The slot of the ring of the port `port` of the boundary `bound`,
    /// at its phase, written from `from`.
    Ring { bound: u32, port: Port, from: Feed },
    /// The stage `body` of the head run (its function called); its result
    /// to `out`.
    Run { body: ClockStage, out: Out },
    /// The elements of the array of the boundary `from` written to `to`
    /// (the array of a boundary outside it that deals, or the value), in
    /// the window of one frame inside the boundary `by` (§11.9): of the two
    /// windows the narrower, of the boundary whose tick it is at (of the
    /// count of the boundaries, the frame of the caller).
    Deal { to: To, from: u32, by: u32 },
    /// The runs of the part an `.up~(N)` boundary `bound` wraps: each of
    /// its N runs j (`once`: the run j = 0 alone, of a stage slower than
    /// the `sample` of its caller), and in each the ops of each stage of
    /// the part, when j is at the tick of that stage.
    Each { bound: u32, once: bool, groups: Vec<(ClockStage, Vec<Op>)> },
    /// The ops of the part the `.when~` of the guard `guard` wraps, run
    /// while it runs (§11.10, S-1209): its condition read as `cond` says,
    /// `due` the stage of the part slower than the clock W it is read at,
    /// run at the ticks of that stage of the count of the ticks it ran
    /// (`Part::Count`), else run each time; `advance`: that count goes on
    /// after them.
    When { guard: u32, cond: CondRead, due: Option<ClockStage>, ops: Vec<Op>, advance: bool },
    /// The state of the part the `.reset_if~` at `at` of the chain wraps
    /// back to its start where its condition is true (§11.10): the soft
    /// reset of its head, and the rings, the arrays and the held outputs of
    /// the boundaries and the guards inside it at `T.default()`, not the
    /// conditions and the counts of the guards.
    Reset { at: u32 },
    /// The value of the part the guard `guard` wraps (§11.10): of one that
    /// is not a burst its held output, which the ops of its runs wrote;
    /// of a burst the array the runs made when it ran (and its last
    /// element held), else that held N times. Its result to `out`.
    Hold { guard: u32, out: Out },
}

/// How an [`Op::When`] reads its condition: at its clock W, here (and into
/// [`Part::On`] when the table has a `Kept` of it); as the one before it in
/// the same list read it; or as the last tick of W did, of `Part::On`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CondRead {
    Read,
    Local,
    Kept,
}

/// A port of the part a boundary wraps that it gathers (§11.9, §11.10): the
/// input of the head by its index, or the condition of the `.when~` or the
/// `.reset_if~` at this place of the chain, an input of the part at its
/// place (the memo of W7-10 U3, 2.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Port {
    Input(u32),
    Cond(u32),
}

/// Where a ring is written from: the argument of the call (of a condition,
/// its expression), or the ring of the boundary outside that gathers the
/// same port.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Feed {
    Arg,
    Ring(u32),
}

/// Where the result of a run goes: nowhere, the value of the instance, or
/// the array of the boundary that deals it (the innermost that deals).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Out {
    None,
    Value,
    Deal(u32),
    /// The held output of the guard (§11.10, [`Op::Hold`]).
    Held(u32),
}

/// Where an [`Op::Deal`] writes: the array of a boundary, or the value of
/// the instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum To {
    Array(u32),
    Value,
    Held(u32),
}

/// How a flow reads the value of an instance: the value the ops of its
/// entry read make, or the window of the array of the outermost
/// boundary that deals (one no `.up~` outside it widens, [`steps`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Read {
    Run,
    Array(u32),
}

impl Entry {
    /// Each run of the entries `entries` ([`Op::Run`], in an [`Op::Each`]
    /// too): the stage of the body of the callee with the stage of the
    /// caller whose function runs it, in the order of the entries.
    pub fn runs(entries: &[Entry]) -> Vec<(ClockStage, ClockStage)> {
        let mut runs = Vec::new();
        for e in entries {
            Op::walk(&e.ops, &mut |op| {
                if let Op::Run { body, .. } = *op {
                    runs.push((body, e.caller));
                }
            });
        }
        runs
    }
}

impl Op {
    /// `f` of each op of `ops`, of the groups of each [`Op::Each`] and of
    /// the ops of each [`Op::When`] in them, in their order: as deep as the
    /// `.up~` and the `.when~` of the chain.
    pub fn walk<'a>(ops: &'a [Op], f: &mut impl FnMut(&'a Op)) {
        for op in ops {
            f(op);
            match op {
                Op::Each { groups, .. } => groups.iter().for_each(|g| Op::walk(&g.1, f)),
                Op::When { ops, .. } => Op::walk(ops, f),
                _ => {}
            }
        }
    }

    /// Whether it makes the value of the instance (§11.9, §11.10): a run of
    /// [`Out::Value`], a copy to [`To::Value`] or a hold of it.
    pub fn makes_value(&self) -> bool {
        matches!(
            self,
            Op::Run { out: Out::Value, .. } | Op::Deal { to: To::Value, .. } | Op::Hold { out: Out::Value, .. }
        )
    }
}

/// A boundary of a chain (§11.9, §11.10, S-1207): a `.down~(N)` or an
/// `.up~(N)` of it, which runs the part it wraps (the head and the
/// modifiers inside it) as one part in the frame of its own caller, and
/// gathers and deals at the ports of that part. Its ports are of the
/// record ([`bounds::bounds`]): the fields and the Core read them, and do
/// not work them out of the ratios again; the work of the instance in the
/// stages of its caller is of [`PlanNode::entries`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlanBound {
    /// Its modifier, by its place in the `chain` of the node.
    pub at: u32,
    /// The ratio of its modifier (`chain[at].ratio`).
    pub ratio: Ratio,
    /// The exponent of each input of the part it wraps, in the frame that
    /// part is called in (`sample * 2^k`); none of a parameter kind.
    pub ins: Vec<Option<Ratio>>,
    /// The exponent of the output of that part.
    pub out: Option<Ratio>,
    /// The exponent of the condition of each `.when~` and `.reset_if~`
    /// inside it with a port ([`PlanModifier::port`]), by its place in the
    /// chain, in that frame.
    pub conds: Vec<(u32, Ratio)>,
    /// The ports it gathers (a `.down~` of an input of the part faster than
    /// its `sample`, [`bounds::gathers`]): the inputs by their index, then
    /// the conditions, each with the stage that writes its ring, of the frame
    /// around it (the caller of the part it makes; of this flow, that of the
    /// [`Op::Ring`] of the entries).
    pub gathers: Vec<(Port, ClockStage)>,
    /// It deals the output of the part (a `.down~` of an output faster than
    /// its `sample`), at its own tick.
    pub deals: bool,
}

/// A guard of a chain (§11.10, S-1209): a `.when~` of it, which runs the
/// part it wraps while its condition `cond` is true at the clock W it reads
/// it at, of the record ([`bounds::bounds`]): the place `at` of its
/// modifier in the `chain`, the exponent `w` of W in the frame it is in
/// (that of the output of the part it wraps when slower than the `sample`
/// of the frame, else 0) and that of the output of that part (none of a
/// parameter kind).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlanGuard {
    pub at: u32,
    pub cond: ExprId,
    pub w: Ratio,
    pub out: Option<Ratio>,
}

impl PlanBound {
    /// The exponent `k` of a port of the part it wraps in the frame around
    /// it: `k + r`. The one sum of it (D-15): the ports of the next boundary
    /// ([`bounds::bounds`]) and the places of the Core read it.
    pub fn outside(&self, k: Ratio) -> Ratio {
        Ratio(k.0.saturating_add(self.ratio.0))
    }
}

/// The words of the time the function of a stage takes ([`FlowInfo::time`]):
/// `t`, the low word of the count of the outermost `sample` (§11.4), or `t`
/// and `t_hi`, its upper word, under a `.down~` (§12.4, S-1211).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Words {
    One = 1,
    Two = 2,
}

/// Where the counter of the phase of a flow advances ([`FlowInfo::counter`]):
/// nowhere (it has none), in its `tick` or in its `process`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Counter {
    None,
    Tick,
    Process,
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
    /// The condition of `.when~` and `.reset_if~`.
    pub cond: Option<ExprId>,
    /// The name of the modifier (`down`).
    pub name: Span,
    /// Of `.reset_if~`, the exponent of the tick R its condition resets at
    /// in its frame (§11.10), written by the walk of the clocks (the one
    /// writer of it, [`build`]); none of another and of a chain in error.
    pub reset: Option<Ratio>,
    /// Of `.when~` and `.reset_if~`, the exponent in its frame of the clock
    /// of its condition, a port of the part at its place (§11.10: read as an
    /// input of the head is); of the same writer; none of a parameter kind.
    pub port: Option<Ratio>,
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
    let nodes = recorded.into_iter().zip(children).map(|(mut r, ch)| {
        let (clock, args) = match (w.node_of.get(&r.expr), info.clocks.exprs.get(&r.expr)) {
            (Some(&k), _) => {
                // The tick of each `.reset_if~` the walk found (§11.10).
                for &(at, tick) in &w.nodes[k].resets {
                    r.chain.get_mut(at as usize).into_iter().for_each(|m| m.reset = Some(tick));
                }
                // The port of each condition (§11.10), gathered as an input is.
                for &(at, port) in &w.nodes[k].ports {
                    r.chain.get_mut(at as usize).into_iter().for_each(|m| m.port = Some(port));
                }
                bounds::conds(&r.chain, &mut r.bounds);
                (w.nodes[k].clock, w.nodes[k].args.clone())
            }
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
            guards: r.guards,
            entries: Vec::new(),
            read: Read::Run,
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
