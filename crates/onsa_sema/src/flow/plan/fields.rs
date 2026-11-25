//! The fields of the state of a flow (S-05, S-06, §12.4): of its `State`
//! ([`FlowInfo::fields`]) and of the replica of each `par~` with state
//! ([`PlanKind::Par`]), in their order and with their names. The lowering
//! gives them their Core types and reads their places by what they hold
//! ([`FlowInfo::field_at`]); it does not name, order or choose them.

use super::*;
use crate::flow_names::FixedField;

/// A field of a node (S-06).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Part {
    /// The node's own: the value of `prev~`, the state of an instance, the
    /// replicas of a `par~`.
    Own,
    /// The `init` of a delay whose `init` is an `Init`-rate expression
    /// ([`InitArg::Init`]): `reset` reads it.
    Init,
    /// The ring of `delay~` / `vdelay~`.
    Buf,
    /// The write index of the ring.
    W,
    /// The ring that gathers the port `port` at the boundary `bound` of
    /// the chain of an instance ([`PlanNode::bounds`], §11.9, S-1208).
    Gather {
        bound: u32,
        port: Port,
    },
    /// The array that deals the output at the boundary of the chain.
    Deal(u32),
    /// Of the guard of the chain (`.when~`, §11.10, S-1209, S-1220): the
    /// condition it read at its last tick of W, the count of the ticks it
    /// ran, and its held output.
    On(u32),
    Count(u32),
    Held(u32),
    /// Of a delay with a `.when~` in its chain: it ran at this tick, so it
    /// stores (§11.4, §11.10, S-1220).
    Ran,
    /// Of a delay an event of another stage resets (§11.3, S-1250): between its
    /// place and its store; the reset at this place of its chain waits for that store.
    Open,
    Back(u32),
}

/// What a field of the state holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FieldOf {
    SampleRate,
    /// The counter of the phase (§11.9, §12.4, S-1179).
    Tick,
    /// The upper word of the time (§11.4, §12.4, S-1211, [`FlowInfo::wide`]).
    TickHi,
    Input(LocalId),
    Let(LocalId),
    Node(NodeId, Part),
    Hoist(HoistId),
    Poisoned,
    Initialized,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Field {
    pub name: String,
    pub of: FieldOf,
}

impl FlowInfo {
    /// The fields of the struct that holds the nodes of `owner`: the
    /// `State` of the flow, or the replica of a `par~`.
    pub fn fields_of(&self, owner: Owner) -> &[Field] {
        match owner {
            Owner::Let(_) | Owner::Output => &self.fields,
            Owner::Par(p) => match &self.node(p).kind {
                PlanKind::Par { fields, .. } => fields,
                _ => &[],
            },
        }
    }

    /// The place of the field that holds `of` in the struct that holds it
    /// (that of its node, or the `State`); `None` when the state does not
    /// keep it. Of the table the fields are made with: no search (R-498).
    pub fn field_at(&self, of: FieldOf) -> Option<u32> {
        self.places.get(&of).copied()
    }

    /// The name of the field that holds `of`, in the struct that holds it;
    /// `None` when the state does not keep it.
    pub fn field(&self, of: FieldOf) -> Option<&str> {
        let fields = match of {
            FieldOf::Node(id, _) => self.fields_of(self.node(id).owner),
            FieldOf::Hoist(h) => self.fields_of(self.hoist(h).owner),
            _ => &self.fields,
        };
        Some(fields.get(self.field_at(of)? as usize)?.name.as_str())
    }
}

/// The fields of the state of `info` (S-05, §12.4): `_sample_rate` when it
/// is kept, `_tick` when the flow counts the time (S-1179) and `_tick_hi`
/// when it takes the upper word of the time (S-1211), the kept inputs in their order, then for each `let` in its
/// order its kept locals and the fields of its nodes, the fields of the
/// nodes of the output, the hoisted fields of the `let`s and the output in
/// their order, `_poisoned` and `_initialized`; and the fields of the
/// replica of each `par~`: of its `children`, then those hoisted in its
/// body (S-1140). The names are of [`names`] and [`FixedField`].
pub(super) fn build(info: &mut FlowInfo) {
    let n = info.nodes.len();
    let mut s = Structs { info, at: vec![None; n], pars: vec![Vec::new(); n] };
    let p = s.info;
    let mut top = Vec::new();
    let field = |of: FieldOf, name: &str| Field { name: name.to_string(), of };
    let local = |of: fn(LocalId) -> FieldOf, v: LocalId| field(of(v), &p.body.locals[v.0 as usize].name);
    if p.stored(Kept::SampleRate) {
        top.push(field(FieldOf::SampleRate, FixedField::SampleRate.name()));
    }
    if p.counts_time() {
        top.push(field(FieldOf::Tick, FixedField::Tick.name()));
    }
    if p.wide() {
        top.push(field(FieldOf::TickHi, FixedField::TickHi.name()));
    }
    top.extend(p.inputs.iter().filter(|&&v| p.stored(Kept::Local(v))).map(|&v| local(FieldOf::Input, v)));
    for (k, l) in p.lets.iter().enumerate() {
        if l.state {
            top.extend(l.locals.iter().map(|&v| local(FieldOf::Let, v)));
        }
        for &id in p.roots(Owner::Let(k as u32)) {
            s.node(id, &mut top);
        }
    }
    for &id in p.roots(Owner::Output) {
        s.node(id, &mut top);
    }
    let hoists = p.hoists.iter().enumerate().filter(|(_, x)| !matches!(x.owner, Owner::Par(_)));
    top.extend(hoists.map(|(h, x)| field(FieldOf::Hoist(HoistId(h as u32)), &x.path)));
    top.push(field(FieldOf::Poisoned, FixedField::Poisoned.name()));
    top.push(field(FieldOf::Initialized, FixedField::Initialized.name()));
    let (at, pars) = (s.at, s.pars);
    let mut places = HashMap::default();
    for fs in pars.iter().chain([&top]) {
        unique(info, fs);
        // What a field holds is one in all the structs: a node's fields are its.
        for (k, f) in fs.iter().enumerate() {
            let before = places.insert(f.of, k as u32);
            debug_assert!(before.is_none(), "two fields hold {:?}", f.of);
        }
    }
    info.places = places;
    for (node, (at, fs)) in info.nodes.iter_mut().zip(at.into_iter().zip(pars)) {
        node.field = at;
        if let PlanKind::Par { fields, .. } = &mut node.kind {
            *fields = fs;
        }
    }
    info.fields = top;
}

/// Two fields of one struct of the state never have one name: the names
/// the processor makes are of a form no user writes, and the user's names
/// are apart (§11.6, S-1138). An internal error at the later of the two.
fn unique(info: &FlowInfo, fields: &[Field]) {
    let span = |of: FieldOf| match of {
        FieldOf::Node(id, _) => Some(info.node(id).span),
        FieldOf::Input(l) | FieldOf::Let(l) => Some(info.body.locals[l.0 as usize].span),
        FieldOf::Hoist(h) => Some(info.hoist(h).span),
        FieldOf::SampleRate | FieldOf::Tick | FieldOf::TickHi | FieldOf::Poisoned | FieldOf::Initialized => None,
    };
    let mut seen: HashMap<&str, FieldOf> = HashMap::default();
    for f in fields {
        if let Some(first) = seen.insert(&f.name, f.of) {
            let at = span(f.of).or_else(|| span(first));
            onsa_diag::internal::bug(at, format!("two fields `{}` in a struct of the state of a flow", f.name));
        }
    }
}

/// The structs of the state while they are made: the place of the first
/// field of each node, and the fields of each `par~`.
struct Structs<'a> {
    info: &'a FlowInfo,
    at: Vec<Option<u32>>,
    pars: Vec<Vec<Field>>,
}

impl Structs<'_> {
    /// The fields of the node `id` (S-06) after `out`, of the struct that
    /// holds it: `n` of `prev~` and of an instance, `n.buf` and `n.w` of
    /// `delay~` / `vdelay~`, then `n.init` of a delay whose `init` is an
    /// `Init`-rate expression; after `n` of an instance the rings and the
    /// array of each boundary of its chain; of either, those its guards
    /// read, of a delay with a guard `n._ran`, its flags (S-1250); `n` of a `par~` whose replicas have fields
    /// (of its nodes, then its hoisted ones by their names), and none of
    /// one with no state.
    fn node(&mut self, id: NodeId, out: &mut Vec<Field>) {
        let info = self.info;
        let n = info.node(id);
        let start = out.len() as u32;
        let own = names::field(n);
        // Of a guard, the name of its held output reads which is the outermost.
        let outermost =
            guard_parts(n).into_iter().filter_map(|p| if let Part::Held(g) = p { Some(g) } else { None }).max();
        let mut push =
            |part: Part| out.push(Field { name: names::part(own, part, outermost), of: FieldOf::Node(id, part) });
        // §11.6 (S-1208, S-1220): after its state, by the modifiers of its chain inner
        // first, the rings then the array of a boundary, of a guard what its table reads.
        let mut parts = Vec::new();
        for (b, at) in (0u32..).zip(&n.bounds) {
            parts.extend(at.gathers.iter().map(|&(port, _)| (at.at, Part::Gather { bound: b, port })));
            parts.extend(at.deals.then_some((at.at, Part::Deal(b))));
        }
        let read = guard_parts(n);
        for (g, at) in (0u32..).zip(&n.guards) {
            let of = [Part::On(g), Part::Count(g), Part::Held(g)];
            parts.extend(of.into_iter().filter(|p| read.contains(p)).map(|p| (at.at, p)));
        }
        parts.sort_by_key(|p| p.0);
        let chain = parts.into_iter().map(|p| p.1);
        let init = match &n.kind {
            PlanKind::Prev { init, .. } => {
                push(Part::Own);
                Some(init)
            }
            PlanKind::Delay { init, .. } | PlanKind::Vdelay { init, .. } => {
                push(Part::Buf);
                push(Part::W);
                Some(init)
            }
            PlanKind::Instance { .. } => {
                push(Part::Own);
                None
            }
            PlanKind::Par { children, .. } => {
                let mut inner = Vec::new();
                for &c in children {
                    self.node(c, &mut inner);
                }
                let hoists = info.hoists.iter().enumerate().filter(|(_, x)| x.owner == Owner::Par(id));
                let hoist =
                    |(h, x): (usize, &Hoist)| Field { name: x.name.clone(), of: FieldOf::Hoist(HoistId(h as u32)) };
                inner.extend(hoists.map(hoist));
                if inner.is_empty() {
                    return;
                }
                self.pars[id.0 as usize] = inner;
                push(Part::Own);
                None
            }
        };
        if let Some(InitArg::Init(_)) = init {
            push(Part::Init);
        }
        chain.for_each(&mut push);
        // The store of a delay is of the ticks it ran (§11.10).
        if n.kind.delay().is_some() && !n.guards.is_empty() {
            push(Part::Ran);
        }
        n.late_flags().into_iter().for_each(&mut push);
        self.at[id.0 as usize] = Some(start);
    }
}

/// The fields of the guards of the chain of `n` its table reads (§11.10,
/// S-1220): [`Part::On`] of a guard read where its condition is not, its
/// [`Part::Count`] of one that counts, its [`Part::Held`] of one that holds.
fn guard_parts(n: &PlanNode) -> Vec<Part> {
    let mut read = Vec::new();
    for e in &n.entries {
        Op::walk(&e.ops, &mut |op| match *op {
            Op::When { guard, cond, due, advance, .. } => {
                read.extend((cond == CondRead::Kept).then_some(Part::On(guard)));
                read.extend((advance || due.is_some()).then_some(Part::Count(guard)));
            }
            Op::Hold { guard, .. } => read.push(Part::Held(guard)),
            _ => {}
        });
    }
    read
}

#[cfg(test)]
mod tests;
