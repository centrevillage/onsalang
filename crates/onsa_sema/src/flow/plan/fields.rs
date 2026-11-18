//! The fields of the state of a flow (S-05, S-06, §12.4): of its `State`
//! ([`FlowInfo::fields`]) and of the replica of each `par~` with state
//! ([`PlanKind::Par`]), in their order and with their names. The lowering
//! gives them their Core types and reads their names by what they hold
//! ([`FlowInfo::field`]); it does not name, order or choose them.

use super::*;

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
}

/// What a field of the state holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FieldOf {
    SampleRate,
    Input(LocalId),
    Let(LocalId),
    Node(NodeId, Part),
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

    /// The name of the field that holds `of`, in the struct that holds it;
    /// `None` when the state does not keep it.
    pub fn field(&self, of: FieldOf) -> Option<&str> {
        let found = match of {
            FieldOf::Node(id, _) => {
                let n = self.node(id);
                let own = self.fields_of(n.owner).get(n.field? as usize..)?;
                own.iter().take_while(|f| matches!(f.of, FieldOf::Node(m, _) if m == id)).find(|f| f.of == of)
            }
            _ => self.fields.iter().find(|f| f.of == of),
        };
        found.map(|f| f.name.as_str())
    }
}

/// The fields of the state of `info` (S-05, §12.4): `sample_rate` when it
/// is kept, the kept inputs in their order, then for each `let` in its
/// order its kept locals and the fields of its nodes, the fields of the
/// nodes of the output, `poisoned` and `initialized`; and the fields of
/// the replica of each `par~`, of its `children`.
pub(super) fn build(info: &mut FlowInfo) {
    let n = info.nodes.len();
    let mut s = Structs { info, at: vec![None; n], pars: vec![Vec::new(); n] };
    let p = s.info;
    let mut top = Vec::new();
    let field = |of: FieldOf, name: &str| Field { name: name.to_string(), of };
    let local = |of: fn(LocalId) -> FieldOf, v: LocalId| field(of(v), &p.body.locals[v.0 as usize].name);
    if p.stored(Kept::SampleRate) {
        top.push(field(FieldOf::SampleRate, SAMPLE_RATE));
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
    top.push(field(FieldOf::Poisoned, "poisoned"));
    top.push(field(FieldOf::Initialized, "initialized"));
    let (at, pars) = (s.at, s.pars);
    for (node, (at, fs)) in info.nodes.iter_mut().zip(at.into_iter().zip(pars)) {
        node.field = at;
        if let PlanKind::Par { fields, .. } = &mut node.kind {
            *fields = fs;
        }
    }
    info.fields = top;
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
    /// `Init`-rate expression; `n` of a `par~` whose replicas have fields,
    /// and none of one with no state.
    fn node(&mut self, id: NodeId, out: &mut Vec<Field>) {
        let info = self.info;
        let n = info.node(id);
        let start = out.len() as u32;
        let mut push = |part: Part, name: String| out.push(Field { name, of: FieldOf::Node(id, part) });
        let init = match &n.kind {
            PlanKind::Prev { init, .. } => {
                push(Part::Own, n.name.clone());
                Some(init)
            }
            PlanKind::Delay { init, .. } | PlanKind::Vdelay { init, .. } => {
                push(Part::Buf, format!("{}.buf", n.name));
                push(Part::W, format!("{}.w", n.name));
                Some(init)
            }
            PlanKind::Instance { .. } => {
                push(Part::Own, n.name.clone());
                None
            }
            PlanKind::Par { children, .. } => {
                let mut inner = Vec::new();
                for &c in children {
                    self.node(c, &mut inner);
                }
                if inner.is_empty() {
                    return;
                }
                self.pars[id.0 as usize] = inner;
                push(Part::Own, n.name.clone());
                None
            }
        };
        if let Some(InitArg::Init(_)) = init {
            push(Part::Init, format!("{}.init", n.name));
        }
        self.at[id.0 as usize] = Some(start);
    }
}

#[cfg(test)]
mod tests;
