//! The stateful nodes of a flow body (§11.4, §11.5, S-06): their names,
//! their order and the nesting of `par~`, apart from the clocks. The walk of
//! the clocks checks a node first and then builds it here.

use super::*;

/// The node lists of a flow body while a walk goes through it
/// ([`FlowInfo::nodes`], [`FlowInfo::node_of_expr`]). It knows no clock.
///
/// The walk of the clocks calls it at stage 2 in the order of the source,
/// at each node after the checks of its clocks:
/// - [`NodeBuilder::node`] at a delay or an instance call;
/// - at `par~`, [`NodeBuilder::enter_par`] before the body and
///   [`NodeBuilder::leave_par`] after it, even when the body stopped, and
///   then [`NodeBuilder::par`] with the nodes of the body;
/// - [`NodeBuilder::finish`] at the end, for the tables.
///
/// The names are numbered per kind in the order of the calls (S-06).
pub(super) struct NodeBuilder {
    lists: Vec<Vec<Node>>,
    node_of_expr: HashMap<ExprId, usize>,
    counters: HashMap<String, u32>,
    let_names: HashMap<ExprId, String>,
}

impl NodeBuilder {
    /// The node of the whole initializer of a `let` of a single name takes
    /// that name (S-06).
    pub(super) fn new(pending: &[PendingLet]) -> NodeBuilder {
        let let_names = pending.iter().filter_map(|p| Some((p.init, p.name.clone()?))).collect();
        NodeBuilder {
            lists: vec![Vec::new()],
            node_of_expr: HashMap::default(),
            counters: HashMap::default(),
            let_names,
        }
    }

    /// The nodes of the body and the index of each in its list.
    pub(super) fn finish(mut self) -> (Vec<Node>, HashMap<ExprId, usize>) {
        (self.lists.pop().unwrap_or_default(), self.node_of_expr)
    }

    fn next_name(&mut self, kind: &str) -> String {
        let n = self.counters.entry(kind.to_string()).or_insert(0);
        let name = format!("{kind}_{n}");
        *n += 1;
        name
    }

    fn push(&mut self, node: Node) {
        let list = self.lists.last_mut().expect("node list");
        let idx = list.len();
        self.node_of_expr.insert(node.expr(), idx);
        list.push(node);
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
        let node = match call.kind {
            NodeKind::Instance(callee) => {
                let name = self.node_name(e, &a.def(callee).name);
                Node::Instance { name, expr: e, callee, args: call.args.clone(), span }
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
                match (delay, d_e) {
                    (Delay::Prev, _) => Node::Prev { name, expr: e, arg, init, ty },
                    (Delay::Fixed, _) => Node::Delay { name, expr: e, arg, n: len, init, ty },
                    (Delay::Variable, Some(d)) => Node::Vdelay { name, expr: e, arg, d, max: len, init, ty },
                    (Delay::Variable, None) => onsa_diag::internal::bug(Some(span), "a `vdelay~` without its `d`"),
                }
            }
        };
        self.push(node);
        Ok(())
    }

    /// The nodes of the body of a `par~` go to a list of their own.
    pub(super) fn enter_par(&mut self) {
        self.lists.push(Vec::new());
    }

    /// The nodes of the body of the `par~` entered last.
    pub(super) fn leave_par(&mut self) -> Vec<Node> {
        self.lists.pop().unwrap_or_default()
    }

    /// `par~ var in from..<to { body }` (§11.5) at `e`, holding `nodes`.
    pub(super) fn par(&mut self, e: ExprId, var: LocalId, from: u32, to: u32, body: ExprId, nodes: Vec<Node>) {
        let name = self.node_name(e, "par");
        self.push(Node::Par { name, expr: e, var, from, to, body, nodes });
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
