//! The state fields of a flow (S-05, S-06): the nodes of a flow and the
//! fields each one adds to `State`.

use super::*;

pub(super) fn ast_span(lw: &Lowerer, flow: DefId, e: ExprId) -> R<Span> {
    let a = lw.a;
    let d = a.def(flow);
    let m = a.ast(lw.pkg, d.module).ok_or_else(|| internal(d.span, "module source not found"))?;
    Ok(m.parsed.ast.expr(e).span)
}

/// Top-level nodes whose expression lies inside `span`, in source order.
pub(super) fn nodes_in(lw: &Lowerer, flow: DefId, nodes: &[Node], span: Span) -> R<Vec<Node>> {
    let mut out = Vec::new();
    for n in nodes {
        let s = ast_span(lw, flow, n.expr())?;
        if span.start <= s.start && s.end <= span.end {
            out.push(n.clone());
        }
    }
    Ok(out)
}

/// Every node at any depth, by its expression.
pub(super) fn flat_nodes(nodes: &[Node]) -> HashMap<ExprId, Node> {
    fn go(nodes: &[Node], out: &mut HashMap<ExprId, Node>) {
        for n in nodes {
            out.insert(n.expr(), n.clone());
            if let Node::Par { nodes, .. } = n {
                go(nodes, out);
            }
        }
    }
    let mut out = HashMap::new();
    go(nodes, &mut out);
    out
}

/// Whether a node holds any state (a `par` of pure replicas has none).
pub(super) fn node_has_state(n: &Node) -> bool {
    match n {
        Node::Par { nodes, .. } => nodes.iter().any(node_has_state),
        _ => true,
    }
}

/// The state fields of one node (S-06).
pub(super) fn node_fields(lw: &mut Lowerer, flow: DefId, n: &Node, fields: &mut Vec<(String, Ty)>) -> R<()> {
    let span = ast_span(lw, flow, n.expr())?;
    match n {
        Node::Prev { name, init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            fields.push((name.clone(), t.clone()));
            if matches!(init, InitArg::Init(_)) {
                fields.push((format!("{name}.init"), t));
            }
        }
        Node::Delay { name, n: len, init, ty, .. } | Node::Vdelay { name, max: len, init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = if matches!(n, Node::Vdelay { .. }) { *len + 1 } else { *len };
            fields.push((format!("{name}.buf"), Ty::Array(Box::new(t.clone()), len)));
            fields.push((format!("{name}.w"), Ty::u32()));
            if matches!(init, InitArg::Init(_)) {
                fields.push((format!("{name}.init"), t));
            }
        }
        Node::Instance { name, callee, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            fields.push((name.clone(), Ty::Struct(sub.state)));
        }
        Node::Par { name, from, to, nodes, .. } => {
            if !node_has_state(n) {
                return Ok(());
            }
            let mut inner = Vec::new();
            for sub in nodes {
                node_fields(lw, flow, sub, &mut inner)?;
            }
            let tname = format!("{}.{name}.State", lw.qual_name(flow));
            let id = TypeId(lw.m.types.len() as u32);
            lw.m.types.push(TypeDef { name: tname, kind: TypeDefKind::Struct { fields: inner } });
            fields.push((name.clone(), Ty::Array(Box::new(Ty::Struct(id)), to - from)));
        }
    }
    Ok(())
}
