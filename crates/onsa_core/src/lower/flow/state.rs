//! The state fields of a flow (S-05, S-06): the nodes of a flow and the
//! fields each one adds to `State`.

use super::*;

pub(super) fn ast_span(lw: &Lowerer, flow: DefId, e: ExprId) -> R<Span> {
    let a = lw.a;
    let d = a.def(flow);
    let m = a.ast(lw.pkg, d.module).ok_or_else(|| internal(d.span, "module source not found"))?;
    Ok(m.parsed.ast.expr(e).span)
}

/// Whether a node holds any state (a `par` of pure replicas has none).
pub(super) fn node_has_state(info: &FlowInfo, id: NodeId) -> bool {
    match &info.node(id).kind {
        PlanKind::Par { children, .. } => children.iter().any(|&c| node_has_state(info, c)),
        _ => true,
    }
}

/// The state fields of one node (S-06).
pub(super) fn node_fields(
    lw: &mut Lowerer,
    flow: DefId,
    info: &FlowInfo,
    id: NodeId,
    fields: &mut Vec<(String, Ty)>,
) -> R<()> {
    let n = info.node(id);
    let (span, name) = (ast_span(lw, flow, n.expr)?, &n.name);
    match &n.kind {
        PlanKind::Prev { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            fields.push((name.clone(), t.clone()));
            if matches!(init, InitArg::Init(_)) {
                fields.push((format!("{name}.init"), t));
            }
        }
        PlanKind::Delay { n: len, init, ty, .. } | PlanKind::Vdelay { max: len, init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = if matches!(n.kind, PlanKind::Vdelay { .. }) { *len + 1 } else { *len };
            fields.push((format!("{name}.buf"), Ty::Array(Box::new(t.clone()), len)));
            fields.push((format!("{name}.w"), Ty::u32()));
            if matches!(init, InitArg::Init(_)) {
                fields.push((format!("{name}.init"), t));
            }
        }
        PlanKind::Instance { callee, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            fields.push((name.clone(), Ty::Struct(sub.state)));
        }
        PlanKind::Par { from, to, children, .. } => {
            if !node_has_state(info, id) {
                return Ok(());
            }
            let mut inner = Vec::new();
            for &sub in children {
                node_fields(lw, flow, info, sub, &mut inner)?;
            }
            let tname = format!("{}.{name}.State", lw.qual_name(flow));
            let id = TypeId(lw.m.types.len() as u32);
            lw.m.types.push(TypeDef { name: tname, kind: TypeDefKind::Struct { fields: inner } });
            fields.push((name.clone(), Ty::Array(Box::new(Ty::Struct(id)), to - from)));
        }
    }
    Ok(())
}
