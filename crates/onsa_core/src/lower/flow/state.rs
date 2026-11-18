//! The state fields of a flow (S-05, S-06): the Core types of the fields
//! the plan names and orders.

use super::*;

pub(super) fn ast_span(lw: &Lowerer, flow: DefId, e: ExprId) -> R<Span> {
    let a = lw.a;
    let d = a.def(flow);
    let m = a.ast(lw.pkg, d.module).ok_or_else(|| internal(d.span, "module source not found"))?;
    Ok(m.parsed.ast.expr(e).span)
}

/// The Core fields of a struct of the state, the `State` of the flow or the
/// replica of a `par~`, of the fields the plan names and orders (S-05,
/// S-06, §12.4; [`FlowInfo::fields_of`]): their Core types.
pub(super) fn state_fields(
    lw: &mut Lowerer,
    flow: DefId,
    fd: &FlowDef,
    info: &FlowInfo,
    fs: &[Field],
) -> R<Vec<(String, Ty)>> {
    fs.iter().map(|f| Ok((f.name.clone(), field_ty(lw, flow, fd, info, f.of)?))).collect()
}

fn field_ty(lw: &mut Lowerer, flow: DefId, fd: &FlowDef, info: &FlowInfo, of: FieldOf) -> R<Ty> {
    let local = |l: onsa_sema::LocalId| info.body.locals[l.0 as usize].ty;
    match of {
        FieldOf::SampleRate => Ok(Ty::Float(FloatKind::F32)),
        FieldOf::Poisoned | FieldOf::Initialized => Ok(Ty::Bool),
        FieldOf::Input(l) => {
            let input = info.inputs.iter().position(|&i| i == l).and_then(|k| fd.inputs.get(k));
            let input = input.ok_or_else(|| internal(lw.a.def(flow).span, "a stored input the flow has not"))?;
            lw.core_ty(input.ty, &[], input.span)
        }
        FieldOf::Let(l) => {
            let at = info.lets.iter().find(|x| x.locals.contains(&l));
            let at = at.ok_or_else(|| internal(lw.a.def(flow).span, "a stored local of no `let`"))?;
            lw.core_ty(local(l), &[], at.span)
        }
        FieldOf::Node(id, part) => node_field_ty(lw, flow, fd, info, id, part),
    }
}

/// The Core type of the field `part` of the node `id` (S-06).
fn node_field_ty(lw: &mut Lowerer, flow: DefId, fd: &FlowDef, info: &FlowInfo, id: NodeId, part: Part) -> R<Ty> {
    let n = info.node(id);
    let span = ast_span(lw, flow, n.expr)?;
    match (&n.kind, part) {
        (PlanKind::Prev { ty, .. }, Part::Own | Part::Init)
        | (PlanKind::Delay { ty, .. } | PlanKind::Vdelay { ty, .. }, Part::Init) => lw.core_ty(*ty, &[], span),
        (PlanKind::Delay { n: len, ty, .. }, Part::Buf) => Ok(Ty::Array(Box::new(lw.core_ty(*ty, &[], span)?), *len)),
        (PlanKind::Vdelay { max, ty, .. }, Part::Buf) => Ok(Ty::Array(Box::new(lw.core_ty(*ty, &[], span)?), max + 1)),
        (PlanKind::Delay { .. } | PlanKind::Vdelay { .. }, Part::W) => Ok(Ty::u32()),
        (PlanKind::Instance { callee, .. }, Part::Own) => Ok(Ty::Struct(lw.ensure_flow(*callee)?.state)),
        (PlanKind::Par { from, to, fields, .. }, Part::Own) => {
            let inner = state_fields(lw, flow, fd, info, fields)?;
            let tname = format!("{}.{}.State", lw.qual_name(flow), n.path);
            let tid = TypeId(lw.m.types.len() as u32);
            lw.m.types.push(TypeDef { name: tname, kind: TypeDefKind::Struct { fields: inner } });
            Ok(Ty::Array(Box::new(Ty::Struct(tid)), to - from))
        }
        _ => Err(internal(span, format!("no field {part:?} of the node {}", n.path))),
    }
}
