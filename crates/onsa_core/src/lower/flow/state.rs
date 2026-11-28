//! The state fields of a flow (S-05, S-06): the Core types of the fields
//! the plan names and orders.

use super::*;
use onsa_sema::ty::TyId;

pub(super) fn ast_span(lw: &Lowerer, flow: DefId, e: ExprId) -> R<Span> {
    let a = lw.a;
    let d = a.def(flow);
    let m = a.ast(lw.pkg, d.module).ok_or_else(|| internal(d.span, "module source not found"))?;
    Ok(m.parsed.ast.expr(e).span)
}

/// The value type of each local the state may keep and the place its
/// diagnostics go: of an input its declaration, of a local of a `let` the
/// `let` (S-05). Made once, so a field finds its own at once (R-498).
pub(super) type Decls = HashMap<onsa_sema::LocalId, (TyId, Span)>;

pub(super) fn decls(info: &FlowInfo, inputs: &[Input]) -> Decls {
    let mut out: Decls = inputs.iter().map(|i| (i.local, (i.decl.ty, i.decl.span))).collect();
    for l in &info.lets {
        for &v in &l.locals {
            out.entry(v).or_insert((info.body.locals[v.0 as usize].ty, l.span));
        }
    }
    out
}

/// The types of the state of a flow and what is known of their fields ([`FlowMeta::states`]).
pub(super) type States = Vec<(TypeId, Vec<StateField>)>;

/// The Core fields of a struct of the state, the `State` of the flow or the
/// replica of a `par~`, of the fields the plan names and orders (S-05,
/// S-06, §12.4; [`FlowInfo::fields_of`]): their Core types and what is
/// known of them; the types of the replicas inside, in `states`.
pub(super) fn state_fields(
    lw: &mut Lowerer,
    (flow, states): (DefId, &mut States),
    decls: &Decls,
    info: &FlowInfo,
    fs: &[Field],
) -> R<Vec<(String, CTy, StateField)>> {
    let mut one = |f: &Field| {
        let ty = field_ty(lw, (flow, &mut *states), decls, info, f.of)?;
        // The write position of a delay is below the length of its ring (V-26).
        let below = match f.of {
            FieldOf::Node(id, Part::W) => Some(ring_len(&info.node(id).kind, ast_span(lw, flow, info.node(id).expr)?)?),
            _ => None,
        };
        Ok((f.name.clone(), ty, StateField { below }))
    };
    fs.iter().map(&mut one).collect()
}

fn field_ty(
    lw: &mut Lowerer,
    (flow, states): (DefId, &mut States),
    decls: &Decls,
    info: &FlowInfo,
    of: FieldOf,
) -> R<CTy> {
    match of {
        FieldOf::SampleRate => Ok(Types::float(FloatKind::F32)),
        FieldOf::Tick | FieldOf::TickHi => Ok(Types::U32),
        FieldOf::Poisoned | FieldOf::Initialized => Ok(Types::BOOL),
        FieldOf::Input(l) | FieldOf::Let(l) => {
            let decl =
                decls.get(&l).ok_or_else(|| internal(lw.a.def(flow).span, "a stored local of no declaration"))?;
            lw.core_ty(decl.0, &[], decl.1)
        }
        FieldOf::Node(id, part) => node_field_ty(lw, (flow, states), decls, info, (id, part)),
        FieldOf::Hoist(h) => {
            let x = info.hoist(h);
            let ty = info.body.expr_types.get(&x.expr).ok_or_else(|| internal(x.span, "a hoisted field of no type"))?;
            lw.core_ty(*ty, &[], x.span)
        }
    }
}

/// The Core type of the field `part` of the node `id` (S-06).
fn node_field_ty(
    lw: &mut Lowerer,
    (flow, states): (DefId, &mut States),
    decls: &Decls,
    info: &FlowInfo,
    (id, part): (NodeId, Part),
) -> R<CTy> {
    let n = info.node(id);
    let span = ast_span(lw, flow, n.expr)?;
    match (&n.kind, part) {
        (PlanKind::Prev { ty, .. }, Part::Own | Part::Init)
        | (PlanKind::Delay { ty, .. } | PlanKind::Vdelay { ty, .. }, Part::Init) => lw.core_ty(*ty, &[], span),
        (PlanKind::Delay { ty, .. } | PlanKind::Vdelay { ty, .. }, Part::Buf) => {
            let elem = lw.core_ty(*ty, &[], span)?;
            Ok(lw.ty(TyKind::Array(elem, ring_len(&n.kind, span)?)))
        }
        (PlanKind::Delay { .. } | PlanKind::Vdelay { .. }, Part::W) => Ok(Types::U32),
        (PlanKind::Instance { callee, .. }, Part::Own) => {
            let state = lw.ensure_flow(*callee)?.state;
            Ok(lw.ty(TyKind::Struct(state)))
        }
        // The ring of an input of the head and the array of its output (§11.9, S-1208).
        (PlanKind::Instance { callee, .. }, Part::Gather { .. } | Part::Deal(_)) => {
            let fd = lw.a.def(*callee).as_flow();
            let ty = match part {
                Part::Gather { port: Port::Input(input), .. } => {
                    fd.and_then(|f| f.inputs.get(input as usize)).map(|i| i.ty)
                }
                _ => fd.map(|f| f.out),
            };
            let ty = ty.ok_or_else(|| internal(span, format!("a ring or an array {part:?} of no port")));
            // The ring of a condition (§11.10).
            let ty = if let Part::Gather { port: Port::Cond(_), .. } = part {
                Types::BOOL
            } else {
                lw.core_ty(ty?, &[], span)?
            };
            Ok(lw.ty(TyKind::Array(ty, super::chain::len(n, part, span)?)))
        }
        // Of a guard (§11.10, S-1220): its condition, its count, its held output; of a
        // delay whether it ran.
        (_, Part::On(_) | Part::Ran | Part::Open | Part::Back(_)) => Ok(Types::BOOL),
        (_, Part::Count(_)) => Ok(Types::U32),
        (PlanKind::Prev { ty, .. } | PlanKind::Delay { ty, .. } | PlanKind::Vdelay { ty, .. }, Part::Held(_)) => {
            lw.core_ty(*ty, &[], span)
        }
        (PlanKind::Instance { callee, .. }, Part::Held(_)) => {
            let out = lw.a.def(*callee).as_flow().map(|f| f.out);
            lw.core_ty(out.ok_or_else(|| internal(span, "a held output of no flow"))?, &[], span)
        }
        (PlanKind::Par { fields, count, .. }, Part::Own) => {
            let inner = state_fields(lw, (flow, &mut *states), decls, info, fields)?;
            let (inner, known) = inner.into_iter().map(|(name, t, f)| ((name, t), f)).unzip();
            let tname = format!("{}.{}.State", lw.qual_name(flow), n.path);
            let tid = lw.new_type(tname, TypeDefKind::Struct { fields: inner });
            states.push((tid, known));
            // The array of the states of the replicas (§11.5).
            let state = lw.ty(TyKind::Struct(tid));
            Ok(lw.ty(TyKind::Array(state, *count)))
        }
        _ => Err(internal(span, format!("no field {part:?} of the node {}", n.path))),
    }
}
