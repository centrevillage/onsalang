//! The cycles of the constants (E0312, §6.6) and of the flow instances
//! (E0817, §11.5), from the records of the bodies alone (D-15): a constant
//! reads the constants its initializer names ([`super::BodyNames::paths`]
//! and [`super::BodyNames::interp`]), a flow makes instances of the flows
//! of [`super::BodyNames::instances`]. No edge goes from a flow to a
//! constant, so one graph holds both, and each cycle is of one kind. One
//! report per collection (§18.1, S-734, S-742), at the name of its first
//! declaration, whose unit stops in the names stage; the units of the
//! others are checked. O(D + B) for D declarations and B records, and the
//! components ([`crate::names::cyclic`]) with no recursion.

use std::collections::HashMap;

use onsa_diag::Code;

use super::PathRes;
use crate::def::{DefKind, ModId};
use crate::resolve::Entity;
use crate::{Analysis, DefId, Package};

pub(super) fn report(flat: &[&Package], a: &mut Analysis) {
    let mut points: Vec<DefId> =
        a.names.keys().copied().filter(|&d| matches!(a.def(d).kind, DefKind::Const(_) | DefKind::Flow(_))).collect();
    points.sort();
    let at: HashMap<DefId, usize> = points.iter().enumerate().map(|(p, &d)| (d, p)).collect();
    // SPEC-GAP(S-761): a name after the stop of a walk (at an error of the
    // names stage) is no edge: the record ends there.
    let adj: Vec<Vec<usize>> =
        points.iter().map(|d| edges(a, *d).into_iter().filter_map(|t| at.get(&t).copied()).collect()).collect();
    let (comp, cycled) = crate::names::cyclic(&adj);
    let mut groups: Vec<Vec<DefId>> = vec![Vec::new(); points.len()];
    let mut order = Vec::new();
    for p in (0..points.len()).filter(|&p| cycled[p]) {
        if groups[comp[p]].is_empty() {
            order.push(comp[p]);
        }
        groups[comp[p]].push(points[p]);
    }
    for c in order {
        let decls = std::mem::take(&mut groups[c]);
        let mods: Vec<ModId> = decls.iter().map(|&d| a.def(d).module).collect();
        // SPEC-GAP(S-760): a cycle of flow instances across modules is in a
        // cycle of the imports, as one of types and constants: its E0310 is
        // the one report.
        if a.modules.across_one_cycle(&mods) {
            continue;
        }
        let flow = matches!(a.def(decls[0]).kind, DefKind::Flow(_));
        let what =
            if flow { (Code::E0817, "cyclic flow instances, §11.5") } else { (Code::E0312, "cyclic constant, §6.6") };
        let in_cycle = |t: &DefId| at.get(t).is_some_and(|&q| comp[q] == c);
        let notes = flow.then(|| {
            let instances = decls.iter().flat_map(|d| &a.names[d].instances).filter(|(t, _)| in_cycle(t));
            instances.map(|&(_, span)| (span, "this instance is in the cycle".to_string())).collect()
        });
        let (first, d) = crate::names::cycle_diagnostic((a, flat), what, decls, notes);
        a.diagnostics.push(d);
        if let Some(n) = a.names.get_mut(&first) {
            (n.reported, n.complete) = (true, false);
        }
    }
}

/// The declarations the body of `d` depends on: of a flow, the flows it
/// makes instances of; else the items its names stop at.
fn edges(a: &Analysis, d: DefId) -> Vec<DefId> {
    let n = &a.names[&d];
    if matches!(a.def(d).kind, DefKind::Flow(_)) {
        return n.instances.iter().map(|&(f, _)| f).collect();
    }
    let names = n.paths.values().chain(n.interp.values().flatten().map(|(_, r)| r));
    let items = names.filter_map(|r| match r {
        PathRes::Item { entity: Entity::Def(c) | Entity::Member(c), .. } => Some(*c),
        _ => None,
    });
    items.collect()
}
