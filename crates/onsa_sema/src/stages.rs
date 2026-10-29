//! The order of the stages that check the bodies (spec §18.1, S-267), and
//! the record of the failed stages that they read (S-64, S-78): in a unit
//! where a stage found an error, the stages that depend on it are not run.
//! The signatures are checked before, by `sig::collect_and_lower`, in every
//! unit: the other units read the tables they make. What a later stage
//! reports there is dropped by the choice of a unit's diagnostic
//! (`onsa_driver::reduce`), which also chooses among those of one stage.

use std::collections::HashMap;

use onsa_diag::{Diagnostic, FileId, Stage};
use onsa_syntax::ast::ItemId;

use crate::{Analysis, DefId, Package, body, effects, flatten, modes, names, rt};

/// Check the bodies: names, types (a flow body's types and flow checks in
/// one walk), argument modes and moves, `rt` and effects (§18.1). Each stage
/// after the names reads the record made after the stage before it. The
/// unused bindings (E0309), the last stage, are reported by the names walk
/// with their stage, and dropped by the choice in a unit with another error
/// (S-726).
pub(crate) fn check_bodies(pkg: &Package, a: &mut Analysis) {
    names::body::walk_bodies(pkg, a);
    a.failures = Failures::of(pkg, a);
    body::check_all(pkg, a);
    a.failures = Failures::of(pkg, a);
    let moved = modes::check_all(pkg, a);
    a.failures = Failures::of(pkg, a);
    rt::check_all(pkg, a, &moved);
    effects::check_all(pkg, a, &moved);
}

/// The earliest check stage that found an error in the unit of each def
/// with an error (§18.1). No stage writes it: a stage that reports a
/// diagnostic with its stage ([`Diagnostic::stage`]) records the failure
/// (D-15), and [`Failures::of`] makes the record again from all of them.
/// What stops a walk with no diagnostic (a name the names stage holds as an
/// error, S-692) is no failure of the unit and not in it: the marks of the
/// bodies tell it (`complete`).
#[derive(Debug, Default)]
pub(crate) struct Failures {
    by_def: HashMap<DefId, Stage>,
}

impl Failures {
    /// The record of the diagnostics so far: of the syntax stage in each
    /// module, and of the analysis. A diagnostic goes to its unit as the
    /// choice of a unit's diagnostic puts it ([`onsa_syntax::units::Units::assign`]):
    /// the members of an item whose heading has an error are of its unit.
    /// O(D log U + U + N) for D diagnostics, U units and N defs.
    pub(crate) fn of(pkg: &Package, a: &Analysis) -> Failures {
        let mut of_file: HashMap<FileId, Vec<&Diagnostic>> = HashMap::new();
        for d in &a.diagnostics {
            of_file.entry(d.span.file).or_default().push(d);
        }
        let mut failed: HashMap<(FileId, ItemId), Stage> = HashMap::new();
        for m in flatten(pkg).into_iter().flat_map(|p| &p.modules) {
            let theirs = of_file.remove(&m.file).unwrap_or_default();
            let ds: Vec<&Diagnostic> = m.parsed.diagnostics.iter().chain(theirs).collect();
            if ds.is_empty() {
                continue;
            }
            let units = &m.parsed.units;
            let (assigned, heading_error) = units.assign(&ds);
            let mut first: Vec<Option<Stage>> = vec![None; units.list.len()];
            for (d, u) in ds.iter().zip(assigned) {
                if let Some(u) = u {
                    first[u] = Some(earlier(first[u], d.stage));
                }
            }
            for (u, unit) in units.list.iter().enumerate() {
                let stage = match unit.parent {
                    Some(p) if heading_error[p] => first[p],
                    _ => first[u],
                };
                if let (Some(stage), Some(item)) = (stage, unit.item) {
                    failed.insert((m.file, item), stage);
                }
            }
        }
        let by_def = (0..a.defs.len() as u32)
            .map(DefId)
            .filter_map(|id| {
                let def = a.def(id);
                let file = a.modules.get(def.module).file?;
                failed.get(&(file, def.item?)).map(|&s| (id, s))
            })
            .collect();
        Failures { by_def }
    }

    /// `stage` is not run on the body of `def`: a stage before it found an
    /// error in its unit. One of the same stage does not stop it (the choice
    /// takes the first of a stage by its place).
    pub(crate) fn skips(&self, def: DefId, stage: Stage) -> bool {
        self.by_def.get(&def).is_some_and(|s| s.check_rank() < stage.check_rank())
    }

    /// The earliest stage that found an error in the unit of `def`.
    #[cfg(test)]
    pub(crate) fn of_def(&self, def: DefId) -> Option<Stage> {
        self.by_def.get(&def).copied()
    }
}

/// The earlier of a unit's stage so far and a check stage, in
/// [`Stage::CHECK_ORDER`].
fn earlier(so_far: Option<Stage>, stage: Stage) -> Stage {
    match so_far {
        Some(s) if s.check_rank() <= stage.check_rank() => s,
        _ => stage,
    }
}
