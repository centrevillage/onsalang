//! The entry of the new modes stage (W4-07 memo 1.1, 1.4, 2.10): one walk
//! of each body the stage reads, in source order, and its one diagnostic.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Ast, StmtId};

use super::MovedLocals;
use super::flow::Run;
use super::state::{LoopSum, Status};
use super::walk::Pos;
use crate::binding::Bind;
use crate::body::{BodyInfo, LocalId, generics_of, root_of};
use crate::def::GenericDef;
use crate::names::body::{BodyNames, Origin};
use crate::ty::TyId;
use crate::{Analysis, DefId, Kind, Package, module_of_def};

/// Check the argument modes and the moves of every body the stage reads
/// (§5.2, §5.4, §7; §18.1: a body whose unit failed before is skipped), and
/// the locals each moved.
#[allow(dead_code)] // Wired at the switch (W4-07 U4); the unit tests call it.
pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) -> MovedLocals {
    let mut ids: Vec<DefId> = a.bodies.keys().copied().collect();
    ids.sort();
    let (mut moved, mut found) = (MovedLocals::new(), Vec::new());
    for id in ids {
        if !a.body_checked(id, Stage::Modes) {
            continue;
        }
        let (Some(module), Some(root)) = (module_of_def(pkg, a, id), root_of(a, id)) else { continue };
        let (Some(info), Some(names)) = (a.bodies.get(&id), a.names.get(&id)) else { continue };
        let _scope = onsa_diag::internal::item_scope(a.def(id).span);
        let mut w = Walker::new(a, &module.parsed.ast, names, info, generics_of(a, id));
        w.expr(&mut Run::new(), root, Pos::Return);
        found.extend(w.m.found.into_iter().min_by(|x, y| x.order_in_file().cmp(&y.order_in_file())));
        if !w.m.moved.is_empty() {
            moved.insert(id, w.m.moved);
        }
    }
    a.diagnostics.extend(found);
    moved
}

/// The walk of one body: what it reads, and what it found. The walk does
/// not stop at an error (an erroneous operation leaves the state as it is);
/// the body reports the first of what it found in the order of §18.1.
pub(super) struct Walker<'a> {
    pub(super) a: &'a Analysis,
    pub(super) ast: &'a Ast,
    pub(super) names: &'a BodyNames,
    pub(super) info: &'a BodyInfo,
    generics: Vec<GenericDef>,
    /// The local of each `var`.
    pub(super) vars: HashMap<StmtId, LocalId>,
    /// The walk reports: the one of the body, not one that makes a loop's
    /// summary, which does not know the state before the loop.
    pub(super) reports: bool,
    pub(super) m: Made,
}

/// What the walk of a body makes as it goes.
#[derive(Default)]
pub(super) struct Made {
    kinds: HashMap<TyId, Option<Kind>>,
    /// The summary of each loop, made once (memo 3).
    pub(super) loops: HashMap<StmtId, LoopSum>,
    found: Vec<Diagnostic>,
    /// The owned Affine locals a move made `Moved` ([`MovedLocals`]).
    moved: HashSet<LocalId>,
    /// The expressions visited (memo 3: at most twice each).
    #[cfg(test)]
    pub(super) visits: usize,
}

impl<'a> Walker<'a> {
    pub(super) fn new(
        a: &'a Analysis,
        ast: &'a Ast,
        names: &'a BodyNames,
        info: &'a BodyInfo,
        generics: Vec<GenericDef>,
    ) -> Self {
        let vars = (names.bindings.iter().enumerate())
            .filter_map(|(i, b)| match b.origin {
                Origin::Var(s) => Some((s, LocalId(i as u32))),
                _ => None,
            })
            .collect();
        Walker { a, ast, names, info, generics, vars, reports: true, m: Made::default() }
    }

    /// The kind of the values of `l` (R-30: an unknown one is Affine;
    /// `None` for a second-class value and the error type).
    pub(super) fn kind(&mut self, l: LocalId) -> Option<Kind> {
        let ty = self.info.locals[l.0 as usize].ty;
        let (a, generics) = (self.a, &self.generics);
        *self.m.kinds.entry(ty).or_insert_with(|| crate::kind::kind_in_body(a, ty, generics))
    }

    /// Whether the binding `l` owns its value (§5.4).
    pub(super) fn owns(&self, l: LocalId) -> bool {
        matches!(self.info.locals[l.0 as usize].state, Bind::Owned | Bind::OwnedMut)
    }

    /// Whether the binding `l` can be written as a whole (§5.1).
    pub(super) fn writable(&self, l: LocalId) -> bool {
        matches!(self.info.locals[l.0 as usize].state, Bind::OwnedMut | Bind::Inout)
    }

    /// `l` is used at `at`: an E0704 if it is not live.
    pub(super) fn used(&mut self, r: &Run, l: LocalId, at: Span) -> bool {
        let Some(status) = r.cur.status(l).filter(|_| self.reports) else { return true };
        let name = &self.info.locals[l.0 as usize].name;
        let d = match status {
            Status::Moved { at: m, via_loop } => {
                let message = if via_loop {
                    format!(
                        "`{name}` is moved here in a previous iteration of the loop; assign it before the loop ends (§5.2)"
                    )
                } else {
                    format!("`{name}` was moved and cannot be used again (§5.2)")
                };
                Diagnostic::new(Stage::Modes, Code::E0704, at, message).with_note(m, "moved here")
            }
            Status::Stale { changed } => {
                let message = format!("`{name}` cannot be used after the place it derives from changed (§7)");
                Diagnostic::new(Stage::Modes, Code::E0704, at, message).with_note(changed, "changed here")
            }
        };
        self.m.found.push(d);
        false
    }

    /// The owned Affine local `l` is moved at `at` (§5.2).
    pub(super) fn move_local(&mut self, r: &mut Run, l: LocalId, at: Span) {
        r.cur.set(l, Status::Moved { at, via_loop: false });
        if self.reports {
            self.m.moved.insert(l);
        }
    }
}
