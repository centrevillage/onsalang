//! The entry of the new modes stage (W4-07 memo 1.1, 1.4, 2.10): one walk
//! of each body the stage reads, in source order, and its one diagnostic.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Ast, StmtId};

use super::MovedLocals;
use super::capture::Frame;
use super::flow::Run;
use super::place::{Deps, Place};
use super::state::{LoopSum, Status};
use super::walk::Pos;
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
        // A body is made with its names, for an item of a module that has
        // one (`body::check_all`): never without them.
        let found_all = (module_of_def(pkg, a, id), root_of(a, id), a.bodies.get(&id), a.names.get(&id));
        let (Some(module), Some(root), Some(info), Some(names)) = found_all else {
            onsa_diag::internal::bug(Some(a.def(id).span), "a body the modes stage reads with no module, root or names")
        };
        let _scope = onsa_diag::internal::item_scope(a.def(id).span);
        let mut w = Walker::new(a, (&module.parsed.ast, &module.text), names, info, generics_of(a, id));
        w.deps = Deps::of_body((w.ast, names, info), root, |t| w.kind_of(t) == Some(Kind::Copy));
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
    /// The text of the module (the blanks a candidate removes with a mark).
    pub(super) text: &'a str,
    pub(super) names: &'a BodyNames,
    pub(super) info: &'a BodyInfo,
    generics: Vec<GenericDef>,
    /// The local of each `var`.
    pub(super) vars: HashMap<StmtId, LocalId>,
    /// The walk reports: the one of the body, not one that makes a loop's
    /// summary, which does not know the state before the loop.
    pub(super) reports: bool,
    /// The index of §7 (`place.rs`).
    pub(super) deps: Deps,
    pub(super) inside: Inside,
    pub(super) m: Made,
}

/// What the walk is in: the anonymous functions (`capture.rs`), and the
/// call whose arguments it walks (`calls.rs`).
#[derive(Default)]
pub(super) struct Inside {
    pub(super) frames: Vec<Frame>,
    /// The changes of the places of the call's direct arguments, made after
    /// it (§7, S-796).
    pub(super) after_call: Vec<(Place, Span)>,
    /// The next consumption is of a direct argument (a `move self` receiver).
    pub(super) direct: bool,
    /// An argument that overlaps an earlier one of its call (E0702), and
    /// the call: its root is not reported as used after a move in the call.
    pub(super) excuse: Option<(LocalId, Span)>,
}

/// What the walk of a body makes as it goes.
#[derive(Default)]
pub(super) struct Made {
    kinds: HashMap<TyId, Option<Kind>>,
    /// The summary of each loop, made once (memo 3).
    pub(super) loops: HashMap<StmtId, LoopSum>,
    pub(super) found: Vec<Diagnostic>,
    /// The owned Affine locals a move made `Moved` ([`MovedLocals`]).
    moved: HashSet<LocalId>,
    /// The expressions visited (memo 3: at most twice each).
    #[cfg(test)]
    pub(super) visits: usize,
}

impl<'a> Walker<'a> {
    pub(super) fn new(
        a: &'a Analysis,
        (ast, text): (&'a Ast, &'a str),
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
        let (deps, inside) = (Deps::default(), Inside::default());
        Walker { a, ast, text, names, info, generics, vars, reports: true, deps, inside, m: Made::default() }
    }

    /// The kind of the values of the type `ty` (R-30: an unknown one is
    /// Affine; `None` for a second-class value and the error type).
    pub(super) fn kind_of(&mut self, ty: TyId) -> Option<Kind> {
        let (a, generics) = (self.a, &self.generics);
        *self.m.kinds.entry(ty).or_insert_with(|| crate::kind::kind_in_body(a, ty, generics))
    }

    /// Whether the binding `l` can be written as a whole (§5.1).
    pub(super) fn writable(&self, l: LocalId) -> bool {
        self.info.locals[l.0 as usize].state.writable()
    }

    /// Whether `l` is live in `r` (in a walk that makes a loop's summary,
    /// always: the state before the loop is not known there).
    pub(super) fn live(&self, r: &Run, l: LocalId) -> bool {
        !self.reports || r.cur.status(l).is_none()
    }

    /// `l` is used at `at`: an E0704 if it is not live.
    pub(super) fn used(&mut self, r: &Run, l: LocalId, at: Span) -> bool {
        self.read_captured(l, at);
        let Some(status) = r.cur.status(l).filter(|_| self.reports) else { return true };
        let name = &self.info.locals[l.0 as usize].name;
        let d = match status {
            // The E0702 of the argument, not this symptom (memo 2.10).
            Status::Moved { at: m, .. } if self.inside.excuse.is_some_and(|(x, c)| x == l && c.contains(m.start)) => {
                return false;
            }
            Status::Moved { at: m, via_loop } => {
                let message = if via_loop {
                    // Only a binding that can be written is live again (S-789).
                    let assign = if self.writable(l) { "; assign it before the loop ends" } else { "" };
                    format!("`{name}` is moved here in a previous iteration of the loop{assign} (§5.2)")
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
        self.report(d);
        false
    }

    /// Found by the walk that reports.
    pub(super) fn report(&mut self, d: Diagnostic) {
        if self.reports {
            self.m.found.push(d);
        }
    }

    /// The owned Affine local `l` is moved at `at` (§5.2): a change (§7),
    /// after the call of a `direct` argument.
    pub(super) fn move_local(&mut self, r: &mut Run, l: LocalId, at: Span, direct: bool) {
        r.cur.set(l, Status::Moved { at, via_loop: false });
        self.change(r, Place { root: l, proj: Vec::new() }, at, direct);
        if self.reports {
            self.m.moved.insert(l);
        }
    }
}
