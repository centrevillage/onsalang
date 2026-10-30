//! The entry of the modes stage (W4-07 memo 1.1, 1.4, 2.10): one walk
//! of each body the stage reads, in source order, and its one diagnostic.

use std::collections::{HashMap, HashSet};

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, StmtId};

use super::MovedLocals;
use super::capture::Frame;
use super::flow::Run;
use super::frozen::Frozen;
use super::place::{Change, Deps, Place, Proj, path_text};
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
            bug(Some(a.def(id).span), "a body the modes stage reads with no module, root or names")
        };
        let _scope = onsa_diag::internal::item_scope(a.def(id).span);
        let mut w = Walker::new(a, (&module.parsed.ast, &module.text), (names, info, root), generics_of(a, id));
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
    /// The local of each binding no pattern makes (a `var`).
    pub(super) origins: HashMap<Origin, LocalId>,
    /// The walk reports: the one of the body, not one that makes a loop's
    /// summary, which does not know the state before the loop.
    pub(super) reports: bool,
    /// The index of §7 (`place.rs`).
    pub(super) deps: Deps,
    pub(super) inside: Inside,
    pub(super) m: Made,
}

/// What the walk is in: the anonymous functions (`capture.rs`), the
/// borrowed `for` loops (`frozen.rs`), and the call whose arguments it walks
/// (`calls.rs`).
#[derive(Default)]
pub(super) struct Inside {
    pub(super) frames: Vec<Frame>,
    pub(super) frozen: Vec<Frozen>,
    /// The changes of the places of the call's direct arguments, made after
    /// it (§7, S-796).
    pub(super) after_call: Vec<(Place, Span)>,
    /// The next consumption is of a direct argument (a `move self` receiver).
    pub(super) direct: bool,
    /// An argument that overlaps an earlier one of its call (E0702), and
    /// the call: its root is not reported as used after a move in the call.
    pub(super) excuse: Option<(LocalId, Span)>,
    /// The changes made in the arguments of the calls the walk is in, and
    /// how many those calls are (S-193, S-799: `exclusive.rs`).
    pub(super) changes: Vec<(Place, Span)>,
    pub(super) calls: u32,
}

/// Why a place cannot be used: its root moved (at, by the loop), or it
/// overlaps the change at a place (and ends before it).
enum Why {
    Moved(Span, bool),
    Stale(Span, bool, usize),
}

/// What the walk of a body makes as it goes.
#[derive(Default)]
pub(super) struct Made {
    kinds: HashMap<TyId, Option<Kind>>,
    /// Each place changed (§7) and its change, made once, by its number.
    pub(super) places: Vec<(Place, Change)>,
    pub(super) ids: HashMap<Place, u32>,
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
    /// The walk of the body `root`, with its index of §7.
    pub(super) fn new(
        a: &'a Analysis,
        (ast, text): (&'a Ast, &'a str),
        (names, info, root): (&'a BodyNames, &'a BodyInfo, ExprId),
        generics: Vec<GenericDef>,
    ) -> Self {
        let (origins, deps, inside) = (crate::body::origins(names), Deps::default(), Inside::default());
        let mut w =
            Walker { a, ast, text, names, info, generics, origins, reports: true, deps, inside, m: Made::default() };
        w.deps = Deps::of_body((ast, names, info), root, |t| w.kind_of(t) == Some(Kind::Copy));
        w
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

    /// Whether the place `p` is live in `r` (in a walk that makes a loop's
    /// summary, always: the state before the loop is not known there).
    pub(super) fn live(&self, r: &Run, p: &Place) -> bool {
        !self.reports || self.unusable(r, p).is_none()
    }

    /// Why the place `p` cannot be used in `r`: its root moved, or a change
    /// it overlaps, the first, and whether `p` ends before it (§7, S-803: a
    /// path of a binding is the place it derives from, the steps composed).
    fn unusable(&self, r: &Run, p: &Place) -> Option<Why> {
        match r.cur.status(p.root)? {
            &Status::Moved { at, via_loop } => Some(Why::Moved(at, via_loop)),
            Status::Stale { changes } => (changes.iter())
                .filter_map(|(&k, &c)| Some(Why::Stale(c, self.m.places[k as usize].1.reaches(p)?, k as usize)))
                .min_by_key(|why| match why {
                    Why::Stale(c, ..) | Why::Moved(c, _) => *c,
                }),
        }
    }

    /// The place `p` is used at `at` (read by the pattern element `by` of a
    /// head, S-803): an E0704 if it is not live.
    pub(super) fn used(&mut self, r: &Run, p: &Place, at: Span, by: Option<Span>) -> bool {
        let l = p.root;
        self.read_captured(l, at);
        let Some(why) = self.unusable(r, p).filter(|_| self.reports) else { return true };
        let name = &self.info.locals[l.0 as usize].name;
        let d = match why {
            // The E0702 of the argument, not this symptom (memo 2.10).
            Why::Moved(m, _) if self.inside.excuse.is_some_and(|(x, c)| x == l && c.contains(m.start)) => {
                return false;
            }
            Why::Moved(m, via_loop) => {
                let message = if via_loop {
                    // Only a binding that can be written is live again (S-789).
                    let assign = if self.writable(l) { "; assign it before the loop ends" } else { "" };
                    format!("`{name}` is moved here in a previous iteration of the loop{assign} (§5.2)")
                } else {
                    format!("`{name}` was moved and cannot be used again (§5.2)")
                };
                Diagnostic::new(Stage::Modes, Code::E0704, at, message).with_note(m, "moved here")
            }
            Why::Stale(c, prefix, k) => {
                // As written, unless read by a pattern.
                let what = match by {
                    None => self.place_text(at, &[], p),
                    Some(_) => path_text(name, &p.proj),
                };
                let changed = self.place_text(c, &[], &self.m.places[k].0);
                let message = format!(
                    "`{what}` cannot be used after `{changed}` changed: the place it borrows overlaps the changed place (§7)"
                );
                let (bound, note) = self.bound_note(l);
                let d = Diagnostic::new(Stage::Modes, Code::E0704, at, message)
                    .with_note(c, "changed here")
                    .with_note(bound, note);
                let d = by.into_iter().fold(d, |d, b| d.with_note(b, "read by this pattern"));
                match prefix {
                    true => d.with_rule(format!(
                        "a path of `{name}` that does not overlap `{changed}` can still be used (§7)"
                    )),
                    false => d,
                }
            }
        };
        self.report(d);
        false
    }

    /// The note at the binding `l` of the index (§5.4): the places it
    /// derives from directly, as written (a source and the steps of the
    /// pattern; E0704's and E0702's).
    pub(super) fn bound_note(&self, l: LocalId) -> (Span, String) {
        let mut from: Vec<String> = Vec::new();
        for s in self.deps.sources(l) {
            let t = self.place_text(s.at, &s.pat, &s.place);
            if !from.contains(&t) {
                from.push(t);
            }
        }
        let local = &self.info.locals[l.0 as usize];
        (local.span, format!("`{}` is bound here as a borrow of `{}` (§5.4)", local.name, from.join("` or `")))
    }

    /// The text of the place `p` in a message: as written at `at`, then
    /// the steps `more`; on more than one line, its name and path (an index
    /// `[_]`).
    pub(super) fn place_text(&self, at: Span, more: &[Proj], p: &Place) -> String {
        let text = &self.text[at.start as usize..at.end as usize];
        match text.contains('\n') {
            false => path_text(text, more),
            true => path_text(&self.info.locals[p.root.0 as usize].name, &p.proj),
        }
    }

    /// Found by the walk that reports.
    pub(super) fn report(&mut self, d: Diagnostic) {
        if self.reports {
            self.m.found.push(d);
        }
    }

    /// The owned Affine local `l` is moved at `at` (§5.2): a change (§7),
    /// after the call of a `direct` argument. Of a place a `for` holds, the
    /// E0715 only (S-798).
    pub(super) fn move_local(&mut self, r: &mut Run, l: LocalId, at: Span, direct: bool) {
        let whole = Place { root: l, proj: Vec::new() };
        if self.held(&whole, at) {
            return self.record(&whole, at);
        }
        r.cur.set(l, Status::Moved { at, via_loop: false });
        self.change(r, whole, at, direct);
        if self.reports {
            self.m.moved.insert(l);
        }
    }
}
