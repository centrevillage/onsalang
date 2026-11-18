//! The entry of the modes stage: one walk of each body the stage reads,
//! in source order, and its one diagnostic (§18.1). The walker and what it
//! makes, and the E0704 of a place used after its root moved or a change
//! it overlaps (`Walker::used`).

use onsa_diag::hash::HashMap;
use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, StmtId};

use super::capture::Frame;
use super::flow::Run;
use super::frozen::Frozen;
use super::place::{Change, Deps, Place, Proj, path_text};
use super::release::kept;
use super::state::{LoopSum, Releases, Status};
use super::walk::Pos;
use crate::body::{BodyInfo, Copied, CopiedWhy, DropPoint, LocalId, generics_of, root_of};
use crate::def::{BodyKind, GenericDef};
use crate::names::body::{BodyNames, Origin};
use crate::ty::TyId;
use crate::{Analysis, DefId, Kind, Package, module_of_def};

/// Check the argument modes and the moves of every body the stage reads
/// (§5.2, §5.4, §7; §18.1: a body whose unit failed before is skipped), and
/// the drop points of each ([`BodyInfo::drops`]).
pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) {
    let mut ids: Vec<DefId> = a.bodies.keys().copied().filter(|&id| a.is_new(id)).collect();
    ids.sort();
    let (mut found, mut drops) = (Vec::new(), Vec::new());
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
        // The parameters of a function; a flow's body drops its state
        // freely (§12.4; R-453 is W7-04), and makes no table of drops.
        let (n, drops_made) = match a.body_kind(id) {
            Some(BodyKind::Fn(f)) => (f.params.len() as u32, true),
            Some(BodyKind::Test(_) | BodyKind::Initializer(_)) => (0, true),
            Some(BodyKind::Flow(_)) => (0, false),
            None => bug(Some(a.def(id).span), "a body the modes stage reads of no body kind"),
        };
        let mut run = w.start(w.params(), None, n);
        w.expr(&mut run, root, Pos::Return);
        w.body_end(&run, root);
        found.extend(Diagnostic::first_in_file(w.m.found));
        if drops_made {
            let ast = w.ast;
            let mut copied: Vec<Copied> =
                (w.m.copied.into_iter()).map(|((root, at), why)| Copied { root, at, why }).collect();
            copied.sort_unstable_by_key(|c| (c.root, ast.expr(c.at).span.start, c.at.0));
            drops.push((id, kept(w.m.drops, &w.m.unless, &copied), copied));
        }
    }
    a.diagnostics.extend(found);
    // The stages after read the drop points and the copies (R-32, R-83,
    // S-1035; D-15: decided here only).
    for (id, d, copied) in drops {
        let Some(info) = a.bodies.get_mut(&id) else { bug(Some(a.def(id).span), "a body walked and gone") };
        (info.drops, info.copied) = (d, copied);
    }
}

/// The rule of an E0704 after a field was taken out (S-85, §5.2).
const TAKEN: &str = "read the other fields before, or take them out together with a destructuring `let` (§5.2)";

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
    pub(super) generics: Vec<GenericDef>,
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
/// borrowed `for` loops and the guards of a borrowed `match` (`frozen.rs`),
/// and the call whose arguments it walks (`calls.rs`).
#[derive(Default)]
pub(super) struct Inside {
    pub(super) frames: Vec<Frame>,
    pub(super) frozen: Vec<Frozen>,
    /// The changes of the places of the call's direct arguments, made after
    /// it (§7, S-796).
    pub(super) after_call: Vec<(Place, Span)>,
    /// The next consumption is of a direct argument (a `move self`
    /// receiver, the argument of a `move` parameter).
    pub(super) direct: bool,
    /// An argument that overlaps an earlier one of its call (E0702), and
    /// the call: its root is not reported as used after a move in the call.
    pub(super) excuse: Option<(LocalId, Span)>,
    /// The changes made in the arguments of the calls the walk is in, and
    /// how many those calls are (S-193, S-799: `exclusive.rs`).
    pub(super) changes: Vec<Changed>,
    pub(super) calls: u32,
    /// The value of the `let` walked and the tail that made its row owned
    /// (R-476), which the E0710 of another tail notes.
    pub(super) owned_by: Option<(ExprId, ExprId)>,
}

/// A change of the place `place` at `at` in an argument of a call
/// ([`Inside::changes`]): of a direct argument, the depth of its call
/// (`direct`); `release`: the release of a Dup value (S-1030).
pub(super) struct Changed {
    pub(super) place: Place,
    pub(super) at: Span,
    pub(super) direct: Option<u32>,
    pub(super) release: bool,
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
    /// The summary of each loop, made once (the walk does not grow with
    /// the depth of the loops).
    pub(super) loops: HashMap<StmtId, LoopSum>,
    pub(super) found: Vec<Diagnostic>,
    /// The paths of fields taken out (S-85), by every walk: the E0704 after.
    pub(super) takes: HashMap<Span, Place>,
    /// The drop points the walk that reports met ([`BodyInfo::drops`]).
    pub(super) drops: Vec<DropPoint>,
    /// Of a point of a binding released on every path to it, its number
    /// and the releases: it is one only if one of them copies (S-1030).
    pub(super) unless: Vec<(usize, Releases)>,
    /// The consumptions that copy a Dup value, by the binding that keeps
    /// it and the expression, and the first reason found, by every walk
    /// (S-1030, S-1035: [`Walker::restore`], [`Walker::release`]).
    pub(super) copied: HashMap<(LocalId, ExprId), CopiedWhy>,
    /// Of each borrow binding consumed, the owned bindings whose whole it
    /// derives from, the heads that derive them and whether their value is
    /// it ([`Walker::release`]).
    pub(super) heads: HashMap<LocalId, Vec<(LocalId, crate::binding::Head, bool)>>,
    /// The expressions visited (at most twice each: by the walk that
    /// reports and by the one that makes a loop's summary).
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

    /// The kind of the values of the type `ty`, a type parameter by its
    /// bounds (R-30, [`crate::kind::kind_in_body`]); `None` with no answer.
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
        match r.cur.state().status(p.root)? {
            &Status::Moved { at, via_loop } => Some(Why::Moved(at, via_loop)),
            Status::Released { .. } => None,
            Status::Stale { changes } => (changes.iter())
                .filter_map(|(&k, &c)| Some(Why::Stale(c, self.m.places[k as usize].1.reaches(p)?, k as usize)))
                .min_by_key(|why| match why {
                    Why::Stale(c, ..) | Why::Moved(c, _) => *c,
                }),
        }
    }

    /// The place `p` is used at `at` (read by the pattern element `by` of a
    /// head, S-803): an E0704 if it is not live.
    pub(super) fn used(&mut self, r: &mut Run, p: &Place, at: Span, by: Option<Span>) -> bool {
        let l = p.root;
        self.read_captured(l, at);
        self.restore(r, l, (at, None));
        let Some(why) = self.unusable(r, p).filter(|_| self.reports) else { return true };
        let name = &self.info.locals[l.0 as usize].name;
        let d = match why {
            // The E0702 of the argument, not this symptom (§18.1).
            Why::Moved(m, _) if self.inside.excuse.is_some_and(|(x, c)| x == l && c.contains(m.start)) => {
                return false;
            }
            Why::Moved(m, via_loop) => {
                // S-85: by a field taken out, said so, with how to read the others.
                let took =
                    self.m.takes.get(&m).map(|t| format!(" when `{}` was taken out", self.place_text(m, &[], t)));
                let when = took.as_deref().unwrap_or_default();
                let message = if via_loop {
                    // Only a binding that can be written is live again (S-789).
                    let assign = if self.writable(l) { "; assign it before the loop ends" } else { "" };
                    format!("`{name}` is moved here in a previous iteration of the loop{when}{assign} (§5.2)")
                } else {
                    format!("`{name}` was moved{when} and cannot be used again (§5.2)")
                };
                let d = Diagnostic::new(Stage::Modes, Code::E0704, at, message);
                match took {
                    None => d.with_note(m, "moved here"),
                    Some(_) => d.with_note(m, "taken out here").with_rule(TAKEN),
                }
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
}
