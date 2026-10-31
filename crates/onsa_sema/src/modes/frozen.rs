//! The places a borrowed `for` holds while its loop is walked (W4-09 memo
//! 2.1; §5.4, R-24, S-798) and a borrowed `match` while a guard of it is
//! (W4-10 memo 2.1; §7, R-110): no change of one of them, nor of a part of
//! one, where a derived binding stands for the places it derives from
//! (S-796).

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Span, Stage};

use std::collections::BTreeSet;

use super::check::Walker;
use super::place::{Place, head_places, path_text};
use crate::binding::Head;
use crate::body::LocalId;

/// The places of a head the walk is in (`Head::For` or `Head::Match`), and
/// the text of each (S-604: of each tail; a view's base, S-217); none at an
/// owned row. With the roots of each ([`super::place::Deps::origins`]).
pub(super) struct Frozen {
    head: Head,
    places: Vec<(Place, Span, BTreeSet<LocalId>)>,
}

impl Walker<'_> {
    /// The frame of `head`: of a `for` while its loop is walked, of a
    /// `match` while a guard of it is.
    pub(super) fn frame(&self, head: Head) -> Frozen {
        let places = head_places((self.ast, self.names, self.info), head).unwrap_or_default();
        let places = places.into_iter().map(|(p, at)| {
            let roots = self.deps.origins(p.root);
            (p, at, roots)
        });
        Frozen { head, places: places.collect() }
    }

    /// Whether the change of `w` at `at` (a write, a move; of the whole
    /// that a field `taken` out of it moves, S-85) is of a place a frame
    /// holds: then an E0715 at `at`, worded by the outermost frame it
    /// overlaps, noted at the place of each and at a binding that place
    /// derives from. The caller changes no state then (S-798).
    pub(super) fn held(&mut self, w: &Place, at: Span, taken: Option<&Place>) -> bool {
        let hits = self.hits(w);
        let Some((head, p, first)) = hits.first() else { return false };
        let what = match taken {
            Some(t) => {
                let whole = path_text(&self.info.locals[w.root.0 as usize].name, &w.proj);
                format!("`{whole}` (taking out `{}` moves the whole)", self.place_text(at, &[], t))
            }
            None => format!("`{}`", self.place_text(at, &[], w)),
        };
        let ((place, section, _, rule), over) = (words(*head, *first), self.place_text(*first, &[], p));
        let message = format!("cannot change {what} in {place} `{over}`, which it overlaps ({section})");
        let mut d = Diagnostic::new(Stage::Modes, Code::E0715, at, message).with_rule(rule);
        let mut bound = Vec::new();
        for (head, p, span) in &hits {
            d = d.with_note(*span, words(*head, *span).2);
            if self.deps.indexed(p.root) && !bound.contains(&p.root) {
                bound.push(p.root);
                let (b, note) = self.bound_note(p.root);
                d = d.with_note(b, note);
            }
        }
        self.report(d);
        true
    }

    /// Whether a change of `w` is of a place a frame holds (an E0715 if it
    /// were made): a candidate that makes one is none (§18.1).
    pub(super) fn holds(&self, w: &Place) -> bool {
        !self.hits(w).is_empty()
    }

    /// The places the frames hold that `w` overlaps, outermost first, with
    /// the head of each frame.
    fn hits(&self, w: &Place) -> Vec<(Head, Place, Span)> {
        // A place of no root in common is passed over before `meets` (memo 3: its ways are long).
        let mine = self.deps.origins(w.root);
        (self.inside.frozen.iter())
            .flat_map(|f| f.places.iter().map(move |p| (f.head, p)))
            .filter(|(_, (p, _, o))| !mine.is_disjoint(o) && self.deps.meets(w, p))
            .map(|(head, (p, at, _))| (head, p.clone(), *at))
            .collect()
    }
}

/// The words of an E0715 of a frame of `head` (holding a place at `at`):
/// where the change is, the section of the rule, the note at a place it
/// holds, and the rule. Only a `for` and a `match` make frames.
fn words(head: Head, at: Span) -> (&'static str, &'static str, &'static str, &'static str) {
    match head {
        Head::Match { .. } => (
            "a guard of a `match` on",
            "§7",
            "matched by this `match`",
            "the arms are tried on the value as it was matched; change it in the arm's body (§7)",
        ),
        Head::For(_) => (
            "the body of a `for` over",
            "§5.4",
            "iterated by this `for`",
            "to change the elements while iterating, loop over the indexes (§5.4)",
        ),
        Head::Let(_) => bug(Some(at), "a frame of the head of a `let`"),
    }
}
