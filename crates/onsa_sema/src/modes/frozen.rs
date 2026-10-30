//! The places a borrowed `for` holds (W4-09 memo 2.1; §5.4, R-24, S-798):
//! its body changes none of them, nor a part of one, where a derived
//! binding stands for the places it derives from (S-796). W4-10's guards
//! hold the places of their head by the same frames.

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::StmtId;

use std::collections::BTreeSet;

use super::check::Walker;
use super::place::{Place, head_places};
use crate::binding::Head;
use crate::body::LocalId;

/// The places of the head of a `for` the walk is in, and the text of each
/// (S-604: of each tail; a view's base, S-217); none at an owned row. With
/// the roots of each ([`super::place::Deps::origins`]).
pub(super) struct Frozen {
    places: Vec<(Place, Span, BTreeSet<LocalId>)>,
}

impl Walker<'_> {
    /// The frame of the `for` `s`, while its loop is walked.
    pub(super) fn freeze(&mut self, s: StmtId) {
        let places = head_places((self.ast, self.names, self.info), Head::For(s)).unwrap_or_default();
        let places = places.into_iter().map(|(p, at)| {
            let roots = self.deps.origins(p.root);
            (p, at, roots)
        });
        let places = places.collect();
        self.inside.frozen.push(Frozen { places });
    }

    /// Whether the change of `w` at `at` (a write, a move) is of a place a
    /// frame holds: then an E0715 at `at`, noted at the place of each frame
    /// it overlaps and at a binding that place derives from. The caller
    /// changes no state then (S-798).
    pub(super) fn held(&mut self, w: &Place, at: Span) -> bool {
        // A place of no root in common is passed over before `meets` (memo 3: its ways are long).
        let mine = self.deps.origins(w.root);
        let hits: Vec<(Place, Span)> = (self.inside.frozen.iter().flat_map(|f| &f.places))
            .filter(|(p, _, o)| !mine.is_disjoint(o) && self.deps.meets(w, p))
            .map(|(p, at, _)| (p.clone(), *at))
            .collect();
        let Some((p, first)) = hits.first() else { return false };
        let (what, over) = (self.place_text(at, &[], w), self.place_text(*first, &[], p));
        let message = format!("cannot change `{what}` in the body of a `for` over `{over}`, which it overlaps (§5.4)");
        let mut d = Diagnostic::new(Stage::Modes, Code::E0715, at, message)
            .with_rule("to change the elements while iterating, loop over the indexes (§5.4)");
        let mut bound = Vec::new();
        for (p, span) in &hits {
            d = d.with_note(*span, "iterated by this `for`");
            if self.deps.indexed(p.root) && !bound.contains(&p.root) {
                bound.push(p.root);
                let (b, note) = self.bound_note(p.root);
                d = d.with_note(b, note);
            }
        }
        self.report(d);
        true
    }
}
