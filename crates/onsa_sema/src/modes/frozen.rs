//! The places a borrowed `for` holds while its loop is walked (§5.4, R-24,
//! S-798) and a borrowed `match` while a guard of it is (§7, R-110): no
//! change of one of them, nor of a part of
//! one, where a derived binding stands for the places it derives from
//! (S-796). The bindings of an arm of an owned `match` are held the same
//! way while its guard is walked (§7, S-1039): no consumption of them.

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Span, Stage};

use std::collections::BTreeSet;

use onsa_syntax::ast::PatId;

use super::check::Walker;
use super::place::{Place, path_text};
use crate::binding::Head;
use crate::body::LocalId;

/// What a frame holds: the places a borrowed `for` reads while its loop is
/// walked, or a borrowed `match` while a guard of it is; or the bindings of
/// an arm of an owned `match` while its guard is.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Holds {
    For,
    Match,
    Arm,
}

/// The places a frame holds, and the text of each (S-604: of each tail; a
/// view's base, S-217; of an arm, where each binding is), with the roots of
/// each ([`super::place::Deps::origins`]); the head of the frame.
pub(super) struct Frozen {
    holds: Holds,
    head: Head,
    places: Vec<(Place, Span, BTreeSet<LocalId>)>,
}

impl Walker<'_> {
    /// The frame of `head`, borrowed from `places`, if it makes one
    /// ([`super::place::Deps::holds`]: a `for` and a `match` with a guard,
    /// never a `let`): of a `for` while its loop is walked, of a `match`
    /// while a guard of it is ([`Walker::holding`]).
    pub(super) fn frame(&self, head: Head, places: Vec<(Place, Span)>) -> Option<Frozen> {
        let holds = match head {
            Head::For(_) => Holds::For,
            Head::Match { .. } => Holds::Match,
            Head::Let(s) => bug(Some(self.ast.stmt(s).span), "the frame of a `let`"),
        };
        self.deps.holds(head).then(|| self.frozen((holds, head), places))
    }

    fn frozen(&self, (holds, head): (Holds, Head), places: Vec<(Place, Span)>) -> Frozen {
        let places = places.into_iter().map(|(p, at)| {
            let roots = self.deps.origins(p.root).collect();
            (p, at, roots)
        });
        Frozen { holds, head, places: places.collect() }
    }

    /// The frame of a guard of the arm `pat` of an owned `match` `head` (§7,
    /// S-1039): its bindings, which own the value only once the arm is
    /// chosen (a Dup one is copied where it is consumed: no change).
    pub(super) fn arm_frame(&self, head: Head, pat: PatId) -> Frozen {
        let mut places = Vec::new();
        self.each_local(pat, &mut |l| {
            places.push((Place { root: l, proj: Vec::new() }, self.info.locals[l.0 as usize].span))
        });
        self.frozen((Holds::Arm, head), places)
    }

    /// Walk `f` in the frame `held` (pushed, then popped and kept for the
    /// next walk in it, a guard's).
    pub(super) fn holding(&mut self, held: &mut Option<Frozen>, f: impl FnOnce(&mut Self)) {
        let Some(frame) = held.take() else { return f(self) };
        self.inside.frozen.push(frame);
        f(self);
        *held = self.inside.frozen.pop();
    }

    /// Whether the change of `w` at `at` (a write, a move; of the whole
    /// that a field `taken` out of it moves, S-85) is of a place a frame
    /// holds: then an E0715 at `at`, worded by the outermost frame it
    /// overlaps, noted at the place of each and at a binding that place
    /// derives from. The caller changes no state then (S-798).
    pub(super) fn held(&mut self, w: &Place, at: Span, taken: Option<&Place>) -> bool {
        let hits = self.hits(w);
        let Some(&(holds, ref p, first, _)) = hits.first() else { return false };
        let what = match taken {
            Some(t) => {
                let whole = path_text(&self.info.locals[w.root.0 as usize].name, &w.proj);
                format!("`{whole}` (taking out `{}` moves the whole)", self.place_text(at, &[], t))
            }
            None => format!("`{}`", self.place_text(at, &[], w)),
        };
        let ((place, section, _, rule), over) = (words(holds), self.place_text(first, &[], p));
        let message = match holds {
            Holds::Arm => format!(
                "cannot consume {what} in {place}: `{over}` owns its value only once the arm is chosen ({section})"
            ),
            _ => format!("cannot change {what} in {place} `{over}`, which it overlaps ({section})"),
        };
        let mut d = Diagnostic::new(Stage::Modes, Code::E0715, at, message).with_rule(rule);
        let mut bound = Vec::new();
        for &(holds, ref p, span, _) in &hits {
            d = d.with_note(span, words(holds).2);
            if self.deps.indexed(p.root) && !bound.contains(&p.root) {
                bound.push(p.root);
                let (b, note) = self.bound_note(p.root);
                d = d.with_note(b, note);
            }
        }
        self.report(d);
        true
    }

    /// The head of the outermost frame that holds a place a change of `w`
    /// is of (an E0715 if it were made): a candidate that makes one is none
    /// (§18.1), a Dup value there is copied (§5.2).
    pub(super) fn holder(&self, w: &Place) -> Option<Head> {
        self.hits(w).first().map(|h| h.3)
    }

    /// The places the frames hold that `w` overlaps, outermost first, with
    /// what each frame holds and its head.
    fn hits(&self, w: &Place) -> Vec<(Holds, Place, Span, Head)> {
        // A place of no root in common is passed over before `meets` (its ways are long).
        let mine: BTreeSet<_> = self.deps.origins(w.root).collect();
        (self.inside.frozen.iter())
            .flat_map(|f| f.places.iter().map(move |p| (f, p)))
            .filter(|(_, (p, _, o))| !mine.is_disjoint(o) && self.deps.meets(w, p))
            .map(|(f, (p, at, _))| (f.holds, p.clone(), *at, f.head))
            .collect()
    }
}

/// The words of an E0715 of a frame that `holds`: where the change is, the
/// section of the rule, the note at a place it holds, and the rule.
fn words(holds: Holds) -> (&'static str, &'static str, &'static str, &'static str) {
    match holds {
        Holds::Arm => (
            "a guard of a `match`",
            "§7",
            "bound by this arm",
            "if the guard is false, the later arms are tried on the same value; consume it in the arm's body (§7)",
        ),
        Holds::Match => (
            "a guard of a `match` on",
            "§7",
            "matched by this `match`",
            "the arms are tried on the value as it was matched; change it in the arm's body (§7)",
        ),
        Holds::For => (
            "the body of a `for` over",
            "§5.4",
            "iterated by this `for`",
            "to change the elements while iterating, loop over the indexes (§5.4)",
        ),
    }
}
