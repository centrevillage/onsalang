//! The exclusivity of the places of one call (§5.2, §3.5; W4-07 memo 2.5,
//! W4-08 memo 2): its arguments that are places, which overlap one another
//! or a change made in another argument (E0702).

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Stage};
use onsa_syntax::ast::{Arg, ExprId, Mode};

use super::calls::Takes;
use super::check::Walker;
use super::place::{Place, place_of};
use crate::Kind;
use crate::body::LocalId;

/// An argument of a call that is a place (E0702): its expression, how it
/// is passed, its place, and its root if a binding of the index (S-796);
/// `copied`, a Dup value at a `move` parameter or receiver, which counts as
/// a read (S-801).
pub(super) struct Passed {
    at: ExprId,
    mode: Mode,
    place: Place,
    via: Option<LocalId>,
    copied: bool,
}

/// The note of a Dup value passed to a `move` parameter (S-801).
const COPIED: &str = "a Dup value passed to a `move` parameter is copied, and read here (§5.2)";

/// How a place is passed, in a message.
fn how(m: Mode) -> &'static str {
    match m {
        Mode::Inout => "as `inout`",
        Mode::Move => "as `move`",
        Mode::Borrow => "borrowed",
    }
}

impl Walker<'_> {
    /// E0702 (memo 2.5; §5.2, S-787, S-796): an argument (the receiver
    /// first) that is a place overlapping the place of an earlier one, one
    /// of them `inout` or `move`, at the later one; the arguments found so.
    /// Each argument is evaluated before the call, so the order is not what
    /// counts, and a value made of a place (`xs.fill!(xs.len())`) is no
    /// place. A borrow binding that is not Copy stands for the places it
    /// derives from (S-796). And the places passed, for the changes made
    /// in the other arguments ([`Walker::changed_in_args`]).
    pub(super) fn exclusive(
        &mut self,
        receiver: Option<(ExprId, Mode)>,
        args: &[Arg],
        takes: &[Takes],
    ) -> (Vec<ExprId>, Vec<Passed>) {
        let params = args.iter().zip(takes).filter_map(|(a, t)| match t {
            Takes::Param(m, _) => Some((a.expr, *m)),
            Takes::Element => None,
        });
        let passed: Vec<Passed> = receiver.into_iter().chain(params).filter_map(|(x, m)| self.passed(x, m)).collect();
        let mut later = Vec::new();
        for (j, b) in passed.iter().enumerate() {
            let excl = b.mode != Mode::Borrow;
            let mut earlier = passed[..j].iter().filter(|a| excl || a.mode != Mode::Borrow);
            if let Some(a) = earlier.find(|a| self.deps.meets(&a.place, &b.place)) {
                later.push(b.at);
                let d = self.overlapping(a, b);
                self.report(d);
            }
        }
        (later, passed)
    }

    /// The argument `x` passed as `mode`, if it is a place (S-787: the
    /// `move` of an Affine field's path consumes its root whole; S-801: a
    /// Dup value at a `move` parameter or receiver is copied, and counts as
    /// a read of its place, as at a borrowed one; a value with no kind too).
    fn passed(&mut self, x: ExprId, mut mode: Mode) -> Option<Passed> {
        let mut place = place_of(self.ast, self.names, x)?;
        let ty = self.info.expr_types.get(&self.ast.without_parens(x)).copied();
        let kind = ty.and_then(|t| self.kind_of(t));
        // A value with no kind (§18.1: an unknown bound, the error type) may move or not: a read too.
        let read = mode == Mode::Move && kind != Some(Kind::Affine);
        let copied = read && kind.is_some();
        if read {
            mode = Mode::Borrow;
        } else if mode == Mode::Move {
            place.proj.clear();
        }
        let via = self.deps.indexed(place.root).then_some(place.root);
        Some(Passed { at: x, mode, place, via, copied })
    }

    /// The E0702 of `b`, which overlaps the earlier `a`: "twice" of two of
    /// one mode, else "and" (§5.2's two forms), of their root, or of the
    /// arguments as written when one is a binding of the index (S-796), noted
    /// at it; noted at `a`.
    fn overlapping(&self, a: &Passed, b: &Passed) -> Diagnostic {
        let n = &self.info.locals[a.place.root.0 as usize].name;
        let text = |p: &Passed| self.passed_text(p);
        let derived = a.via.is_some() || b.via.is_some();
        let (message, note) = if a.mode == b.mode {
            let message = match derived {
                true => format!(
                    "`{}` and `{}` are both passed {} in one call; the places may overlap (§5.2)",
                    text(a),
                    text(b),
                    how(a.mode)
                ),
                false => {
                    format!("`{n}` is passed {} twice in one call; the two places may overlap (§5.2)", how(a.mode))
                }
            };
            (message, format!("first {} here", how(a.mode).trim_start_matches("as ")))
        } else {
            let rank = |m: Mode| [Mode::Inout, Mode::Move, Mode::Borrow].iter().position(|&x| x == m);
            let (x, y) = if rank(a.mode) < rank(b.mode) { (a.mode, b.mode) } else { (b.mode, a.mode) };
            let message = match derived {
                true => format!(
                    "`{}` is passed {} and `{}` {} in the same call; the places may overlap (§5.2)",
                    text(a),
                    how(a.mode),
                    text(b),
                    how(b.mode)
                ),
                false => {
                    format!("`{n}` is passed {} and {} in the same call; the places may overlap (§5.2)", how(x), how(y))
                }
            };
            (message, format!("{} here", how(a.mode).trim_start_matches("as ")))
        };
        let mut d = Diagnostic::new(Stage::Modes, Code::E0702, self.ast.expr(b.at).span, message)
            .with_note(self.ast.expr(a.at).span, note);
        for p in [a, b].into_iter().filter(|p| p.copied) {
            d = d.with_note(self.ast.expr(p.at).span, COPIED);
        }
        [a, b].into_iter().filter_map(|p| p.via).fold(d, |d, l| {
            let (at, note) = self.bound_note(l);
            d.with_note(at, note)
        })
    }

    /// The argument `p` as written (on more than one line, its name and path).
    fn passed_text(&self, p: &Passed) -> String {
        let at = self.ast.expr(p.at).span;
        let Some(place) = place_of(self.ast, self.names, p.at) else { bug(Some(at), "a place passed is no place") };
        self.place_text(at, &[], &place)
    }

    /// The E0702 of the changes (§7) made while the arguments of a call were
    /// walked, from `start` on (§3.5, §5.2, S-193, S-799): each that may
    /// overlap a place `passed` in the call, other than the arguments it is
    /// in, at the later of the two, the first such place (S-796: a binding
    /// of the index stands for its places). The change of a direct argument
    /// is `exclusive`'s, and changes are not compared with one another
    /// (`h(next(inout k), next(inout k))`). Out of the arguments of every
    /// call, the record is emptied.
    pub(super) fn changed_in_args(&mut self, start: usize, passed: &[Passed]) {
        for (w, at) in self.inside.changes[start..].iter().filter(|_| self.reports) {
            let span = |p: &Passed| self.ast.expr(p.at).span;
            let own = |p: &Passed| *at == span(p) || *at == self.ast.expr(self.ast.without_parens(p.at)).span;
            let holds = |p: &Passed| span(p).start <= at.start && at.end <= span(p).end;
            if passed.iter().any(own) {
                continue;
            }
            let Some(q) = passed.iter().find(|q| !holds(q) && self.deps.meets(w, &q.place)) else { continue };
            let (changed, arg) = (self.place_text(*at, &[], w), self.passed_text(q));
            let message = format!(
                "`{changed}` is changed in another argument while `{arg}` is passed {} in the same call; the places may overlap (§3.5, §5.2)",
                how(q.mode)
            );
            let (first, last, note) = match at.start < span(q).start {
                true => (*at, span(q), "changed here".to_string()),
                false => (span(q), *at, format!("{} here", how(q.mode).trim_start_matches("as "))),
            };
            let mut d = Diagnostic::new(Stage::Modes, Code::E0702, last, message).with_note(first, note);
            if q.copied {
                d = d.with_note(span(q), COPIED);
            }
            if let Some(l) = q.via {
                let (at, note) = self.bound_note(l);
                d = d.with_note(at, note);
            }
            self.m.found.push(d);
        }
        if self.inside.calls == 0 {
            self.inside.changes.clear();
        }
    }
}
