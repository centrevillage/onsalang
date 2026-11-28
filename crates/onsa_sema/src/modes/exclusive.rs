//! The exclusivity of the places of one call (§5.2, §3.5; S-193, S-799):
//! its arguments that are places, which overlap one another
//! or a change made in another argument (E0702); and of the base of an
//! index, with a change made in its index (S-1275).

use std::rc::Rc;

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Arg, ExprId, Mode};

use super::calls::Takes;
use super::check::{Changed, Walker};
use super::flow::Run;
use super::place::{ByRoot, Place, place_of};
use super::scoped::Reader;
use super::walk::Pos;
use crate::Kind;
use crate::body::LocalId;
use crate::sources::{Cx, Leaf, Open, What, leaves};

/// A place an argument of a call passes (E0702, [`crate::sources::leaves`]):
/// the argument or the element of a literal opened at it (`arg`), the unit
/// that is opened in (`up`), the argument as written (`outer`) and the
/// elements opened in it, at every depth (`opened`),
/// the expression that gives the place (`at`: the argument, an element, a tail),
/// how it is passed, its place, its root if a binding of the index (S-796),
/// and why it is read at a `move` parameter or receiver ([`Read`]).
pub(super) struct Passed {
    arg: ExprId,
    up: ExprId,
    outer: ExprId,
    opened: Rc<[ExprId]>,
    at: ExprId,
    mode: Mode,
    place: Place,
    via: Option<LocalId>,
    read: Option<Read>,
}

impl Passed {
    /// Whether `b` is in the unit of `self` (the tails of one unit, S-1113).
    fn unit_of(&self, b: &Passed) -> bool {
        self.arg == b.arg || self.arg == b.up
    }
}

/// Why a value passed to a `move` parameter or receiver is read there, not
/// moved: a Dup value, copied (S-801), or a value with no kind (§18.1), which
/// is said as written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Read {
    Copied,
    Unknown,
}

/// The window of E0702's changes (§3.5, §5.2): the arguments of a call,
/// or the index of an index (S-1275).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Window {
    Call,
    Index,
}

/// The note of a Dup value passed to a `move` parameter (S-801), and of a value with no kind.
const COPIED: &str = "a Dup value passed to a `move` parameter is copied, and read here (§5.2)";
const UNKNOWN: &str = "a value whose kind is not known (§18.1) counts as a read";

/// How a place is passed, in a message.
fn how(m: Mode) -> &'static str {
    match m {
        Mode::Inout => "as `inout`",
        Mode::Move => "as `move`",
        Mode::Borrow => "borrowed",
    }
}

impl Walker<'_> {
    /// E0702 (§5.2, S-787, S-796): an argument (the receiver
    /// first) that is a place overlapping the place of an earlier one, one
    /// of them `inout` or `move`, at the later one; the places of what each
    /// stands for ([`leaves`]: its tails, the bases of its paths and partial
    /// views, the elements of a literal opened at it, S-1113, S-1114, R-482),
    /// by where and their root, the tails of one argument not with one another.
    /// Each argument is evaluated before the call, so the order is not what
    /// counts, and a value made of a place (`xs.fill!(xs.len())`) is no
    /// place. A borrow binding that is not Copy stands for the places it
    /// derives from (S-796). The leaves of a borrowed one are E0716's
    /// ([`Walker::ends_inside`]). And the places passed, by their roots too
    /// (looked up there: linear in the places of no root in common), for
    /// the changes made in the other arguments ([`Walker::changed_in_args`]).
    pub(super) fn exclusive(
        &mut self,
        receiver: Option<(ExprId, Mode)>,
        args: &[Arg],
        takes: &[Takes],
    ) -> (Vec<(Span, LocalId)>, Vec<Passed>, ByRoot) {
        let params = args.iter().zip(takes).filter_map(|(a, t)| match t {
            Takes::Param(m, _) => Some((a.expr, *m)),
            Takes::Element => None,
        });
        let mut passed = Vec::new();
        for (x, m) in receiver.into_iter().chain(params) {
            let leaves = leaves(self.cx(), x, Open::Arg);
            if m == Mode::Borrow {
                self.ends_inside(&leaves, x, Reader::CALL);
            }
            self.pass(leaves, x, m, &mut passed);
        }
        let (mut later, index) = (Vec::new(), ByRoot::new(&self.deps, passed.iter().map(|q| &q.place)));
        for (j, b) in passed.iter().enumerate() {
            let excl = |p: &Passed| p.mode != Mode::Borrow && p.read != Some(Read::Unknown);
            let earlier = index.sharing(&self.deps, b.place.root).take_while(|&k| k < j).map(|k| &passed[k]);
            // The tails of one unit are not passed at once (S-1113).
            let mut earlier = earlier.filter(|a| !a.unit_of(b) && !b.unit_of(a) && (excl(b) || excl(a)));
            if let Some(a) = earlier.find(|a| self.deps.meets(&a.place, &b.place)) {
                later.push((self.ast.expr(b.at).span, b.place.root));
                let d = self.overlapping(a, b);
                self.report(d);
            }
        }
        (later, passed, index)
    }

    /// The places the argument `x` passes as `m`, of its leaves `leaves`,
    /// pushed on `passed`.
    fn pass(&mut self, leaves: Vec<Leaf>, x: ExprId, m: Mode, passed: &mut Vec<Passed>) {
        let mut opened: Vec<_> = leaves.iter().flat_map(|l| [l.up, l.arg]).filter(|&a| a != x).collect();
        opened.sort_unstable();
        opened.dedup();
        let opened: Rc<[ExprId]> = opened.into();
        for leaf in leaves {
            let What::Place(b) = leaf.what else { continue };
            let Some(place) = place_of(self.ast, self.names, b) else {
                bug(Some(self.ast.expr(b).span), "a place leaf with no place")
            };
            passed.push(self.passed(&leaf, (x, &opened), m, place.then(&leaf.over)));
        }
    }

    /// The index `index` of `base` (§3.5, §5.2, S-1275), walked as an
    /// argument of a call is: a change in it that may overlap a place of the
    /// base, which stands for its places as a borrowed argument does, is
    /// E0702 ([`Walker::changed_in_args`]); whether one was found.
    pub(super) fn indexed(&mut self, r: &mut Run, base: ExprId, index: ExprId) -> bool {
        let mut passed = Vec::new();
        self.pass(leaves(self.cx(), base, Open::Arg), base, Mode::Borrow, &mut passed);
        if passed.is_empty() {
            self.expr(r, index, Pos::Read);
            return false;
        }
        let by_root = ByRoot::new(&self.deps, passed.iter().map(|q| &q.place));
        let start = self.inside.changes.len();
        // One deeper, as the arguments of a call: its changes are recorded.
        self.inside.calls += 1;
        self.expr(r, index, Pos::Read);
        self.inside.calls -= 1;
        self.changed_in_args(r, start, (&passed, &by_root), Window::Index)
    }

    /// What the stages after the types read of the body ([`crate::sources`]).
    pub(super) fn cx(&self) -> Cx<'_> {
        Cx::after_types(self.ast, self.names, self.info, self.a)
    }

    /// The place passed as `mode` by the leaf `leaf` of an argument
    /// (S-787: the `move` of an Affine field's path consumes its root whole;
    /// S-801: a Dup value at a `move` parameter or receiver is copied, and
    /// counts as a read of its place, as at a borrowed one; a value with no
    /// kind too), of the kind of the argument (or element) as passed.
    fn passed(
        &mut self,
        leaf: &Leaf,
        (outer, opened): (ExprId, &Rc<[ExprId]>),
        mut mode: Mode,
        mut place: Place,
    ) -> Passed {
        let ty = self.info.expr_types.get(&self.ast.without_parens(leaf.arg)).copied();
        let kind = ty.and_then(|t| self.kind_of(t));
        // A value with no kind (§18.1: an unknown bound, the error type) may move or not: a read too.
        let read = match (mode, kind) {
            (Mode::Move, Some(Kind::Copy | Kind::Shared)) => Some(Read::Copied),
            (Mode::Move, None) => Some(Read::Unknown),
            _ => None,
        };
        match read {
            Some(Read::Copied) => mode = Mode::Borrow,
            None if mode == Mode::Move => place.proj.clear(),
            _ => {}
        }
        let via = self.deps.indexed(place.root).then_some(place.root);
        Passed { arg: leaf.arg, up: leaf.up, outer, opened: opened.clone(), at: leaf.at, mode, place, via, read }
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
        let (x, y) = (self.ast.expr(a.at).span, self.ast.expr(b.at).span);
        self.at_later(message, (x, note.clone()), (y, note), &[a, b])
    }

    /// The E0702 of two places of one call, at `a` or `b`, whichever is
    /// written later (the other, its note; `a` first if both start at once),
    /// with the notes of the places `of` passed: a copy (S-801), a binding of
    /// the index (S-796).
    fn at_later(&self, message: String, a: (Span, String), b: (Span, String), of: &[&Passed]) -> Diagnostic {
        let ((first, note), last) = if b.0.start < a.0.start { (b, a.0) } else { (a, b.0) };
        let d = Diagnostic::new(Stage::Modes, Code::E0702, last, message).with_note(first, note);
        let d = [(Read::Copied, COPIED), (Read::Unknown, UNKNOWN)].into_iter().fold(d, |d, (read, note)| {
            (of.iter().filter(|p| p.read == Some(read))).fold(d, |d, p| d.with_note(self.ast.expr(p.at).span, note))
        });
        of.iter().filter_map(|p| p.via).fold(d, |d, l| {
            let (at, note) = self.bound_note(l);
            d.with_note(at, note)
        })
    }

    /// The argument `p` as written (on more than one line, its name and path).
    fn passed_text(&self, p: &Passed) -> String {
        self.place_text(self.ast.expr(p.at).span, &[], &p.place)
    }

    /// The E0702 of the changes (§7) made while the arguments of a call were
    /// walked, from `start` on (§3.5, §5.2, S-193, S-799): each that may
    /// overlap a place `passed` in the call, other than the arguments it is
    /// in (its unit, or a unit around it out of the elements opened there,
    /// R-486), at the later of the two, the first such place (S-796: a
    /// binding of the index stands for its places). The change of a direct argument
    /// (marked with the depth of this call, the one after `calls`) is
    /// `exclusive`'s, and changes are not compared with one another
    /// (`h(next(inout k), next(inout k))`). A release of a Dup value that
    /// such a place overlaps (a direct argument's too: `mm(s, s)`), by every
    /// walk, copies (§5.2, S-1030: E0702's test, no error). Out of the
    /// arguments of every call, the record is emptied. The places passed are
    /// looked up by their roots (`index`): linear in the changes and the
    /// places of no root in common. Of the window of an index (`of`), the
    /// places are its base's ([`Walker::indexed`]). Whether one was found.
    pub(super) fn changed_in_args(
        &mut self,
        r: &mut Run,
        start: usize,
        (passed, index): (&[Passed], &ByRoot),
        of: Window,
    ) -> bool {
        let (this, mut copies, mut found) = (Some(self.inside.calls + 1), Vec::new(), false);
        let window = self.inside.changes[start..].iter().filter(|c| c.release || (self.reports && c.direct != this));
        // The elements opened in the call, each argument's once (its places share them).
        let fresh = |&(i, p): &(usize, &Passed)| i == 0 || !Rc::ptr_eq(&passed[i - 1].opened, &p.opened);
        let all: Vec<ExprId> =
            passed.iter().enumerate().filter(fresh).flat_map(|(_, p)| p.opened.iter().copied()).collect();
        for Changed { place: w, at, release, .. } in window {
            let span = |p: &Passed| self.ast.expr(p.at).span;
            let within = |e: ExprId| self.ast.expr(e).span.start <= at.start && at.end <= self.ast.expr(e).span.end;
            // In the unit `u` and in none opened in it (of those the change is in, as many as the nesting).
            let inside: Vec<ExprId> = all.iter().copied().filter(|&e| within(e)).collect();
            let free = |p: &Passed, u: ExprId| {
                within(u) && !inside.iter().any(|&e| e != u && p.opened.binary_search(&e).is_ok())
            };
            let holds = |p: &Passed| within(p.arg) || free(p, p.up) || free(p, p.outer);
            let mut shared = index.sharing(&self.deps, w.root).map(|k| &passed[k]);
            let Some(q) = shared.find(|q| !holds(q) && self.deps.meets(w, &q.place)) else { continue };
            if *release {
                copies.push((w.root, span(q), q.place.root));
                continue;
            }
            let (changed, arg) = (self.place_text(*at, &[], w), self.passed_text(q));
            let (message, note) = match of {
                Window::Call => (
                    format!(
                        "`{changed}` is changed in another argument while `{arg}` is passed {} in the same call; the places may overlap (§3.5, §5.2)",
                        how(q.mode)
                    ),
                    format!("{} here", how(q.mode).trim_start_matches("as ")),
                ),
                Window::Index => (
                    format!(
                        "`{changed}` is changed in the index while `{arg}` is indexed; the places may overlap (§3.5, §5.2)"
                    ),
                    "indexed here".to_string(),
                ),
            };
            let d = self.at_later(message, (span(q), note), (*at, "changed here".to_string()), &[q]);
            self.m.found.push(d);
            found = true;
        }
        copies.into_iter().for_each(|(l, by, b)| self.restore(r, l, (by, Some(b))));
        if self.inside.calls == 0 {
            self.inside.changes.clear();
        }
        found
    }
}
