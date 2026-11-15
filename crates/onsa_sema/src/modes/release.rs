//! The releases of the Dup values (§5.2, S-1030): the whole of an owned
//! binding consumed moves unless it is used after; a use after makes its
//! releases copies, and the drop points of the binding they leave stay.
//! The consumptions that copy, and why (S-1035, `BodyInfo::copied`).

use std::rc::Rc;

use onsa_diag::Span;
use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::internal::bug;
use onsa_syntax::ast::ExprId;

use super::check::{Changed, Walker};
use super::flow::Run;
use super::place::{Place, bound_by};
use super::state::Releases;
use crate::Kind;
use crate::binding::{Bind, Head};
use crate::body::{Copied, CopiedWhy, DropPoint, LocalId};

/// The drop points `points` of a body that stay: a point of a binding
/// released on every path (`unless`) is kept if one of its releases copied
/// (one of `copied`, S-1030); a set the points share is read once.
pub(super) fn kept(points: Vec<DropPoint>, unless: &[(usize, Releases)], copied: &[Copied]) -> Vec<DropPoint> {
    let reverted: HashSet<ExprId> = copied.iter().map(|c| c.at).collect();
    let mut moves = HashMap::default();
    debug_assert!(unless.windows(2).all(|p| p[0].0 < p[1].0), "the points of `unless` in order, once");
    let gone = (unless.iter())
        .filter(|(_, at)| *moves.entry(Rc::as_ptr(at)).or_insert_with(|| !at.iter().any(|x| reverted.contains(x))));
    let (mut gone, mut points, mut k) = (gone.map(|p| p.0).peekable(), points, 0);
    if gone.peek().is_some() {
        points.retain(|_| {
            k += 1;
            gone.next_if_eq(&(k - 1)).is_none()
        });
    }
    points
}

impl Walker<'_> {
    /// The place `p` of a Dup value of the kind `kind`, consumed by `x` (at
    /// any consuming position): released (§5.2, R-255, S-1030: moved unless
    /// used after, `Walker::restore`) if it is the whole of an owned
    /// binding, not Copy, and not held by a borrowed `for` or a guard
    /// (E0715's test); else copied. In the arguments of a call, recorded
    /// (by every walk) for [`Walker::changed_in_args`]. The whole of a
    /// borrow binding of a head copies, and the owned bindings whose whole
    /// the head reads keep their values (S-1035).
    pub(super) fn release(&mut self, r: &mut Run, p: &Place, (x, at): (ExprId, Span), kind: Kind) {
        let (l, whole) = (p.root, p.proj.is_empty());
        let state = self.info.locals[l.0 as usize].state;
        if kind != Kind::Copy && state.owned() && whole && !self.holds(p) {
            r.cur.change(l, |d| d.released(l, x));
            if self.inside.calls > 0 {
                let change = Changed { place: p.clone(), at, direct: None, release: true };
                self.inside.changes.push(change);
            }
        } else if kind == Kind::Shared && whole && state == (Bind::Borrow { no_drop: false }) {
            for (root, head) in self.owned_sources(l) {
                self.m.copied.entry((root, x)).or_insert(CopiedWhy::Head(head));
            }
        }
    }

    /// The owned bindings whose whole the head of the borrow binding `l`
    /// reads (§5.4: `match o`, `for s in xs`; [`bound_by`]), with the head;
    /// once for each binding. Not through another borrow binding (`let t = s`
    /// of a `match`'s `s`): a note of S-1035 is not made there.
    fn owned_sources(&mut self, l: LocalId) -> Vec<(LocalId, Head)> {
        if let Some(found) = self.m.heads.get(&l) {
            return found.clone();
        }
        // A parameter: no head.
        let Some((head, places)) = bound_by((self.ast, self.names, self.info), l) else { return Vec::new() };
        let Some(places) = places else {
            bug(Some(self.info.locals[l.0 as usize].span), "a borrow binding of a head with no borrow row")
        };
        let owned = |p: &Place| p.proj.is_empty() && self.info.locals[p.root.0 as usize].state.owned();
        let found: Vec<_> = places.iter().filter(|(p, _)| owned(p)).map(|(p, _)| (p.root, head)).collect();
        self.m.heads.insert(l, found.clone());
        found
    }

    /// A place of `l` used at `by` (or released in an argument of a call
    /// that another of its places, at `by`, overlaps: `in_call`, E0702's
    /// test, `Walker::changed_in_args`): the releases of its root, and of
    /// the roots it derives from, are copies, and the roots live (§5.2,
    /// S-1030: used after, by the next iteration or a borrow binding derived
    /// from it), each with why (S-1035: by the next iteration where `by` is
    /// written at or before it). The one place that decides it. A read
    /// before a release in the same expression (`s == take(s)`) is not
    /// after: that release moves.
    pub(super) fn restore(&mut self, r: &mut Run, l: LocalId, (by, in_call): (Span, bool)) {
        let roots: Vec<_> = if self.deps.indexed(l) { self.deps.origins(l).collect() } else { Vec::new() };
        for root in roots.into_iter().chain([l]) {
            for &x in r.cur.restore(root).iter().flat_map(|at| at.iter()) {
                let why = match in_call {
                    true => CopiedWhy::InCall(by),
                    false if by.start <= self.ast.expr(x).span.start => CopiedWhy::Loop(by),
                    false => CopiedWhy::After(by),
                };
                self.m.copied.entry((root, x)).or_insert(why);
            }
        }
    }
}
