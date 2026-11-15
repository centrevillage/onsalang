//! The releases of the Dup values (§5.2, S-1030): the whole of an owned
//! binding consumed moves unless it is used after; a use after makes its
//! releases copies, and the drop points of the binding they leave stay.

use std::rc::Rc;

use onsa_diag::Span;
use onsa_diag::hash::{HashMap, HashSet};
use onsa_syntax::ast::ExprId;

use super::check::Walker;
use super::flow::Run;
use super::place::Place;
use super::state::Releases;
use crate::Kind;
use crate::body::{DropPoint, LocalId};

/// The drop points `points` of a body that stay: a point of a binding
/// released on every path (`unless`) is kept if one of its releases copied
/// (`reverted`, S-1030); a set the points share is read once.
pub(super) fn kept(points: Vec<DropPoint>, unless: &[(usize, Releases)], reverted: &HashSet<ExprId>) -> Vec<DropPoint> {
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
    /// (by every walk) for [`Walker::changed_in_args`].
    pub(super) fn release(&mut self, r: &mut Run, p: &Place, (x, at): (ExprId, Span), kind: Kind) {
        let l = p.root;
        let owned = self.info.locals[l.0 as usize].state.owned() && p.proj.is_empty();
        if kind != Kind::Copy && owned && !self.holds(p) {
            r.cur.change(l, |d| d.released(l, x));
            if self.inside.calls > 0 {
                self.inside.changes.push((p.clone(), at, None, true));
            }
        }
    }

    /// A place of `l` used (or released in an argument of a call that
    /// another of its places overlaps, E0702's test,
    /// `Walker::changed_in_args`): the releases of its root, and of the
    /// roots it derives from, are copies, and the roots live (§5.2, S-1030:
    /// used after, by the next iteration or a borrow binding derived from it).
    /// The one place that decides it. A read before a release in the same
    /// expression (`s == take(s)`) is not after: that release moves.
    pub(super) fn restore(&mut self, r: &mut Run, l: LocalId) {
        let roots = if self.deps.indexed(l) { self.deps.origins(l) } else { Default::default() };
        for root in roots.into_iter().chain([l]) {
            if let Some(at) = r.cur.restore(root) {
                self.m.reverted.extend(at.iter());
            }
        }
    }
}
