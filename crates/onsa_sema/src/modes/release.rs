//! The releases of the Dup values (§5.2, S-1030): the whole of an owned
//! binding consumed moves unless it is used after; a use after makes its
//! releases copies, and the drop points of the binding they leave stay.
//! The consumptions that copy, and why (S-1035, R-466, `BodyInfo::copied`).

use std::rc::Rc;

use onsa_diag::Span;
use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::internal::bug;
use onsa_syntax::ast::ExprId;

use super::check::{Changed, Walker};
use super::flow::Run;
use super::place::{Place, bound_by, place_of};
use super::state::{Releases, within};
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
    /// (by every walk) for [`Walker::changed_in_args`]. The one place that
    /// decides why a consumption of the value of an owned binding copies
    /// where it is (S-1035, R-466), the first of: a path (of the binding,
    /// or of a borrow binding derived from it), a borrow binding of a head,
    /// a place held. A borrowed argument and a static value have no row.
    pub(super) fn release(&mut self, r: &mut Run, p: &Place, (x, at): (ExprId, Span), kind: Kind) {
        let (l, whole) = (p.root, p.proj.is_empty());
        let state = self.info.locals[l.0 as usize].state;
        let rows = match () {
            _ if kind == Kind::Copy => return,
            _ if state.owned() && !whole => vec![(l, CopiedWhy::Part)],
            _ if state.owned() => match self.holder(p) {
                Some(head) => vec![(l, CopiedWhy::Held(head))],
                None => {
                    r.cur.change(l, |d| d.released(l, x));
                    if self.inside.calls > 0 {
                        let change = Changed { place: p.clone(), at, direct: None, release: true };
                        self.inside.changes.push(change);
                    }
                    return;
                }
            },
            _ if state != (Bind::Borrow { no_drop: false }) => return,
            _ => (self.owned_sources(l).into_iter())
                .map(|(root, head, own)| (root, if whole { CopiedWhy::Head(head, own) } else { CopiedWhy::Part }))
                .collect(),
        };
        for (root, why) in rows {
            self.m.copied.entry((root, x)).or_insert(why);
        }
    }

    /// The owned bindings, not Copy, the borrow binding `l` derives from
    /// (§5.4: `match o`, `for s in xs`), through the borrow bindings between
    /// (`let t = s`, an inner `match` or `for`), each once (the first found),
    /// with the head that reads it and whether its value is that binding
    /// (through parentheses, R-466 F5). Of a binding of the index, its roots
    /// ([`Deps::heads_of`], the one reading of a chain); else of its head
    /// ([`bound_by`]: a `for`). Made once for each binding, by a stack (a
    /// chain is not walked by the recursion of Rust); a binding derives from
    /// earlier ones only, so it ends. O(P + B·R log R) for P places of the
    /// heads, B bindings and R owned roots of one.
    fn owned_sources(&mut self, l: LocalId) -> Vec<(LocalId, Head, bool)> {
        let (ast, info, mut todo) = (self.ast, self.info, vec![l]);
        while let Some(&b) = todo.last() {
            if self.m.heads.contains_key(&b) {
                todo.pop();
                continue;
            }
            let direct: Vec<_> = match bound_by((ast, self.names, info), b) {
                _ if self.deps.indexed(b) => self.deps.heads_of(b).collect(),
                Some((head, Some(places))) => places.iter().map(|(p, _)| (p.root, head)).collect(),
                Some((_, None)) => {
                    bug(Some(info.locals[b.0 as usize].span), "a borrow binding of a head with no borrow row")
                }
                // A parameter.
                None => Vec::new(),
            };
            let owned = |r: LocalId| info.locals[r.0 as usize].state.owned();
            let before = todo.len();
            todo.extend(direct.iter().map(|d| d.0).filter(|&r| !owned(r) && !self.m.heads.contains_key(&r)));
            if todo.len() > before {
                continue;
            }
            let mut found = Vec::new();
            for (r, head) in direct {
                let value = place_of(ast, self.names, ast.without_parens(head.value(ast).0));
                let own = value.is_some_and(|p| p.root == r && p.proj.is_empty());
                match owned(r) {
                    true if self.kind_of(info.locals[r.0 as usize].ty) != Some(Kind::Copy) => {
                        found.push((r, head, own))
                    }
                    true => {}
                    false => found.extend(self.m.heads[&r].iter().copied()),
                }
            }
            found.sort_by_key(|f| f.0);
            found.dedup_by_key(|f| f.0);
            self.m.heads.insert(b, found);
            todo.pop();
        }
        self.m.heads[&l].clone()
    }

    /// A place of `l` used at `by` (or released in an argument of a call
    /// that a place of the binding `in_call`, at `by`, overlaps: E0702's
    /// test, `Walker::changed_in_args`): the releases of its root, and of
    /// the roots it derives from, are copies, and the roots live (§5.2,
    /// S-1030: used after, by the next iteration or a borrow binding derived
    /// from it), each with why and by the binding (S-1035: by the next iteration
    /// where the release reached here by the back edge of a loop alone, in
    /// it, [`super::state::Status::Released`]). The one place that decides it.
    /// A read before a release in the same expression (`s == take(s)`) is
    /// not after: that release moves.
    pub(super) fn restore(&mut self, r: &mut Run, l: LocalId, (by, in_call): (Span, Option<LocalId>)) {
        let roots: Vec<_> = if self.deps.indexed(l) { self.deps.origins(l).collect() } else { Vec::new() };
        for root in roots.into_iter().chain([l]) {
            let Some((at, via_loop)) = r.cur.restore(root) else { continue };
            let why = match (in_call, via_loop) {
                (Some(b), _) => CopiedWhy::InCall(by, b),
                (None, Some(of)) if within(by, of) => CopiedWhy::Loop(by, l),
                (None, _) => CopiedWhy::After(by, l),
            };
            for &x in at.iter() {
                self.m.copied.entry((root, x)).or_insert(why);
            }
        }
    }
}
