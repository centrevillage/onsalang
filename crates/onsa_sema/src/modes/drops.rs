//! The drop points of a body (R-32, §12.2): what the end of a scope, an
//! exit, a consumer that ran or an assignment leaves, and the items that
//! wait for them (the walk of the control and its items are `flow.rs`).

use onsa_diag::Span;
use onsa_diag::internal::bug;
use onsa_syntax::ast::{ExprId, ExprKind, PatId, PatKind};

use super::check::Walker;
use super::consume::Movable;
use super::flow::{Item, Run};
use super::place::place_of;
use super::state::Releases;
use super::walk::Pos;
use crate::Kind;
use crate::binding::no_drop;
use crate::body::{DropPoint, Dropped, LocalId, Unbound};
use crate::tails::Tail;
use crate::ty::{Len, Ty, TyId};

impl Walker<'_> {
    /// The drop points at the end of `scope`, of the items after the first
    /// `outer`: its bindings.
    pub(super) fn ends(&mut self, r: &Run, outer: usize, scope: Span) {
        self.drops(r, outer, Span::empty(scope.file, scope.end), false);
    }

    /// The drop points of the items after the first `from`, which the end
    /// of their scope, of the call or the index that waits for them
    /// ([`Walker::ran`]), or an exit at `at` (`exit`: a `return`, a `?`, a
    /// `break`, a `continue`) leaves (R-32, §12.2): each owned binding that
    /// may hold its value there, not Copy (surely if live on every path; of
    /// one released on every path, unless each release moves, S-1030); a
    /// value that waits (A-1), surely: it is made on every path to the
    /// exit, and consumed at the end of its consumer; one borrowed, there too;
    /// the rest of an owned `for` (S-1037), at its end (`iterate`) or left
    /// early; none where no path reaches (S-873). The one place that decides them.
    pub(super) fn drops(&mut self, r: &Run, from: usize, at: Span, exit: bool) {
        for i in from..r.declared.len() {
            let (what, sure, unless) = match r.declared[i] {
                Item::Local(l) => {
                    let local = &self.info.locals[l.0 as usize];
                    let held = if local.state.owned() { self.has_value(r, l, local.ty) } else { None };
                    let Some((sure, unless)) = held else { continue };
                    (if exit { Dropped::Exit(l) } else { Dropped::End(l) }, sure, unless)
                }
                Item::Value(e) if exit => (Dropped::Value(e), true, None),
                Item::Temp(e) => (if exit { Dropped::Value(e) } else { Dropped::Temp(e) }, true, None),
                Item::Value(_) => continue,
                Item::IterRest(e) => (Dropped::IterRest { iter: e, early: exit }, true, None),
                Item::Discard(u, sure) => (Dropped::Discard(u), sure, None),
            };
            self.drop_point(r, at, what, (sure, unless));
        }
    }

    /// Whether `l` may hold there a value of the type `ty` (a place of it)
    /// that is not Copy, and surely; of one released on every path, its
    /// releases (`Delta::lives`). The one test of
    /// [`Walker::drops`] and of an overwrite.
    fn has_value<'r>(&mut self, r: &'r Run, l: LocalId, ty: TyId) -> Option<(bool, Option<&'r Releases>)> {
        r.cur.state().lives(l).filter(|_| self.kind_of(ty) != Some(Kind::Copy))
    }

    /// The assignment to `target`, a place of `l`: the value the place held
    /// is dropped there (R-32, S-1038: of a `var`, a `move` or an `inout`
    /// parameter alike, by the type of the place), if it may hold one (not
    /// after the whole was moved on every path). The one place that decides it.
    pub(super) fn overwrite(&mut self, r: &Run, l: LocalId, target: ExprId) {
        let at = self.ast.expr(target).span;
        let Some(&ty) = self.info.expr_types.get(&target) else {
            bug(Some(at), "an assignment to a place with no type")
        };
        if let Some(held) = self.has_value(r, l, ty) {
            self.drop_point(r, at, Dropped::Overwrite(target), held);
        }
    }

    /// The operand `e`, walked at `pos` (of a call, a receiver, a literal,
    /// an assignment or an index, whose consumer runs after the operands
    /// after it): its value waits there for them (A-1), until the consumer
    /// runs ([`Walker::ran`]), if it is owned ([`Walker::owned`]) and `pos`
    /// consumes; a value made in its tails (of the root of a path of one,
    /// D2) where a call or an index borrows it, too (D3, [`Walker::temps`]).
    /// The one place that decides it.
    pub(super) fn waits(&mut self, r: &mut Run, e: ExprId, pos: Pos) {
        let x = self.value_of(e);
        if pos.consumes() {
            if self.owned(x) {
                r.declared.push(Item::Value(x));
            }
        } else if pos.waits() {
            self.temps(r, x);
        }
    }

    /// The element `elem` of `[elem; N]`, the literal `e`, at `pos`: where
    /// the length may be 0 (0, or a const parameter), the value it puts, if
    /// owned ([`Walker::owned`]) and `pos` consumes, is put in no element and
    /// dropped there (S-1045, §2.4, §12.2). The one place that decides it.
    pub(super) fn repeated(&mut self, r: &Run, e: ExprId, elem: ExprId, pos: Pos) {
        let x = self.value_of(elem);
        let ty = self.info.expr_types.get(&e).map(|&t| self.a.types.get(t));
        if pos.consumes() && matches!(ty, Some(Ty::Array(_, Len::Const(0) | Len::Param(_)))) && self.owned(x) {
            self.drop_point(r, self.ast.expr(x).span, Dropped::Unplaced(x), (true, None));
        }
    }

    /// The value `e` puts: without parentheses and `move`.
    fn value_of(&self, e: ExprId) -> ExprId {
        let mut x = self.ast.without_parens(e);
        while let ExprKind::Move(y) = &self.ast.expr(x).kind {
            x = self.ast.without_parens(*y);
        }
        x
    }

    /// The values made in the tails of `e` where a call or an index borrows
    /// them (D3): of a path, those in the tails of its root, again (§5.2: a
    /// block, an `if`, a `match` puts its tails where it is); a place in
    /// them is borrowed, not dropped. Linear in `e`.
    fn temps(&mut self, r: &mut Run, e: ExprId) {
        let mut tails = Vec::new();
        crate::tails::tails(self.ast, e, &self.info.diverging, &mut tails);
        for t in tails {
            let Tail::Value(v) = t else { continue };
            let root = self.root_of_path(v, None);
            if self.made(v, false) {
                r.declared.push(Item::Temp(v));
            } else if root != v {
                self.temps(r, root);
            }
        }
    }

    /// Whether the value of `x` is owned where it is consumed or dropped:
    /// an Affine place moved, a Dup value not Copy (released or copied,
    /// §5.2) that needs a drop (not a static value, a literal or a binding
    /// that needs no drop or a path of one, S-610, S-613, R-461: the
    /// binding stage's [`no_drop`]), an Affine new value. The one place that
    /// decides it.
    pub(super) fn owned(&mut self, x: ExprId) -> bool {
        let Some(&ty) = self.info.expr_types.get(&x) else { return false };
        match (self.kind_of(ty), place_of(self.ast, self.names, x)) {
            (Some(Kind::Shared), _) => !no_drop(self.ast, self.names, self.info, x),
            (_, Some(p)) => self.movable(&p, ty) == Some(Movable::Owned),
            (kind, None) => kind == Some(Kind::Affine),
        }
    }

    /// The consumer of the items after the first `from` (a call, an index)
    /// ran: the values it borrows are dropped (R-32), the others it took.
    pub(super) fn ran(&mut self, r: &mut Run, from: usize, at: Span) {
        self.drops(r, from, at, false);
        r.forget(from);
    }

    /// The end of the body `root` walked in `r`: the drop points of the
    /// parameters.
    pub(super) fn body_end(&mut self, r: &Run, root: ExprId) {
        self.ends(r, 0, self.ast.expr(root).span);
    }

    /// A drop point met by the walk that reports, where a path reaches;
    /// `unless`: the releases it is one only if one of them copies.
    pub(super) fn drop_point(&mut self, r: &Run, at: Span, what: Dropped, (sure, unless): (bool, Option<&Releases>)) {
        if self.reports && r.cur.state().reaches() {
            let closure = self.closure_in();
            if let Some(xs) = unless {
                self.m.unless.push((self.m.drops.len(), xs.clone()));
            }
            self.m.drops.push(DropPoint { at, what, closure, sure });
        }
    }

    /// The parts of a value an owned head consumes that the pattern `p`
    /// binds to no name (§5.4, S-1036, S-1044), in the scope: of a `_`, a
    /// literal and a constant, the part it matches; of a struct pattern's
    /// last `_`, the fields it leaves; none of a variant with no payload;
    /// in a choice, maybe (`sure`). The one place that decides them.
    // A variant with no payload leaves nothing, nested too; a constant drops
    // the part it matches, as a literal does (S-1044).
    pub(super) fn discards(&mut self, r: &mut Run, p: PatId, sure: bool) {
        let ast = self.ast;
        self.discard(r, Unbound::Pat(p), sure);
        match &ast.pat(p).kind {
            PatKind::TupleStruct { elems: ps, .. } | PatKind::Tuple(ps) => {
                ps.iter().for_each(|&q| self.discards(r, q, sure))
            }
            PatKind::Or(ps) => ps.iter().for_each(|&q| self.discards(r, q, false)),
            PatKind::Struct { fields, .. } => fields.iter().for_each(|&(_, q)| self.discards(r, q, sure)),
            PatKind::Bind(_) | PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
        }
    }

    /// `u` in the scope, if it binds a part that is not Copy to no name
    /// (`BodyInfo::discards`).
    pub(super) fn discard(&mut self, r: &mut Run, u: Unbound, sure: bool) {
        let info = self.info;
        let tys = info.discards.get(&u).map_or(&[][..], |d| &d.tys);
        if tys.iter().any(|&t| self.kind_of(t) != Some(Kind::Copy)) {
            r.declared.push(Item::Discard(u, sure));
        }
    }
}
