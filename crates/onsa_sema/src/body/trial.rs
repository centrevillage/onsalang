//! The trials of a candidate (§18.1): whether the form it puts in place of
//! an error leaves no other error of this stage. A trial has two forms.
//!
//! - In the state of now ([`Checker::quietly`]), when what is put has the
//!   type the expression it replaces would have had: what the later
//!   statements see does not change, so it is read here with no diagnostic
//!   (the place of the expression, the arguments of a function form, the patterns of
//!   later arms, the end of the body in [`Checker::end_is_clean`]).
//! - Read again ([`super::reread`]), when the candidate changes a type the
//!   later statements see (it takes statements away, or joins two items):
//!   the body is read with it applied, from a new state, after the first
//!   read. The join of an E0418 is still a trial in the state of now (R-389).

use onsa_syntax::ast::OperandPlace;

use super::*;
use crate::slot::{Slot, slot_of};

/// Where what a read that is not kept leaves in the analysis starts.
pub(super) struct Marks {
    held: bool,
    uses: usize,
}

impl Marks {
    pub(super) fn of(a: &Analysis, def: DefId) -> Marks {
        Marks { held: a.read_held.contains(&def), uses: a.uses.borrow().len() }
    }

    /// Undo it: whether the read read what the check does not read.
    pub(super) fn undo(self, a: &mut Analysis, def: DefId) -> bool {
        a.uses.borrow_mut().truncate(self.uses);
        !self.held && a.read_held.remove(&def)
    }
}

impl<'a> Checker<'a> {
    /// A trial of a candidate: `f` run with no diagnostic. Its `Err` is the
    /// answer "it does not fit", not a failure dropped. What leaks out of it
    /// (`read_held`, `uses`) is undone; of what reads what the check does not,
    /// an error is elsewhere (§18.1): none. What it binds and defers stays in
    /// this body, which the caller stops with the diagnostic the candidate is
    /// for, so its end is not checked ([`Checker::finish`] holds it to that);
    /// a later trial of the same diagnostic sees what this one bound.
    pub(super) fn quietly<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> Option<T> {
        let (failed, marks) = (self.failed, Marks::of(self.a, self.def));
        self.tried = true;
        self.failed = true;
        let out = f(self);
        self.failed = failed;
        let read_unread = marks.undo(self.a, self.def);
        out.ok().filter(|_| !read_unread)
    }

    /// Whether the end of the body has no error with what has been checked
    /// so far: the trial of the `let _` of an E0418 at a statement whose type
    /// is the variable of an integer literal itself, which `let _` leaves to
    /// its default (`5000000000` does not fit it, §6.1). A trial, as
    /// [`Checker::quietly`], that also undoes what the end of the body decides
    /// and reports: the join of the same E0418 is tried after it, with the
    /// literal not defaulted.
    pub(super) fn end_is_clean(&mut self) -> bool {
        if self.failed {
            return false;
        }
        let kept = (self.infer.clone(), self.deferred.clone(), self.deferred_end.clone());
        let mark = self.a.diagnostics.len();
        let clean = self.quietly(|ck| {
            ck.failed = false;
            ck.end_checks();
            if ck.failed { Err(Stop) } else { Ok(()) }
        });
        self.a.diagnostics.truncate(mark);
        (self.infer, self.deferred, self.deferred_end) = kept;
        clean.is_some()
    }

    /// The slot of `e` when a value of the type `c` put there by a candidate
    /// leaves no error of its parent (§18.1); none in an expression
    /// statement (its value is dropped). As a receiver, only of a method `c`
    /// has (in `x.abs().sqrt()` the missing `sqrt` would be the error left);
    /// before `as`, only where `as` converts `c` (§3.3); before `at`, any (the
    /// type of `e at k` is that of `e`, §11.3). In parentheses, the place of
    /// the outermost. The one answer of the candidates of every family.
    pub(super) fn place_fits(&mut self, e: ExprId, c: TyId) -> Option<Slot> {
        let place = slot_of(self.ast, self.root, e)?;
        let parent = place.parent.map(|p| &self.ast.expr(p).kind);
        let fits = match (place.outer, parent) {
            (Slot::Discarded, _) => false,
            (Slot::Operand(OperandPlace::Postfix), Some(ExprKind::Field { name, .. })) => {
                self.has_method(c, &name.name)
            }
            (Slot::Operand(OperandPlace::Postfix), _) => false,
            (Slot::Operand(OperandPlace::AsAtLeft), Some(&ExprKind::Cast { ty, .. })) => {
                // The type after `as`, lowered as its check does, quietly.
                let to = self.quietly(|ck| ck.lower_type_expr(ty));
                let error = |t: TyId| matches!(self.a.types.get(t), Ty::Error);
                to.is_some_and(|to| crate::cast::cast_allowed(&self.a.types, c, to) || error(to))
            }
            _ => true,
        };
        fits.then_some(place.slot)
    }

    /// Whether the builtin type `recv` has the method `name`: of `len`,
    /// whether it is a type with a length (§4.2), as far as this version
    /// gives it `len`. A method of a user type is none.
    pub(super) fn has_method(&mut self, recv: TyId, name: &str) -> bool {
        self.method_key(recv, name).1.is_none() && self.is_method(recv, name)
    }

    /// Whether a value of the type `c` may be where the type `t` is expected
    /// (§4.7): `t` is `c`, a variable not of a literal or of a literal of
    /// the kind of `c`, the error type, or the same type of what fits. `c`
    /// has no variable and is a number, `Bool`, a type parameter or an
    /// `Option` of one: this is whether they unify.
    pub(super) fn may_fit(&self, t: TyId, c: TyId) -> bool {
        let t = self.shallow(t);
        match (self.ty(t), self.ty(c)) {
            (Ty::Error, _) => true,
            (Ty::Var(i), c) => match self.infer.var_lit(i) {
                None => true,
                Some(LitKind::Int) => matches!(c, Ty::Int(_)),
                Some(LitKind::Float) => self.infer.float_fits(&c),
            },
            (Ty::Named(a, t), Ty::Named(b, c)) if a == b => t.iter().zip(&c).all(|(&t, &c)| self.may_fit(t, c)),
            _ => t == c,
        }
    }
}
