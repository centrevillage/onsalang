//! Second-class values (§5.3, §5.4): which values are (a `Span` or an
//! array of them, an anonymous function that captures, a function-type
//! parameter of the default mode) and the E0710 of one out of its place.

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{ExprId, ExprKind, PatId};

use super::check::Walker;
use super::flow::Run;
use super::place::place_of;
use super::walk::Pos;
use crate::binding::Bind;
use crate::body::{LocalId, Target, view_base};
use crate::bounds::Bounds;
use crate::sig::second_class;
use crate::tails::Tail;
use crate::ty::{BuiltinTy, Ty, TyId};

/// S-190: what keeps a function value instead.
const KEEP_FN: &str = "to keep a function value, declare the parameter `move f: fn(...)`; it then takes function values with no captures (§5.2)";

/// A second-class value (§5.3), by why it is: a borrow row binds
/// a view only (§5.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SecondClass {
    /// A `Span` (an element of a planar array, a view) or an array of them.
    View,
    /// A value of a `?Escape` type parameter or an array of them (§4.5),
    /// which may be a `Span`: it is read as a [`Self::View`] is (S-928).
    Lifted,
    /// An anonymous function that captures.
    Closure,
    /// A function-type parameter of the default mode (S-190).
    FnParam,
}

impl Walker<'_> {
    /// The one predicate of the second-class values (§5.3; the head is
    /// the types stage's, D-15): a `Span` or an array of them, and an
    /// anonymous function that captures, a function-type parameter of the
    /// default mode.
    pub(super) fn second_class(&self, e: ExprId) -> Option<SecondClass> {
        let x = self.ast.without_parens(e);
        if let ExprKind::Closure { .. } = self.ast.expr(x).kind {
            return self.info.captures.get(&x).is_some_and(|c| !c.is_empty()).then_some(SecondClass::Closure);
        }
        let ty = *self.info.expr_types.get(&x)?;
        match self.info.targets.get(&x) {
            Some(&Target::Local(l)) => self.class_of_local(l, ty),
            _ => self.class_of(ty),
        }
    }

    /// The second-class values of the local `l` of the type `ty`: a
    /// function-type parameter of the default mode by its binding
    /// ([`crate::body::LocalInfo::fn_param`]), else by its type.
    pub(super) fn class_of_local(&self, l: LocalId, ty: TyId) -> Option<SecondClass> {
        let fn_param = self.info.locals[l.0 as usize].fn_param(&self.a.types);
        if fn_param { Some(SecondClass::FnParam) } else { self.class_of(ty) }
    }

    /// The second-class values of the type `ty` (an array of them too), by
    /// the head of [`second_class`]: a `Span`, or a `?Escape` type parameter
    /// (§4.5), which may be one. A generated `Out` is not one here until
    /// W7-03 makes `Rendered` apart from it (R-334): `render` returns the
    /// type `Out` now, and its result binds (§11.6).
    pub(super) fn class_of(&self, mut ty: TyId) -> Option<SecondClass> {
        while let Ty::Array(t, _) = self.a.types.get(ty) {
            ty = *t;
        }
        if !second_class(&Bounds { a: self.a, generics: &self.generics }, ty) {
            return None;
        }
        match self.a.types.get(ty) {
            Ty::Builtin(BuiltinTy::Span, _) => Some(SecondClass::View),
            Ty::Param(_) => Some(SecondClass::Lifted),
            _ => None,
        }
    }

    /// The E0710 of a second-class `e` out of its place at `pos` (§5.3):
    /// at a consuming position any, at a borrow row's value and at a
    /// parameter not of a function type (S-809) any but a `Span` (S-217,
    /// S-788: the name it binds stays second-class). `true` if reported; `e`
    /// is then walked as read.
    pub(super) fn out_of_place(&mut self, r: &mut Run, e: ExprId, pos: Pos) -> bool {
        let Some(how) = pos.out() else { return false };
        let class = match self.second_class(e) {
            None => return false,
            Some(SecondClass::View | SecondClass::Lifted) if matches!(pos, Pos::Bind | Pos::Kept) => return false,
            Some(class) => class,
        };
        self.report(self.second_class_error(class, how, self.ast.expr(e).span));
        self.expr(r, e, Pos::Read);
        true
    }

    /// The second-class value in the tails of `e` (§5.2), through a `move`
    /// on one: the first (they are of one type).
    pub(super) fn tail_class(&self, e: ExprId) -> Option<SecondClass> {
        let mut tails = Vec::new();
        crate::tails::tails(self.ast, e, &self.info.diverging, &mut tails);
        tails.into_iter().find_map(|t| match t {
            Tail::Value(v) => match self.ast.expr(v).kind {
                ExprKind::Move(x) => self.second_class(x),
                _ => self.second_class(v),
            },
            Tail::Exits | Tail::Unit(_) => None,
        })
    }

    /// S-809's B1 through the tails (§18.1): a mark on `e` at `pos` is no
    /// error of its own when a tail is a function value that is E0710 there,
    /// which removing the mark would leave; `e` is walked at `pos`.
    pub(super) fn marked_tail(&self, e: ExprId, pos: Pos) -> bool {
        pos.out().is_some() && matches!(self.tail_class(e), Some(SecondClass::FnParam | SecondClass::Closure))
    }

    /// The E0710 of the second-class value at `at` of `class`, which cannot
    /// be `how` (stored, returned, moved, captured, passed: §5.3).
    pub(super) fn second_class_error(&self, class: SecondClass, how: &str, at: Span) -> Diagnostic {
        let what = match class {
            SecondClass::View => "a `Span` (or an array of them)",
            SecondClass::Lifted => "a value of a `?Escape` type parameter (or an array of them)",
            SecondClass::Closure => "an anonymous function that captures",
            SecondClass::FnParam => "a function-type parameter of the default mode (it may capture)",
        };
        let message =
            format!("this value is second-class, {what}: it stands at an argument only and cannot be {how} (§5.3)");
        let d = Diagnostic::new(Stage::Modes, Code::E0710, at, message);
        if class == SecondClass::FnParam { d.with_rule(KEEP_FN) } else { d }
    }

    /// S-217: a `for` or `match` head of a borrow row on a place of an
    /// `inout` parameter (or a view of one) binds no `Span` with its patterns
    /// `pats`: E0710 at the value. (A `let` of one is of an owned row, and
    /// consumed.)
    pub(super) fn view_of_inout(&mut self, value: ExprId, pats: impl IntoIterator<Item = PatId>) {
        let base = view_base((self.ast, self.info, self.a), value, |t| t).unwrap_or(value);
        let Some(place) = place_of(self.ast, self.names, base) else { return };
        if self.info.locals[place.root.0 as usize].state != Bind::Inout {
            return;
        }
        let mut views = false;
        for p in pats {
            self.each_local(p, &mut |l| views |= self.class_of(self.info.locals[l.0 as usize].ty).is_some());
        }
        if views {
            let message = "this `Span` is of an `inout` parameter: it stands at an argument only and cannot be bound (§5.3, §5.4)";
            self.report(Diagnostic::new(Stage::Modes, Code::E0710, self.ast.expr(value).span, message));
        }
    }
}
