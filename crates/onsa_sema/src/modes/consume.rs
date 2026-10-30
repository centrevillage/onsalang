//! Consumption and moves (W4-07 memo 2.2; §5.2, §5.4): a value at a
//! consuming position, decided by the state of its root, its kind and its
//! `move` mark. An erroneous consumption moves nothing (review 2).

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, FileId, Fix, Span, Stage};
use onsa_syntax::ast::{ExprId, ExprKind, PatId};

use super::check::Walker;
use super::flow::Run;
use super::place::{Proj, place_of};
use super::walk::Pos;
use crate::Kind;
use crate::binding::Bind;
use crate::body::{MOVE_NEEDS_A_PLACE, view_base};
use crate::sig::second_class;
use crate::ty::{BuiltinTy, Ty, TyId};

/// S-784, S-785: at `?` and a `move self` receiver, how to read the value
/// instead.
const EXTRACT: &str = "`?` and a `move self` receiver consume their operand (§5.2, §9.1): read it with `match` instead, or own it (a `move` parameter)";

/// A second-class value (memo 1.2, §5.3), by why it is: a borrow row binds
/// a view only (§5.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SecondClass {
    /// A `Span` (an element of a planar array, a view) or an array of them.
    View,
    /// An anonymous function that captures.
    Closure,
}

impl Walker<'_> {
    /// The value `e` at the consuming position `pos` (`Consume`, `MoveArg`,
    /// `Return` or `Extract`), with the offset of the `move` written on it,
    /// if any (of a `for` head, its value's: no candidate removes that one).
    pub(super) fn consume(&mut self, r: &mut Run, e: ExprId, pos: Pos, mark: Option<u32>) {
        // A direct argument changes its place after the call (§7, S-796).
        let direct = std::mem::take(&mut self.inside.direct) || pos == Pos::MoveArg;
        let x = self.ast.without_parens(e);
        let at = self.ast.expr(x).span;
        // The second-class values come first, before the table (memo 2.6, R-325).
        if self.out_of_place(r, x, pos) {
            return;
        }
        let Some(place) = place_of(self.ast, self.names, x) else {
            if mark.is_none() {
                return self.expr(r, x, pos);
            }
            self.needs_a_place(at);
            return self.expr(r, x, Pos::Read);
        };
        let (l, live) = (place.root, self.live(r, &place));
        self.expr(r, x, Pos::Read);
        let Some(&ty) = self.info.expr_types.get(&x) else {
            onsa_diag::internal::bug(Some(at), "a consumed place with no type")
        };
        // Not live (E0704 above), or the error type.
        let Some(kind) = self.kind_of(ty).filter(|_| live) else { return };
        let (text, local) = (self.text, &self.info.locals[l.0 as usize]);
        let (name, root) = (&text[at.start as usize..at.end as usize], &local.name);
        let plain = |message: String| Diagnostic::new(Stage::Modes, Code::E0711, at, message);
        let error = |message: String| match pos {
            Pos::Extract => plain(message).with_rule(EXTRACT),
            _ => plain(message),
        };
        let d = match (kind, local.state) {
            // Copied; a `move` on a `move` argument is E0703 (S-609).
            (Kind::Copy | Kind::Shared, _) => match (pos, mark) {
                (Pos::MoveArg, Some(m)) => Diagnostic::new(
                    Stage::Modes,
                    Code::E0703,
                    at,
                    format!(
                        "`{name}` is {}, so it is copied; a `move` parameter takes it with no `move` (§5.2)",
                        kind.name()
                    ),
                )
                .with_fix(self.unmark(at.file, m, "move")),
                _ => return,
            },
            // R-117, S-41: with no candidate (the fix is the mode, away from here).
            (_, Bind::Inout) => error(format!(
                "cannot move `{name}`: `{root}` is an `inout` parameter, which does not own its value (§5.2)"
            )),
            (_, Bind::Borrow { .. }) => error(format!(
                "cannot move `{name}`: `{root}` is borrowed here and the value is Affine; only owned values move (§5.2, §5.4)"
            )),
            (_, Bind::Owned | Bind::OwnedMut) if place.proj.contains(&Proj::Index) => error(format!(
                "cannot move `{name}` out of an array: its elements move with the array (`for x in move xs`) (§5.2)"
            )),
            // W4-09 (S-85): the field consumes its root.
            (_, Bind::Owned | Bind::OwnedMut) if !place.proj.is_empty() => plain(format!(
                "cannot move `{name}` out of `{root}`: Affine values move as a whole (partial moves are not allowed) (§5.2)"
            )),
            (_, Bind::Owned | Bind::OwnedMut) => match (pos, mark) {
                (Pos::Consume, None) => {
                    error(format!("Affine value `{name}` is consumed here; write `move {name}` (§5.2)"))
                        .with_fix(self.add_move(e))
                }
                (Pos::MoveArg, None) => Diagnostic::new(
                    Stage::Modes,
                    Code::E0703,
                    at,
                    "this parameter is `move`; write `move` before the argument (§5.2)",
                )
                .with_fix(self.add_move(e)),
                // An erroneous move (E0712 at the anonymous function) moves nothing.
                _ if self.captured(l) => return,
                _ => return self.move_local(r, l, at, direct),
            },
        };
        self.report(d);
    }

    /// `move e` at `pos` (`e` its operand): consumed where a value is, else
    /// the E0200 of a `move` on a tail (W4-09 makes it S-605's E0703).
    pub(super) fn marked(&mut self, r: &mut Run, m: ExprId, e: ExprId, pos: Pos) {
        let span = self.ast.expr(m).span;
        if pos.consumes() {
            return self.consume(r, e, pos, Some(span.start));
        }
        self.report(Feature::MoveOnUnconsumedTail.diagnostic(Stage::Modes, span, &[]));
        self.expr(r, e, Pos::Read);
    }

    /// The one predicate of the second-class values (memo 2.6; the head is
    /// the types stage's, D-15): a `Span` or an array of them, and an
    /// anonymous function that captures. W4-11 adds the function parameters
    /// of the default mode.
    pub(super) fn second_class(&self, e: ExprId) -> Option<SecondClass> {
        let x = self.ast.without_parens(e);
        if let ExprKind::Closure { .. } = self.ast.expr(x).kind {
            return self.info.captures.get(&x).is_some_and(|c| !c.is_empty()).then_some(SecondClass::Closure);
        }
        self.class_of(*self.info.expr_types.get(&x)?)
    }

    /// The second-class values of the type `ty` (an array of them too), by
    /// the head of [`second_class`]. A generated `Out` is not one here until
    /// W7-03 makes `Rendered` apart from it (R-334): `render` returns the
    /// type `Out` now, and its result binds (§11.6).
    pub(super) fn class_of(&self, mut ty: TyId) -> Option<SecondClass> {
        while let Ty::Array(t, _) = self.a.types.get(ty) {
            ty = *t;
        }
        let view = matches!(self.a.types.get(ty), Ty::Builtin(BuiltinTy::Span, _));
        (view && second_class(self.a, ty)).then_some(SecondClass::View)
    }

    /// The E0710 of a second-class `e` out of its place at `pos` (memo 2.6,
    /// §5.3): at a consuming position any, at a borrow row's value any but a
    /// `Span` (S-217, S-788: the name it binds stays second-class). `true` if
    /// reported; `e` is then walked as read.
    pub(super) fn out_of_place(&mut self, r: &mut Run, e: ExprId, pos: Pos) -> bool {
        let how = match pos {
            Pos::Read | Pos::Arg(_) | Pos::Unknown => return false,
            Pos::Bind | Pos::Consume => "stored",
            Pos::Return => "returned",
            Pos::MoveArg | Pos::Extract => "moved",
        };
        let class = match self.second_class(e) {
            None => return false,
            Some(SecondClass::View) if pos == Pos::Bind => return false,
            Some(class) => class,
        };
        self.report(self.second_class_error(class, how, self.ast.expr(e).span));
        self.expr(r, e, Pos::Read);
        true
    }

    /// The E0710 of the second-class value at `at` of `class`, which cannot
    /// be `how` (stored, returned, moved, captured: §5.3).
    pub(super) fn second_class_error(&self, class: SecondClass, how: &str, at: Span) -> Diagnostic {
        let what = match class {
            SecondClass::View => "a `Span` (or an array of them)",
            SecondClass::Closure => "an anonymous function that captures",
        };
        let message =
            format!("this value is second-class, {what}: it stands at an argument only and cannot be {how} (§5.3)");
        Diagnostic::new(Stage::Modes, Code::E0710, at, message)
    }

    /// S-217: a `for` or `match` head of a borrow row on a place of an
    /// `inout` parameter (or a view of one) binds no `Span` with its patterns
    /// `pats`: E0710 at the value. (A `let` of one is of an owned row, and
    /// consumed.)
    pub(super) fn view_of_inout(&mut self, value: ExprId, pats: impl IntoIterator<Item = PatId>) {
        let base = view_base((self.ast, self.info, &self.a.types), value, |t| t).unwrap_or(value);
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

    /// R-198: `move` on the value at `at`, which is no place: E0711 at any
    /// position, with no candidate (W4-09 adds them).
    pub(super) fn needs_a_place(&mut self, at: Span) {
        self.report(Diagnostic::new(Stage::Modes, Code::E0711, at, MOVE_NEEDS_A_PLACE));
    }

    /// The candidate that writes `move` before `e` (outside its parentheses:
    /// a mark is not written in them, §5.2).
    fn add_move(&self, e: ExprId) -> Fix {
        let span = self.ast.expr(e).span;
        Fix::insert("add `move`", span.file, span.start, "move ")
    }

    /// The candidate that removes the mark `word` at `m` and the blanks
    /// after it (not a comment, which is no part of the mark).
    pub(super) fn unmark(&self, file: FileId, m: u32, word: &str) -> Fix {
        let after = &self.text[m as usize + word.len()..];
        let end = self.text.len() - after.trim_start_matches([' ', '\t']).len();
        Fix::delete(format!("remove `{word}`"), Span::new(file, m, end as u32))
    }
}
