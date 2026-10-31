//! Consumption and moves (W4-07 memo 2.2; §5.2, §5.4): a value at a
//! consuming position, decided by the state of its root, its kind and its
//! `move` mark. An erroneous consumption moves nothing (review 2).

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
    /// The value `e` at the consuming position `pos` (`Own`, `Value`, `MoveArg`,
    /// `Return` or `Extract`), with the offset of the `move` written on it,
    /// if any.
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
            let Some(m) = mark else { return self.expr(r, x, pos) };
            self.needs_a_place(x, m, pos);
            return self.expr(r, x, Pos::Read);
        };
        let (l, live) = (place.root, self.live(r, &place));
        self.expr(r, x, Pos::Read);
        let Some(&ty) = self.info.expr_types.get(&x) else {
            onsa_diag::internal::bug(Some(at), "a consumed place with no type")
        };
        // The error type. Not live, its E0704 above (and a move recorded only, S-799).
        let Some(kind) = self.kind_of(ty) else { return };
        let (text, local) = (self.text, &self.info.locals[l.0 as usize]);
        let (name, root) = (&text[at.start as usize..at.end as usize], &local.name);
        let plain = |message: String| Diagnostic::new(Stage::Modes, Code::E0711, at, message);
        let error = |message: String| match pos {
            Pos::Extract => plain(message).with_rule(EXTRACT),
            _ => plain(message),
        };
        let d = match (kind, local.state) {
            // Copied; a `move` on a `move` argument (S-609) or where a value is put (S-795) is E0703.
            (Kind::Copy | Kind::Shared, _) => {
                let (how, Some(m)) = (pos, mark) else { return };
                let how = match how {
                    Pos::MoveArg => "a `move` parameter takes it with no `move`",
                    Pos::Value => "`move` here moves nothing",
                    _ => return,
                };
                let message = format!("`{name}` is {}, so it is copied; {how} (§5.2)", kind.name());
                Diagnostic::new(Stage::Modes, Code::E0703, at, message).with_fix(self.unmark(at.file, m, "move"))
            }
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
            (_, Bind::Owned | Bind::OwnedMut) => match (pos, mark) {
                (Pos::Own | Pos::Value, None) => {
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
                _ if !live => return self.record(&place, at),
                // S-85: a path of fields is taken out, and its root moves whole.
                _ => return self.move_place(r, &place, at, direct),
            },
        };
        if live {
            self.report(d);
        }
    }

    /// `move e` at `pos` (`e` its operand, a tail where it is not the
    /// operand of a call, §5.2): consumed where a value is; else, on a place,
    /// the E0703 of S-605 (one for each tail, the walk reports the first) and
    /// on no place R-198's E0711 (at any position). At the argument of an
    /// unknown callee (§18.1), R-198's only.
    pub(super) fn marked(&mut self, r: &mut Run, m: ExprId, e: ExprId, pos: Pos) {
        let span = self.ast.expr(m).span;
        if pos.consumes() {
            return self.consume(r, e, pos, Some(span.start));
        }
        if place_of(self.ast, self.names, e).is_none() {
            self.needs_a_place(e, span.start, pos);
        } else if pos != Pos::Unknown {
            let message = "`move` here consumes nothing: this value is not consumed where it stands (§5.2)";
            let at = self.ast.expr(self.ast.without_parens(e)).span;
            let d = Diagnostic::new(Stage::Modes, Code::E0703, at, message);
            self.report(d.with_fix(self.unmark(span.file, span.start, "move")));
        }
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
            Pos::Bind | Pos::Own | Pos::Value => "stored",
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

    /// R-198: `move` (at `m`) on `e`, no place, at `pos`: E0711 at any
    /// position, with the candidate of `marks.rs`.
    pub(super) fn needs_a_place(&mut self, e: ExprId, m: u32, pos: Pos) {
        if !self.reports {
            return;
        }
        let d = Diagnostic::new(Stage::Modes, Code::E0711, self.ast.expr(e).span, MOVE_NEEDS_A_PLACE);
        let fix = self.unplaced(e, m, pos);
        self.report(fix.into_iter().fold(d, Diagnostic::with_fix));
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
