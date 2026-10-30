//! Consumption and moves (W4-07 memo 2.2; §5.2, §5.4): a value at a
//! consuming position, decided by the state of its root, its kind and its
//! `move` mark. An erroneous consumption moves nothing (review 2).

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::ExprId;

use super::check::Walker;
use super::flow::Run;
use super::place::{Proj, place_of};
use super::walk::Pos;
use crate::Kind;
use crate::binding::Bind;

impl Walker<'_> {
    /// The value `e` at the consuming position `pos` (`Consume`, `MoveArg` or
    /// `Return`), with the offset of the `move` written on it, if any (of a
    /// `for` head, its value's: no candidate removes that one).
    pub(super) fn consume(&mut self, r: &mut Run, e: ExprId, pos: Pos, mark: Option<u32>) {
        let x = self.ast.without_parens(e);
        let at = self.ast.expr(x).span;
        // U2b: the second-class values come first, before the table (memo 2.6).
        let Some(place) = place_of(self.ast, self.names, x) else {
            if mark.is_none() {
                return self.expr(r, x, pos);
            }
            // R-198: at any position, with no candidate (W4-09 adds them).
            let message = "`move` needs a place (a local variable, or a field or element of one); this value is not one and is owned already (§5.2)";
            self.report(Diagnostic::new(Stage::Modes, Code::E0711, at, message));
            return self.expr(r, x, Pos::Read);
        };
        let (l, live) = (place.root, self.live(r, place.root));
        self.expr(r, x, Pos::Read);
        let Some(&ty) = self.info.expr_types.get(&x) else {
            onsa_diag::internal::bug(Some(at), "a consumed place with no type")
        };
        // Not live (E0704 above); second-class (U2b) or the error type.
        let Some(kind) = self.kind_of(ty).filter(|_| live) else { return };
        let (text, local) = (self.text, &self.info.locals[l.0 as usize]);
        let (name, root) = (&text[at.start as usize..at.end as usize], &local.name);
        let error = |message: String| Diagnostic::new(Stage::Modes, Code::E0711, at, message);
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
                .with_fix(self.unmark(at, m)),
                _ => return,
            },
            // R-117, S-41: with no candidate (the fix is the mode, away from here).
            (_, Bind::Inout) => error(format!(
                "cannot move `{name}`: `{root}` is an `inout` parameter, which does not own its value (§5.2)"
            )),
            (_, Bind::Borrow { .. }) => error(format!(
                "cannot move `{name}`: `{root}` is borrowed here and the value is Affine; only owned values move (§5.2, §5.4)"
            )),
            _ if place.proj.contains(&Proj::Index) => error(format!(
                "cannot move `{name}` out of an array: its elements move with the array (`for x in move xs`) (§5.2)"
            )),
            // W4-09 (S-85): the field consumes its root.
            _ if !place.proj.is_empty() => error(format!(
                "cannot move `{name}` out of `{root}`: Affine values move as a whole (partial moves are not allowed) (§5.2)"
            )),
            _ => match (pos, mark) {
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
                _ => return self.move_local(r, l, at),
            },
        };
        self.report(d);
    }

    /// `move e` at `pos` (`e` its operand): consumed where a value is, else
    /// the E0200 of a `move` on a tail (W4-09 makes it S-605's E0703).
    pub(super) fn marked(&mut self, r: &mut Run, m: ExprId, e: ExprId, pos: Pos) {
        let span = self.ast.expr(m).span;
        if matches!(pos, Pos::Consume | Pos::MoveArg | Pos::Return) {
            return self.consume(r, e, pos, Some(span.start));
        }
        self.report(Feature::MoveOnUnconsumedTail.diagnostic(Stage::Modes, span, &[]));
        self.expr(r, e, Pos::Read);
    }

    /// The candidate that writes `move` before `e` (outside its parentheses:
    /// a mark is not written in them, §5.2).
    fn add_move(&self, e: ExprId) -> Fix {
        let span = self.ast.expr(e).span;
        Fix::insert("add `move`", span.file, span.start, "move ")
    }

    /// The candidate that removes the `move` at `m` and the blanks after it
    /// (not a comment, which is no part of the mark).
    fn unmark(&self, at: Span, m: u32) -> Fix {
        let after = &self.text[m as usize + "move".len()..];
        let end = self.text.len() - after.trim_start_matches([' ', '\t']).len();
        Fix::delete("remove `move`", Span::new(at.file, m, end as u32))
    }
}
