//! Consumption and moves (§5.2, §5.4): a value at a
//! consuming position, decided by the state of its root, its kind and its
//! `move` mark. An erroneous consumption moves nothing (§18.1: a later
//! diagnostic is then no symptom of it).

use onsa_diag::{Code, Diagnostic, FileId, Fix, Span, Stage};
use onsa_syntax::ast::ExprId;

use super::check::Walker;
use super::flow::Run;
use super::place::{Place, Proj, place_of};
use super::walk::Pos;
use super::write::Of;
use crate::Kind;
use crate::binding::Bind;
use crate::ty::TyId;

/// S-784, S-785: at `?` and a `move self` receiver, how to read the value
/// instead.
const EXTRACT: &str = "`?` and a `move self` receiver consume their operand (§5.2, §9.1): read it with `match` instead, or own it (a `move` parameter)";

/// The E0711 of `move` on a value that is no place (§5.2, R-198), wherever
/// it stands ([`Walker::needs_a_place`]).
pub(super) const MOVE_NEEDS_A_PLACE: &str =
    "`move` needs a place (a variable or its field); other values are already owned by the expression";

/// What a place does at a consuming position (§5.2), by its kind, the state
/// of its root and its path: the one table of the E0711s and E0703s here
/// and of the candidate of `marks.rs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Movable {
    /// A Dup value: copied.
    Copied(Kind),
    /// An Affine value of an `inout` parameter (R-117, S-41) and of a
    /// borrow: it cannot move.
    Inout,
    Borrowed,
    /// An element of an owned array: it moves with the array only.
    Element,
    /// An owned Affine place: it moves.
    Owned,
}

impl Walker<'_> {
    /// What the place `p`, of the type `ty`, does where it is consumed;
    /// `None` of no kind (the error type, a second-class value).
    pub(super) fn movable(&mut self, p: &Place, ty: TyId) -> Option<Movable> {
        Some(match (self.kind_of(ty)?, self.info.locals[p.root.0 as usize].state) {
            (kind @ (Kind::Copy | Kind::Shared), _) => Movable::Copied(kind),
            (_, Bind::Inout) => Movable::Inout,
            (_, Bind::Borrow { .. }) => Movable::Borrowed,
            (_, Bind::Owned | Bind::OwnedMut) if p.proj.contains(&Proj::Index) => Movable::Element,
            (_, Bind::Owned | Bind::OwnedMut) => Movable::Owned,
        })
    }

    /// The value `e` at the consuming position `pos` (`Own`, `Value`, `MoveArg`,
    /// `Return` or `Extract`), with the offset of the `move` written on it,
    /// if any.
    pub(super) fn consume(&mut self, r: &mut Run, e: ExprId, pos: Pos, mark: Option<u32>) {
        // A direct argument changes its place after the call (§7, S-796).
        let of = match (std::mem::take(&mut self.inside.direct), pos) {
            (true, _) => Of::Arg,
            (false, Pos::MoveArg) => Of::Tail,
            _ => Of::Other,
        };
        let x = self.ast.without_parens(e);
        let at = self.ast.expr(x).span;
        // The second-class values come first, before the table (R-325).
        if self.out_of_place(r, x, pos) {
            return;
        }
        let Some(place) = place_of(self.ast, self.names, x) else {
            let Some(m) = mark else { return self.expr(r, x, pos) };
            if self.marked_tail(x, pos) {
                return self.expr(r, x, pos);
            }
            self.needs_a_place(x, m, pos);
            return self.expr(r, x, Pos::Read);
        };
        let (l, live) = (place.root, self.live(r, &place));
        self.expr(r, x, Pos::Read);
        let Some(&ty) = self.info.expr_types.get(&x) else {
            onsa_diag::internal::bug(Some(at), "a consumed place with no type")
        };
        // The error type. Not live, its E0704 above (and a move recorded only, S-799).
        let Some(movable) = self.movable(&place, ty) else { return };
        let (text, local) = (self.text, &self.info.locals[l.0 as usize]);
        let (name, root) = (&text[at.start as usize..at.end as usize], &local.name);
        let plain = |message: String| Diagnostic::new(Stage::Modes, Code::E0711, at, message);
        let error = |message: String| match pos {
            Pos::Extract => plain(message).with_rule(EXTRACT),
            _ => plain(message),
        };
        let d = match movable {
            // Copied; a `move` on a `move` argument (S-609) or where a value is put (S-795) is E0703.
            Movable::Copied(kind) => {
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
            Movable::Inout => error(format!(
                "cannot move `{name}`: `{root}` is an `inout` parameter, which does not own its value (§5.2)"
            )),
            Movable::Borrowed => error(format!(
                "cannot move `{name}`: `{root}` is borrowed here and the value is Affine; only owned values move (§5.2, §5.4)"
            )),
            Movable::Element => error(format!(
                "cannot move `{name}` out of an array: its elements move with the array (`for x in move xs`) (§5.2)"
            )),
            Movable::Owned => match mark {
                None if pos.takes_move() => {
                    let d = match pos {
                        Pos::MoveArg => {
                            let message = "this parameter is `move`; write `move` before the argument (§5.2)";
                            Diagnostic::new(Stage::Modes, Code::E0703, at, message)
                        }
                        _ => error(format!("Affine value `{name}` is consumed here; write `move {name}` (§5.2)")),
                    };
                    self.add_move(e, &place).into_iter().fold(d, Diagnostic::with_fix)
                }
                // An erroneous move (E0712 at the anonymous function) moves nothing.
                _ if self.captured(l) => return,
                _ if !live => return self.record(&place, at, of),
                // S-85: a path of fields is taken out, and its root moves whole.
                _ => return self.move_place(r, &place, at, of),
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
        if self.marked_tail(e, pos) {
            return self.expr(r, e, pos);
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
    /// a mark is not written in them, §5.2), of the place `p`. None when a
    /// `for` or a guard holds the whole of its root, which the `move` moves
    /// (a field taken out too, S-85): it would leave an E0715 of this stage
    /// (§18.1).
    fn add_move(&self, e: ExprId, p: &Place) -> Option<Fix> {
        if self.holds(&Place { root: p.root, proj: Vec::new() }) {
            return None;
        }
        let span = self.ast.expr(e).span;
        Some(Fix::insert("add `move`", span.file, span.start, "move "))
    }

    /// The candidate that removes the mark `word` at `m` and the blanks
    /// after it (not a comment, which is no part of the mark).
    pub(super) fn unmark(&self, file: FileId, m: u32, word: &str) -> Fix {
        let after = &self.text[m as usize + word.len()..];
        let end = self.text.len() - after.trim_start_matches([' ', '\t']).len();
        Fix::delete(format!("remove `{word}`"), Span::new(file, m, end as u32))
    }
}
