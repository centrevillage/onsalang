//! The candidate of R-198's E0711 (§5.2, S-605, S-807; §18.1, 27): a `move`
//! on a value that is no place. Of a block, an `if` or a `match`, the outer
//! `move` goes and, at a consuming position, each tail that is an owned
//! Affine place gets one; of any other value, the `move` goes.
//!
//! Applied, it leaves no error of the stage (memo 2.5): the `move`s left are
//! on owned Affine tails at a consuming position, which take them, and none
//! is put on a tail that is no place or a Dup one (no E0703 of S-605, S-795).
//! Applied again, nothing is left to fix: it stops at once.

use onsa_diag::internal::bug;
use onsa_diag::{Edit, Fix};
use onsa_syntax::ast::{ExprId, ExprKind};
use onsa_syntax::tails::Tail;

use super::check::Walker;
use super::place::{Proj, place_of};
use super::walk::Pos;
use crate::Kind;
use crate::binding::Bind;

impl Walker<'_> {
    /// The candidate of the E0711 of the `move` at `m` on `e`, no place, at
    /// `pos`; none when a tail is an Affine place that does not move from
    /// there (borrowed, `inout`; at a consuming position an element too).
    pub(super) fn unplaced(&mut self, e: ExprId, m: u32, pos: Pos) -> Option<Fix> {
        let x = self.ast.without_parens(e);
        let remove = self.unmark(self.ast.expr(x).span.file, m, "move");
        if !matches!(self.ast.expr(x).kind, ExprKind::Block(_) | ExprKind::If { .. } | ExprKind::Match { .. }) {
            return Some(remove);
        }
        // S-807: at no consuming position, and at a return, the tails take no `move`.
        let consumes = matches!(pos, Pos::Own | Pos::Value | Pos::MoveArg);
        let takes = consumes || matches!(pos, Pos::Return | Pos::Extract);
        let mut tails = Vec::new();
        self.ast.tails(x, &mut tails);
        let mut edits = remove.edits().to_vec();
        for tail in tails {
            let Tail::Value(v) = tail else { continue };
            if let Some(at) = self.wants_move(v, (consumes, takes))? {
                edits.push(Edit::insert(remove.edits()[0].span.file, at, "move "));
            }
        }
        Some(match edits.len() {
            1 => remove,
            _ => Fix::new("write `move` on the tails", edits),
        })
    }

    /// Where the tail `v` (without parentheses) takes `move` (at a consuming
    /// position, `consumes`): an owned Affine place with none, before its
    /// parentheses. `None` if it is an Affine place that cannot move, or an
    /// element of an array where the value is taken (`takes`, a return too).
    fn wants_move(&mut self, v: ExprId, (consumes, takes): (bool, bool)) -> Option<Option<u32>> {
        let Some(place) = place_of(self.ast, self.names, v) else { return Some(None) };
        let Some(&ty) = self.info.expr_types.get(&v) else { bug(Some(self.ast.expr(v).span), "a tail with no type") };
        if self.kind_of(ty) != Some(Kind::Affine) {
            return Some(None);
        }
        match self.info.locals[place.root.0 as usize].state {
            // An element does not move out of its array (§5.2): read, the `move` only goes.
            Bind::Owned | Bind::OwnedMut if place.proj.contains(&Proj::Index) => (!takes).then_some(None),
            Bind::Owned | Bind::OwnedMut if !consumes => Some(None),
            Bind::Owned | Bind::OwnedMut => self.before_parens(v).map(Some),
            _ => None,
        }
    }

    /// The offset before the parentheses around `v` (a mark is not written
    /// in them, §5.2); `None` if a comment stands in them.
    fn before_parens(&self, v: ExprId) -> Option<u32> {
        let span = self.ast.expr(v).span;
        let (mut start, mut end) = (span.start as usize, span.end as usize);
        loop {
            let ((before, c), (after, d)) = (code_before(&self.text[..start]), code_after(&self.text[end..]));
            match (before.ends_with('('), after.starts_with(')')) {
                (false, false) => return Some(start as u32),
                (true, true) if !(c || d) => (start, end) = (before.len() - 1, self.text.len() - after.len() + 1),
                _ => return None,
            }
        }
    }
}

/// `s` without the blanks and line comments at its end, and whether a
/// comment was there (a `//` in a string of that line counts too: no fix).
fn code_before(mut s: &str) -> (&str, bool) {
    let mut comment = false;
    loop {
        let t = s.trim_end();
        let line = t.rfind('\n').map_or(0, |i| i + 1);
        match t[line..].find("//") {
            Some(k) => (s, comment) = (&t[..line + k], true),
            None => return (t, comment),
        }
    }
}

/// `s` without the blanks and line comments at its start, and whether a
/// comment was there.
fn code_after(mut s: &str) -> (&str, bool) {
    let mut comment = false;
    loop {
        let t = s.trim_start();
        if !t.starts_with("//") {
            return (t, comment);
        }
        (s, comment) = (t.find('\n').map_or("", |i| &t[i..]), true);
    }
}
