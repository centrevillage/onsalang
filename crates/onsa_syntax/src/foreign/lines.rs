//! The rows of the line breaks where a symbol touches its partner (§2.5,
//! W3-06): after a member `.` (S-353), after a prefix `-` / `!` / `^` and
//! before a postfix `?` (S-369). The candidate moves the symbol to its
//! partner's line ([`crate::layout::move_token_down`],
//! [`crate::layout::move_token_up`]).

use super::*;
use crate::layout::{ends_operand, move_token_down, move_token_up};

/// A line break after a member `.` (`s.` and `f` on the next line, also in
/// a list; S-353): the `.` moves to the head of the next line, before a
/// name, a tuple index or the `(` of `.(`. Before anything else the form
/// has no candidate (E0002 with the note).
pub(super) fn newline_after_dot(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Postfix || c.kind(c.at) != TokenKind::Dot || c.gap_after(c.at) != Gap::Newline {
        return None;
    }
    let next = c.kind(c.sig_after(c.at));
    // A name, a tuple index or the `(` of `.(` (§2.5); a keyword starts the
    // next statement (`let c = s.` and `let d = 1`), which the `.` would join.
    let member = matches!(next, TokenKind::Ident | TokenKind::Int | TokenKind::LParen);
    let fixes = if member {
        move_token_down(c, "move the `.` to the next line", c.at).into_iter().collect()
    } else {
        Vec::new()
    };
    hit(c.span(c.at), fixes)
}

/// A line break after a prefix `-` / `!` / `^` (`two(-` and `a, 1)` on the
/// next line; `let y = -` and `a`; S-369): the symbol moves to its
/// operand's line. Before what no operand starts (and no name, for `^`) the
/// form has no candidate.
pub(super) fn newline_after_prefix(c: &Cursor) -> Option<Hit> {
    let kind = c.kind(c.at);
    let want = if kind == TokenKind::Caret { Want::Expr } else { Want::Prefix };
    if !matches!(kind, TokenKind::Minus | TokenKind::Bang | TokenKind::Caret)
        || c.want != want
        || c.gap_after(c.at) != Gap::Newline
    {
        return None;
    }
    let next = c.kind(c.sig_after(c.at));
    let operand = if kind == TokenKind::Caret { next == TokenKind::Ident } else { crate::parser::starts_operand(next) };
    let fixes = if operand {
        move_token_down(c, "write it against its operand", c.at).into_iter().collect()
    } else {
        Vec::new()
    };
    hit(c.span(c.at), fixes)
}

/// A line break before a postfix `?` (`two(o` and `?, 1)` on the next line;
/// `let v = o` and `?`; S-369): the `?` moves up to its operand.
pub(super) fn newline_before_question(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Question || c.gap(c.at) != Gap::Newline {
        return None;
    }
    let operand = c.sig_before(c.at).is_some_and(|p| ends_operand(c.kind(p)));
    if !operand {
        return None;
    }
    hit(c.span(c.at), move_token_up(c, "write it against its operand", c.at).into_iter().collect())
}
