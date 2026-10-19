//! The edits of the candidates that move a symbol to the line of its partner
//! (S-216, S-369, S-353, S-385), on the rows' [`Cursor`]: the one place of
//! each. The edits that need no cursor are in [`crate::edits`].

use onsa_diag::{Edit, Fix, Span};

use super::Cursor;
use crate::token::TokenKind;

/// The full-list index of the parser's token `i`, and the line of it: its
/// line holds nothing but it (blanks aside).
fn alone_on_its_line(c: &Cursor, i: usize) -> Option<Span> {
    let k = c.full[i] as usize;
    let mut a = k;
    if a > 0 && c.all[a - 1].kind == TokenKind::Whitespace {
        a -= 1;
    }
    let starts = a == 0 || c.all[a - 1].kind == TokenKind::Newline;
    let mut b = k + 1;
    if c.all.get(b).is_some_and(|t| t.kind == TokenKind::Whitespace) {
        b += 1;
    }
    let ends = c.all.get(b).is_none_or(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof));
    // The line and its newline (the line of the end of the file has none).
    let end = c.all.get(b).filter(|t| t.kind == TokenKind::Newline).map_or(c.span(i).end, |t| t.span.end);
    (starts && ends).then(|| Span::new(c.file, c.all[a].span.start, end))
}

/// The candidate that moves the symbol `i` (`?`, the `~` of `if~`) up to the
/// end of the code before it, written against it, before the comment of
/// that line (S-216, S-369, S-385). What follows the symbol on its line stays
/// there; a line left empty goes.
pub(super) fn move_token_up(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
    let s = c.span(i);
    move_token_up_as(c, title, i, &c.text[s.start as usize..s.end as usize])
}

/// [`move_token_up`], the symbol written as `symbol` where it goes (` +`
/// after a blank for a binary operator, ` ..<` for `..`, S-124, S-335).
pub(super) fn move_token_up_as(c: &Cursor, title: &str, i: usize, symbol: &str) -> Option<Fix> {
    let prev = c.sig_before(i)?;
    let removed = alone_on_its_line(c, i).unwrap_or_else(|| {
        let k = c.full[i] as usize + 1;
        let end = c.all.get(k).filter(|t| t.kind == TokenKind::Whitespace).map_or(c.span(i).end, |t| t.span.end);
        Span::new(c.file, c.span(i).start, end)
    });
    Some(Fix::new(title, vec![Edit::insert(c.file, c.span(prev).end, symbol), Edit::delete(removed)]))
}

/// The candidate that moves the symbol `i` at the end of its line (a member
/// `.`, a prefix `-` / `!` / `^`) down to the token after it, written
/// against it (S-353, S-369). The comments and blank lines between stay; the
/// blanks before the symbol go with it, and a line left empty goes.
pub(super) fn move_token_down(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
    let next = c.sig_after(i);
    if next == i || c.kind(next) == TokenKind::Eof {
        return None;
    }
    let removed = alone_on_its_line(c, i).unwrap_or_else(|| {
        let k = c.full[i] as usize;
        let start = k.checked_sub(1).map(|p| c.all[p]).filter(|t| t.kind == TokenKind::Whitespace);
        Span::new(c.file, start.map_or(c.span(i).start, |t| t.span.start), c.span(i).end)
    });
    let s = c.span(i);
    let symbol = &c.text[s.start as usize..s.end as usize];
    Some(Fix::new(title, vec![Edit::delete(removed), Edit::insert(c.file, c.span(next).start, symbol)]))
}
