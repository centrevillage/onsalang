//! The edits of the candidates that move a symbol to the line of its partner
//! (S-216, S-369, S-353, S-385), on the rows' [`Cursor`]: the one place of
//! each. The edits that need no cursor are in [`crate::edits`].

use onsa_diag::{Edit, Fix, Span};

use super::Cursor;
use crate::token::TokenKind;

/// The line of the parser's token `i` when it holds nothing but it (blanks
/// aside, [`crate::edits::whole_line`]).
fn alone_on_its_line(c: &Cursor, i: usize) -> Option<Span> {
    let k = c.full[i] as usize;
    let stop = k + 1 + usize::from(c.all.get(k + 1).is_some_and(|t| t.kind == TokenKind::Whitespace));
    c.at_line_head(i).then(|| crate::edits::whole_line(c.file, c.all, (k, stop, c.span(i).end))).flatten()
}

/// The candidate that moves the symbol `i` (`?`, the `~` of `if~`) up to the
/// end of the code before it, written against it, before the comment of
/// that line (S-216, S-369, S-385). What follows the symbol on its line stays
/// there; a line left empty goes.
pub(super) fn move_token_up(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
    let s = c.span(i);
    move_token_up_as(c, title, i, &c.text[s.start as usize..s.end as usize])
}

/// [`move_token_up`], the symbol written as `symbol` where it goes
/// ([`crate::edits::move_token_up`]).
pub(super) fn move_token_up_as(c: &Cursor, title: &str, i: usize, symbol: &str) -> Option<Fix> {
    let prev = c.sig_before(i)?;
    Some(crate::edits::move_token_up(c.file, c.text, c.all, title, c.span(prev).end, c.full[i] as usize, symbol))
}

/// The candidate that moves the symbol `i` at the end of its line (a member
/// `.`, a prefix `-` / `!` / `^`) down to the token after it, written
/// against it (S-353, S-369). The comments and blank lines between stay; the
/// blanks before the symbol go with it, and a line left empty goes.
pub(super) fn move_token_down(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
    let s = c.span(i);
    move_token_down_as(c, title, i, &c.text[s.start as usize..s.end as usize])
}

/// [`move_token_down`], the symbol written as `symbol` where it goes (the
/// `~` of C as `!`, S-957).
pub(super) fn move_token_down_as(c: &Cursor, title: &str, i: usize, symbol: &str) -> Option<Fix> {
    let next = c.sig_after(i);
    if next == i || c.kind(next) == TokenKind::Eof {
        return None;
    }
    Some(Fix::new(title, vec![Edit::delete(taken_down(c, i)), Edit::insert(c.file, c.span(next).start, symbol)]))
}

/// What [`move_token_down`] takes out of the line of the symbol `i` (and the
/// `--` of an increment written out on the line after it, S-429).
pub(super) fn taken_down(c: &Cursor, i: usize) -> Span {
    alone_on_its_line(c, i).unwrap_or_else(|| {
        let k = c.full[i] as usize;
        let start = k.checked_sub(1).map(|p| c.all[p]).filter(|t| t.kind == TokenKind::Whitespace);
        Span::new(c.file, start.map_or(c.span(i).start, |t| t.span.start), c.span(i).end)
    })
}
