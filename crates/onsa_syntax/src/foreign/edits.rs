//! The edits of the candidates that move code up to the line before it
//! ([`move_up`], S-216: the parser's E0003 and the rows), that move a symbol
//! to the line of its partner (S-216, S-369, S-353, S-385) and that write a
//! word next to code (R-205): the one place of each.

use onsa_diag::{Edit, FileId, Fix, Span};

use super::Cursor;
use crate::token::{Token, TokenKind};

/// The candidate that moves `next` up to the line that ends at `end`, with
/// `sep` between them (S-216: the E0003 of `else`, the line break before a
/// postfix opener). With only blanks and line breaks between, they become
/// `sep`. Comments between and after it are kept and keep their order: the code of
/// `next`'s line (up to a comment or the end of the line) moves to `end`,
/// before the comment of that line, and the line of `next` is removed when
/// nothing else is left on it (W3-02/b 4).
pub(crate) fn move_up(file: FileId, text: &str, all: &[Token], title: &str, end: u32, next: Token, sep: &str) -> Fix {
    let at = all.partition_point(|t| t.span.start < next.span.start);
    let comment = |t: &Token| matches!(t.kind, TokenKind::Comment | TokenKind::DocComment);
    let between = all[..at].iter().rev().take_while(|t| t.span.start >= end);
    let rest = &all[at..];
    let after = rest.iter().take_while(|t| !matches!(t.kind, TokenKind::Newline | TokenKind::Eof));
    if !between.clone().any(comment) && !after.clone().any(comment) {
        return Fix::replace(title, Span::new(file, end, next.span.start), sep);
    }
    // The code of `next`'s line: up to a comment, a newline or the end.
    let code_len = rest
        .iter()
        .position(|t| {
            matches!(t.kind, TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment | TokenKind::Eof)
        })
        .unwrap_or(rest.len());
    let code_end =
        rest[..code_len].iter().rev().find(|t| t.kind != TokenKind::Whitespace).map_or(next.span.end, |t| t.span.end);
    let moved = &text[next.span.start as usize..code_end as usize];
    let after = rest[code_len..].first().copied();
    let removed = match after.map(|t| t.kind) {
        // Nothing else on the line: remove the line, its indentation and its newline.
        Some(TokenKind::Newline) | Some(TokenKind::Eof) | None => {
            let line_start = match all[at.saturating_sub(1)] {
                t if at > 0 && t.kind == TokenKind::Whitespace => t.span.start,
                _ => next.span.start,
            };
            Span::new(file, line_start, after.map_or(code_end, |t| t.span.end))
        }
        // A comment stays on the line, after the indentation.
        Some(_) => Span::new(file, next.span.start, after.map_or(code_end, |t| t.span.start)),
    };
    Fix::new(title, vec![Edit::insert(file, end, format!("{sep}{moved}")), Edit::delete(removed)])
}

/// The edit that inserts `s` at `offset` of `text` apart from the tokens
/// around it: a blank goes between `s` and a name or a number it would
/// touch (R-205: ` at a` before `e` would read as ` at ae`). The one
/// insertion of the candidates that write a word next to code.
pub(super) fn insert_apart(file: FileId, text: &str, offset: u32, s: &str) -> Edit {
    let word = |c: Option<char>| c.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_');
    let before = word(text[..offset as usize].chars().next_back()) && word(s.chars().next());
    let after = word(text[offset as usize..].chars().next()) && word(s.chars().next_back());
    let s = format!("{}{s}{}", if before { " " } else { "" }, if after { " " } else { "" });
    Edit::insert(file, offset, s)
}

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
