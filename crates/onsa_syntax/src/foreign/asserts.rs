//! The rows of the `assert` of other languages (§7, S-879, S-964): the
//! `assert!(c)` of Rust, which Onsa would read as the negated condition, and
//! the message of Rust's `assert!(c, m)` and of Python's `assert c, m`.

use super::*;
use crate::layout::Lines;
use crate::scan::Brackets;

/// The `)` of the `assert!(` of Rust at token `kw`: a `!` right after the
/// `assert` and a `(` right after the `!`, with no blank between them, and
/// the `)` that closes it (§7, S-964; `assert !(c)` and `assert!c` are the
/// prefix `!`, and an `!(` that does not close is read as one). The one test
/// of the form, for the parser (which fails at the `!`,
/// `Parser::parse_stmt`) and the table.
pub(crate) fn rust_assert(tokens: &[Token], lines: &Lines, brackets: &Brackets, kw: usize) -> Option<usize> {
    let form = tokens[kw].kind == TokenKind::KwAssert
        && tokens.get(kw + 2).is_some_and(|t| t.kind == TokenKind::LParen)
        && tokens[kw + 1].kind == TokenKind::Bang
        && lines.before(kw + 1) == Gap::None
        && lines.before(kw + 2) == Gap::None;
    form.then(|| brackets.closing(kw + 2)).flatten()
}

/// The rows [`assert_form`] names ([`super::Matcher::many`]).
pub(super) const ASSERT_ROWS: &[RowId] = &[RowId::AssertBang, RowId::AssertMessage];

/// The title of the candidate that drops a message (§7).
const DROP_MESSAGE: &str = "drop the message: `assert` takes none";

/// The forms of `assert` of other languages, at the failure of the parser:
/// the `!` of Rust's `assert!(`, or the `,` after the statement `assert c`
/// of Python.
pub(super) fn assert_form(c: &Cursor) -> Option<(RowId, Hit)> {
    match c.closed.last() {
        Some(&(NodeKind::AssertStmt, start)) if c.kind(c.at) == TokenKind::Comma => python_message(c, start),
        _ => rust_form(c),
    }
}

/// `assert!(c)` and `assert!(c, m)` (S-964, S-879): the form is `assert` to
/// the `)` that closes the `!(`. With no `,` directly in it, the two
/// readings are the candidates: `assert(c)` and `assert !(c)`; with one, the
/// message is everything from it and the one candidate drops it
/// ([`rust_message`]).
fn rust_form(c: &Cursor) -> Option<(RowId, Hit)> {
    let kw = c.at.checked_sub(1)?;
    let close = rust_assert(c.tokens, c.lines, c.brackets(), kw)?;
    let (bang, open) = (c.at, c.at + 1);
    let span = c.file_span(c.span(kw).start, c.span(close).end);
    let Some(comma) = first_comma(c, open, close) else {
        let fixes = vec![
            Fix::delete("assert the condition: `assert(…)`", c.span(bang)),
            Fix::insert("assert the negated condition: `assert !(…)`", c.file, c.span(bang).start, " "),
        ];
        return found(RowId::AssertBang, span, fixes);
    };
    found(RowId::AssertMessage, span, rust_message(c, kw, comma, close).into_iter().collect())
}

/// The candidate of `assert!(c, m)`: `assert c`, the `!(`, the message
/// and the `)` out (the comments among them go too). With tokens after
/// the `)` in the statement, a condition that is no plain operand keeps its
/// parentheses (`assert(a < b) == d`, [`operand`]); else every line break
/// in it goes on with its line (§2.5), as the parentheses are no more. None
/// for an empty condition.
fn rust_message(c: &Cursor, kw: usize, comma: usize, close: usize) -> Option<Fix> {
    let first = c.sig_after(c.at + 1);
    let last = c.sig_before(comma).filter(|_| first < comma)?;
    let kinds: Vec<TokenKind> = (first..=last).map(|i| c.kind(i)).collect();
    if !ends_statement(c, close) && operand(&kinds) != Operand::Plain {
        let message = c.file_span(c.span(last).end, c.span(close).start);
        return Some(Fix::new(DROP_MESSAGE, vec![Edit::delete(c.span(c.at)), Edit::delete(message)]));
    }
    if !goes_on(c, first, last) {
        return None;
    }
    let edits = vec![
        Edit::replace(c.file_span(c.span(kw).end, c.span(first).start), " "),
        Edit::delete(c.file_span(c.span(last).end, c.span(close).end)),
    ];
    Some(Fix::new(DROP_MESSAGE, edits))
}

/// `assert c, m` (S-879): the parser read the statement `assert c` that
/// starts at `start` and fails at the `,`. The message is the rest of the
/// statement ([`message_end`]), and the one candidate drops it; a bracket in
/// it that does not close ends the form, with no candidate (§18.1).
fn python_message(c: &Cursor, start: u32) -> Option<(RowId, Hit)> {
    let last = c.sig_before(c.at)?;
    match message_end(c, c.at) {
        Ok(end) => {
            let fix = Fix::delete(DROP_MESSAGE, c.file_span(c.span(last).end, c.span(end).end));
            found(RowId::AssertMessage, c.file_span(start, c.span(end).end), vec![fix])
        }
        Err(open) => found(RowId::AssertMessage, c.file_span(start, c.span(open).end), Vec::new()),
    }
}

/// The last token of the statement whose `,` is at `comma`: it goes on to a
/// line break that does not go on with its line, a `;`, a closer of what it
/// is in or the end of the file, a bracket in it passed over to its closer
/// ([`closing`], as the parser pairs them). Err with a bracket that does
/// not close.
fn message_end(c: &Cursor, comma: usize) -> Result<usize, usize> {
    use TokenKind::*;
    let (mut i, mut last) = (comma + 1, comma);
    loop {
        match c.kind(i) {
            _ if c.comment(i) => {}
            Newline if c.lines.goes_on(i) => {}
            Newline | Semi | Eof | RParen | RBracket | RBrace => return Ok(last),
            LParen | LBracket | LBrace => {
                let close = closing(c, i).ok_or(i)?;
                (i, last) = (close, close);
            }
            _ => last = i,
        }
        i += 1;
    }
}

/// The first `,` directly in the brackets `open..close` (the brackets in
/// them passed over, [`closing`]).
fn first_comma(c: &Cursor, open: usize, close: usize) -> Option<usize> {
    let mut i = open + 1;
    while i < close {
        match c.kind(i) {
            TokenKind::Comma => return Some(i),
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => i = closing(c, i)?,
            _ => {}
        }
        i += 1;
    }
    None
}

/// Whether every line break directly in the tokens `first..=last` (out of
/// the brackets in them) goes on with its line ([`crate::layout::Lines::goes_on`]).
fn goes_on(c: &Cursor, first: usize, last: usize) -> bool {
    let mut i = first;
    while i <= last {
        match c.kind(i) {
            TokenKind::Newline if !c.lines.goes_on(i) => return false,
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => match closing(c, i) {
                Some(close) => i = close,
                None => return false,
            },
            _ => {}
        }
        i += 1;
    }
    true
}
