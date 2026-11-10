//! The candidates of the E0002 of a `,` after the rest of a struct pattern
//! (`_`, `..`) or of a struct literal (`...`), which is its last element
//! (§7, §4.4, S-512): the `,` taken out, or every `_` taken out and one put
//! last.

use onsa_diag::{Edit, Fix};

use super::Cursor;
use crate::cst::NodeKind;
use crate::token::TokenKind;

/// An element of the list of a struct pattern: its first and last token.
#[derive(Clone, Copy)]
struct Element {
    first: usize,
    last: usize,
    rest: bool,
}

/// The candidate at the `,` after the rest `rest`: before the `}` that
/// closes the list, the `,` taken out (`Item { x: a, _, }`, `..,`, `...,`);
/// after a `_` that is not last, [`underscore_last`]. None for the others
/// (a `..` or a `...` that is not last).
pub(super) fn rest_fix(c: &Cursor, rest: usize) -> Option<Fix> {
    if c.kind(c.sig_after(c.at)) == TokenKind::RBrace {
        return Some(Fix::delete("take the `,` after the last element out", c.span(c.at)));
    }
    (c.kind(rest) == TokenKind::Underscore).then(|| underscore_last(c)).flatten()
}

/// The candidate of a `_` that is not the last element of a struct pattern
/// (`Item { _, x: a }`): every `_` taken out with what separates it from the
/// next element, and one `_` last (a `_` already last stays, and a `,`
/// after it goes). None when another element is no field whose pattern
/// reads alone with no form of its own (`.., _`: an error of the stage
/// would stay), or when what it takes out holds a comment. A `_` put last
/// is moved ([`Fix::moved`]): the writer's text.
fn underscore_last(c: &Cursor) -> Option<Fix> {
    let &(_, start) = c.open.iter().rev().find(|o| o.0 == NodeKind::StructPat)?;
    let open = (c.index_at(start)..c.at).find(|&i| c.kind(i) == TokenKind::LBrace)?;
    let close = super::closing(c, open)?;
    let mut elements = Vec::new();
    let mut from = open + 1;
    let mut depth = 0u32;
    for i in open + 1..=close {
        match c.kind(i) {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if depth > 0 => depth -= 1,
            TokenKind::Comma | TokenKind::RBrace if depth == 0 => {
                let code: Vec<usize> =
                    (from..i).filter(|&k| !c.comment(k) && c.kind(k) != TokenKind::Newline).collect();
                if let (Some(&first), Some(&last)) = (code.first(), code.last()) {
                    elements.push(Element {
                        first,
                        last,
                        rest: c.kind(first) == TokenKind::Underscore && first == last,
                    });
                } else if c.kind(i) != TokenKind::RBrace || elements.is_empty() {
                    return None;
                }
                from = i + 1;
            }
            _ => {}
        }
    }
    let fine = |e: &Element| e.rest || field_reads(c, e);
    let last = *elements.last()?;
    if !elements.iter().all(fine) || (open..close).any(|i| c.kind(i) == TokenKind::BlockComment) {
        return None;
    }
    let trailing = c.sig_before(close).filter(|&k| c.kind(k) == TokenKind::Comma);
    let mut edits = Vec::new();
    for (k, e) in elements.iter().enumerate().filter(|(k, e)| e.rest && *k + 1 < elements.len()) {
        let next = elements[k + 1].first;
        if (e.first..next).any(|i| c.comment(i)) {
            return None;
        }
        edits.push(Edit::delete(c.file_span(c.span(e.first).start, c.span(next).start)));
    }
    let title = "put the one `_` last";
    match trailing {
        Some(comma) if last.rest => edits.push(Edit::delete(c.span(comma))),
        _ if last.rest => {}
        Some(comma) if c.at_line_head(close) => {
            let at = c.span(comma).end;
            let line = format!("{}{}_", c.line_break(at), c.indent(c.span(last.first).start));
            edits.push(Edit::insert(c.file, at, line));
        }
        Some(comma) => edits.push(Edit::insert(c.file, c.span(comma).end, " _")),
        None => edits.push(Edit::insert(c.file, c.span(last.last).end, ", _")),
    }
    Some(if last.rest { Fix::new(title, edits) } else { Fix::moved(title, edits) })
}

/// Whether the element `e` is a field `name: pattern` whose pattern reads
/// alone ([`super::arms::reads_alone`]).
fn field_reads(c: &Cursor, e: &Element) -> bool {
    e.last >= e.first + 2
        && c.kind(e.first) == TokenKind::Ident
        && c.kind(e.first + 1) == TokenKind::Colon
        && super::arms::reads_alone(c, c.sig_after(e.first + 1), e.last)
}
