//! The rows of the blanks inside a line (§2.5, W3-06): a blank before a
//! postfix opener (S-89, S-123, S-399), around the member `.` (S-203), and a
//! name written right against a string literal (S-400).

use onsa_diag::{Edit, Fix};

use super::{Cursor, Hit, RowId, Want, closing, hit};
use crate::token::{Gap, TokenKind};

/// A blank before a postfix opener that the parser did not read on
/// (`square (x)`, `xs [0]`, `fn f (x: I32)`, `p.scale !(2)`, `lp ~(x)`;
/// [`crate::layout::Detached`], S-89, S-123): E0020, and the candidate takes
/// the blank out (`xs [0]` has the call `xs([0])` as the second, §2.5).
/// When the token before is no path of names (`)`, `]`, `}`, a literal, `?`;
/// S-399), the form is the missing `,` in a list
/// ([`crate::layout::list_fixes`]); out of a list the candidate is made only
/// when the code without the blank reads (`h(x) [0]`; `g(x) (y)` has none:
/// E0002, R-203). When no candidate reads in a list (`(I32 [I32; 2])`: an
/// array type is no list of type arguments), the form is the missing `,`
/// too (S-387, S-236). A line break before the opener is the missing `,`
/// in a list, and elsewhere the general E0002 with the line break taken out
/// (S-89; the parser's `fail_with`).
pub(super) fn space_before_open(c: &Cursor) -> Option<Hit> {
    let d = c.detached.filter(|d| d.at == c.at)?;
    // A line break before a required list is the blank of it (S-412: the
    // `(` after `fn` in a list, where a line break is a blank).
    let newline = c.gap(c.at) == Gap::Newline;
    if newline && !d.required {
        return None;
    }
    let row = match c.kind(c.at) {
        TokenKind::LParen => RowId::SpaceBeforeParen,
        TokenKind::LBracket => RowId::SpaceBeforeBracket,
        TokenKind::Bang => RowId::SpaceBeforeBang,
        TokenKind::Tilde => RowId::SpaceBeforeTilde,
        _ => return None,
    };
    let in_list = matches!(c.want, Want::Separator(_));
    if !d.by_name && in_list {
        return None;
    }
    let mut fixes = Vec::new();
    if d.joins(c.tokens) {
        fixes.extend(crate::layout::join_fix(c));
    }
    if row == RowId::SpaceBeforeBracket
        && d.expr
        && d.by_name
        && let Some(close) = closing(c, c.at)
        && let Some(space) = c.space_before(c.at)
    {
        fixes.push(Fix::new(
            "call it with the array",
            vec![Edit::replace(space, "("), Edit::insert(c.file, c.span(close).end, ")")],
        ));
    }
    if fixes.is_empty() && in_list {
        return None;
    }
    c.say(row);
    hit(c.span(c.at), fixes)
}

/// A string or character literal right against a name (`f"{x}"`, `r"\d"`,
/// `b"x"`, `u8"x"`, `b'x'`) or a name right against a literal (`"x"_s`): the
/// prefixes and suffixes of other languages (§2.4, S-400). E0002 with the
/// note and no candidate; found before the missing `,` of a list (S-387),
/// so no `,` goes between them. The range is the name and the literal (one
/// form, S-316). The literal is one the lexer read whole; else its E0001 is
/// the error (`f"abc` at the end of a line, `x'ab'`).
pub(super) fn string_prefix(c: &Cursor) -> Option<Hit> {
    let literal = |k: TokenKind| matches!(k, TokenKind::Str | TokenKind::Char);
    let prev = c.before(c.at)?;
    if c.gap(c.at) != Gap::None {
        return None;
    }
    let (here, there) = (c.kind(c.at), c.kind(prev));
    let lit = match (here, there) {
        (h, TokenKind::Ident) if literal(h) => c.at,
        (TokenKind::Ident, t) if literal(t) => prev,
        _ => return None,
    };
    // A literal that does not close or holds an error is the lexer's E0001
    // (§2.4): the form is a whole literal against a name.
    if !c.literal_ok(lit) {
        return None;
    }
    hit(c.file_span(c.span(prev).start, c.span(c.at).end), Vec::new())
}

/// A space before or after a member `.` inside a line (`p . x`, `f .(x)`,
/// §2.5, S-203): the candidate removes it. A `.` that starts a line
/// continues the expression; one at the end of a line, or before what no
/// member is, is the general E0002.
pub(super) fn space_around_dot(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Postfix || c.kind(c.at) != TokenKind::Dot {
        return None;
    }
    let (before, after) = (c.gap(c.at), c.gap(c.at + 1));
    if after == Gap::Newline || (before != Gap::Space && after != Gap::Space) {
        return None;
    }
    // `t. 0.5` would become the indexes `t.0.5`, `1 . 5` the number `1.5`
    // and `1 .(2)` the literal `1.` (as `1.(2)` reads, S-350): no candidate
    // keeps their reading.
    let literal_before =
        c.at.checked_sub(1)
            .filter(|&b| b.checked_sub(1).is_none_or(|d| c.kind(d) != TokenKind::Dot))
            .map(|b| c.kind(b))
            .filter(|&k| matches!(k, TokenKind::Int | TokenKind::Float));
    let next = c.kind(c.at + 1);
    if !(matches!(next, TokenKind::Ident | TokenKind::Int | TokenKind::LParen) || next.is_keyword())
        || (literal_before.is_some() && next == TokenKind::Int)
        || (literal_before == Some(TokenKind::Int) && next == TokenKind::LParen)
    {
        return None;
    }
    let mut edits = Vec::new();
    if before == Gap::Space {
        edits.extend(c.space_before(c.at).map(Edit::delete));
    }
    if after == Gap::Space {
        edits.extend(c.space_after(c.at).map(Edit::delete));
    }
    hit(c.span(c.at), vec![Fix::new("remove the space", edits)])
}
