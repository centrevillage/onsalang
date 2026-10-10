//! The row of a callee that is no path of names (`.(`, §6.1, S-191, S-256;
//! what a callee is, [`crate::callee`]), and the candidate that calls a
//! value with `.(`.

use super::literals::literal_call;
use super::*;

/// The candidate that calls the value `callee` with `.(` in place of the
/// type arguments in `first..=last` (the call's `(` follows `last`): the
/// list and the blanks before it become `.`, and the parentheses around a
/// postfix expression go (`(s.f)` is `s.f.(x)`, §4.5).
pub(super) fn value_call(c: &Cursor, callee: (NodeKind, u32), first: usize, last: usize) -> Option<Fix> {
    if c.kind(last + 1) != TokenKind::LParen || c.gap(last + 1) != Gap::None {
        return None;
    }
    let before = first.checked_sub(1)?;
    let mut edits = vec![Edit::replace(c.file_span(c.span(before).end, c.span(last).end), ".")];
    if let Some(open) = removable_parens(c, callee, before) {
        edits.push(Edit::delete(c.span(open)));
        edits.push(Edit::delete(c.span(before)));
    }
    Some(Fix::new("call the function value with `.(`", edits))
}

/// The `(` of the callee `callee` that closes at `close`, when the
/// parentheses can go before `.(`: the callee is a parenthesis around a
/// postfix expression (a path of names and the fields, tuple indexes,
/// indexes, calls and `?` after it), which `.(` follows with the same
/// reading (S-236). `(a + b)` keeps them, and so does a `(` that touches a
/// word before it (`return(s.f)`: the word would join the name, S-302).
fn removable_parens(c: &Cursor, callee: (NodeKind, u32), close: usize) -> Option<usize> {
    if callee.0 != NodeKind::ParenExpr || c.kind(close) != TokenKind::RParen {
        return None;
    }
    let open = c.index_at(callee.1);
    let word = |k: TokenKind| matches!(k, TokenKind::Ident | TokenKind::Int | TokenKind::Float) || k.is_keyword();
    if c.gap(open) == Gap::None && open.checked_sub(1).is_some_and(|b| word(c.kind(b))) {
        return None;
    }
    is_postfix_chain(c, open + 1, close.checked_sub(1)?).then_some(open)
}

/// The tokens `first..=last` are a postfix expression on one line: a name,
/// `self` or `Self` and, after it, only `.name`, `.0`, `.(…)`, `(…)`,
/// `[…]`, `::[…]`, `~(…)`, `!(…)` and `?` (the links of
/// [`crate::callee::Link`], read in the text).
fn is_postfix_chain(c: &Cursor, first: usize, last: usize) -> bool {
    if first > last || !matches!(c.kind(first), TokenKind::Ident | TokenKind::KwSelf | TokenKind::KwSelfType) {
        return false;
    }
    let after_group = |open: usize| closing(c, open).map(|close| close + 1);
    let mut i = first + 1;
    while i <= last {
        let next = match (c.kind(i), c.kind(i + 1)) {
            (TokenKind::Dot, TokenKind::LParen) => after_group(i + 1),
            (TokenKind::Dot, k) if k == TokenKind::Ident || k == TokenKind::Int || k.is_keyword() => Some(i + 2),
            (TokenKind::LParen | TokenKind::LBracket, _) => after_group(i),
            (TokenKind::ColonColon, TokenKind::LBracket)
            | (TokenKind::Tilde, TokenKind::LParen)
            | (TokenKind::Bang, TokenKind::LParen) => after_group(i + 1),
            (TokenKind::Question, _) => Some(i + 1),
            _ => None,
        };
        let Some(next) = next else { return false };
        i = next;
    }
    i == last + 1
}

/// A call whose callee is neither a path of names nor a path of names with
/// `[…]` (`(s.f)(x)`, `pick(true)(5)`, `h.(1)(2)`, §6.1, S-191): no item is
/// such a callee, so the parser fails at its `(`. The one candidate calls the
/// value with `.(`: the parentheses around a postfix expression go and the
/// `)` becomes the `.` (`s.f.(x)`); else a `.` goes before the `(`
/// (`pick(true).(5)`, `(a + b).(1)`). An integer literal as the callee has
/// none (`1.(2)` reads as the literal `1.`, §2.4).
pub(super) fn callee_expression(c: &Cursor) -> Option<Hit> {
    // The parser has judged the callee ([`crate::callee::Callee::by_name`]).
    if c.want != Want::Callee {
        return None;
    }
    let callee = closed_expr(c)?;
    let before = c.at.checked_sub(1)?;
    // From the callee to the `(` the parser failed at: the arguments, not
    // read yet, may hold errors of their own.
    let span = c.file_span(callee.1, c.span(c.at).end);
    let edits = match removable_parens(c, callee, before) {
        Some(open) => vec![Edit::delete(c.span(open)), Edit::replace(c.span(before), ".")],
        // Not a tuple index (`ts[0].0.(x)` reads as written).
        None if callee.0 == NodeKind::Literal && literal_call(c, before) == Some(TokenKind::Int) => {
            return hit(span, Vec::new());
        }
        None => vec![Edit::insert(c.file, c.span(c.at).start, ".")],
    };
    // The call takes the callee one level down (§2.5): no candidate that
    // takes the unit over the limit, where the check after it would report
    // the E0006 of the same stage (S-236, R-200).
    let added = u32::from(edits.len() == 1);
    if crate::groups::nests_too_deep(c.text, span, &edits, added, crate::parser::NESTING_LIMIT) {
        return hit(span, Vec::new());
    }
    hit(span, vec![Fix::new("call the function value with `.(`", edits)])
}
