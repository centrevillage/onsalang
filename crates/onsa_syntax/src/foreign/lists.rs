//! The candidates of the general E0002 of a failure that no row names
//! (§2.5, §18.1): the missing `,` between two elements of a list (S-384,
//! S-387, S-386, S-398, S-405), the two string literals made one (S-388),
//! and the blank or the line break taken out before a postfix opener (S-89,
//! S-373, S-399). The parser asks them with the rows ([`super::at_failure`]).

use onsa_diag::{Edit, Fix, Span};

use super::{Cursor, Want};
use crate::cst::NodeKind;
use crate::scan::{arm_ahead, bracket_contents};
use crate::starts::{declares_a_function, starts_element};
use crate::token::TokenKind;

/// The candidate that takes out the blank or the line break before the
/// opener at `c.at` (S-89, S-399): its line moves up to the token before it
/// ([`super::edits::move_up`], S-216). The one place of that candidate.
pub(super) fn join_fix(c: &Cursor) -> Option<Fix> {
    let prev = c.sig_before(c.at)?;
    let title = if c.at_line_head(c.at) { "remove the line break" } else { "remove the space" };
    Some(super::edits::move_up(c.file, c.text, c.all, title, c.span(prev).end, c.tokens[c.at], ""))
}

/// The candidates of the general E0002 at the token after an element of a
/// list of `list`, where a `,` or the closing bracket goes (§2.5), in the
/// order of the decisions (out of a list, `None`: only the opener after a
/// line break has its candidate, S-89):
///
/// - two string literals next to each other (S-388): the `,`, and the one
///   literal they make;
/// - an opener after a line break (S-89, S-373), or after a blank when the
///   token before is no path of names (S-399): the `,` when the opener
///   starts an element, and the gap taken out when that reads;
/// - else the `,` when the token starts an element (S-384, S-387), whatever
///   is between the elements;
/// - in the arms of a `match`, a `-`, `|` or `+` that a `=>` follows starts
///   the next arm (S-386): the `,`, which takes a `+` out (S-405); a `- 1`
///   has none, as its blank is an error of its own.
///
/// The two candidates of an opener after a line break are only those that
/// the scan of the tokens reads (S-419): in the arms, the `,` when a `=>`
/// follows ([`arm_ahead`](crate::scan::arm_ahead)) and the line break taken out when none does; in
/// a list of types only, a `[` starts an element when a `;` is in it.
///
/// The `,` goes right after the last token of the element, before the
/// comment of its line.
pub(super) fn list_fixes(c: &Cursor, list: Option<NodeKind>) -> Vec<Fix> {
    let Some(prev) = c.sig_before(c.at) else { return Vec::new() };
    let kind = c.kind(c.at);
    let arms = list == Some(NodeKind::MatchArms);
    if arms && matches!(kind, TokenKind::Minus | TokenKind::Pipe | TokenKind::Plus) && arm_ahead(c.tokens, c.at) {
        let spaced = kind == TokenKind::Minus && c.gap_after(c.at).is_some();
        return if spaced { Vec::new() } else { vec![comma_before_sign(c, prev, c.at)] };
    }
    let mut fixes = Vec::new();
    let declaration = declares_a_function(kind, c.kind(c.sig_after(c.at)));
    let joins = c.detached.is_some_and(|d| d.at == c.at && d.joins(c.tokens));
    let types = matches!(list, Some(NodeKind::VariantFields | NodeKind::TupleType | NodeKind::FnTypeParams));
    let array =
        (kind != TokenKind::LBracket || !types || bracket_contents(c.tokens, c.at).is_some_and(|(_, _, semi)| semi))
            && !(list == Some(NodeKind::ArrayExpr) && array_repeats(c));
    let comma = !(arms && joins && !arm_ahead(c.tokens, c.at));
    if list.is_some_and(|l| starts_element(l, kind)) && !declaration && array && comma {
        fixes.push(Fix::new("write the `,` between the elements", vec![Edit::insert(c.file, c.span(prev).end, ",")]));
    }
    let strings = kind == TokenKind::Str && c.kind(prev) == TokenKind::Str;
    if strings && list.is_some() {
        fixes.extend(merge_strings(c, prev));
    } else if joins && !(arms && arm_ahead(c.tokens, c.at)) {
        fixes.extend(join_fix(c));
    }
    fixes
}

/// The two string literals `prev` and `c.at` as one (S-388): the text of the
/// second goes before the closing `"` of the first, and the token of the
/// second goes; the other tokens and the comments stay on their lines (as
/// S-216 moves code). Only two literals that the lexer read whole (closed,
/// with no error in them, [`Cursor::literal_ok`]): a literal that does not
/// close is the lexer's E0001.
fn merge_strings(c: &Cursor, prev: usize) -> Option<Fix> {
    if !(c.literal_ok(prev) && c.literal_ok(c.at)) {
        return None;
    }
    let (first, second) = (c.span(prev), c.span(c.at));
    let text = |s: Span| &c.text[s.start as usize..s.end as usize];
    // A closed literal starts and ends with the one-byte `"`.
    let one = format!("{}{}", &text(first)[..text(first).len() - 1], &text(second)[1..]);
    Some(Fix::new("make the two literals one", vec![Edit::replace(first, one), Edit::delete(second)]))
}

/// The candidate that makes the sign `sign` the start of the element after
/// `prev` in a list: the `,` after `prev`, before the comment of its line,
/// and for a `+`, which is no prefix (§3.1), the `+` and the blanks after it
/// taken out with it (S-370, S-386, S-398, S-405). The one candidate of the
/// `,` before a `-`, `^`, `|` or `+`.
pub(super) fn comma_before_sign(c: &Cursor, prev: usize, sign: usize) -> Fix {
    let comma = Edit::insert(c.file, c.span(prev).end, ",");
    if c.kind(sign) != TokenKind::Plus {
        return Fix::new("write the `,` between the elements", vec![comma]);
    }
    let s = c.span(sign);
    let end = c.space_after(sign).map_or(s.end, |w| w.end);
    Fix::new("write the `,` and take the `+` out", vec![comma, Edit::delete(Span::new(c.file, s.start, end))])
}

/// Whether the list of the failure is one whose elements are expressions
/// (arguments, a tuple, an array; S-370, S-398), where a sign may start the
/// next element: not the repetition `[v; n]` of an array, which a `,` does
/// not make a list (a `;` in its brackets, the scan of S-419).
pub(super) fn expression_list(c: &Cursor) -> bool {
    match c.want {
        Want::Separator(NodeKind::ArgList | NodeKind::TupleExpr) => true,
        Want::Separator(NodeKind::ArrayExpr) => !array_repeats(c),
        _ => false,
    }
}

/// Whether the innermost array open at the failure is a repetition (a `;`
/// at its depth): its brackets close, and a `;` is in them.
fn array_repeats(c: &Cursor) -> bool {
    let Some(&(_, start)) = c.open.iter().rev().find(|o| o.0 == NodeKind::ArrayExpr) else { return false };
    bracket_contents(c.tokens, c.index_at(start)).is_some_and(|(_, _, semi)| semi)
}
