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
/// opener at `c.at` (S-89, S-399): a blank right after the token before it
/// goes, and else its line moves up to that token
/// ([`crate::edits::move_up`], S-216). The one place of that candidate.
pub(super) fn join_fix(c: &Cursor) -> Option<Fix> {
    // Only the blank changes: what follows the opener on its line stays out
    // of the edit (§18.1, R-214).
    if c.before(c.at).is_some() {
        return Some(crate::edits::take_out_blanks("remove the space", vec![c.space_before(c.at)?]));
    }
    let prev = c.sig_before(c.at)?;
    let title = if c.at_line_head(c.at) { "remove the line break" } else { "remove the space" };
    Some(crate::edits::move_up(c.file, c.text, c.all, title, c.span(prev).end, c.tokens[c.at], ""))
}

/// The candidates of the general E0002 at the token after an element of a
/// list of `list`, where a `,` or the closing bracket goes (§2.5), in the
/// order of the decisions (out of a list, `None`: only the opener after a
/// line break has its candidate, S-89), the cases of [`CASES`]:
///
/// - in the arms of a `match`, a `-`, `|` or `+` that a `=>` follows starts
///   the next arm (S-386): the `,`, which takes a `+` out (S-405); a `- 1`
///   has none, as its blank is an error of its own; nothing else;
/// - the `,` when the token starts an element (S-384, S-387), whatever is
///   between the elements;
/// - two string literals next to each other (S-388): the one literal they
///   make, after the `,`;
/// - else an opener after a line break (S-89, S-373), or after a blank when
///   the token before is no path of names (S-399): the gap taken out when
///   that reads, after the `,` when the opener starts an element.
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
    let a = After {
        c,
        list,
        prev,
        kind: c.kind(c.at),
        arms: list == Some(NodeKind::MatchArms),
        joins: c.detached.is_some_and(|d| d.at == c.at && d.joins(c.tokens)),
    };
    let mut fixes = Vec::new();
    for case in CASES {
        if (case.holds)(&a) {
            fixes.extend((case.makes)(&a));
            if case.last {
                break;
            }
        }
    }
    fixes
}

/// The failure after an element of a list that [`list_fixes`] reads.
struct After<'c, 'a> {
    c: &'c Cursor<'a>,
    list: Option<NodeKind>,
    /// The last token of the element.
    prev: usize,
    /// The token of the failure, `c.at`.
    kind: TokenKind,
    /// The list is the arms of a `match`.
    arms: bool,
    /// The token is an opener that a gap keeps from the token before, and
    /// that reads as the postfix with the gap taken out ([`super::Detached::joins`]).
    joins: bool,
}

/// A case of the candidates of [`list_fixes`]: when it holds, the
/// candidates it makes, and whether the cases after it are read then.
struct Case {
    holds: fn(&After) -> bool,
    makes: fn(&After) -> Option<Fix>,
    last: bool,
}

/// The cases of [`list_fixes`], in the order of the decisions and of their
/// candidates.
const CASES: [Case; 4] = [
    Case { holds: arm_sign, makes: sign_comma, last: true },
    Case { holds: comma_goes, makes: comma_fix, last: false },
    Case { holds: two_strings, makes: one_string, last: true },
    Case { holds: rejoins, makes: joined, last: true },
];

/// A `-`, `|` or `+` that starts the next arm of a `match` (S-386).
fn arm_sign(a: &After) -> bool {
    a.arms && matches!(a.kind, TokenKind::Minus | TokenKind::Pipe | TokenKind::Plus) && arm_ahead(a.c.tokens, a.c.at)
}

/// The `,` before the sign; none before a `-` with a blank after it,
/// which is an error of its own.
fn sign_comma(a: &After) -> Option<Fix> {
    let spaced = a.kind == TokenKind::Minus && a.c.gap_after(a.c.at).is_some();
    (!spaced).then(|| comma_before_sign(a.c, a.prev, a.c.at))
}

/// Whether a `,` goes before the token (S-384, S-387): it starts an
/// element of the list, and is not `fn name`, which no expression is;
/// in a list of types, a `[` holds a `;` (S-419); not in the repetition
/// of an array; in the arms, not before an opener after a gap when no `=>`
/// follows (the gap taken out is then the one candidate, when it reads,
/// §2.5: `0 => t.0 (x), _ => 1` has none).
fn comma_goes(a: &After) -> bool {
    let c = a.c;
    let declaration = declares_a_function(a.kind, c.kind(c.sig_after(c.at)));
    let types = matches!(a.list, Some(NodeKind::VariantFields | NodeKind::TupleType | NodeKind::FnTypeParams));
    let array =
        (a.kind != TokenKind::LBracket || !types || bracket_contents(c.tokens, c.at).is_some_and(|(_, _, semi)| semi))
            && !(a.list == Some(NodeKind::ArrayExpr) && array_repeats(c));
    let gap = c.detached.is_some_and(|d| d.at == c.at);
    let comma = !(a.arms && gap && !arm_ahead(c.tokens, c.at));
    a.list.is_some_and(|l| starts_element(l, a.kind)) && !declaration && array && comma
}

fn comma_fix(a: &After) -> Option<Fix> {
    let edit = Edit::insert(a.c.file, a.c.span(a.prev).end, ",");
    Some(Fix::new("write the `,` between the elements", vec![edit]))
}

/// Two string literals next to each other in a list (S-388).
fn two_strings(a: &After) -> bool {
    a.kind == TokenKind::Str && a.c.kind(a.prev) == TokenKind::Str && a.list.is_some()
}

fn one_string(a: &After) -> Option<Fix> {
    merge_strings(a.c, a.prev)
}

/// An opener after a gap that reads joined (S-89, S-373, S-399); in the
/// arms, none that a `=>` follows.
fn rejoins(a: &After) -> bool {
    a.joins && !(a.arms && arm_ahead(a.c.tokens, a.c.at))
}

fn joined(a: &After) -> Option<Fix> {
    join_fix(a.c)
}

/// The two string literals `prev` and `c.at` as one (S-388): the text of the
/// second goes before the closing `"` of the first, and the token of the
/// second goes; the other tokens and the comments stay on their lines (as
/// S-216 moves code). Only two literals that close on their line
/// ([`crate::literal::Literals::closed`]), also with an error in them, which
/// stays the lexer's E0001 in the one literal (S-438): a literal that does
/// not close has no end to join.
fn merge_strings(c: &Cursor, prev: usize) -> Option<Fix> {
    if !(c.literals.closed(c.span(prev)) && c.literals.closed(c.span(c.at))) {
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
