//! The rows of the line breaks where a symbol touches its partner (§2.5,
//! W3-06): after a member `.` (S-353), after a prefix `-` / `!` / `^` and
//! before a postfix `?` (S-369). The candidate moves the symbol to its
//! partner's line ([`super::edits::move_token_down`],
//! [`super::edits::move_token_up`]). And the symbols at the head of a line
//! that go at the end of the line before (S-124, S-370, S-374, S-380), the
//! `|` and `||` of a pattern out of their place (S-383, S-389), and the
//! prefix `+` that Onsa has not (S-405).

use super::edits::move_up;
use super::edits::{move_token_down, move_token_up};
use super::lists::comma_before_sign;
use super::*;
use crate::scan::arm_ahead;
use crate::starts::ends_operand;

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
    let operand = if kind == TokenKind::Caret { next == TokenKind::Ident } else { crate::starts::starts_operand(next) };
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
    if c.kind(c.at) != TokenKind::Question || !c.at_line_head(c.at) {
        return None;
    }
    let operand = c.sig_before(c.at).is_some_and(|p| ends_operand(c.kind(p)));
    if !operand {
        return None;
    }
    hit(c.span(c.at), move_token_up(c, "write it against its operand", c.at).into_iter().collect())
}

/// Whether the failure is inside a pattern: where one starts, after one
/// that closed there, or in a list of patterns.
fn in_pattern(c: &Cursor) -> bool {
    use crate::cst::Class;
    // The innermost node that closed there and is an expression, a type or a
    // pattern (a name's path inside a pattern is none of them: `Red`).
    let innermost = c.closed.iter().find(|n| n.0.class() != Class::Other);
    c.want == Want::Pattern
        || innermost.is_some_and(|n| n.0.class() == Class::Pat)
        || matches!(c.want, Want::Separator(NodeKind::TuplePat | NodeKind::TupleStructPat | NodeKind::StructPat))
}

/// A symbol at the head of a line that goes at the end of the line before
/// (§2.5): an operator only binary (`leading_operator`, S-124, S-370), the
/// `|` of a pattern choice (S-380), the `->` of a result and the `=` of a
/// binding or a definition (S-374), or a `-` / `^` that is a prefix too
/// (`leading_minus`). The candidate moves the symbol to the end of the code
/// of the line before, before its comment (S-216); a `- b` with a blank
/// joins the line instead (its blank is an error of its own, so the symbol
/// alone would not do). In a list whose elements are expressions, a `-`,
/// `^` or `+` touching its operand may start the next element too: the `,`
/// is the second candidate ([`comma_before_sign`], S-370, S-405). In the
/// arms of a `match`, a symbol that a `=>` follows starts the next arm
/// (S-386): the missing `,` of the list.
pub(super) fn leading_symbol(c: &Cursor) -> Option<(RowId, Hit)> {
    use TokenKind::*;
    let (s, prev) = leading(c)?;
    let sign = matches!(c.kind(s), Minus | Caret);
    let fixes = match c.gap_after(s) {
        Gap::Newline if sign => return None,
        Gap::Space if sign => {
            let title = "join it to the line before";
            vec![move_up(c.file, c.text, c.all, title, c.span(prev).end, c.tokens[s], " ")]
        }
        gap => moved_to_the_line_before(c, s, prev, gap),
    };
    found(if sign { RowId::LeadingMinus } else { RowId::LeadingOperator }, c.span(s), fixes)
}

/// The candidates of a symbol `s` at the head of a line that moves to the end
/// of the line before (after `prev`), and in a list whose elements are
/// expressions, of a `-`, `^` or `+` touching its operand, the `,` before it
/// (S-370, S-405).
fn moved_to_the_line_before(c: &Cursor, s: usize, prev: usize, gap: Gap) -> Vec<Fix> {
    use TokenKind::*;
    let symbol = &c.text[c.span(s).start as usize..c.span(s).end as usize];
    let title = "move it to the end of the line before";
    let mut fixes: Vec<Fix> = super::edits::move_token_up_as(c, title, s, &format!(" {symbol}")).into_iter().collect();
    let list = super::lists::expression_list(c);
    let operand = gap == Gap::None && crate::starts::starts_operand(c.kind(s + 1));
    if list && operand && matches!(c.kind(s), Minus | Caret | Plus) {
        fixes.push(comma_before_sign(c, prev, s));
    }
    fixes
}

/// Whether the failure is at a symbol at the head of a line that goes on with
/// the line before ([`leading_symbol`]): the symbol and the code before it,
/// by the kind of the symbol ([`leading_arrow`], [`leading_eq`],
/// [`leading_binary`]). Not in a pattern (the rows of the patterns judge it),
/// nor a symbol that starts the next arm of a `match` (S-386, the missing
/// `,`), nor one that another touches (`+=`, `===`, `&*x`): what is left
/// would be wrong (S-236). A `&` or a `+` at the head of a line that this
/// finds is read as the binary one (W3-06, S-405): the reference's and the
/// prefix `+`'s rows ask it ([`super::modes::reference`], [`prefix_plus`]).
pub(super) fn leading(c: &Cursor) -> Option<(usize, usize)> {
    use TokenKind::*;
    let kind = c.kind(c.symbol_ahead());
    if !(matches!(kind, Arrow | Eq) || kind.binop().is_some()) {
        return None;
    }
    let (s, prev) = c.head_symbol_after_operand()?;
    let arm = c.want == Want::Separator(NodeKind::MatchArms) && arm_ahead(c.tokens, s);
    let touching = c.gap_after(s) == Gap::None && !crate::starts::starts_operand(c.kind(s + 1));
    if c.want == Want::Pattern || arm || touching {
        return None;
    }
    let fits = match kind {
        Arrow => leading_arrow(c),
        Eq => leading_eq(c, prev),
        _ => leading_binary(c, s),
    };
    fits.then_some((s, prev))
}

/// A `->` at the head of a line: the result of a head, with a body or
/// without (a member of a trait, an effect or an `extern`, a `target fn`;
/// S-374).
fn leading_arrow(c: &Cursor) -> bool {
    c.closed.iter().any(|n| matches!(n.0, NodeKind::ParamList | NodeKind::FnTypeParams))
}

/// A `=` at the head of a line (S-374): of a binding or a definition waiting
/// for it, after a statement after which it goes on to an assignment (not
/// one that has its `=` already: `x = 2` and `= 3` on the next line), or the
/// value of a constant of a trait.
fn leading_eq(c: &Cursor, prev: usize) -> bool {
    if c.kind(c.at) == TokenKind::Newline {
        return matches!(
            c.context(),
            Some((_, NodeKind::LetStmt | NodeKind::VarStmt | NodeKind::Const | NodeKind::TypeAlias))
        );
    }
    (c.want == Want::Expr && c.closed.is_empty() && c.end_at(prev).is_none())
        || (c.closed.iter().any(|n| n.0 == NodeKind::Const) && closed_expr(c).is_none())
}

/// A binary operator at the head of a line (S-124, S-370), or the `|` of a
/// pattern choice (S-380): after an operand that closed there, or at the
/// start of a statement after one (the line break read, nothing closed
/// since). A `- b` and a `^ b` where an expression goes are the prefix rows',
/// a `||` in a pattern is `pattern_double_vert`'s (S-389), and `&mut` is the
/// reference's ([`Cursor::ref_mut`]).
fn leading_binary(c: &Cursor, s: usize) -> bool {
    use TokenKind::*;
    let kind = c.kind(s);
    if matches!(kind, Minus | Caret) && matches!(c.want, Want::Prefix | Want::Expr) {
        return false;
    }
    if (kind == OrOr && in_pattern(c)) || (kind == Amp && c.ref_mut(s)) {
        return false;
    }
    if kind == Pipe && in_pattern(c) {
        return true;
    }
    closed_expr(c).is_some() || (c.kind(c.at) != Newline && c.closed.is_empty())
}

/// A `|` where a pattern starts (`| 0 | 1 =>`, `Some(| 0)`, `let | (a, b) = p`;
/// §7, S-383): the `|` goes between the alternatives only, and the
/// candidate takes it out with the blanks after it. When no pattern follows
/// (`| =>`), or what follows reads as more than a pattern (`| x > 0 =>`, an
/// operator in it), there is none (E0002).
pub(super) fn leading_vert(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Pattern || c.kind(c.at) != TokenKind::Pipe {
        return None;
    }
    let next = c.sig_after(c.at);
    let starts = c.kind(next) == TokenKind::Pipe || crate::starts::starts_element(NodeKind::TuplePat, c.kind(next));
    let kinds = c.tokens[next..].iter().map(|t| t.kind).filter(|k| !k.is_trivia());
    let (n, _) = crate::scan::pattern_alternative(kinds.clone());
    let mut depth = 0u32;
    let operator = kinds.take(n).enumerate().any(|(k, kind)| {
        match kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth = depth.saturating_sub(1),
            _ => {}
        }
        depth == 0 && kind.binop().is_some() && !(k == 0 && kind == TokenKind::Minus)
    });
    if !starts || operator {
        return None;
    }
    let s = c.span(c.at);
    let end = c.space_after(c.at).map_or(s.end, |w| w.end);
    hit(s, vec![Fix::delete("take the `|` out", Span::new(c.file, s.start, end))])
}

/// A `||` in a pattern (`0 || 1 =>`, `|| 0 =>`, `Some(0 || 1)`; §7, S-389):
/// a pattern choice is one `|`, and the candidate writes it. Only when a
/// pattern follows that is no `|` (`0 ||| 1` would read `||` again).
pub(super) fn pattern_double_vert(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::OrOr || !in_pattern(c) {
        return None;
    }
    let next = c.kind(c.sig_after(c.at));
    if next == TokenKind::Pipe || !crate::starts::starts_element(NodeKind::TuplePat, next) {
        return None;
    }
    hit(c.span(c.at), vec![Fix::replace("write one `|`", c.span(c.at), "|")])
}

/// A prefix `+` (`let a = +1`, `[1, +1]`, `two(+x, 1)`, `+1 =>`, an argument of
/// an attribute; §3.1, S-405): Onsa has no prefix `+`, and the candidate
/// takes it out with the blanks after it. After a line break (`let y = +`
/// and `a` on the next line, S-425) the operand's line comes up to its place,
/// before the comment of the `+`'s line (S-216). A `+` at the head of a line
/// after an operand is read as the binary one, `leading_operator`'s
/// ([`leading`], S-405): no form of its own. The order of the diagnostics
/// would choose the same (S-281), by the order of the two messages (`a
/// line …` before `there …`: to be checked again when either changes), but
/// the reading is decided, and a second diagnostic that is never reported
/// costs its candidates at every such line (W3-06's long inputs). In a
/// pattern only before an integer.
pub(super) fn prefix_plus(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Plus || !matches!(c.want, Want::Expr | Want::Pattern) || leading(c).is_some() {
        return None;
    }
    let next = c.sig_after(c.at);
    let fits = if c.want == Want::Pattern {
        c.kind(next) == TokenKind::Int
    } else {
        crate::starts::starts_operand(c.kind(next))
    };
    if !fits {
        return None;
    }
    let s = c.span(c.at);
    let title = "take the `+` out";
    let fix = match c.gap_after(c.at) {
        Gap::Newline => {
            let up = move_up(c.file, c.text, c.all, title, s.end, c.tokens[next], "");
            let mut edits = vec![Edit::delete(s)];
            edits.extend(up.edits().iter().cloned());
            Fix::new(title, edits)
        }
        _ => Fix::delete(title, Span::new(c.file, s.start, c.space_after(c.at).map_or(s.end, |w| w.end))),
    };
    hit(s, vec![fix])
}
