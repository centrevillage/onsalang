//! The rows of the line breaks where a symbol touches its partner (§2.5,
//! W3-06): after a member `.` (S-353), after a prefix `-` / `!` / `^` and
//! before a postfix `?` (S-369). The candidate moves the symbol to its
//! partner's line ([`crate::layout::move_token_down`],
//! [`crate::layout::move_token_up`]). And the symbols at the head of a line
//! that go at the end of the line before (S-124, S-370, S-374, S-380), the
//! `|` and `||` of a pattern out of their place (S-383, S-389), and the
//! prefix `+` that Onsa has not (S-405).

use super::*;
use crate::layout::{arm_ahead, comma_before_sign, ends_operand, line_head, move_token_down, move_token_up, move_up};

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
    let operand = if kind == TokenKind::Caret { next == TokenKind::Ident } else { crate::parser::starts_operand(next) };
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
    if c.kind(c.at) != TokenKind::Question || c.gap(c.at) != Gap::Newline {
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
    use crate::lower::{Class, class};
    // The innermost node that closed there and is an expression, a type or a
    // pattern (a name's path inside a pattern is none of them: `Red`).
    let innermost = c.closed.iter().find(|n| class(n.0) != Class::Other);
    c.want == Want::Pattern
        || innermost.is_some_and(|n| class(n.0) == Class::Pat)
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
pub(super) fn leading_symbol(c: &Cursor) -> Option<Hit> {
    use TokenKind::*;
    let (s, prev) = leading(c)?;
    let kind = c.kind(s);
    let sign = matches!(kind, Minus | Caret);
    let symbol = &c.text[c.span(s).start as usize..c.span(s).end as usize];
    let mut fixes = Vec::new();
    match c.gap_after(s) {
        Gap::Newline if sign => return None,
        Gap::Space if sign => {
            let title = "join it to the line before";
            fixes.push(move_up(c.file, c.text, c.all, title, c.span(prev).end, c.tokens[s], " "));
        }
        gap => {
            fixes.extend(crate::layout::move_token_up_as(
                c,
                "move it to the end of the line before",
                s,
                &format!(" {symbol}"),
            ));
            let list = crate::layout::expression_list(c);
            let operand = gap == Gap::None && crate::parser::starts_operand(c.kind(s + 1));
            if list && operand && matches!(kind, Minus | Caret | Plus) {
                fixes.push(comma_before_sign(c, prev, s));
            }
        }
    }
    c.say(if sign { RowId::LeadingMinus } else { RowId::LeadingOperator });
    hit(c.span(s), fixes)
}

/// Whether the failure is at a symbol at the head of a line that goes on with
/// the line before ([`leading_symbol`]): the symbol and the code before it.
/// The one judgement: the rows that a symbol at the head of a line could
/// also be (the references `&x` and `&mut x`, the prefix `+`) take it when
/// this does not. A symbol that another touches (`+=`, `===`, `&*x`,
/// `&mut x`) does not move: what is left would be wrong (S-236).
pub(super) fn leading(c: &Cursor) -> Option<(usize, usize)> {
    use TokenKind::*;
    let (s, prev) = line_head(c)?;
    let kind = c.kind(s);
    let sign = matches!(kind, Minus | Caret);
    let operator = crate::lower::binop(kind).is_some() || matches!(kind, Arrow | Eq);
    // The prefix rows judge a `- b` and a `^ b` where an expression goes.
    if !operator || (sign && matches!(c.want, Want::Prefix | Want::Expr)) || c.want == Want::Pattern {
        return None;
    }
    if (kind == OrOr && in_pattern(c)) || (c.want == Want::Separator(NodeKind::MatchArms) && arm_ahead(c, s)) {
        return None;
    }
    let touching = c.gap_after(s) == Gap::None && !crate::parser::starts_operand(c.kind(s + 1));
    if touching || (kind == Amp && c.is_ident(c.sig_after(s), "mut")) {
        return None;
    }
    let newline = c.kind(c.at) == Newline;
    let closed = |kinds: &[NodeKind]| c.closed.iter().any(|n| kinds.contains(&n.0));
    let fits = match kind {
        // The result of a head, with a body or without (a member of a trait,
        // an effect or an `extern`, a `target fn`).
        Arrow => closed(&[NodeKind::ParamList, NodeKind::FnTypeParams]),
        Eq if newline => matches!(
            c.context(),
            Some((_, NodeKind::LetStmt | NodeKind::VarStmt | NodeKind::Const | NodeKind::TypeAlias))
        ),
        // A statement after which a `=` goes on to an assignment, not one
        // that has its `=` already (`x = 2` and `= 3` on the next line); the
        // value of a constant of a trait.
        Eq => {
            (c.want == Want::Expr && c.closed.is_empty() && crate::layout::end_at(c, prev).is_none())
                || (closed(&[NodeKind::Const]) && closed_expr(c).is_none())
        }
        // After an operand that closed there, or at the start of a statement
        // after one (the line break read, nothing closed since).
        Pipe if in_pattern(c) => true,
        _ => closed_expr(c).is_some() || (!newline && c.closed.is_empty()),
    };
    fits.then_some((s, prev))
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
    let starts = c.kind(next) == TokenKind::Pipe || crate::layout::starts_element(NodeKind::TuplePat, c.kind(next));
    let kinds = c.tokens[next..].iter().map(|t| t.kind).filter(|k| !k.is_trivia());
    let (n, _) = crate::parser::pattern_alternative(kinds.clone());
    let mut depth = 0u32;
    let operator = kinds.take(n).enumerate().any(|(k, kind)| {
        match kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth = depth.saturating_sub(1),
            _ => {}
        }
        depth == 0 && crate::lower::binop(kind).is_some() && !(k == 0 && kind == TokenKind::Minus)
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
    if next == TokenKind::Pipe || !crate::layout::starts_element(NodeKind::TuplePat, next) {
        return None;
    }
    hit(c.span(c.at), vec![Fix::replace("write one `|`", c.span(c.at), "|")])
}

/// A prefix `+` (`let a = +1`, `[1, +1]`, `two(+x, 1)`, `+1 =>`, an argument of
/// an attribute; §3.1, S-405): Onsa has no prefix `+`, and the candidate
/// takes it out with the blanks after it. After a line break (`let y = +`
/// and `a` on the next line, S-425) the operand's line comes up to its place,
/// before the comment of the `+`'s line (S-216). A `+` at the head of a line
/// after an operand is `leading_operator`'s ([`leading`]). In a pattern only
/// before an integer.
pub(super) fn prefix_plus(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Plus || !matches!(c.want, Want::Expr | Want::Pattern) || leading(c).is_some() {
        return None;
    }
    let next = c.sig_after(c.at);
    let fits = if c.want == Want::Pattern {
        c.kind(next) == TokenKind::Int
    } else {
        crate::parser::starts_operand(c.kind(next))
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
