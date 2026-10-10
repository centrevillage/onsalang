//! The rows of the blanks inside a line (§2.5, W3-06): a blank before a
//! postfix opener (S-89, S-123, S-399), around the member `.` (S-203), and a
//! name written right against a string literal (S-400).

use onsa_diag::{Edit, Fix};

use super::{Cursor, Hit, RowId, Want, closed_expr, closing, hit};
use crate::cst::NodeKind;
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
    let mark = matches!(row, RowId::SpaceBeforeBang | RowId::SpaceBeforeTilde);
    if mark && c.gap_after(c.at).is_some() {
        // A gap between the mark and its `(` (S-412): the one candidate takes
        // both gaps out (`saw ~ (f0)` is one form).
        let paren = c.tokens.iter().enumerate().skip(c.at + 1).find(|(_, t)| !t.kind.is_trivia()).map(|(k, _)| k)?;
        let after =
            crate::layout::move_up(c.file, c.text, c.all, "remove the space", c.span(c.at).end, c.tokens[paren], "");
        match c.gap(c.at) {
            Gap::None => fixes.push(after),
            Gap::Space => {
                let mut edits = vec![Edit::delete(c.space_before(c.at)?)];
                edits.extend(after.edits().iter().cloned());
                fixes.push(Fix::new("remove the spaces", edits));
            }
            Gap::Newline => {}
        }
    } else if d.joins(c.tokens) {
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
    let (before, after) = (c.gap(c.at), c.gap_after(c.at));
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

/// A blank before a postfix `?` (`o ?`, S-203): `x ?` reads as the start of
/// the conditional operator of C. The candidate takes the blank out.
pub(super) fn space_before_question(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Question || c.gap(c.at) != Gap::Space {
        return None;
    }
    let prev = c.before(c.at)?;
    if !crate::layout::ends_operand(c.kind(prev)) {
        return None;
    }
    hit(c.span(c.at), vec![Fix::delete("remove the space", c.space_before(c.at)?)])
}

/// A blank after a prefix `-` / `!` (`- x`, `! done`, also of a negative
/// literal pattern `- 1`; S-123, S-411) or after the `^` of a name (`^ y`):
/// the candidate takes the blank out. A stack of prefix operators with
/// blanks is the E0012 of the stack (S-410), which the parser reads on.
pub(super) fn space_after_prefix(c: &Cursor) -> Option<Hit> {
    let kind = c.kind(c.at);
    // The parser judged the gap after a `-` / `!` (`Want::Prefix`); a `^`
    // with no name right after it fails where an expression goes.
    let want = if kind == TokenKind::Caret { Want::Expr } else { Want::Prefix };
    if !matches!(kind, TokenKind::Minus | TokenKind::Bang | TokenKind::Caret)
        || c.want != want
        || c.gap_after(c.at) != Gap::Space
    {
        return None;
    }
    let next = c.kind(c.at + 1);
    let mut fixes = vec![Fix::delete("remove the space", c.space_after(c.at)?)];
    if kind == TokenKind::Caret {
        if next != TokenKind::Ident {
            return None;
        }
        c.say(RowId::SpaceAfterCaret);
        // A line that starts with `^ b` goes on the line before as the binary
        // `^` too (S-123). The `- b` of `leading_minus` is W3-06's unit 2.
        if c.gap(c.at) == Gap::Newline
            && let Some(prev) = c.sig_before(c.at).filter(|&p| crate::layout::ends_operand(c.kind(p)))
        {
            let title = "join it to the line before";
            fixes.push(crate::layout::move_up(c.file, c.text, c.all, title, c.span(prev).end, c.tokens[c.at], " "));
        }
    } else if !crate::parser::starts_operand(next) {
        return None;
    }
    hit(c.span(c.at), fixes)
}

/// A binary `-` / `^` with a blank before it and its operand touching it
/// (`a -b`, `[1 -1]`, `two(a -b, 1)`, `[a ^b]`; S-398): it reads as the prefix
/// of a next element too. The candidates are the blanks on both sides, and,
/// in a list whose elements are expressions (arguments, an array, a tuple),
/// the `,` before it (S-370's order). `a - -b` has blanks on both sides and
/// is no such form.
pub(super) fn asymmetric_binary_space(c: &Cursor) -> Option<Hit> {
    if !matches!(c.kind(c.at), TokenKind::Minus | TokenKind::Caret)
        || c.gap(c.at) != Gap::Space
        || c.gap_after(c.at) != Gap::None
        || !crate::parser::starts_operand(c.kind(c.at + 1))
        || closed_expr(c).is_none()
    {
        return None;
    }
    let prev = c.before(c.at)?;
    let mut fixes = vec![Fix::insert("write blanks on both sides", c.file, c.span(c.at).end, " ")];
    if matches!(c.want, Want::Separator(NodeKind::ArgList | NodeKind::ArrayExpr | NodeKind::TupleExpr)) {
        fixes.push(Fix::insert("write the `,` between the elements", c.file, c.span(prev).end, ","));
    }
    hit(c.span(c.at), fixes)
}
