//! The rows of the range symbols out of place (§7, S-257, S-278).

use super::*;

/// The range symbol at the failure (`..<`, `..=`, `..`, `...`) after an
/// expression on its line, outside a pattern (the range patterns are the
/// rows `range_pattern` and `range_pattern_choice`, [`guard`]): whether it is
/// in the head of a `for` or a `par`, where a range is the whole expression
/// (§3.1), or else none for a symbol in a head after a range
/// (`for i in 0..<4..5`: the general E0002, as no candidate makes it one).
fn range_symbol(c: &Cursor) -> Option<bool> {
    if c.kind(c.at).range_readings().is_empty() || c.want == Want::Pattern || c.before(c.at).is_none() {
        return None;
    }
    let pattern = |k: NodeKind| k.class() == crate::cst::Class::Pat;
    if c.closed.first().is_some_and(|n| pattern(n.0)) || c.top().is_some_and(pattern) {
        return None;
    }
    head(c)
}

/// Whether the expression that closed at the failure is the start of the
/// head of a `for` or a `par`, where a range is the whole expression (§3.1),
/// or else none for one in a head after a range.
fn head(c: &Cursor) -> Option<bool> {
    closed_expr(c)?;
    // The head: the expression that closed here starts right after `in`
    // (or `in move`) of the innermost open `for` or `par` (the context: the
    // block of the body may be open before its `{`).
    let outer = c.closed.iter().rev().find(|n| n.0.class() == crate::cst::Class::Expr)?;
    let head = matches!(c.context(), Some((_, NodeKind::ForStmt | NodeKind::ParExpr)))
        && c.sig_before(c.index_at(outer.1)).is_some_and(|i| matches!(c.kind(i), TokenKind::KwIn | TokenKind::KwMove));
    if head && outer.0 == NodeKind::RangeExpr {
        return None;
    }
    Some(head)
}

/// `a..b` and `a...b` in a head (S-257): whether the end is included is
/// read both ways across languages, so the two candidates edit the symbol
/// only (S-251), `..<` first. The end is a token that starts an operand
/// ([`crate::starts::starts_operand`]; an end that a later stage rejects is
/// the error of that stage, after the candidate) but `{`, which a head
/// reads as its body (S-338): a range with one end is another row
/// ([`range_header_one_sided`], S-278).
pub(super) fn range_dots(c: &Cursor) -> Option<Hit> {
    if !range_symbol(c)? || !c.kind(c.at).is_foreign_range() {
        return None;
    }
    // A symbol is never the last token (`Eof` is).
    let next = c.kind(c.at + 1);
    if !crate::starts::starts_operand(next) || next == TokenKind::LBrace {
        return None;
    }
    let span = c.span(c.at);
    let fixes = c
        .kind(c.at)
        .range_readings()
        .iter()
        .map(|end| {
            let label = match end {
                crate::ast::RangeEnd::Excluded => "exclude the end with `..<`",
                crate::ast::RangeEnd::Included => "include the end with `..=`",
            };
            Fix::replace(label, span, end.symbol())
        })
        .collect();
    hit(span, fixes)
}

/// A range with one end in the head of a `for` or a `par` (`for i in 0.. {`,
/// `for i in ..<n {`; §7, S-278): E0002 with the note, as nothing says what
/// the missing end is. A `{` after `..<` or `..=` is the parser's (S-338).
pub(super) fn range_header_one_sided(c: &Cursor) -> Option<Hit> {
    let kind = c.kind(c.at);
    if kind.range_readings().is_empty() || c.want == Want::Pattern {
        return None;
    }
    let in_head = matches!(c.context(), Some((_, NodeKind::ForStmt | NodeKind::ParExpr)));
    // No start: the symbol starts the head.
    let starts =
        in_head && c.sig_before(c.at).is_some_and(|i| matches!(c.kind(i), TokenKind::KwIn | TokenKind::KwMove));
    // No end: `..` or `...` before the body.
    let next = c.kind(c.sig_after(c.at));
    let ends = range_symbol(c) == Some(true)
        && kind.is_foreign_range()
        && (!crate::starts::starts_operand(next) || next == TokenKind::LBrace);
    if !starts && !ends {
        return None;
    }
    // The range as written: from the start of the head to the body's `{`.
    let mut first = c.at;
    while let Some(b) = c.sig_before(first).filter(|&b| !matches!(c.kind(b), TokenKind::KwIn | TokenKind::KwMove)) {
        first = b;
    }
    let mut last = c.at;
    while !matches!(c.kind(c.sig_after(last)), TokenKind::LBrace | TokenKind::Eof | TokenKind::Newline)
        && c.sig_after(last) != last
    {
        last = c.sig_after(last);
    }
    hit(c.file_span(c.span(first).start, c.span(last).end), Vec::new())
}

/// A range symbol at the head of a line after an operand (the token of the
/// failure, or the first of the line after a head that waits for its `{`,
/// [`Cursor::head_symbol_after_operand`]), and whether it goes on with the head of a
/// `for` or a `par` (§2.5, S-335): after a statement that ended, it does not.
fn line_range(c: &Cursor) -> Option<(usize, bool)> {
    let (s, _) = c.head_symbol_after_operand()?;
    if c.kind(s).range_readings().is_empty() || c.want == Want::Pattern {
        return None;
    }
    if c.closed.is_empty() {
        return Some((s, false));
    }
    Some((s, head(c)?))
}

/// A range symbol at the head of a line in the head of a `for` or a `par`
/// (`for i in 0` and `..<n {` on the next line; §2.5, S-335): it goes at the
/// end of the line, as a binary operator does, and the candidate moves it
/// there. `..` and `...` are written as `..<` and `..=` there, one candidate
/// each (S-257).
pub(super) fn leading_range(c: &Cursor) -> Option<Hit> {
    let (s, true) = line_range(c)? else { return None };
    let readings = c.kind(s).range_readings();
    let fixes = readings
        .iter()
        .filter_map(|end| {
            // The two readings of `..` and `...` say which end they write (as `range_dots`).
            let title = match end {
                _ if readings.len() == 1 => "move it to the end of the line before",
                crate::ast::RangeEnd::Excluded => "exclude the end with `..<` at the end of the line before",
                crate::ast::RangeEnd::Included => "include the end with `..=` at the end of the line before",
            };
            super::edits::move_token_up_as(c, title, s, &format!(" {}", end.symbol()))
        })
        .collect();
    hit(c.span(s), fixes)
}

/// A range after an expression outside the head of a `for` or a `par`
/// (`let r = 0..<4`, `xs[1..<3]`, `for i in (0..<4)`): E0002 with the note,
/// whatever its symbol (a candidate for `..` would leave the range where
/// none goes, §18.1).
pub(super) fn range_outside_header(c: &Cursor) -> Option<Hit> {
    let at = match range_symbol(c) {
        Some(head) => (!head).then_some(c.at),
        // A symbol at the head of a line after a statement (`let r = 0` and
        // `..<n`, S-335): moved up, the range would be outside a head.
        None => line_range(c).and_then(|(s, head)| (!head).then_some(s)),
    }?;
    hit(c.span(at), Vec::new())
}
