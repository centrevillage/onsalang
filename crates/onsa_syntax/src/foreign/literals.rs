//! The rows of the literals of other languages: the numbers (a suffix,
//! `0o17`, `017`, `1.`, `1.e3`, `.5`) and the strings with a delimiter of
//! other languages (`$"…"`, `"""…"""`; §2.4, §18.1).

use super::*;
use crate::literal::{Base, Form, Number, Point, int_value, point_after_int};

/// The rows [`foreign_literal`] names ([`super::Matcher::many`]).
pub(super) const FOREIGN_LITERAL_ROWS: &[RowId] =
    &[RowId::FloatTrailingDot, RowId::FloatDotExponent, RowId::OctalPrefix, RowId::LeadingZero, RowId::LiteralSuffix];

/// A number written as in other languages (the token `ForeignLit`): the row
/// of the form the lexer found ([`crate::literal::number`]), and its
/// candidates, which keep the value and whether it is an integer or a float
/// (§18.1). Where no literal goes (a declaration), the place is an error of
/// its own (S-281: the driver reports the E0002 there).
pub(super) fn foreign_literal(c: &Cursor) -> Option<(RowId, Hit)> {
    if c.kind(c.at) != TokenKind::ForeignLit {
        return None;
    }
    let span = c.span(c.at);
    let text = c.src(c.at);
    let n = number_at(c, c.at);
    // In a pattern a float is a float pattern, one form with it (S-248): no
    // form of its own, whatever the float pattern's row finds (a decided
    // reading, outside the order of the diagnostics of S-281, which would
    // choose the suffix). A bound of a range is no float pattern
    // ([`bounds_range`]).
    if c.want == Want::Pattern && !bounds_range(c, c.at) && float_spelling(text, &n).is_some() {
        return None;
    }
    let (row, titles): (RowId, &[&str]) = match n.form {
        Form::Suffix => (RowId::LiteralSuffix, &["remove the type suffix"]),
        Form::Octal => (RowId::OctalPrefix, &["write the number in decimal"]),
        Form::LeadingZero => (RowId::LeadingZero, &["read it as decimal", "read it as octal"]),
        Form::TrailingDot => (RowId::FloatTrailingDot, &["add the `0` after the point"]),
        Form::DotExponent => (RowId::FloatDotExponent, &["add the `0` after the point"]),
        Form::Int | Form::Float | Form::Invalid(_) => {
            onsa_diag::internal::bug(Some(span), "a `ForeignLit` of no form of other languages")
        }
    };
    // A decimal integer written in the place of the token reads with a `.`
    // after it when the `.` would read as the point of a float (`1u8.5`
    // would be `1.5`, `1u8.)` would be `1.)`), S-302: no such candidate.
    // `0u32..n`, `1u8.abs()` and `1i32.(x)` read the same (S-350).
    let rest = &c.text[span.end as usize..];
    let joins = |s: &str| {
        rest.starts_with('.')
            && s.bytes().all(|b| b.is_ascii_digit() || b == b'_')
            && !matches!(point_after_int(rest), Point::Range | Point::Member)
    };
    // A number called (`017(2)`) is a callee too, the row
    // `callee_expression` at the same failure ([`called_number`]): the
    // number's row comes first (S-281) and its candidate leaves the callee's
    // E0020, a second error (S-457).
    let fixes = spellings(text, &n)
        .into_iter()
        .zip(titles)
        .filter(|(s, _)| !joins(s))
        .map(|(s, title)| Fix::replace(*title, span, s))
        .collect();
    Some((row, Hit::new(span, fixes).misplaced_if(!matches!(c.want, Want::Expr | Want::Pattern))))
}

/// A tuple index with a leading `0` (`t.01`, `t.00`; §2.4, S-508), where the
/// parser failed at it ([`Want::TupleIndex`]): the one candidate takes the
/// leading `0`s out (no language reads a tuple index as octal).
pub(super) fn tuple_index_zero(c: &Cursor) -> Option<Hit> {
    if c.want != Want::TupleIndex {
        return None;
    }
    let digits = crate::literal::tuple_index_unpadded(c.src(c.at))?;
    hit(c.span(c.at), vec![Fix::replace("remove the leading zero", c.span(c.at), digits)])
}

/// The parts of the number written as in other languages at token `i` (a
/// `ForeignLit`), as the lexer read them.
fn number_at(c: &Cursor, i: usize) -> Number {
    let span = c.span(i);
    *c.literals
        .number(span)
        .unwrap_or_else(|| onsa_diag::internal::bug(Some(span), "a `ForeignLit` the lexer did not read"))
}

/// The Onsa spellings of the number `text` written as in other languages
/// (§2.4, §18.1), the candidates of its row in their order: the value and
/// whether it is an integer or a float stay. The suffix goes with the `_`
/// before it, and a float suffix on an integer adds `.0` (`1f32` is `1.0`;
/// a hexadecimal or binary one has none, S-456);
/// `0o17` is `15`; `017` is `17` and `15` (one when the readings agree or
/// it is no octal number: `00` is `0`, `09` is `9`, S-63); `1.` is `1.0`
/// and `1.e3` is `1.0e3`.
pub(super) fn spellings(text: &str, n: &Number) -> Vec<String> {
    let body = &text[..n.body];
    match n.form {
        // SPEC-GAP(S-456): a float suffix on a hexadecimal, binary or octal integer (`0b11f32`) has no candidate.
        // A float whose body is written as an integer.
        Form::Suffix if n.is_float() && !n.float => match n.base {
            Base::Dec => vec![format!("{body}.0")],
            _ => Vec::new(),
        },
        Form::Suffix => vec![body.to_string()],
        Form::Octal => int_value(body).map(|v| v.to_string()).into_iter().collect(),
        Form::LeadingZero => {
            let decimal = body.trim_start_matches(['0', '_']);
            let mut out = vec![if decimal.is_empty() { "0".to_string() } else { decimal.to_string() }];
            // As `0o…` reads (a digit 8 or 9 makes no octal number).
            if let Some(v) = int_value(&format!("0o{body}"))
                && Some(v) != int_value(body)
            {
                out.push(v.to_string());
            }
            out
        }
        Form::TrailingDot => vec![format!("{text}0")],
        Form::DotExponent => {
            let (int, after) = text.split_once('.').unwrap_or((text, ""));
            vec![format!("{int}.0{after}")]
        }
        Form::Int | Form::Float | Form::Invalid(_) => Vec::new(),
    }
}

/// The Onsa spelling of a number written as in other languages that is a
/// float in Onsa (§2.4): `1.` is `1.0`, `1.e3` is `1.0e3`, `0.5f32` is
/// `0.5`, `1f32` is `1.0`; `None` for an integer (`1u8`, `0o17`, `017`).
pub(super) fn float_spelling(text: &str, n: &Number) -> Option<String> {
    if !n.is_float() {
        return None;
    }
    spellings(text, n).into_iter().next()
}

/// [`float_spelling`] of the token `i`, a `ForeignLit`.
pub(super) fn float_spelling_at(c: &Cursor, i: usize) -> Option<String> {
    float_spelling(c.src(i), &number_at(c, i))
}

/// Whether a range symbol follows the literal that ends at token `last`
/// (`1f32..<3`, `.5..<3`): in a pattern the literal is a bound of a range
/// pattern then, not a float pattern of its own (S-248), and its form is
/// the error, which ends before the range does (S-281, R-206).
fn bounds_range(c: &Cursor, last: usize) -> bool {
    c.tokens.get(last + 1).is_some_and(|t| !t.kind.range_readings().is_empty())
}

/// `.5`: `0.5` (§2.4). The form is what the number with its `0` reads
/// ([`crate::literal::number`]): `.5E3` and `.2_5` are one number with the
/// `0` (`0.5E3`, `0.2_5`), though the `E3` and `_5` after a `.` read as
/// names, so the candidate takes them in (S-302).
pub(super) fn leading_point(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Dot
        || c.kind(c.at + 1) != TokenKind::Int
        || c.gap_after(c.at).is_some()
        || !(c.want == Want::Expr || (c.want == Want::Pattern && bounds_range(c, c.at + 1)))
    {
        return None;
    }
    let start = c.span(c.at).start as usize;
    let line = c.text[start..].lines().next().unwrap_or_default();
    let number = crate::literal::number(&format!("0{line}"));
    let span = c.file_span(start as u32, (start + number.len - 1) as u32);
    let text = format!("0{}", &c.text[span.start as usize..span.end as usize]);
    hit(span, vec![Fix::replace("add the `0` before the point", span, text)])
}

/// The `(` right after a number of the rows above where the parser failed at
/// it in an expression (`017(2)`, `1u8(2)`, `.5(2)`): the number is a callee
/// that is no path too (§6.1), which the row `callee_expression` reports at
/// the same failure (S-457). The one test of a number called.
pub(super) fn called_number(c: &Cursor) -> Option<usize> {
    let last = match c.kind(c.at) {
        TokenKind::ForeignLit => c.at,
        TokenKind::Dot if c.kind(c.at + 1) == TokenKind::Int && c.gap_after(c.at) == Gap::None => c.at + 1,
        _ => return None,
    };
    let paren = last + 1;
    (c.want == Want::Expr && c.kind(paren) == TokenKind::LParen && c.gap(paren) == Gap::None).then_some(paren)
}

/// A string written with a delimiter of other languages (the token
/// `ForeignStr`, §2.4, S-406): E0002 with the note and no candidate, which
/// would have to guess a plain, an interpolated or a raw string. The range is
/// the lexer's ([`crate::literal::Literals::foreign_string`]). The place
/// does not matter: the form is the lexer's.
pub(super) fn string_delimiter(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ForeignStr {
        return None;
    }
    let span = c.span(c.at);
    let range = c
        .literals
        .foreign_string(span)
        .unwrap_or_else(|| onsa_diag::internal::bug(Some(span), "a `ForeignStr` the lexer did not read"));
    hit(range, Vec::new())
}
