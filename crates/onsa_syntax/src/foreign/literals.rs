//! The rows of the number literals of other languages (a suffix, `1.`, `.5`;
//! §2.4).

use super::*;
use crate::literal::{is_integer, split_suffix};

/// `1.` (a digit after the point is needed) and `1u8` (no type suffix, §2.4).
/// Where no literal goes (a declaration), the place is an error of its own
/// (S-281: the driver reports the E0002 there).
pub(super) fn foreign_literal(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ForeignLit {
        return None;
    }
    let span = c.span(c.at);
    let text = c.src(c.at);
    // In a pattern a float is a float pattern, one form with it (S-248).
    if c.want == Want::Pattern && float_spelling(text).is_some() {
        return None;
    }
    // What the text after the token starts with: a number written in its
    // place must stay a token of its own (S-302).
    let next = c.text.as_bytes().get(span.end as usize).copied();
    let fixes = if let Some(number) = text.strip_suffix('.') {
        debug_assert!(number.bytes().all(|b| b.is_ascii_digit() || b == b'_'), "{number}");
        c.say(RowId::FloatTrailingDot);
        // The token is replaced whole: a `0` inserted after it would change
        // the reading of a token outside the edit (S-302).
        vec![Fix::replace("add the `0` after the point", span, format!("{text}0"))]
    } else {
        c.say(RowId::LiteralSuffix);
        // The `_` before the suffix goes with it (`1_u8` is `1`).
        let number = split_suffix(text).0.trim_end_matches('_');
        // An integer before a `.` reads with it when a digit follows the `.`
        // (`1d.5` would be `1.5`) or neither a name nor a `.` (`1d.` would be
        // `1.`); `0u32..n` and `1u8.abs()` read the same.
        let after_dot = c.text.as_bytes().get(span.end as usize + 1).copied();
        let joins = next == Some(b'.')
            && is_integer(number)
            && !after_dot.is_some_and(|b| b == b'.' || b.is_ascii_alphabetic() || b == b'_');
        if joins { Vec::new() } else { vec![Fix::replace("remove the type suffix", span, number)] }
    };
    // A literal right before a `(` would be a callee that is no path, an
    // error of the syntax stage at the same place (§6.1): no candidate.
    let fixes = if next == Some(b'(') { Vec::new() } else { fixes };
    Some(Hit { span, fixes, misplaced: !matches!(c.want, Want::Expr | Want::Pattern) })
}

/// The Onsa spelling of a float written as in other languages, in a
/// pattern (§2.4): `1.` is `1.0`, `0.5f32` is `0.5`, `1f32` is `1.0`, the
/// `_` before a suffix goes (`1.5_f32` is `1.5`); `None` for an integer with
/// an integer suffix (`1u8`).
pub(super) fn float_spelling(text: &str) -> Option<String> {
    if let Some(n) = text.strip_suffix('.') {
        return Some(format!("{n}.0"));
    }
    let (number, suffix) = split_suffix(text);
    let number = number.trim_end_matches('_');
    if !is_integer(number) {
        return Some(number.to_string());
    }
    suffix.trim_start_matches('_').starts_with(['f', 'F']).then(|| format!("{number}.0"))
}

/// `.5`: `0.5` (§2.4).
pub(super) fn leading_point(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr
        || c.kind(c.at) != TokenKind::Dot
        || c.kind(c.at + 1) != TokenKind::Int
        || c.gap_after(c.at).is_some()
    {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(c.at + 1).end);
    // A literal right before a `(` would be a callee that is no path (§6.1).
    if c.kind(c.at + 2) == TokenKind::LParen && c.gap(c.at + 2) == Gap::None {
        return hit(span, Vec::new());
    }
    let text = format!("0{}", &c.text[span.start as usize..span.end as usize]);
    hit(span, vec![Fix::replace("add the `0` before the point", span, text)])
}
