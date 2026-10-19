//! The kinds of characters of the text (§2.3, §2.5): the blanks, the
//! characters of a name and the line break. The lexer and the literals
//! ([`crate::literal`]) read them here.

/// The blanks (§2.5, S-201, S-441): the space and the tab. The one
/// definition, for the lexer, fmt, the table of the forms of other languages
/// and the `found` of a diagnostic (a range of blanks has none, §18.1).
pub const BLANKS: [char; 2] = [' ', '\t'];

/// Whether `c` is a blank ([`BLANKS`]).
pub fn is_blank(c: char) -> bool {
    BLANKS.contains(&c)
}

/// The length of the line break at the start of `rest`: 1 for a line feed,
/// 2 for a carriage return and a line feed, `None` for anything else (a
/// carriage return alone is no line break, §2.5). The one test of a line
/// break, for the lexer and the escapes ([`crate::literal::escape`]).
pub(crate) fn line_break(rest: &[u8]) -> Option<usize> {
    match rest {
        [b'\n', ..] => Some(1),
        [b'\r', b'\n', ..] => Some(2),
        _ => None,
    }
}

pub(crate) fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

pub(crate) fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}
