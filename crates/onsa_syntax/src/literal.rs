//! The literal tokens (§2.4) after the lexer: their values (one function
//! each, for the parser's checks and the lowering), the parts of a number
//! written as in other languages (`1u8`, the token `ForeignLit`), and the
//! facts the lexer found in them ([`Literals`]: their holes, its errors in
//! them), which the parser and the table of the forms of other languages
//! read alike (D-15).

use onsa_diag::{Diagnostic, Span};

use crate::ast::{Ident, Path, StrLit, StrSeg};

/// The facts of the string and character literals that the lexer read: the
/// holes of the strings (`{x}`, also of a form an interpolation may not
/// have, `{X}`, from the `{` to after the `}`; the parser tells an
/// interpolation in the name of a `test` by them, §11.8, S-244) and the
/// spans of the lexer's errors, each in the order of the file.
#[derive(Debug, Clone, Default)]
pub(crate) struct Literals {
    holes: Vec<Span>,
    errors: Vec<Span>,
}

impl Literals {
    /// The facts of the holes `holes` (in the order of the file) and of the
    /// lexer's diagnostics `diagnostics`.
    pub(crate) fn new(holes: Vec<Span>, diagnostics: &[Diagnostic]) -> Literals {
        let mut errors: Vec<Span> = diagnostics.iter().map(|d| d.span).collect();
        errors.sort_by_key(|s| s.start);
        Literals { holes, errors }
    }

    /// The facts of the literals between `from` and `to`, for a run of tokens
    /// read on its own (`parser::reads_as_expr`): its holes and the errors of
    /// the lexer in it, so that a literal reads there as it does in the file.
    pub(crate) fn within(&self, from: u32, to: u32) -> Literals {
        Literals { holes: inside(&self.holes, from, to), errors: inside(&self.errors, from, to) }
    }

    /// Every hole, in the order of the file.
    pub(crate) fn holes(&self) -> &[Span] {
        &self.holes
    }

    /// The holes inside `span` (a literal), found by a binary search.
    pub(crate) fn holes_in(&self, span: Span) -> &[Span] {
        let first = self.holes.partition_point(|h| h.start < span.start);
        let n = self.holes[first..].iter().take_while(|h| h.end <= span.end).count();
        &self.holes[first..first + n]
    }

    /// Whether the literal at `span` is one the lexer read with no error in
    /// it (closed, with valid escapes and holes, one scalar in a character).
    pub(crate) fn ok(&self, span: Span) -> bool {
        let from = self.errors.partition_point(|l| l.start < span.start);
        !self.errors[from..].iter().take_while(|l| l.start < span.end).any(|l| l.end <= span.end)
    }

    /// Whether the string literal at `span` interpolates (§2.4, §7, S-225):
    /// it has a hole, and the lexer finds no error in it (a hole of another
    /// form, `{}`, `{a + b}`, is the lexer's E0001, which a guard that copies
    /// the literal would keep).
    pub(crate) fn interpolated(&self, span: Span) -> bool {
        !self.holes_in(span).is_empty() && self.ok(span)
    }
}

/// The spans of `spans` (ordered by their start) that lie between `from`
/// and `to`, found by a binary search.
fn inside(spans: &[Span], from: u32, to: u32) -> Vec<Span> {
    let first = spans.partition_point(|s| s.start < from);
    let last = spans.partition_point(|s| s.start <= to);
    spans[first..last].iter().copied().filter(|s| s.end <= to).collect()
}

/// Whether a number may carry `suffix` as a type suffix of another
/// language (§2.4, §18.1): the lexer reads such a number as one token
/// (`ForeignLit`), whose row the table of the forms of other languages
/// finds. Every suffix until W3-05 closes the list here (the others are
/// E0001 then).
pub(crate) fn is_type_suffix(_suffix: &str) -> bool {
    true
}

/// The number and the suffix of a `ForeignLit` written with a suffix
/// (`1u8`: `1` and `u8`), as the lexer reads them.
pub(crate) fn split_suffix(text: &str) -> (&str, &str) {
    let b = text.as_bytes();
    let mut i = 0;
    let digits = |i: &mut usize, ok: &dyn Fn(u8) -> bool| {
        while *i < b.len() && ok(b[*i]) {
            *i += 1;
        }
    };
    if b.len() > 1 && b[0] == b'0' && matches!(b[1], b'x' | b'b') {
        let hex = b[1] == b'x';
        i = 2;
        if hex {
            digits(&mut i, &|x: u8| x.is_ascii_hexdigit() || x == b'_');
        } else {
            digits(&mut i, &|x: u8| matches!(x, b'0' | b'1' | b'_'));
        }
    } else {
        digits(&mut i, &|x: u8| x.is_ascii_digit() || x == b'_');
        if i + 1 < b.len() && b[i] == b'.' && b[i + 1].is_ascii_digit() {
            i += 1;
            digits(&mut i, &|x: u8| x.is_ascii_digit() || x == b'_');
        }
        if i < b.len() && matches!(b[i], b'e' | b'E') {
            let mut j = i + 1;
            if j < b.len() && matches!(b[j], b'+' | b'-') {
                j += 1;
            }
            let start = j;
            digits(&mut j, &|x: u8| x.is_ascii_digit());
            if j > start {
                i = j;
            }
        }
    }
    text.split_at(i)
}

/// Whether the number `number` (no suffix) is written as an integer.
pub(crate) fn is_integer(number: &str) -> bool {
    let hex = number.starts_with("0x") || number.starts_with("0b");
    hex || !number.contains(['.', 'e', 'E'])
}

/// The number part of a number written as in other languages (`1u8`: `1`).
pub(crate) fn number_part(text: &str) -> &str {
    split_suffix(text).0
}

/// The value of an integer literal (`1_000`, `0xFF`, `0b1010`), or `None`
/// when it is larger than `u64::MAX` (E0408).
pub(crate) fn int_value(text: &str) -> Option<u64> {
    let digits: String = text.chars().filter(|&c| c != '_').collect();
    let parsed = if let Some(h) = digits.strip_prefix("0x") {
        u64::from_str_radix(h, 16)
    } else if let Some(b) = digits.strip_prefix("0b") {
        u64::from_str_radix(b, 2)
    } else {
        digits.parse::<u64>()
    };
    parsed.ok()
}

/// The value of a tuple index (`t.0`), or `None` when it is too large (E0408).
pub(crate) fn tuple_index_value(text: &str) -> Option<u32> {
    text.parse::<u32>().ok()
}

/// The character of a char literal (`'a'`, `'\n'`).
pub(crate) fn char_value(text: &str) -> char {
    let inner = &text[1..];
    let inner = inner.strip_suffix('\'').unwrap_or(inner);
    let mut chars = inner.chars();
    match chars.next() {
        Some('\\') => unescape(&mut chars).unwrap_or('\u{FFFD}'),
        Some(c) => c,
        None => '\u{FFFD}',
    }
}

/// A string literal with its interpolations split out (§2.4). The parser
/// counts the levels of the holes with it (spec §2.5).
pub(crate) fn str_lit(raw: &str, span: Span) -> StrLit {
    let inner = raw.strip_prefix('"').unwrap_or(raw);
    let inner = inner.strip_suffix('"').unwrap_or(inner);
    let base = span.start + 1;
    let mut segments = Vec::new();
    let mut text = String::new();
    let mut chars = inner.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' => {
                let mut rest = inner[i + 1..].chars();
                if let Some(ch) = unescape(&mut rest) {
                    text.push(ch);
                    let consumed = inner[i + 1..].len() - rest.as_str().len();
                    for _ in inner[i + 1..i + 1 + consumed].chars() {
                        chars.next();
                    }
                }
            }
            '{' if chars.peek().is_some_and(|&(_, n)| n == '{') => {
                chars.next();
                text.push('{');
            }
            '}' if chars.peek().is_some_and(|&(_, n)| n == '}') => {
                chars.next();
                text.push('}');
            }
            '{' => {
                if !text.is_empty() {
                    segments.push(StrSeg::Text(std::mem::take(&mut text)));
                }
                let path_start = i + 1;
                let mut path_end = path_start;
                for (j, n) in chars.by_ref() {
                    if n == '}' {
                        path_end = j;
                        break;
                    }
                }
                let path_text = &inner[path_start..path_end];
                let mut offset = base + path_start as u32;
                let mut seg_spans = Vec::new();
                for seg in path_text.split('.') {
                    let span = Span::new(span.file, offset, offset + seg.len() as u32);
                    seg_spans.push(Ident { name: seg.to_string(), span });
                    offset += seg.len() as u32 + 1;
                }
                let pspan = Span::new(span.file, base + path_start as u32, base + path_end as u32);
                segments.push(StrSeg::Interp(Path { segments: seg_spans, span: pspan }));
            }
            _ => text.push(c),
        }
    }
    if !text.is_empty() || segments.is_empty() {
        segments.push(StrSeg::Text(text));
    }
    StrLit { segments, span }
}

/// `\n` etc. after the backslash has been consumed (S-19).
fn unescape(chars: &mut std::str::Chars) -> Option<char> {
    match chars.next()? {
        'n' => Some('\n'),
        't' => Some('\t'),
        'r' => Some('\r'),
        '0' => Some('\0'),
        '\\' => Some('\\'),
        '"' => Some('"'),
        '\'' => Some('\''),
        'u' => {
            let rest = chars.as_str();
            let rest = rest.strip_prefix('{')?;
            let end = rest.find('}')?;
            let ch = u32::from_str_radix(&rest[..end], 16).ok().and_then(char::from_u32)?;
            for _ in 0..end + 2 {
                chars.next();
            }
            Some(ch)
        }
        _ => None,
    }
}
