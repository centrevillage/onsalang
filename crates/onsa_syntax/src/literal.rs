//! The literal tokens (§2.4) after the lexer: their values (one function
//! each, for the parser's checks and the lowering), the parts of a number
//! written as in other languages (`1u8`, the token `ForeignLit`), and the
//! facts the lexer found in them ([`Literals`]: their holes, its errors in
//! them), which the parser and the table of the forms of other languages
//! read alike (D-15).

use onsa_diag::{Diagnostic, Span};

use std::ops::Range;

use crate::ast::{Ident, Path, StrLit, StrSeg};
use crate::token::TokenKind;

/// A hole of a string literal (`{x}`, from the `{` to after the `}`), as
/// the lexer read it once: the parser counts its levels and tells an
/// interpolation in the name of a `test` by it (§11.8, S-244), and the AST
/// takes its path from it (§2.4, S-90).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Hole {
    pub(crate) span: Span,
    /// The spans of the segments of its name path (the head, then each name
    /// or tuple index after a `.`), or `None` when it holds no name path
    /// (the lexer's E0001).
    pub(crate) path: Option<Vec<Span>>,
    /// The head of its path when it is a reserved word, whose unsupported
    /// feature the lexer reported there (§2.2, S-371).
    pub(crate) reserved_head: Option<Span>,
}

/// The facts of the string and character literals that the lexer read: the
/// holes of the strings (also of a form an interpolation may not have,
/// `{a + 1}`) and the spans of the lexer's errors, each in the order of the
/// file.
#[derive(Debug, Clone, Default)]
pub(crate) struct Literals {
    holes: Vec<Hole>,
    errors: Vec<Span>,
}

impl Literals {
    /// The facts of the holes `holes` (in the order of the file) and of the
    /// lexer's diagnostics `diagnostics`.
    pub(crate) fn new(holes: Vec<Hole>, diagnostics: &[Diagnostic]) -> Literals {
        let mut errors: Vec<Span> = diagnostics.iter().map(|d| d.span).collect();
        errors.sort_by_key(|s| s.start);
        Literals { holes, errors }
    }

    /// The facts of the literals between `from` and `to`, for a run of tokens
    /// read on its own (`parser::reads_as_expr`): its holes and the errors of
    /// the lexer in it, so that a literal reads there as it does in the file.
    pub(crate) fn within(&self, from: u32, to: u32) -> Literals {
        let first = self.holes.partition_point(|h| h.span.start < from);
        let last = self.holes.partition_point(|h| h.span.start <= to);
        let holes = self.holes[first..last].iter().filter(|h| h.span.end <= to).cloned().collect();
        Literals { holes, errors: inside(&self.errors, from, to) }
    }

    /// Every hole, in the order of the file.
    pub(crate) fn holes(&self) -> &[Hole] {
        &self.holes
    }

    /// The holes inside `span` (a literal), found by a binary search.
    pub(crate) fn holes_in(&self, span: Span) -> &[Hole] {
        let first = self.holes.partition_point(|h| h.span.start < span.start);
        let n = self.holes[first..].iter().take_while(|h| h.span.end <= span.end).count();
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
    match inner.strip_prefix('\\') {
        Some(rest) => escape(rest).0.unwrap_or('\u{FFFD}'),
        None => inner.chars().next().unwrap_or('\u{FFFD}'),
    }
}

/// A string literal with its interpolations split out (§2.4): the text
/// between the holes with its escapes read ([`escape`]), and the path of
/// each of its holes `holes` (the lexer's, [`Literals::holes_in`]; `text` is
/// the file). A hole that holds no name path (the lexer's E0001) is left out.
pub(crate) fn str_lit(text: &str, span: Span, holes: &[Hole]) -> StrLit {
    let raw = &text[span.start as usize..span.end as usize];
    let close = usize::from(raw.len() > 1 && raw.ends_with('"'));
    let (from, to) = (span.start as usize + 1, span.end as usize - close);
    let mut segments = Vec::new();
    let mut buf = String::new();
    let mut i = from;
    let mut holes = holes.iter().peekable();
    while i < to {
        if let Some(h) = holes.next_if(|h| h.span.start as usize == i) {
            if !buf.is_empty() {
                segments.push(StrSeg::Text(std::mem::take(&mut buf)));
            }
            if let Some(path) = &h.path {
                let name = |s: &Span| Ident { name: text[s.start as usize..s.end as usize].to_string(), span: *s };
                let pspan = Span::new(span.file, path[0].start, path[path.len() - 1].end);
                segments.push(StrSeg::Interp(Path { segments: path.iter().map(name).collect(), span: pspan }));
            }
            i = h.span.end as usize;
            continue;
        }
        let rest = &text[i..to];
        if let Some(after) = rest.strip_prefix('\\') {
            let (c, n) = escape(after);
            buf.extend(c);
            i += 1 + n;
        } else if rest.starts_with("{{") || rest.starts_with("}}") {
            buf.push_str(&rest[..1]);
            i += 2;
        } else {
            let c = rest.chars().next().unwrap_or_default();
            buf.push(c);
            i += c.len_utf8();
        }
    }
    if !buf.is_empty() || segments.is_empty() {
        segments.push(StrSeg::Text(buf));
    }
    StrLit { segments, span }
}

/// The escape after a backslash (§2.4, S-19), `after` being the text after
/// the `\`: its character, or `None` when it is no escape of the closed list
/// (the lexer's E0001), and how many bytes of `after` it takes. The one
/// grammar of the escapes, for the lexer and the values alike: `\n \t \r \0
/// \\ \" \'`, and `\u{…}` with 1 to 6 hexadecimal digits that make a Unicode
/// scalar value (its digits and its `}` are taken also when they do not).
/// An unknown escape takes the whole character after the `\` (none at the
/// end of a line or of the text).
pub(crate) fn escape(after: &str) -> (Option<char>, usize) {
    // SPEC-GAP(S-437): 7 hexadecimal digits or more are E0001, leading zeros too.
    let Some(c) = after.chars().next() else { return (None, 0) };
    let simple = match c {
        'n' => Some('\n'),
        't' => Some('\t'),
        'r' => Some('\r'),
        '0' => Some('\0'),
        '\\' => Some('\\'),
        '"' => Some('"'),
        '\'' => Some('\''),
        _ => None,
    };
    if simple.is_some() {
        return (simple, 1);
    }
    if crate::lexer::line_break(after.as_bytes()).is_some() {
        return (None, 0);
    }
    let Some(body) = after.strip_prefix("u{") else { return (None, c.len_utf8()) };
    let digits = body.bytes().take_while(u8::is_ascii_hexdigit).count();
    let closed = body.as_bytes().get(digits) == Some(&b'}');
    let value = (closed && (1..=6).contains(&digits))
        .then(|| u32::from_str_radix(&body[..digits], 16).ok().and_then(char::from_u32))
        .flatten();
    (value, 2 + digits + usize::from(closed))
}

/// The name path a hole holds (§2.4, S-90), `content` being the text
/// between its `{` and `}`: the byte ranges in `content` of its segments, or
/// what keeps it from being one. The head is a name, `self` or `Self` (or a
/// reserved word, whose E0200 is the lexer's); after each `.` a name, a
/// keyword (S-357) or the digits of a tuple index. Nothing else: no blank,
/// no call, no literal, no operator, no format (`{x:.2}`).
pub(crate) fn hole_path(content: &str) -> Result<Vec<Range<usize>>, HoleError> {
    // S-440: a blank, a keyword at the head but `self` / `Self` (`{true}`, `{fn}`) and `_` make no name path.
    if content.contains(':') {
        return Err(HoleError::Format);
    }
    let mut out = Vec::new();
    let mut at = 0;
    for (k, seg) in content.split('.').enumerate() {
        let range = at..at + seg.len();
        at = range.end + 1;
        let b = seg.as_bytes();
        let name = b.first().is_some_and(|&x| x.is_ascii_alphabetic() || x == b'_')
            && b.iter().all(|&x| x.is_ascii_alphanumeric() || x == b'_')
            && seg != "_";
        let ok = if k == 0 {
            name && TokenKind::keyword(seg)
                .is_none_or(|kw| matches!(kw, TokenKind::KwSelf | TokenKind::KwSelfType) || kw.reserved().is_some())
        } else {
            name || (!b.is_empty() && b.iter().all(u8::is_ascii_digit))
        };
        if !ok {
            return Err(HoleError::NotAPath);
        }
        out.push(range);
    }
    Ok(out)
}

/// Why a hole holds no name path ([`hole_path`]), for the note of its E0001.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HoleError {
    /// A format (`{x:.2}`): there is none.
    Format,
    /// Anything else (an expression, a call, a literal, blanks).
    NotAPath,
}
