//! The literal tokens (§2.4): the one grammar of the numbers ([`number`])
//! and of the escapes ([`escape`]), which the lexer calls; their values (one
//! function each, for the parser's checks, the types stage and the
//! lowering); and the facts the lexer found in them ([`Literals`]: the holes
//! of the strings, its errors in them, the numbers and the strings written as
//! in other languages, the literals right against a name), which the parser
//! and the table of the forms of other languages read alike (D-15).

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

/// A string or character literal right against a name, the prefixes and
/// suffixes of other languages (`f"{x}"`, `b'x'`, `"x"_s`; §2.4, S-400), as
/// the lexer found it: the row `string_prefix` reports it where the parser
/// fails at the literal or the name, whatever the literal holds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Touch {
    /// The literal (a token `Str` or `Char`).
    pub(crate) literal: Span,
    /// The name right before the literal or right after it.
    pub(crate) name: Span,
    /// The range of the form: the name and the literal, or the name to the
    /// opening quote when the literal does not close on its line.
    pub(crate) range: Span,
    /// The lexer's errors of the content of the literal (§2.4), held back:
    /// the form's E0002 is the error, and they are reported only where no
    /// `string_prefix` is (`extern "C" lib"m"` reads the literal). A
    /// character written nowhere is not held (§2.5, S-454).
    pub(crate) held: Vec<Diagnostic>,
}

/// The facts of the literals that the lexer read, each in the order of the
/// file: the holes of the strings (also of a form an interpolation may not
/// have, `{a + 1}`), the spans of the lexer's errors (the held ones too), the
/// numbers written as in other languages (the tokens `ForeignLit`,
/// [`Number`]), the strings written with a delimiter of other languages (the
/// tokens `ForeignStr` and the range of their form, S-406), the literals
/// right against a name ([`Touch`]) and the string and character literals
/// that do not close on their line.
#[derive(Debug, Clone, Default)]
pub(crate) struct Literals {
    holes: Vec<Hole>,
    errors: Vec<Span>,
    numbers: Vec<(Span, Number)>,
    strings: Vec<(Span, Span)>,
    touches: Vec<Touch>,
    unclosed: Vec<Span>,
}

/// What the lexer found in the literals, each in the order of the file
/// ([`Literals`]).
#[derive(Debug, Default)]
pub(crate) struct Found {
    pub(crate) holes: Vec<Hole>,
    pub(crate) numbers: Vec<(Span, Number)>,
    pub(crate) strings: Vec<(Span, Span)>,
    pub(crate) touches: Vec<Touch>,
    pub(crate) unclosed: Vec<Span>,
}

impl Literals {
    /// The facts of what the lexer found `found` and of its diagnostics
    /// `diagnostics`.
    pub(crate) fn new(found: Found, diagnostics: &[Diagnostic]) -> Literals {
        let Found { holes, numbers, strings, touches, unclosed } = found;
        let held = touches.iter().flat_map(|t| &t.held);
        let mut errors: Vec<Span> = diagnostics.iter().chain(held).map(|d| d.span).collect();
        errors.sort_by_key(|s| s.start);
        Literals { holes, errors, numbers, strings, touches, unclosed }
    }

    /// The facts of the literals between `from` and `to`, for a run of tokens
    /// read on its own (`parser::reads_as_expr`): its holes and the errors of
    /// the lexer in it, so that a literal reads there as it does in the file.
    pub(crate) fn within(&self, from: u32, to: u32) -> Literals {
        let first = self.holes.partition_point(|h| h.span.start < from);
        let last = self.holes.partition_point(|h| h.span.start <= to);
        let holes = self.holes[first..last].iter().filter(|h| h.span.end <= to).cloned().collect();
        let first = self.numbers.partition_point(|n| n.0.start < from);
        let last = self.numbers.partition_point(|n| n.0.start <= to);
        let numbers = self.numbers[first..last].iter().filter(|n| n.0.end <= to).copied().collect();
        let first = self.strings.partition_point(|s| s.0.start < from);
        let last = self.strings.partition_point(|s| s.0.start <= to);
        let strings = self.strings[first..last].iter().filter(|s| s.0.end <= to).copied().collect();
        let first = self.touches.partition_point(|t| t.literal.start < from);
        let last = self.touches.partition_point(|t| t.literal.start <= to);
        let inner = |t: &&Touch| t.range.start >= from && t.range.end <= to;
        let touches = self.touches[first..last].iter().filter(inner).cloned().collect();
        let unclosed = inside(&self.unclosed, from, to);
        Literals { holes, errors: inside(&self.errors, from, to), numbers, strings, touches, unclosed }
    }

    /// The range of the form of the string written with a delimiter of
    /// other languages at `span` (a token `ForeignStr`), found by a binary
    /// search.
    pub(crate) fn foreign_string(&self, span: Span) -> Option<Span> {
        let i = self.strings.partition_point(|s| s.0.start < span.start);
        self.strings.get(i).filter(|s| s.0 == span).map(|s| s.1)
    }

    /// The literal right against a name of which the token at `span` is the
    /// literal or the name (before it or after it), found by a binary search.
    /// A name between two literals (`"a"x"b"`) is of the first.
    pub(crate) fn touch(&self, span: Span) -> Option<&Touch> {
        let i = self.touches.partition_point(|t| t.literal.start < span.start);
        let mut near = i.checked_sub(1).into_iter().chain([i]).filter_map(|k| self.touches.get(k));
        near.find(|t| t.literal == span || t.name == span)
    }

    /// Whether the string or character literal at `span` closes on its line.
    pub(crate) fn closed(&self, span: Span) -> bool {
        self.unclosed.binary_search_by_key(&span.start, |s| s.start).is_err()
    }

    /// Every literal right against a name, in the order of the file.
    pub(crate) fn touches(&self) -> &[Touch] {
        &self.touches
    }

    /// The number written as in other languages at `span` (a token
    /// `ForeignLit`), found by a binary search.
    pub(crate) fn number(&self, span: Span) -> Option<&Number> {
        let i = self.numbers.partition_point(|n| n.0.start < span.start);
        self.numbers.get(i).filter(|n| n.0 == span).map(|n| &n.1)
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

/// The base of a number (§2.4): its prefix, `0x` / `0X`, `0b` / `0B`, the
/// `0o` / `0O` of other languages, or none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Base {
    Dec,
    Hex,
    Bin,
    Oct,
}

/// What a number is written as (§2.4, §18.1): the one decision of its form,
/// made by [`number`]. A number has one form; one with two (`0o17u8`) has
/// the outer one, its suffix, and the other is found after the candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// An integer of Onsa (the token `Int`).
    Int,
    /// A float of Onsa (the token `Float`).
    Float,
    /// A type suffix of the closed list (`1u8`, `2.5f`): the row `literal_suffix`.
    Suffix,
    /// The octal prefix of other languages (`0o17`): the row `octal_prefix`.
    Octal,
    /// A decimal integer with a leading `0` (`017`, `00`): the row `leading_zero`.
    LeadingZero,
    /// No digit after the point (`1.`): the row `float_trailing_dot`.
    TrailingDot,
    /// No digit between the point and the exponent (`1.e3`): the row `float_dot_exponent`.
    DotExponent,
    /// No number of Onsa nor of the rows: the lexer's E0001.
    Invalid(Invalid),
}

/// Why a number is no number (the lexer's E0001, §18.1), at
/// [`Number::error`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Invalid {
    /// No digit after the prefix (`0x_`, `0b`, `0o`; `_` is no digit).
    NoDigits,
    /// A digit that is not octal after `0o` (`0o19`, S-451).
    OctalDigit,
    /// A suffix outside the closed list (`123abc`).
    Suffix,
}

/// A number as the lexer reads it once ([`number`]): its form and the parts
/// its row, its candidates and its value are made of. The offsets are in the
/// token's text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Number {
    /// The length of the token.
    pub(crate) len: usize,
    /// The length of the number without its suffix and the `_` before it.
    pub(crate) body: usize,
    pub(crate) form: Form,
    pub(crate) base: Base,
    /// Whether the body is written as a float (a point or an exponent).
    pub(crate) float: bool,
    /// Whether the suffix is one of a float type (`f32`, `f`).
    pub(crate) float_suffix: bool,
    /// Where the E0001 of an [`Form::Invalid`] is.
    pub(crate) error: (usize, usize),
    /// The offset of the point of a decimal float (`1.5`, `1.e3`).
    pub(crate) point: Option<usize>,
    /// The offset of the `e` or `E` of the exponent of a decimal float.
    pub(crate) exponent: Option<usize>,
}

impl Number {
    /// Whether the number is a float in Onsa (§2.4, §18.1): its body is
    /// written as one (a point, an exponent; `1.`), or its suffix is of a
    /// float type (`1f32`). Its candidates keep that. The one test.
    pub(crate) fn is_float(&self) -> bool {
        self.float || self.float_suffix || self.form == Form::TrailingDot
    }

    /// The body of the number of the token `text` when it is an integer
    /// (`0o17` of `0o17u8`), for its value ([`int_value`]).
    pub(crate) fn int_body<'t>(&self, text: &'t str) -> Option<&'t str> {
        (!self.is_float()).then(|| &text[..self.body])
    }
}

/// The type suffixes of other languages (§18.1, a closed list): the names
/// of the integer and float types of Rust, and `u l ul ll ull f` of C in
/// lower case or all in upper case (`uL`, `lu`, `U8`, `f16` are none, S-62).
/// Whether `suffix` is one, and whether it is one of a float type.
fn type_suffix(suffix: &str) -> Option<bool> {
    const INTEGER: &[&str] = &[
        "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize", "u", "l", "ul", "ll",
        "ull", "U", "L", "UL", "LL", "ULL",
    ];
    const FLOAT: &[&str] = &["f32", "f64", "f", "F"];
    if INTEGER.contains(&suffix) { Some(false) } else { FLOAT.contains(&suffix).then_some(true) }
}

/// How the `.` after the digits of a decimal integer reads (§2.4, S-350),
/// `rest` being the text from the `.`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Point {
    /// A digit follows: the point of a float (`1.5`).
    Fraction,
    /// `e` or `E` and the digits of an exponent follow: `1.e3` (S-62).
    Exponent,
    /// Another `.` follows: a range symbol starts (`1..<4`), the longest token.
    Range,
    /// A name or `(` follows: the integer ends and the `.` is a member
    /// (`1.abs()`, `1.(x)`).
    Member,
    /// Anything else (`1.`, `2.*x`, `1.[0]`): `1.` written as in other languages.
    TrailingDot,
}

/// How the `.` at the start of `rest`, after the digits of a decimal
/// integer, reads (§2.4, S-350): the one test, for the lexer and for a
/// candidate that puts an integer before such a `.` (S-302).
pub(crate) fn point_after_int(rest: &str) -> Point {
    let b = rest.as_bytes();
    let at = |i: usize| b.get(i).copied();
    match at(1) {
        Some(d) if d.is_ascii_digit() => Point::Fraction,
        Some(b'.') => Point::Range,
        // A sign between the `e` and the digits (`1.e-3`) is the exponent of S-62 too (S-452).
        Some(b'e' | b'E')
            if at(2).is_some_and(|d| d.is_ascii_digit())
                || (matches!(at(2), Some(b'+' | b'-')) && at(3).is_some_and(|d| d.is_ascii_digit())) =>
        {
            Point::Exponent
        }
        // SPEC-GAP(S-453): `1.f`, the float suffix of C after a point, is the member `.f`.
        Some(n) if crate::lexer::is_ident_start(n) || n == b'(' => Point::Member,
        _ => Point::TrailingDot,
    }
}

/// The one grammar of the numbers (§2.4, §18.1, S-62, S-63, S-126), `rest`
/// being the text from the first digit of a number (not of a tuple index,
/// which the lexer reads as digits alone). The lexer calls it, and the parts
/// it finds ([`Number`]) are what the later stages read (D-15).
///
/// The digits take `_` anywhere after the first (`1__000`, `1_`, `0x_1F`,
/// `1e_3`); the prefixes and the exponent take upper case and the exponent
/// a sign. A decimal number takes a point ([`point_after_int`]) and an
/// exponent; the `.` after a hexadecimal or binary number is always a member
/// `.` (`0x1F.abs()`): no float is written in those bases, so `0x1F.` has no
/// spelling as a float to suggest. The letters, digits and `_` after the
/// digits are a suffix.
pub(crate) fn number(rest: &str) -> Number {
    let b = rest.as_bytes();
    let at = |i: usize| b.get(i).copied();
    // The common number, digits alone (`42`, `0`): nothing else to read.
    let plain = run(b, 0, |x| x.is_ascii_digit());
    if !at(plain).is_some_and(|x| x == b'.' || crate::lexer::is_ident_continue(x)) && (plain == 1 || b[0] != b'0') {
        return Number {
            len: plain,
            body: plain,
            form: Form::Int,
            base: Base::Dec,
            float: false,
            float_suffix: false,
            error: (0, 0),
            point: None,
            exponent: None,
        };
    }
    let base = match (at(0), at(1)) {
        (Some(b'0'), Some(b'x' | b'X')) => Base::Hex,
        (Some(b'0'), Some(b'b' | b'B')) => Base::Bin,
        (Some(b'0'), Some(b'o' | b'O')) => Base::Oct,
        _ => Base::Dec,
    };
    let mut n = Number {
        len: 0,
        body: 0,
        form: Form::Int,
        base,
        float: false,
        float_suffix: false,
        error: (0, 0),
        point: None,
        exponent: None,
    };
    let mut i;
    let mut dot_exponent = false;
    match base {
        Base::Dec => {
            i = run(b, 0, |x| x.is_ascii_digit() || x == b'_');
            if at(i) == Some(b'.') {
                match point_after_int(&rest[i..]) {
                    Point::Fraction => {
                        n.point = Some(i);
                        i = run(b, i + 1, |x| x.is_ascii_digit() || x == b'_');
                        n.float = true;
                    }
                    Point::Exponent => {
                        n.point = Some(i);
                        i += 1;
                        dot_exponent = true;
                    }
                    Point::Range | Point::Member => {}
                    Point::TrailingDot => {
                        n.len = i + 1;
                        n.body = i + 1;
                        n.form = Form::TrailingDot;
                        return n;
                    }
                }
            }
            if matches!(at(i), Some(b'e' | b'E')) {
                let sign = usize::from(matches!(at(i + 1), Some(b'+' | b'-')));
                let end = run(b, i + 1 + sign, |x| x.is_ascii_digit() || x == b'_');
                if b[i + 1 + sign..end].iter().any(u8::is_ascii_digit) {
                    n.exponent = Some(i);
                    i = end;
                    n.float = true;
                }
            }
        }
        _ => {
            let digit: fn(u8) -> bool = match base {
                Base::Hex => |x| x.is_ascii_hexdigit(),
                Base::Bin => |x| matches!(x, b'0' | b'1'),
                // Every decimal digit, so that one that is not octal is an
                // error of the number (S-451), and not a number of its own.
                _ => |x| x.is_ascii_digit(),
            };
            i = run(b, 2, |x| digit(x) || x == b'_');
            if !b[2..i].iter().any(|&x| x != b'_') {
                n.form = Form::Invalid(Invalid::NoDigits);
            } else if base == Base::Oct && b[2..i].iter().any(|&x| matches!(x, b'8' | b'9')) {
                n.form = Form::Invalid(Invalid::OctalDigit);
            }
        }
    }
    n.body = i;
    if at(i).is_some_and(crate::lexer::is_ident_start) {
        let suffix = run(b, i, crate::lexer::is_ident_continue);
        n.len = suffix;
        // The `_` before the suffix goes with it (`1_000_u8` is `1_000`).
        n.body = i - rest[..i].bytes().rev().take_while(|&x| x == b'_').count();
        match type_suffix(&rest[i..suffix]) {
            _ if matches!(n.form, Form::Invalid(_)) => {}
            Some(float) => {
                n.float_suffix = float;
                n.form = Form::Suffix;
            }
            None => {
                n.form = Form::Invalid(Invalid::Suffix);
                n.error = (i, suffix);
            }
        }
    } else {
        n.len = i;
    }
    if let Form::Invalid(why) = n.form {
        if why != Invalid::Suffix {
            n.error = (0, n.len);
        }
        return n;
    }
    if n.form == Form::Suffix {
        return n;
    }
    let digits = || rest[..n.body].bytes().filter(|&x| x != b'_');
    n.form = if base == Base::Oct {
        Form::Octal
    } else if dot_exponent {
        n.float = true;
        Form::DotExponent
    } else if n.float {
        Form::Float
    } else if base == Base::Dec && rest.starts_with('0') && digits().count() > 1 {
        Form::LeadingZero
    } else {
        Form::Int
    };
    n
}

/// The end of the run of the bytes of `b` from `i` that `ok` takes.
fn run(b: &[u8], mut i: usize, ok: impl Fn(u8) -> bool) -> usize {
    while i < b.len() && ok(b[i]) {
        i += 1;
    }
    i
}

/// The value of an integer (`1_000`, `0xFF`, `0B1010`, and `0o17` and the
/// decimal `017` of the candidates), or `None` when it is larger than
/// `u64::MAX` (E0408) or no integer.
pub(crate) fn int_value(text: &str) -> Option<u64> {
    let digits: String = text.chars().filter(|&c| c != '_').collect();
    let radix = match digits.get(..2) {
        Some("0x" | "0X") => 16,
        Some("0b" | "0B") => 2,
        Some("0o" | "0O") => 8,
        _ => return digits.parse::<u64>().ok(),
    };
    u64::from_str_radix(&digits[2..], radix).ok()
}

/// The canonical spelling of the number token `text` (`docs/onsa-tools.md`
/// §3.2, §2.4, S-62, S-126), or `None` when it is no integer or float of
/// Onsa: the prefix and the `e` in lower case, no `+` in the exponent, the
/// hexadecimal digits in upper case, one `_` between digits only, and no
/// extra `0` at the head of the integer part of a float. The `0` at the
/// head of an exponent or of hexadecimal digits and at the end of a
/// fraction stay. The parts are those [`number`] read.
pub(crate) fn canonical_number(text: &str) -> Option<String> {
    if !text.starts_with(|c: char| c.is_ascii_digit()) {
        return None;
    }
    let n = number(text);
    if !matches!(n.form, Form::Int | Form::Float) || n.len != text.len() {
        return None;
    }
    let prefix = match n.base {
        Base::Hex => "0x",
        Base::Bin => "0b",
        _ => "",
    };
    if !prefix.is_empty() {
        return Some(format!("{prefix}{}", digit_groups(&text[2..]).to_ascii_uppercase()));
    }
    let mantissa_end = n.exponent.unwrap_or(text.len());
    let mut out = digit_groups(&text[..n.point.unwrap_or(mantissa_end)]);
    if n.float {
        let digits = out.trim_start_matches(['0', '_']);
        out = if digits.is_empty() { "0".to_string() } else { digits.to_string() };
    }
    if let Some(p) = n.point {
        out.push('.');
        out.push_str(&digit_groups(&text[p + 1..mantissa_end]));
    }
    if let Some(e) = n.exponent {
        out.push('e');
        let after = &text[e + 1..];
        if after.starts_with('-') {
            out.push('-');
        }
        out.push_str(&digit_groups(after.trim_start_matches(['+', '-'])));
    }
    Some(out)
}

/// The digits of `text` with one `_` between two runs of digits and no
/// other `_` (`1__000_` is `1_000`).
fn digit_groups(text: &str) -> String {
    text.split('_').filter(|g| !g.is_empty()).collect::<Vec<_>>().join("_")
}

/// The exact decimal value of the float token `text` as a key, for the
/// comparison of `docs/onsa-tools.md` §3.5 (numbers by value, not by
/// spelling): the digits without the `0` at their head and end, and the
/// power of ten (`1.0e3`, `1000.0`, `1_000.0` and `10e2` are `1e3`; zero is
/// `0e0`). The spellings of one value have one key, and two values have two
/// keys however near they are (no rounding to a type hides a change of a
/// digit), whatever the length of the exponent. The text itself when it is
/// no float of Onsa. The parts are those [`number`] read.
pub(crate) fn float_key(text: &str) -> String {
    if !text.starts_with(|c: char| c.is_ascii_digit()) {
        return text.to_string();
    }
    let n = number(text);
    if n.form != Form::Float || n.len != text.len() {
        return text.to_string();
    }
    let mantissa_end = n.exponent.unwrap_or(text.len());
    let fraction = n.point.map_or("", |p| &text[p + 1..mantissa_end]);
    let int = &text[..n.point.unwrap_or(mantissa_end)];
    let digits: String = int.chars().chain(fraction.chars()).filter(|&c| c != '_').collect();
    let head = digits.trim_start_matches('0');
    let significant = head.trim_end_matches('0');
    if significant.is_empty() {
        return "0e0".to_string();
    }
    let fraction_len = fraction.bytes().filter(|&x| x != b'_').count() as i64;
    let zeros = (head.len() - significant.len()) as i64;
    let exponent = n.exponent.map_or("", |e| &text[e + 1..]);
    format!("{significant}e{}", shifted_exponent(exponent, zeros - fraction_len))
}

/// The exponent `exponent` (its text after the `e`: a sign or none, digits
/// and `_`; empty for none) plus `shift`, as a decimal integer with no `+`
/// and no `0` at its head. Exact for an exponent of any length: the digits
/// are added as digits, not as a machine integer.
fn shifted_exponent(exponent: &str, shift: i64) -> String {
    // The digits of a magnitude, the least significant first, without the zeros at the head.
    fn magnitude(text: &str) -> Vec<u8> {
        let mut m: Vec<u8> = text.bytes().filter(u8::is_ascii_digit).map(|x| x - b'0').rev().collect();
        while m.last() == Some(&0) {
            m.pop();
        }
        m
    }
    // `a + b` when `sign` is 1, `a - b` (with `a >= b`) when it is -1.
    fn combine(a: &[u8], b: &[u8], sign: i8) -> Vec<u8> {
        let mut out = Vec::with_capacity(a.len() + 1);
        let mut carry = 0i8;
        for i in 0..a.len().max(b.len()) {
            let d = *a.get(i).unwrap_or(&0) as i8 + sign * *b.get(i).unwrap_or(&0) as i8 + carry;
            carry = d.div_euclid(10);
            out.push(d.rem_euclid(10) as u8);
        }
        if carry > 0 {
            out.push(carry as u8);
        }
        while out.last() == Some(&0) {
            out.pop();
        }
        out
    }
    let (a, a_negative) = (magnitude(exponent), exponent.starts_with('-'));
    let (b, b_negative) = (magnitude(&shift.unsigned_abs().to_string()), shift < 0);
    let a_larger = a.len().cmp(&b.len()).then_with(|| a.iter().rev().cmp(b.iter().rev())).is_ge();
    let (sum, negative) = if a_negative == b_negative {
        (combine(&a, &b, 1), a_negative)
    } else if a_larger {
        (combine(&a, &b, -1), a_negative)
    } else {
        (combine(&b, &a, -1), b_negative)
    };
    if sum.is_empty() {
        return "0".to_string();
    }
    let digits: String = sum.iter().rev().map(|&d| char::from(b'0' + d)).collect();
    if negative { format!("-{digits}") } else { digits }
}

/// The width of a float type, for [`float_value`] (`onsa_syntax` knows no
/// types: the types stage maps its own).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatWidth {
    F32,
    F64,
}

/// Why a float literal has no value in its type (§2.4, E0408).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatRange {
    /// The rounded value is not finite (`F32` of `1.0e40`).
    TooLarge,
    /// The literal is not 0 and rounds to 0 (`F32` of `1.0e-50`).
    ToZero,
    /// The text is no float: the lexer reported its E0001 (`1.5abc`).
    Malformed,
}

impl FloatRange {
    /// Why the literal is out of range, for the message of its E0408 (`None`
    /// for [`FloatRange::Malformed`], whose error is the lexer's E0001).
    pub fn why(self) -> Option<&'static str> {
        match self {
            FloatRange::TooLarge => Some("its value is not finite"),
            FloatRange::ToZero => Some("it is not 0 and rounds to 0"),
            FloatRange::Malformed => None,
        }
    }
}

/// The value of the float literal `text` in the type of `width` (§2.4,
/// R-20, R-45, S-211): the decimal value rounded once to the type, to the
/// nearest with ties to even (`F32` straight from the text, never through
/// `F64`), as an `f64` (which holds every `F32` value exactly). The one
/// conversion of a float literal to its value, for every stage. A value
/// that rounds to a subnormal number is a value (`F32` of `1.0e-40`).
pub fn float_value(text: &str, width: FloatWidth) -> Result<f64, FloatRange> {
    let digits: String = text.chars().filter(|&c| c != '_').collect();
    // The standard parsing rounds correctly; it takes the spellings of
    // §2.4 (`E`, a sign in the exponent, leading zeros).
    let value = match width {
        FloatWidth::F32 => digits.parse::<f32>().map(f64::from),
        FloatWidth::F64 => digits.parse::<f64>(),
    }
    .map_err(|_| FloatRange::Malformed)?;
    if !value.is_finite() {
        return Err(FloatRange::TooLarge);
    }
    let mantissa = digits.split(['e', 'E']).next().unwrap_or_default();
    if value == 0.0 && mantissa.bytes().any(|x| matches!(x, b'1'..=b'9')) {
        return Err(FloatRange::ToZero);
    }
    Ok(value)
}

/// The value `x` of a float type of `width` ([`float_value`]) as it is shown
/// (`onsa interface`): the shortest decimal that reads as the value in its
/// type, as an `f64` whose shortest decimal it is (`F32` 0.1 is shown `0.1`,
/// not as the digits of its `f64`). The one rule of the shown values.
pub fn float_shown(x: f64, width: FloatWidth) -> f64 {
    match width {
        FloatWidth::F32 => (x as f32).to_string().parse().unwrap_or(x),
        FloatWidth::F64 => x,
    }
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
    // S-437: `\u{…}` holds 1 to 6 hexadecimal digits; 7 or more are E0001, leading zeros too.
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
