//! The literal tokens (§2.4): the one grammar of the numbers ([`number`])
//! and of the escapes ([`escape`]), which the lexer calls; their values (one
//! function each, for the parser's checks, the types stage and the
//! lowering); and the facts the lexer found in them ([`Literals`]: the holes
//! of the strings, its errors in them, the numbers written as in other
//! languages, the runs of names and literals), which the parser and the
//! table of the forms of other languages read alike (D-15).

use onsa_diag::{Diagnostic, Span};
use serde::{Deserialize, Serialize};

use std::ops::Range;

use crate::ast::{HolePath, Ident, StrLit, StrSeg};
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
    /// (the lexer's E0001), or a tuple index of no index (its E0020, E0408);
    /// with each the tuple index it is ([`tuple_index`]), or `None` for a name.
    pub(crate) path: Option<Vec<(Span, Option<u32>)>>,
    /// The head of its path when it is a reserved word, whose unsupported
    /// feature the lexer reported there (§2.2, S-371).
    pub(crate) reserved_head: Option<Span>,
}

/// Names, string and character literals and strings with a delimiter of
/// other languages with no space between them (`f"{x}"`, `"x"_s`, `x"a"y`,
/// `r"""x"""`; §2.4, S-400, S-856), as the lexer found them
/// ([`crate::lexer`]'s `runs`): one form, which the rows `string_prefix` and
/// `string_delimiter` report where the parser fails at any part of it,
/// whatever its literals hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Run {
    /// Its tokens, from the first to the last.
    pub(crate) span: Span,
    /// The range of the form: `span`, or to the opening delimiter of the
    /// last part when that does not close on its line. It starts where the
    /// form's main position is.
    pub(crate) range: Span,
    /// Whether a part is a string with a delimiter of other languages.
    pub(crate) delimiter: bool,
    /// The lexer's errors of the content of its literals (§2.4), held back:
    /// the form's E0002 is the error, and they are reported only where no
    /// row is (`extern "C" lib"m"` reads the literal). A character written
    /// nowhere is not held (§2.5, S-454).
    pub(crate) held: Vec<Diagnostic>,
}

/// A number written as in other languages (a token `ForeignLit`), as the
/// lexer read it ([`number`]). Its form, the row of the table, is
/// [`Number::foreign`] of `number`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ForeignNumber {
    /// The token.
    pub(crate) token: Span,
    /// Its parts.
    pub(crate) number: Number,
}

/// The facts of the literals that the lexer read, each in the order of the
/// file: the holes of the strings (also of a form an interpolation may not
/// have, `{a + 1}`), the spans of the lexer's errors (the held ones too), the
/// numbers written as in other languages ([`ForeignNumber`]), the runs of
/// names and literals ([`Run`]), and the opening delimiters of the literals
/// and the strings of other languages that do not close on their line and
/// of the `/*` that never closes.
#[derive(Debug, Clone, Default)]
pub(crate) struct Literals {
    holes: Vec<Hole>,
    errors: Vec<Span>,
    numbers: Vec<ForeignNumber>,
    runs: Vec<Run>,
    unclosed: Vec<Span>,
}

/// What the lexer found in the literals, each in the order of the file
/// ([`Literals`]).
#[derive(Debug, Default)]
pub(crate) struct Found {
    pub(crate) holes: Vec<Hole>,
    pub(crate) numbers: Vec<ForeignNumber>,
    pub(crate) runs: Vec<Run>,
    pub(crate) unclosed: Vec<Span>,
    /// The errors of the content of each literal that has some, until the
    /// runs are known (`Lexer::runs`).
    pub(crate) contents: Vec<(Span, Vec<Diagnostic>)>,
}

/// A fact of [`Literals`] at a place of the file, by which its list is
/// ordered and searched.
trait Placed {
    fn span(&self) -> Span;
}

impl Placed for Span {
    fn span(&self) -> Span {
        *self
    }
}

impl Placed for Hole {
    fn span(&self) -> Span {
        self.span
    }
}

impl Placed for ForeignNumber {
    fn span(&self) -> Span {
        self.token
    }
}

impl Placed for Run {
    fn span(&self) -> Span {
        self.span
    }
}

impl Literals {
    /// The facts of what the lexer found `found` and of its diagnostics
    /// `diagnostics`.
    pub(crate) fn new(found: Found, diagnostics: &[Diagnostic]) -> Literals {
        let Found { holes, numbers, runs, unclosed, .. } = found;
        let held = runs.iter().flat_map(|r| &r.held);
        let mut errors: Vec<Span> = diagnostics.iter().chain(held).map(|d| d.span).collect();
        errors.sort_by_key(|s| s.start);
        Literals { holes, errors, numbers, runs, unclosed }
    }

    /// The facts of the literals between `from` and `to`, for a run of tokens
    /// read on its own (`parser::reads_as_expr`): its holes and the errors of
    /// the lexer in it, so that a literal reads there as it does in the file.
    pub(crate) fn within(&self, from: u32, to: u32) -> Literals {
        Literals {
            holes: inside(&self.holes, from, to),
            errors: inside(&self.errors, from, to),
            numbers: inside(&self.numbers, from, to),
            runs: inside(&self.runs, from, to),
            unclosed: inside(&self.unclosed, from, to),
        }
    }

    /// The run that holds the token at `span`, found by a binary search.
    pub(crate) fn touch(&self, span: Span) -> Option<&Run> {
        let i = self.runs.partition_point(|r| r.span.end <= span.start);
        self.runs.get(i).filter(|r| r.span.start <= span.start)
    }

    /// Whether the string or character literal at `span` closes on its line.
    pub(crate) fn closed(&self, span: Span) -> bool {
        self.unclosed.binary_search_by_key(&span.start, |s| s.start).is_err()
    }

    /// Whether a literal, a string of other languages or a `/*` that does
    /// not close opens from `from` on and before `to`: a closing bracket may
    /// be inside it (§18.1, S-859). A binary search.
    pub(crate) fn unclosed_in(&self, from: u32, to: u32) -> bool {
        let i = self.unclosed.partition_point(|s| s.start < from);
        self.unclosed.get(i).is_some_and(|s| s.start < to)
    }

    /// Whether the lexer has an error from `from` on and before `to`.
    pub(crate) fn errors_in(&self, from: u32, to: u32) -> bool {
        let i = self.errors.partition_point(|s| s.start < from);
        self.errors.get(i).is_some_and(|s| s.start < to)
    }

    /// Every run, in the order of the file.
    pub(crate) fn runs(&self) -> &[Run] {
        &self.runs
    }

    /// The number written as in other languages at `span` (a token
    /// `ForeignLit`), found by a binary search.
    pub(crate) fn number(&self, span: Span) -> Option<&ForeignNumber> {
        at(&self.numbers, span)
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

/// The facts of `items` (ordered by their start) that lie between `from`
/// and `to`, found by a binary search.
fn inside<T: Placed + Clone>(items: &[T], from: u32, to: u32) -> Vec<T> {
    let first = items.partition_point(|x| x.span().start < from);
    let last = items.partition_point(|x| x.span().start <= to);
    items[first..last].iter().filter(|x| x.span().end <= to).cloned().collect()
}

/// The fact of `items` (ordered by their start) at `span`, found by a binary search.
fn at<T: Placed>(items: &[T], span: Span) -> Option<&T> {
    let i = items.partition_point(|x| x.span().start < span.start);
    items.get(i).filter(|x| x.span() == span)
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

impl Base {
    /// Whether `x` is a digit of the base: the one test (S-451).
    fn digit(self, x: u8) -> bool {
        match self {
            Base::Dec => x.is_ascii_digit(),
            Base::Hex => x.is_ascii_hexdigit(),
            Base::Bin => matches!(x, b'0' | b'1'),
            Base::Oct => matches!(x, b'0'..=b'7'),
        }
    }
}

/// What a number is written as (§2.4, §18.1): the one decision of its form,
/// made by [`number`], in three layers: a number of Onsa, one written as in
/// other languages (the token `ForeignLit`, a row of the table) or no number
/// (the lexer's E0001). A number has one form; one with two (`0o17u8`) has
/// the outer one, its suffix, and the other is found after the candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// A number of Onsa (the tokens `Int` and `Float`).
    Onsa(Kind),
    /// A number written as in other languages (the token `ForeignLit`).
    Foreign(Foreign),
    /// No number of Onsa nor of the rows: the lexer's E0001.
    Invalid(Invalid),
}

/// The kind of a number of Onsa ([`Form::Onsa`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    /// An integer (the token `Int`).
    Int,
    /// A float (the token `Float`).
    Float,
}

/// The form of a number written as in other languages ([`Form::Foreign`]):
/// the row of the table that reports it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Foreign {
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
    /// A `'` between digits, the separator of C++14 (`1'000`, S-476): the row `digit_separator`.
    DigitSeparator,
}

/// Why a number is no number (the lexer's E0001, §18.1), at
/// [`Number::error`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Invalid {
    /// No digit after the prefix (`0x_`, `0b`, `0o`; `_` is no digit).
    NoDigits,
    /// A digit outside the base after `0b` or `0o` (`0b12`, `0o19`, S-451).
    BaseDigit,
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
        self.float || self.float_suffix || self.foreign() == Some(Foreign::TrailingDot)
    }

    /// The form of the number when it is written as in other languages (the
    /// token `ForeignLit`): the row of the table that reports it.
    pub(crate) fn foreign(&self) -> Option<Foreign> {
        match self.form {
            Form::Foreign(f) => Some(f),
            Form::Onsa(_) | Form::Invalid(_) => None,
        }
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
    match b.get(1).copied() {
        Some(d) if d.is_ascii_digit() => Point::Fraction,
        Some(b'.') => Point::Range,
        // A sign (`1.e-3`, S-452) and `_` (`1.e_3`, S-472) are in the exponent of S-62 too.
        Some(b'e' | b'E') if exponent_end(b, 1).is_some() => Point::Exponent,
        // `1.f`, the float suffix of C after a point, is the member `.f` (§2.4, S-453).
        Some(n) if crate::chars::is_ident_start(n) || n == b'(' => Point::Member,
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
/// digits are a suffix. A `'` between digits ([`digits`]) makes the outer
/// form: its candidate changes the `'` alone, and the other form of the
/// number is found after it.
pub(crate) fn number(rest: &str) -> Number {
    let mut n = read(rest);
    if !matches!(n.form, Form::Invalid(_)) && rest.as_bytes()[..n.len].contains(&b'\'') {
        n.float = n.is_float();
        n.form = Form::Foreign(Foreign::DigitSeparator);
    }
    n
}

/// [`number`] but the `'` between digits.
fn read(rest: &str) -> Number {
    let b = rest.as_bytes();
    let at = |i: usize| b.get(i).copied();
    // The common number, digits alone (`42`, `0`): nothing else to read.
    let plain = run(b, 0, |x| x.is_ascii_digit());
    if !at(plain).is_some_and(|x| matches!(x, b'.' | b'\'') || crate::chars::is_ident_continue(x))
        && (plain == 1 || b[0] != b'0')
    {
        return Number {
            len: plain,
            body: plain,
            form: Form::Onsa(Kind::Int),
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
        form: Form::Onsa(Kind::Int),
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
            i = digits(b, 0, |x| x.is_ascii_digit());
            if at(i) == Some(b'.') {
                match point_after_int(&rest[i..]) {
                    Point::Fraction => {
                        n.point = Some(i);
                        i = digits(b, i + 1, |x| x.is_ascii_digit());
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
                        n.form = Form::Foreign(Foreign::TrailingDot);
                        return n;
                    }
                }
            }
            if matches!(at(i), Some(b'e' | b'E'))
                && let Some(end) = exponent_end(b, i)
            {
                n.exponent = Some(i);
                i = end;
                n.float = true;
            }
        }
        _ => {
            // Every decimal digit, so that one outside the base is an error
            // of the number (S-451), and not a number of its own.
            i = digits(b, 2, |x| x.is_ascii_digit() || base.digit(x));
            if !b[2..i].iter().any(|&x| x != b'_') {
                n.form = Form::Invalid(Invalid::NoDigits);
            } else if b[2..i].iter().any(|&x| x.is_ascii_digit() && !base.digit(x)) {
                n.form = Form::Invalid(Invalid::BaseDigit);
            }
        }
    }
    n.body = i;
    if at(i).is_some_and(crate::chars::is_ident_start) {
        let suffix = run(b, i, crate::chars::is_ident_continue);
        n.len = suffix;
        // The `_` before the suffix goes with it (`1_000_u8` is `1_000`).
        n.body = i - rest[..i].bytes().rev().take_while(|&x| x == b'_').count();
        match type_suffix(&rest[i..suffix]) {
            // The E0001 of a digit outside the base is the error of `0b12f32` (S-973, S-281).
            _ if matches!(n.form, Form::Invalid(_)) => {}
            Some(float) => {
                n.float_suffix = float;
                n.form = Form::Foreign(Foreign::Suffix);
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
    if n.form == Form::Foreign(Foreign::Suffix) {
        return n;
    }
    let body_digits = || rest[..n.body].bytes().filter(|&x| x != b'_');
    n.form = if base == Base::Oct {
        Form::Foreign(Foreign::Octal)
    } else if dot_exponent {
        n.float = true;
        Form::Foreign(Foreign::DotExponent)
    } else if n.float {
        Form::Onsa(Kind::Float)
    } else if base == Base::Dec && rest.starts_with('0') && body_digits().count() > 1 {
        Form::Foreign(Foreign::LeadingZero)
    } else {
        Form::Onsa(Kind::Int)
    };
    n
}

/// The end of the digits of a number in `b` from `i` (§2.4): those `digit`
/// takes, `_` anywhere, and a `'` between two of them (C++14, S-476). The
/// lexer goes on only forward, and stops at a `'` with no digit on either
/// side (a character literal: `1 '2'`).
fn digits(b: &[u8], mut i: usize, digit: impl Fn(u8) -> bool) -> usize {
    while let Some(&x) = b.get(i) {
        let between = x == b'\'' && i > 0 && digit(b[i - 1]) && b.get(i + 1).is_some_and(|&y| digit(y));
        if !(digit(x) || x == b'_' || between) {
            break;
        }
        i += 1;
    }
    i
}

/// The end of the exponent whose `e` or `E` is at `i` in `b` (§2.4): a
/// sign, then digits and `_` with one digit at least; `None` without one
/// (`1.e_` reads as a member, S-472). The one test, of [`number`] and of
/// [`point_after_int`].
fn exponent_end(b: &[u8], i: usize) -> Option<usize> {
    let from = i + 1 + usize::from(matches!(b.get(i + 1), Some(b'+' | b'-')));
    let end = digits(b, from, |x| x.is_ascii_digit());
    b[from..end].iter().any(u8::is_ascii_digit).then_some(end)
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
    let digits: String = text.chars().filter(|&c| c != '_' && c != '\'').collect();
    let radix = match digits.get(..2) {
        Some("0x" | "0X") => 16,
        Some("0b" | "0B") => 2,
        Some("0o" | "0O") => 8,
        _ => return digits.parse::<u64>().ok(),
    };
    u64::from_str_radix(&digits[2..], radix).ok()
}

/// The canonical spelling of the number token `text` (`spec/tools.md`
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
    if !matches!(n.form, Form::Onsa(_)) || n.len != text.len() {
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
/// comparison of `spec/tools.md` §3.5 (numbers by value, not by
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
    if n.form != Form::Onsa(Kind::Float) || n.len != text.len() {
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
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

/// The digits of a tuple index written with a leading `0` without it (`01`
/// is `1`, `00` is `0`; §2.4, S-508), or `None` when it has none.
pub(crate) fn tuple_index_unpadded(text: &str) -> Option<&str> {
    if text.len() < 2 || !text.starts_with('0') {
        return None;
    }
    let digits = text.trim_start_matches('0');
    Some(if digits.is_empty() { &text[text.len() - 1..] } else { digits })
}

/// The message of the E0408 of a tuple index ([`BadIndex::TooLarge`]).
pub(crate) const TOO_LARGE: &str = "tuple index is too large";

/// Why the digits after a `.` are no tuple index ([`tuple_index`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BadIndex {
    /// It does not fit `U32` (E0408).
    TooLarge,
    /// It starts with `0` and is not `0` (E0020, S-508).
    Padded,
}

/// The value of the tuple index `digits` after a `.` (§2.4), by the one rule
/// of an expression's (`t.0`) and a hole's (`{t.0}`, R-290): a too large one
/// is that before it is a padded one.
pub(crate) fn tuple_index(digits: &str) -> Result<u32, BadIndex> {
    let value = tuple_index_value(digits).ok_or(BadIndex::TooLarge)?;
    if tuple_index_unpadded(digits).is_some() { Err(BadIndex::Padded) } else { Ok(value) }
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
/// the file). A hole that holds no name path (the lexer's E0001) is left out
/// ([`StrLit::pathless_hole`]).
pub(crate) fn str_lit(text: &str, span: Span, holes: &[Hole]) -> StrLit {
    let raw = &text[span.start as usize..span.end as usize];
    let close = usize::from(raw.len() > 1 && raw.ends_with('"'));
    let (from, to) = (span.start as usize + 1, span.end as usize - close);
    let mut segments = Vec::new();
    let mut buf = String::new();
    let mut i = from;
    let mut holes = holes.iter().peekable();
    let mut pathless_hole = false;
    while i < to {
        if let Some(h) = holes.next_if(|h| h.span.start as usize == i) {
            if !buf.is_empty() {
                segments.push(StrSeg::Text(std::mem::take(&mut buf)));
            }
            if let Some(path) = &h.path {
                let name = |&(s, i): &(Span, _)| {
                    (Ident { name: text[s.start as usize..s.end as usize].to_string(), span: s }, i)
                };
                let pspan = Span::new(span.file, path[0].0.start, path[path.len() - 1].0.end);
                segments.push(StrSeg::Interp(HolePath { segments: path.iter().map(name).collect(), span: pspan }));
            }
            pathless_hole |= h.path.is_none();
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
    StrLit { segments, span, pathless_hole }
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
    if crate::chars::line_break(after.as_bytes()).is_some() {
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

/// An escape of other languages whose value is the same in every language
/// of the list that has it (§2.4, S-461, the row `escape_fixed_width`),
/// `after` being the text after the `\` of an escape that [`escape`] does not
/// know: how many bytes of `after` it takes, and the hexadecimal digits of
/// the `\u{…}` of its value. It is `\u` and 4 hexadecimal digits and `\U`
/// and 8, whose value is a scalar value (the digits after them are plain
/// characters), `\x` and 2 whose value is `7F` or less with no hexadecimal
/// digit after them (C reads on), and `\b`, `\f`, `\v`. The digits of `\u`
/// and `\x` are kept as written; `\U` loses its leading zeros (`\U0001F600`
/// is `\u{1F600}`). None for any other escape, an E0001 (`\x414`, `\xff`,
/// `\a`, `\uD800`, `\U00110000`, `\x4`). The one test, for a string and a
/// character literal alike (the lexer's).
pub(crate) fn foreign_escape(after: &str) -> Option<(usize, &str)> {
    let b = after.as_bytes();
    let hex = |n: usize| after.get(1..1 + n).filter(|d| d.bytes().all(|x| x.is_ascii_hexdigit()));
    let (len, digits) = match b.first()? {
        b'b' => return Some((1, "8")),
        b'f' => return Some((1, "C")),
        b'v' => return Some((1, "B")),
        b'u' => (5, hex(4)?),
        b'U' => (9, hex(8)?),
        b'x' if !b.get(3).is_some_and(u8::is_ascii_hexdigit) => (3, hex(2)?),
        _ => return None,
    };
    let value = u32::from_str_radix(digits, 16).ok()?;
    if char::from_u32(value).is_none() || (b[0] == b'x' && value > 0x7f) {
        return None;
    }
    // 8 digits are more than `\u{…}` holds: the leading zeros go, one digit stays.
    let zeros = (digits.len() - digits.trim_start_matches('0').len()).min(digits.len() - 1);
    Some((len, if b[0] == b'U' { &digits[zeros..] } else { digits }))
}

/// The name path a hole holds (§2.4, S-90), `content` being the text
/// between its `{` and `}`: the byte ranges in `content` of its segments
/// with the tuple index of each that is one, or what keeps it from being one.
/// The head is a name, `self` or `Self` (or a reserved word, whose E0200 is
/// the lexer's); after each `.` a name, a keyword (S-357) or the digits of a
/// tuple index. Nothing else: no blank, no call, no literal, no operator, no
/// format (`{x:.2}`). Digits that are no tuple index by the rule of an
/// expression's are a path's still: the lexer reports them (R-290).
pub(crate) fn hole_path(content: &str) -> Result<Vec<Segment>, HoleError> {
    // S-440: a blank, a keyword at the head but `self` / `Self` (`{true}`, `{fn}`) and `_` make no name path.
    // S-448: a format only where a `:` follows the path at its head (`{p.x:.2}`, not `{c ? 1 : 2}`).
    let head = content.find(|c: char| !(c.is_ascii_alphanumeric() || matches!(c, '_' | '.'))).unwrap_or(content.len());
    if head > 0 && content[head..].starts_with(':') {
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
        let digits = k > 0 && !b.is_empty() && b.iter().all(u8::is_ascii_digit);
        let ok = if k == 0 {
            name && TokenKind::keyword(seg)
                .is_none_or(|kw| matches!(kw, TokenKind::KwSelf | TokenKind::KwSelfType) || kw.reserved().is_some())
        } else {
            name || digits
        };
        if !ok {
            return Err(HoleError::NotAPath);
        }
        out.push((range, digits.then(|| tuple_index(seg))));
    }
    Ok(out)
}

/// A segment of the path of a hole ([`hole_path`]): its range in the
/// content, and the tuple index it is (`None` for a name).
pub(crate) type Segment = (Range<usize>, Option<Result<u32, BadIndex>>);

/// Why a hole holds no name path ([`hole_path`]), for its diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HoleError {
    /// A format (`{x:.2}`, a `:` right after the path at the head): there is none.
    Format,
    /// Anything else (an expression, a call, a literal, blanks).
    NotAPath,
}
