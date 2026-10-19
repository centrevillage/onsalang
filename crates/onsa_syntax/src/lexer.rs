//! Lexer (spec §2). Never stops: invalid input yields `Error` tokens and
//! E0001 diagnostics, and lexing continues. A form of another language
//! (a block comment, `1.`, `1u8`, `$"…"`, `++`, `::`, ...) is a token of its own and
//! no diagnostic here: the parser accepts it nowhere, and the table of those
//! forms ([`crate::foreign`]) says what the failure is (E0020 or E0002).
//!
//! It goes by the characters of the text (R-01, K-10): it compares ASCII
//! bytes only, and goes over any other character whole ([`Lexer::bump_char`]),
//! so that every span lies on character boundaries.

use onsa_diag::{Code, Diagnostic, FileId, Span, Stage};

pub use crate::chars::{BLANKS, is_blank};
use crate::chars::{is_ident_continue, is_ident_start, line_break};
use crate::literal::{ForeignNumber, ForeignString, Form, Found, Hole, HoleError, Invalid, Kind, Literals, Touch};
use crate::token::{Token, TokenKind};

/// Result of lexing one file.
#[derive(Debug, Default)]
pub struct Lexed {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
    /// The holes of the string literals and the spans of the errors above,
    /// found once here and read by the parser and the table of the forms of
    /// other languages ([`Literals`]).
    pub(crate) literals: Literals,
}

pub fn lex(file: FileId, text: &str) -> Lexed {
    let mut lx = Lexer {
        file,
        text,
        bytes: text.as_bytes(),
        pos: 0,
        out: Lexed::default(),
        found: Found::default(),
        content: Vec::new(),
    };
    lx.run();
    let mut out = lx.out;
    out.literals = Literals::new(lx.found, &out.diagnostics);
    out
}

/// A character that is written nowhere, also in a comment or a string
/// (§2.5, S-201): the control characters (U+0000 to U+001F and U+007F to
/// U+009F), U+2028 / U+2029 and the bidirectional controls (U+202A to
/// U+202E, U+2066 to U+2069). The lexer takes the tab and the line feed
/// out of it (and a carriage return before a line feed, a line break); the
/// value of the name of a test may hold none of them (§11.8,
/// [`crate::test_name`]). The one list.
pub(crate) fn unwritable(c: char) -> bool {
    matches!(c, '\u{0}'..='\u{1f}' | '\u{7f}'..='\u{9f}' | '\u{2028}' | '\u{2029}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}')
}

/// The text of the comment at `span` of `src` without the blanks at its end:
/// what `onsa fmt` writes and what its check and `diff --ast` compare, for
/// the comments and the doc comments alike (`spec/tools.md` §3.4, §3.5).
pub fn comment_text(src: &str, span: Span) -> &str {
    src[span.start as usize..span.end as usize].trim_end_matches(BLANKS)
}

/// The offset where the line of `offset` in `text` starts.
pub(crate) fn line_start(text: &str, offset: u32) -> u32 {
    text[..offset as usize].rfind('\n').map_or(0, |i| i as u32 + 1)
}

/// The offset where the line of `offset` in `text` starts, when nothing but
/// blanks stands before `offset` on its line (a candidate that moves or adds
/// whole lines).
pub(crate) fn line_head(text: &str, offset: u32) -> Option<u32> {
    let start = line_start(text, offset);
    text[start as usize..offset as usize].chars().all(is_blank).then_some(start)
}

/// The blanks that start the line of `offset` in `text`: its indentation.
/// The one reading of it, for the recovery and the candidates.
pub(crate) fn indent(text: &str, offset: u32) -> &str {
    let rest = &text[line_start(text, offset) as usize..];
    &rest[..rest.len() - rest.trim_start_matches(BLANKS).len()]
}

/// The first token of the line of the token `i` of `tokens` (those of a
/// file, all kinds): lexing anew from its start reads the tokens of the file
/// from there on as they are (`a_line_lexed_anew_reads_its_tokens`). The
/// lexer looks back at the token right before only (a tuple index after a
/// `.`, a `#` after a `#`, a name right before a literal), and a line break
/// is none of them; a token over lines goes back to the line it starts on.
pub(crate) fn line_of(tokens: &[Token], i: usize) -> usize {
    let mut k = i.min(tokens.len());
    while k > 0 && tokens[k - 1].kind != TokenKind::Newline {
        k -= 1;
    }
    k
}

/// What a character that may not be written is, for the message of its E0001.
fn unwritable_kind(c: char) -> &'static str {
    match c {
        '\r' => "a carriage return without a line feed after it",
        '\u{2028}' | '\u{2029}' => "a line or paragraph separator",
        '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}' => "a bidirectional control",
        _ => "a control character",
    }
}

struct Lexer<'a> {
    file: FileId,
    text: &'a str,
    bytes: &'a [u8],
    pos: usize,
    out: Lexed,
    /// The holes of the string literals that a `}` closes, the numbers and
    /// the strings written as in other languages and the literals right
    /// against a name ([`Literals`]).
    found: Found,
    /// The errors of the content of the string or character literal being
    /// read, until it is read whole ([`Lexer::literal`]).
    content: Vec<Diagnostic>,
}

impl<'a> Lexer<'a> {
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn peek_at(&self, n: usize) -> Option<u8> {
        self.bytes.get(self.pos + n).copied()
    }

    /// The character at the position.
    fn peek_char(&self) -> Option<char> {
        self.text[self.pos..].chars().next()
    }

    /// Go over the character at the position, whole.
    fn bump_char(&mut self) {
        self.pos += self.peek_char().map_or(0, char::len_utf8);
    }

    /// The line break at the position ([`line_break`]).
    fn line_break(&self) -> Option<usize> {
        line_break(&self.bytes[self.pos..])
    }

    /// Whether a line ends at the position: a line break, or the end of the
    /// text.
    fn at_line_end(&self) -> bool {
        self.peek().is_none() || self.line_break().is_some()
    }

    fn span(&self, start: usize) -> Span {
        debug_assert!(self.text.is_char_boundary(start) && self.text.is_char_boundary(self.pos));
        Span::new(self.file, start as u32, self.pos as u32)
    }

    fn push(&mut self, kind: TokenKind, start: usize) {
        let span = self.span(start);
        self.out.tokens.push(Token { kind, span });
    }

    fn error(&mut self, code: Code, span: Span, message: impl Into<String>) -> usize {
        self.out.diagnostics.push(Diagnostic::new(Stage::Syntax, code, span, message));
        self.out.diagnostics.len() - 1
    }

    fn run(&mut self) {
        while let Some(b) = self.peek() {
            let start = self.pos;
            if let Some(n) = self.line_break() {
                self.pos += n;
                self.push(TokenKind::Newline, start);
                continue;
            }
            if matches!(b, b'"' | b'\'' | b'`' | b'$' | b'@' | b'#' | b'r')
                && !self.after_hash(start)
                && let Some((open, close)) = foreign_open(&self.text[start..])
            {
                self.foreign_string(start, open, close);
                continue;
            }
            match b {
                b' ' | b'\t' => {
                    while matches!(self.peek(), Some(b' ' | b'\t')) {
                        self.pos += 1;
                    }
                    self.push(TokenKind::Whitespace, start);
                }
                b'/' if self.peek_at(1) == Some(b'/') => self.comment(start),
                b'/' if self.peek_at(1) == Some(b'*') => self.block_comment(start),
                b'"' => self.literal(start, Self::string),
                b'\'' => self.literal(start, Self::char_lit),
                b'0'..=b'9' => self.number(start),
                _ if is_ident_start(b) => self.ident(start),
                _ => self.punct(start),
            }
        }
        let end = self.text.len();
        self.push(TokenKind::Eof, end);
    }

    /// Whether a `#` at `start` follows a `#` token right before it: the run
    /// of `#` from that one opened no delimiter ([`foreign_open`]), so the
    /// rest of the run, before the same character, opens none either. Each
    /// `#` of a run counting it again would be quadratic in its length.
    fn after_hash(&self, start: usize) -> bool {
        self.bytes[start] == b'#'
            && self.out.tokens.last().is_some_and(|t| t.kind == TokenKind::Hash && t.span.end as usize == start)
    }

    /// Whether the character at the position starts no token (§2.3, §2.5):
    /// a character other than ASCII, a control character but the tab and the
    /// line break, and the ASCII characters of no token (`\`, and `$` but
    /// where it opens a string of other languages, [`foreign_open`]).
    fn unusable(&self) -> bool {
        match self.peek() {
            None | Some(b' ' | b'\t') => false,
            _ if self.line_break().is_some() => false,
            Some(b'$') => foreign_open(&self.text[self.pos..]).is_none(),
            Some(b'\\') => true,
            Some(b) => !b.is_ascii_graphic(),
        }
    }

    /// A run of characters that start no token ([`Lexer::unusable`]), read
    /// by characters: one `Error` token and one E0001 (one error, K-10), whose
    /// message shows its first character and the characters of a name and the
    /// blanks (§2.3: the message shows the characters of a name).
    fn invalid(&mut self, start: usize) {
        let c = self.peek_char().unwrap_or_default();
        self.bump_char();
        while self.unusable() {
            self.bump_char();
        }
        let shown = if unwritable(c) || c.is_whitespace() {
            format!("U+{:04X}", c as u32)
        } else {
            format!("`{c}` (U+{:04X})", c as u32)
        };
        let message = format!(
            "{shown} cannot be written outside comments and strings: a name is written with the ASCII letters, digits and `_`, and the blanks are the space and the tab (§2.3, §2.5)"
        );
        let span = self.span(start);
        self.error(Code::E0001, span, message);
        self.push(TokenKind::Error, start);
    }

    /// In a comment, a string or a character: a run of characters that are
    /// written nowhere ([`unwritable`]; a carriage return before a line feed
    /// ends the line instead) is one E0001, and the run is gone over. Whether
    /// there was one.
    fn unwritable_run(&mut self) -> bool {
        let at = |lx: &Self| lx.peek_char().is_some_and(|c| unwritable(c) && c != '\t' && lx.line_break().is_none());
        if !at(self) {
            return false;
        }
        let start = self.pos;
        let c = self.peek_char().unwrap_or_default();
        while at(self) {
            self.bump_char();
        }
        let span = self.span(start);
        self.error(
            Code::E0001,
            span,
            format!(
                "U+{:04X} ({}) cannot be written, also in a comment or a string (§2.5)",
                c as u32,
                unwritable_kind(c)
            ),
        );
        true
    }

    /// `//`, `///` and `//!` to the end of the line (§2.1): `/` four times
    /// or more is a plain comment.
    fn comment(&mut self, start: usize) {
        let rest = &self.text[start..];
        let kind = if rest.starts_with("//!") {
            TokenKind::ModuleDoc
        } else if rest.starts_with("///") && !rest.starts_with("////") {
            TokenKind::DocComment
        } else {
            TokenKind::Comment
        };
        self.pos += 2;
        loop {
            // The printable ASCII and the tab at once: none ends the line or
            // is written nowhere.
            self.pos += self.bytes[self.pos..].iter().take_while(|&&b| (0x20..0x7f).contains(&b) || b == b'\t').count();
            if self.at_line_end() {
                break;
            }
            if !self.unwritable_run() {
                self.bump_char();
            }
        }
        self.push(kind, start);
    }

    /// There are no block comments (§2.1): `/* ... */` is one token, over
    /// lines, to the `*/` that closes it (a `/*` inside opens one more, so a
    /// nested comment is one token too), or to the end of the file. The
    /// table of the forms of other languages reads it.
    fn block_comment(&mut self, start: usize) {
        self.pos += 2;
        let mut depth = 1;
        while let Some(b) = self.peek() {
            if b == b'*' && self.peek_at(1) == Some(b'/') {
                self.pos += 2;
                depth -= 1;
                if depth == 0 {
                    break;
                }
            } else if b == b'/' && self.peek_at(1) == Some(b'*') {
                self.pos += 2;
                depth += 1;
            } else if let Some(n) = self.line_break() {
                self.pos += n;
            } else if !self.unwritable_run() {
                self.bump_char();
            }
        }
        self.push(TokenKind::BlockComment, start);
    }

    fn ident(&mut self, start: usize) {
        while let Some(b) = self.peek() {
            if is_ident_continue(b) {
                self.pos += 1;
            } else {
                break;
            }
        }
        let kind = word_kind(&self.text[start..self.pos]);
        self.push(kind, start);
    }

    /// A number (§2.4): its one grammar is [`crate::literal::number`]. A
    /// number of Onsa is `Int` or `Float`; one written as in other languages
    /// (`1.`, `1u8`, `0o17`, `017`, `1.e3`) is `ForeignLit`, whose parts the
    /// table of those forms reads ([`Literals::number`]); one that is neither
    /// is E0001 (`123abc`, `0x_`, `0o19`).
    fn number(&mut self, start: usize) {
        // After `.`, a digit run is a tuple index (§4.1): no float, no base prefix.
        let after_dot =
            self.out.tokens.last().is_some_and(|t| t.kind == TokenKind::Dot && t.span.end as usize == start);
        if after_dot {
            self.digits(|b| b.is_ascii_digit());
            self.push(TokenKind::Int, start);
            return;
        }
        let n = crate::literal::number(&self.text[start..]);
        self.pos = start + n.len;
        let kind = match n.form {
            Form::Onsa(Kind::Int) => TokenKind::Int,
            Form::Onsa(Kind::Float) => TokenKind::Float,
            Form::Invalid(why) => {
                let message = match why {
                    Invalid::NoDigits => "number prefix without digits",
                    // SPEC-GAP(S-451): a digit that is not octal after `0o` is E0001, no octal form.
                    Invalid::OctalDigit => "a digit that is not octal after `0o`; Onsa has no octal numbers (§2.4)",
                    Invalid::Suffix => "a number has no suffix",
                };
                let span = Span::new(self.file, (start + n.error.0) as u32, (start + n.error.1) as u32);
                self.error(Code::E0001, span, message);
                if n.float { TokenKind::Float } else { TokenKind::Int }
            }
            Form::Foreign(_) => {
                self.found.numbers.push(ForeignNumber { token: self.span(start), number: n });
                TokenKind::ForeignLit
            }
        };
        self.push(kind, start);
    }

    fn digits(&mut self, ok: impl Fn(u8) -> bool) -> usize {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if ok(b) {
                self.pos += 1;
            } else {
                break;
            }
        }
        self.pos - start
    }

    /// A string or character literal (§2.4), read by `lex` ([`Lexer::string`],
    /// [`Lexer::char_lit`]), which says whether it closes on its line. The
    /// errors of its content wait until it is read whole: one right against
    /// a name before it (`f"…"`, `b'x'`) or after it (`"…"_s`) is a form of
    /// other languages whose content is not read (S-400, S-406), and they
    /// are held in its [`Touch`]; else they are reported. A character written
    /// nowhere is reported as it is in either (§2.5, S-454).
    fn literal(&mut self, start: usize, lex: fn(&mut Self, usize) -> bool) {
        let closed = lex(self, start);
        let literal = self.span(start);
        let at = |from: u32, to: u32| Span::new(self.file, from, to);
        let n = self.out.tokens.len();
        let before = n.checked_sub(2).map(|i| self.out.tokens[i]);
        let touch = match before {
            Some(t) if t.kind == TokenKind::Ident && t.span.end == literal.start => {
                // Not closed: the name to the opening quote.
                let end = if closed { literal.end } else { literal.start + 1 };
                Some((t.span, at(t.span.start, end)))
            }
            // A hole that a `"` cuts closes the literal there, so `"{"a"}"` is
            // `"{"` against the name `a` (`string_prefix`), not a literal in a
            // hole (§2.4, S-465: the form of S-400, whose content is not read).
            _ if closed => self.name_after().map(|name| (name, at(literal.start, name.end))),
            _ => None,
        };
        if !closed {
            self.found.unclosed.push(literal);
        }
        let content = std::mem::take(&mut self.content);
        match touch {
            Some((name, range)) => self.found.touches.push(Touch { literal, name, range, held: content }),
            None => self.out.diagnostics.extend(content),
        }
    }

    /// The name right after the position, as the lexer will read it: a
    /// delimiter of other languages is read before a word (`r#"…"#`,
    /// [`Lexer::run`]), and [`word_kind`] tells a name from a keyword or `_`.
    fn name_after(&self) -> Option<Span> {
        let rest = &self.bytes[self.pos..];
        if !rest.first().is_some_and(|&b| is_ident_start(b)) || foreign_open(&self.text[self.pos..]).is_some() {
            return None;
        }
        let n = rest.iter().take_while(|&&b| is_ident_continue(b)).count();
        (word_kind(&self.text[self.pos..self.pos + n]) == TokenKind::Ident)
            .then(|| Span::new(self.file, self.pos as u32, (self.pos + n) as u32))
    }

    /// An E0001 of the content of the literal being read ([`Lexer::literal`]).
    fn content_error(&mut self, span: Span, message: &str) {
        self.content.push(Diagnostic::new(Stage::Syntax, Code::E0001, span, message));
    }

    /// A string written with a delimiter of other languages (§2.4, S-406,
    /// S-455), at its opening delimiter of `open` bytes ([`foreign_open`]):
    /// one token `ForeignStr` to the first closing delimiter `close` on the
    /// line, or to the end of the line. The content is not read, but for a
    /// character written nowhere (§2.5, S-454). The range of the form is the
    /// token, or the opening delimiter when the line has no closing one; the
    /// row `string_delimiter` reports it ([`Literals::foreign_string`]).
    fn foreign_string(&mut self, start: usize, open: usize, close: Close) {
        self.pos = start + open;
        let closed = loop {
            if self.at_line_end() {
                break false;
            }
            if let Some(n) = close.at(&self.text[self.pos..]) {
                self.pos += n;
                break true;
            }
            if !self.unwritable_run() {
                self.bump_char();
            }
        };
        let token = self.span(start);
        let range = if closed { token } else { Span::new(self.file, start as u32, (start + open) as u32) };
        self.found.strings.push(ForeignString { token, range });
        self.push(TokenKind::ForeignStr, start);
    }

    /// A string literal (§2.4): to its closing `"`, on its line. Whether it
    /// closes.
    fn string(&mut self, start: usize) -> bool {
        self.pos += 1;
        let closed = loop {
            if self.at_line_end() {
                let span = self.span(start);
                self.content_error(span, "unterminated string literal");
                break false;
            }
            match self.peek() {
                Some(b'"') => {
                    self.pos += 1;
                    break true;
                }
                Some(b'\\') => self.escape(),
                Some(b'{') if self.peek_at(1) == Some(b'{') => self.pos += 2,
                Some(b'}') if self.peek_at(1) == Some(b'}') => self.pos += 2,
                Some(b'{') => self.hole(),
                // SPEC-GAP(S-439): a `}` alone is E0001 (`}}` is the brace).
                Some(b'}') => {
                    let span = Span::new(self.file, self.pos as u32, self.pos as u32 + 1);
                    self.content_error(span, "lone `}` in string; write `}}` for a literal brace");
                    self.pos += 1;
                }
                _ => {
                    // The plain ASCII text at once (no quote, escape, brace
                    // or control character).
                    let plain =
                        |b: &u8| (0x20..0x7f).contains(b) && !matches!(b, b'"' | b'\\' | b'{' | b'}') || *b == b'\t';
                    let n = self.bytes[self.pos..].iter().take_while(|b| plain(b)).count();
                    self.pos += n;
                    if n == 0 && !self.unwritable_run() {
                        self.bump_char();
                    }
                }
            }
        };
        self.push(TokenKind::Str, start);
        closed
    }

    /// A hole `{…}` of a string literal (§2.4, S-90), at its `{`: what it
    /// holds goes to its `}`, the closing `"` or the end of the line. It
    /// holds a name path ([`crate::literal::hole_path`]); anything else is
    /// E0001, and a reserved word at its head is E0200 (§2.2, S-371). The
    /// lexer reads it once ([`Hole`]); the names stage resolves it (W4-04).
    fn hole(&mut self) {
        let open = self.pos;
        self.pos += 1;
        let mut unwritable = false;
        while !matches!(self.peek(), Some(b'}' | b'"')) && !self.at_line_end() {
            if self.unwritable_run() {
                unwritable = true;
            } else {
                self.bump_char();
            }
        }
        if self.peek() != Some(b'}') {
            let span = self.span(open);
            self.content_error(span, "unterminated interpolation; write `{{` for a literal brace");
            return;
        }
        let content = &self.text[open + 1..self.pos];
        self.pos += 1;
        let span = self.span(open);
        let at =
            |r: std::ops::Range<usize>| Span::new(self.file, (open + 1 + r.start) as u32, (open + 1 + r.end) as u32);
        let path = match crate::literal::hole_path(content) {
            Ok(ranges) => Some(ranges.into_iter().map(at).collect::<Vec<_>>()),
            Err(why) => {
                // A character written nowhere has its own E0001 already.
                if !unwritable {
                    // SPEC-GAP(S-448): the note is chosen by a `:` in the hole.
                    let note = match why {
                        HoleError::Format => {
                            "there is no format in an interpolation; the value is shown as `Show` shows it"
                        }
                        HoleError::NotAPath => {
                            "bind an expression to a name with `let` and interpolate the name; write `{{` and `}}` for braces"
                        }
                    };
                    let d = Diagnostic::new(
                        Stage::Syntax,
                        Code::E0001,
                        span,
                        "an interpolation holds a name path only: a name, then `.` and a field, a tuple index or a member (§2.4)",
                    )
                    .with_rule(note);
                    self.content.push(d);
                }
                None
            }
        };
        // SPEC-GAP(S-449): a reserved word at the head of a hole of another
        // form is not reported; the form's E0001 is.
        let head = path.as_ref().map(|p| p[0]);
        let word = |s: Span| &self.text[s.start as usize..s.end as usize];
        let reserved = head.and_then(|h| TokenKind::keyword(word(h)).and_then(TokenKind::reserved));
        if let (Some(head), Some(feature)) = (head, reserved) {
            self.content.push(feature.diagnostic(Stage::Syntax, head, &[]));
        }
        self.found.holes.push(Hole { span, path, reserved_head: reserved.and(head) });
    }

    /// A character literal (§2.4): to its closing `'`, on its line. Whether
    /// it closes.
    fn char_lit(&mut self, start: usize) -> bool {
        self.pos += 1;
        match self.peek() {
            Some(b'\\') => self.escape(),
            Some(b'\'') => {
                let span = self.span(start);
                self.content_error(span, "empty char literal");
            }
            _ if self.at_line_end() => {
                let span = self.span(start);
                self.content_error(span, "empty char literal");
            }
            // SPEC-GAP(S-445): a character other than ASCII may be written in
            // a character literal, as in a string (§2.5 names comments and
            // strings).
            _ => {
                if !self.unwritable_run() {
                    self.bump_char();
                }
            }
        }
        let mut closed = self.peek() == Some(b'\'');
        if closed {
            self.pos += 1;
        } else {
            // Possibly a lifetime or a multi-char literal from another language.
            while !self.at_line_end() {
                if self.peek() == Some(b'\'') {
                    self.pos += 1;
                    closed = true;
                    break;
                }
                if !self.unwritable_run() {
                    self.bump_char();
                }
            }
            let span = self.span(start);
            let mut d = Diagnostic::new(
                Stage::Syntax,
                Code::E0001,
                span,
                "char literal must hold exactly one Unicode scalar value",
            );
            // `'abc'`: a string of other languages (S-406).
            if closed {
                d = d.with_rule("a string is written `\"…\"`; a character literal holds one character (§2.4)");
            }
            self.content.push(d);
        }
        self.push(TokenKind::Char, start);
        closed
    }

    /// An escape (§2.4, S-19), at its `\`: the one grammar of the escapes
    /// ([`crate::literal::escape`]); one that is not of the closed list is
    /// E0001.
    fn escape(&mut self) {
        let start = self.pos;
        let (value, len) = crate::literal::escape(&self.text[start + 1..]);
        self.pos += 1 + len;
        if value.is_none() {
            let span = self.span(start);
            let message = if self.text[start + 1..].starts_with("u{") {
                "invalid `\\u{...}` escape: 1 to 6 hexadecimal digits of a Unicode scalar value"
            } else {
                "unknown escape; allowed: \\n \\t \\r \\0 \\\\ \\\" \\' \\u{...}"
            };
            self.content_error(span, message);
        }
    }

    fn punct(&mut self, start: usize) {
        use TokenKind::*;
        let b = self.peek().unwrap();
        let b1 = self.peek_at(1);
        let b2 = self.peek_at(2);
        let (kind, len) = match (b, b1, b2) {
            (b'+', Some(b'%'), _) => (PlusPercent, 2),
            (b'-', Some(b'%'), _) => (MinusPercent, 2),
            (b'*', Some(b'%'), _) => (StarPercent, 2),
            (b'+', Some(b'|'), _) => (PlusPipe, 2),
            (b'-', Some(b'|'), _) => (MinusPipe, 2),
            (b'*', Some(b'|'), _) => (StarPipe, 2),
            (b'-', Some(b'>'), _) => (Arrow, 2),
            // Increments of other languages, written without a space (S-250).
            // `a--b` and `5--3` (a binary `-` and a prefix one) read as `--`
            // too, an E0020 of the parser (S-320).
            (b'+', Some(b'+'), _) => (PlusPlus, 2),
            (b'-', Some(b'-'), _) => (MinusMinus, 2),
            // The power and the strict equalities of other languages, one
            // token each so that the failure names them whole (W3-04).
            (b'*', Some(b'*'), _) => (StarStar, 2),
            (b'=', Some(b'='), Some(b'=')) => (EqEqEq, 3),
            (b'!', Some(b'='), Some(b'=')) => (NotEqEq, 3),
            (b'=', Some(b'>'), _) => (FatArrow, 2),
            (b'=', Some(b'='), _) => (EqEq, 2),
            (b'!', Some(b'='), _) => (NotEq, 2),
            (b'<', Some(b'='), _) => (LtEq, 2),
            (b'>', Some(b'='), _) => (GtEq, 2),
            (b'<', Some(b'<'), _) => (Shl, 2),
            (b'>', Some(b'>'), _) => (Shr, 2),
            (b'&', Some(b'&'), _) => (AndAnd, 2),
            (b'|', Some(b'|'), _) => (OrOr, 2),
            (b'.', Some(b'.'), Some(b'<')) => (DotDotLt, 3),
            (b'.', Some(b'.'), Some(b'=')) => (DotDotEq, 3),
            (b'.', Some(b'.'), Some(b'.')) => (DotDotDot, 3),
            (b'.', Some(b'.'), _) => (DotDot, 2),
            (b':', Some(b':'), _) => (ColonColon, 2),
            (b'+', _, _) => (Plus, 1),
            (b'-', _, _) => (Minus, 1),
            (b'*', _, _) => (Star, 1),
            (b'/', _, _) => (Slash, 1),
            (b'%', _, _) => (Percent, 1),
            (b'=', _, _) => (Eq, 1),
            (b'!', _, _) => (Bang, 1),
            (b'<', _, _) => (Lt, 1),
            (b'>', _, _) => (Gt, 1),
            (b'&', _, _) => (Amp, 1),
            (b'|', _, _) => (Pipe, 1),
            (b'^', _, _) => (Caret, 1),
            (b'~', _, _) => (Tilde, 1),
            (b'.', _, _) => (Dot, 1),
            (b',', _, _) => (Comma, 1),
            (b':', _, _) => (Colon, 1),
            (b'?', _, _) => (Question, 1),
            (b'@', _, _) => (At, 1),
            (b'(', _, _) => (LParen, 1),
            (b')', _, _) => (RParen, 1),
            (b'[', _, _) => (LBracket, 1),
            (b']', _, _) => (RBracket, 1),
            (b'{', _, _) => (LBrace, 1),
            (b'}', _, _) => (RBrace, 1),
            (b';', _, _) => (Semi, 1),
            (b'#', _, _) => (Hash, 1),
            _ => return self.invalid(start),
        };
        self.pos += len;
        self.push(kind, start);
    }
}

/// The token of the word `word` (a run of the characters of a name): `_`,
/// a keyword or a name. The one test, for the words the lexer reads and the
/// name it looks for after a literal ([`Lexer::name_after`]).
fn word_kind(word: &str) -> TokenKind {
    if word == "_" { TokenKind::Underscore } else { TokenKind::keyword(word).unwrap_or(TokenKind::Ident) }
}

/// The closing delimiter of a string of other languages ([`foreign_open`]):
/// its quotes and the number of `#` after them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Close {
    quotes: &'static str,
    hashes: usize,
}

impl Close {
    /// The length of the closing delimiter at the start of `rest`, if it is there.
    fn at(self, rest: &str) -> Option<usize> {
        let after = rest.strip_prefix(self.quotes)?;
        let n = after.bytes().take(self.hashes).take_while(|&b| b == b'#').count();
        (n == self.hashes).then_some(self.quotes.len() + n)
    }
}

/// The opening delimiter of a string of other languages at the start of
/// `rest` (§2.4, S-406, S-455): its length and the closing delimiter. They
/// are `$"`, `@"`, `$@"`, `@$"` (C#), `#"`, `r#"` with one `#` or more
/// (Swift, Rust; `rest` starts a token, so the `r` is a name of its own),
/// `"""`, `'''` and `` ` ``. Neither is a token of Onsa: `"""` would be two
/// strings side by side, `'''` an empty character, and `$`, `` ` `` no
/// character of a token.
fn foreign_open(rest: &str) -> Option<(usize, Close)> {
    // SPEC-GAP(S-458): a name right before a delimiter is a name of its own
    // (`r"""x"""`, `` f`x` ``, `br#"x"#`: the row `string_delimiter` at the
    // delimiter, no `string_prefix`), and `$"""x"""` opens with `$"`.
    const QUOTED: [(&str, &str); 7] = [
        ("\"\"\"", "\"\"\""),
        ("'''", "'''"),
        ("`", "`"),
        ("$@\"", "\""),
        ("@$\"", "\""),
        ("$\"", "\""),
        ("@\"", "\""),
    ];
    if let Some((open, close)) = QUOTED.iter().find(|(open, _)| rest.starts_with(open)) {
        return Some((open.len(), Close { quotes: close, hashes: 0 }));
    }
    let b = rest.as_bytes();
    let r = usize::from(b.first() == Some(&b'r'));
    let hashes = b[r..].iter().take_while(|&&c| c == b'#').count();
    (hashes > 0 && b.get(r + hashes) == Some(&b'"')).then_some((r + hashes + 1, Close { quotes: "\"", hashes }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use TokenKind::*;

    /// The kinds of the tokens without the whitespace tokens (R-86 added them;
    /// the tests below compare the other tokens).
    fn kinds(src: &str) -> (Vec<TokenKind>, Vec<Code>) {
        let l = lex(FileId(0), src);
        (
            l.tokens.iter().map(|t| t.kind).filter(|&k| k != Whitespace).collect(),
            l.diagnostics.iter().map(|d| d.code).collect(),
        )
    }

    #[test]
    fn keywords_and_idents() {
        let (k, d) = kinds("pub rt fn soft_clip(x: F32) -> F32 { x }");
        assert_eq!(
            k,
            vec![
                KwPub, KwRt, KwFn, Ident, LParen, Ident, Colon, Ident, RParen, Arrow, Ident, LBrace, Ident, RBrace, Eof
            ]
        );
        assert!(d.is_empty());
    }

    #[test]
    fn numbers() {
        assert_eq!(kinds("42 0xFF 0b1010 1_000_000").0, vec![Int, Int, Int, Int, Eof]);
        assert_eq!(kinds("1.0 2.5e-3 1e3").0, vec![Float, Float, Float, Eof]);
        assert_eq!(kinds("0..n").0, vec![Int, DotDot, Ident, Eof]);
        assert_eq!(kinds("0..<n").0, vec![Int, DotDotLt, Ident, Eof]);
        assert_eq!(kinds("0..=n").0, vec![Int, DotDotEq, Ident, Eof]);
        assert_eq!(kinds("0...4").0, vec![Int, DotDotDot, Int, Eof]);
        // The longest symbol first (S-257).
        assert_eq!(kinds("a....b").0, vec![Ident, DotDotDot, Dot, Ident, Eof]);
        assert_eq!(kinds("1.. ..4").0, vec![Int, DotDot, DotDot, Int, Eof]);
        assert_eq!(kinds("1.5..<2").0, vec![Float, DotDotLt, Int, Eof]);
        assert_eq!(kinds("0..<=n").0, vec![Int, DotDotLt, Eq, Ident, Eof]);
        assert_eq!(kinds("t.0.1").0, vec![Ident, Dot, Int, Dot, Int, Eof]);
        assert_eq!(kinds("1.abs()").0, vec![Int, Dot, Ident, LParen, RParen, Eof]);
        // Forms of other languages are tokens without a diagnostic here.
        assert_eq!(kinds("1."), (vec![ForeignLit, Eof], vec![]));
        assert_eq!(kinds("1.0f32 1u8 0xFFu8"), (vec![ForeignLit, ForeignLit, ForeignLit, Eof], vec![]));
        assert_eq!(kinds("1.)").0, vec![ForeignLit, RParen, Eof]);
        assert_eq!(kinds("0o17 017 00 1.e3 1.e-3"), (vec![ForeignLit; 5].into_iter().chain([Eof]).collect(), vec![]));
        // S-350: an integer, then the member `.` before a name or `(`.
        assert_eq!(kinds("1.(x)").0, vec![Int, Dot, LParen, Ident, RParen, Eof]);
        assert_eq!(kinds("0X1F 0B1 1E3 1e+3").0, vec![Int, Int, Float, Float, Eof]);
        assert_eq!(kinds("0x").1, vec![Code::E0001]);
        assert_eq!(kinds("123abc 0x_ 0o19").1, vec![Code::E0001; 3]);
    }

    #[test]
    fn operators_longest_match() {
        assert_eq!(
            kinds("a +% b -| c *| d").0,
            vec![Ident, PlusPercent, Ident, MinusPipe, Ident, StarPipe, Ident, Eof]
        );
        assert_eq!(kinds("x.f!=y").0, vec![Ident, Dot, Ident, NotEq, Ident, Eof]);
        assert_eq!(kinds("out.fill!(0.0)").0, vec![Ident, Dot, Ident, Bang, LParen, Float, RParen, Eof]);
        assert_eq!(kinds("saw~(f0)").0, vec![Ident, Tilde, LParen, Ident, RParen, Eof]);
        assert_eq!(
            kinds("a << b >= c && d || e").0,
            vec![Ident, Shl, Ident, GtEq, Ident, AndAnd, Ident, OrOr, Ident, Eof]
        );
        assert_eq!(kinds("x => y -> z").0, vec![Ident, FatArrow, Ident, Arrow, Ident, Eof]);
    }

    #[test]
    fn space_before_flags() {
        let l = lex(FileId(0), "saw~(f0) saw ~(f0)");
        let flags: Vec<bool> = (0..l.tokens.len())
            .filter(|&i| l.tokens[i].kind != Whitespace)
            .map(|i| crate::token::gap_before(&l.tokens, i).is_some())
            .collect();
        assert_eq!(flags, vec![false, false, false, false, false, true, true, false, false, false, false]);
    }

    #[test]
    fn comments_and_newlines() {
        let (k, d) = kinds("// c\n/// doc\nfn\n");
        assert_eq!(k, vec![Comment, Newline, DocComment, Newline, KwFn, Newline, Eof]);
        assert!(d.is_empty());
    }

    #[test]
    fn block_comments_are_one_token_over_lines() {
        assert_eq!(kinds("/* x */ a"), (vec![BlockComment, Ident, Eof], vec![]));
        assert_eq!(kinds("a /* x\ny */ b").0, vec![Ident, BlockComment, Ident, Eof]);
        // Nested: one token to the `*/` that closes the first `/*`.
        assert_eq!(kinds("/* a /* b */ c */ d").0, vec![BlockComment, Ident, Eof]);
        // Never closed: to the end of the file.
        assert_eq!(kinds("a /* b\nc").0, vec![Ident, BlockComment, Eof]);
        assert_eq!(kinds("/**/ /** d */ /*! m */").0, vec![BlockComment, BlockComment, BlockComment, Eof]);
    }

    #[test]
    fn increments_are_one_token_without_a_space() {
        assert_eq!(
            kinds("++x x-- - -x ---x").0,
            vec![PlusPlus, Ident, Ident, MinusMinus, Minus, Minus, Ident, MinusMinus, Minus, Ident, Eof]
        );
        assert_eq!(kinds("a->b a-%b").0, vec![Ident, Arrow, Ident, Ident, MinusPercent, Ident, Eof]);
    }

    #[test]
    fn strings() {
        assert!(kinds(r#""plain" "a\nb\n" "({self.x}, {self.y})" "{{lit}}""#).1.is_empty());
        assert_eq!(kinds(r#""{1 + 2}""#).1, vec![Code::E0001]);
        assert_eq!(kinds(r#""{x""#).1, vec![Code::E0001]); // unterminated interpolation; the `"` then closes the string
        assert_eq!(kinds(r#""a}b""#).1, vec![Code::E0001]);
        assert_eq!(kinds(r#""\q""#).1, vec![Code::E0001]);
        assert_eq!(kinds("\"abc").1, vec![Code::E0001]);
        assert!(kinds(r#""\u{1F600}""#).1.is_empty());
    }

    #[test]
    fn chars() {
        assert_eq!(kinds(r"'a' '\n' '音'").0, vec![Char, Char, Char, Eof]);
        assert_eq!(kinds("'ab'").1, vec![Code::E0001]);
        assert_eq!(kinds("''").1, vec![Code::E0001]);
    }

    #[test]
    fn foreign_and_invalid() {
        assert_eq!(
            kinds("a::b; #[x] 0..=1").0,
            vec![Ident, ColonColon, Ident, Semi, Hash, LBracket, Ident, RBracket, Int, DotDotEq, Int, Eof]
        );
        let (k, d) = kinds("a $ b");
        assert_eq!((k, d), (vec![Ident, Error, Ident, Eof], vec![Code::E0001]));
    }

    #[test]
    fn spans_are_byte_offsets() {
        let l = lex(FileId(0), "let 音 = 1");
        let eq = l.tokens.iter().find(|t| t.kind == Eq).unwrap();
        assert_eq!((eq.span.start, eq.span.end), (8, 9));
    }

    /// The tokens with their texts, the blanks included.
    fn texts(src: &str) -> Vec<(TokenKind, &str)> {
        lex(FileId(0), src).tokens.iter().map(|t| (t.kind, &src[t.span.start as usize..t.span.end as usize])).collect()
    }

    /// The codes and texts of the diagnostics.
    fn errors(src: &str) -> Vec<(Code, &str)> {
        lex(FileId(0), src)
            .diagnostics
            .iter()
            .map(|d| (d.code, &src[d.span.start as usize..d.span.end as usize]))
            .collect()
    }

    #[test]
    fn every_span_is_on_character_boundaries_whatever_the_text() {
        // R-01: the places of the old panics, and every kind of text around
        // characters of two to four bytes.
        let chars = ["é", "音", "\u{8f}", "😀", "\u{202e}", "\u{a0}"];
        let forms = [
            "\"{{{c}}}\"",
            "\"{{{c}\"",
            "\"{{{c}",
            "\"\\{c}\"",
            "'{c}'",
            "'\\{c}'",
            "// {c}",
            "/* {c} */",
            "{c}x",
            "x{c}",
        ];
        for c in chars {
            for form in forms {
                let src = form.replace("{c}", c);
                let l = lex(FileId(0), &src);
                for s in l.tokens.iter().map(|t| t.span).chain(l.diagnostics.iter().map(|d| d.span)) {
                    assert!(src.is_char_boundary(s.start as usize) && src.is_char_boundary(s.end as usize), "{src:?}");
                }
                assert_eq!(
                    l.tokens.iter().map(|t| &src[t.span.start as usize..t.span.end as usize]).collect::<String>(),
                    src
                );
            }
        }
    }

    #[test]
    fn the_blanks_are_the_space_and_the_tab_and_a_line_ends_with_lf_or_crlf() {
        assert_eq!(
            texts("a \t b\r\nc\n"),
            vec![
                (Ident, "a"),
                (Whitespace, " \t "),
                (Ident, "b"),
                (Newline, "\r\n"),
                (Ident, "c"),
                (Newline, "\n"),
                (Eof, "")
            ]
        );
        // A comment and a string end before the CR LF.
        assert_eq!(texts("// c\r\n")[0], (Comment, "// c"));
        assert_eq!(errors("\"a\r\n"), vec![(Code::E0001, "\"a")]);
        // A carriage return alone is E0001, in the code, a comment and a string (S-201).
        assert_eq!(texts("a\rb")[1], (Error, "\r"));
        assert_eq!(errors("a\rb"), vec![(Code::E0001, "\r")]);
        assert_eq!(errors("// a\rb\n"), vec![(Code::E0001, "\r")]);
        assert_eq!(errors("\"a\rb\""), vec![(Code::E0001, "\r")]);
    }

    #[test]
    fn the_characters_written_nowhere_are_e0001_also_in_comments_and_strings() {
        for c in [
            '\u{0}', '\u{1b}', '\u{7f}', '\u{85}', '\u{2028}', '\u{2029}', '\u{202a}', '\u{202e}', '\u{2066}',
            '\u{2069}',
        ] {
            for form in ["// a{c}b", "\"a{c}b\"", "'{c}'", "/* {c} */", "a{c}b"] {
                let src = form.replace("{c}", &c.to_string());
                let e = errors(&src);
                assert_eq!(e, vec![(Code::E0001, &*c.to_string())], "{src:?}");
            }
        }
        // A run is one error (K-10, one error of one edit).
        assert_eq!(errors("// a\u{202e}\u{2066}b"), vec![(Code::E0001, "\u{202e}\u{2066}")]);
        // The tab is written anywhere.
        assert!(errors("// a\tb\n\"a\tb\" '\t'").is_empty());
        // Other characters are written in comments and strings only.
        assert!(errors("// é 音 \u{a0}\n\"é 音 \u{a0}\"").is_empty());
        assert_eq!(errors("a\u{a0}b \u{feff}"), vec![(Code::E0001, "\u{a0}"), (Code::E0001, "\u{feff}")]);
    }

    #[test]
    fn a_run_of_characters_of_no_token_is_one_error_token() {
        assert_eq!(texts("let 日本語 = 1")[2], (Error, "日本語"));
        assert_eq!(errors("let 日本語 = 1"), vec![(Code::E0001, "日本語")]);
        let message = &lex(FileId(0), "let é = 1").diagnostics[0].message;
        assert!(message.contains("ASCII letters, digits and `_`"), "{message}");
        // A name stops at a character of no token.
        assert_eq!(kinds("café").0, vec![Ident, Error, Eof]);
        assert_eq!(errors("a $\\ b"), vec![(Code::E0001, "$\\")]);
    }

    #[test]
    fn the_strings_of_other_languages_are_one_token_to_their_closing_delimiter() {
        // S-406, S-455: to the first closing delimiter on the line, the content unread.
        for src in [
            "$\"a{x}\"",
            "@\"C:\\p\"",
            "$@\"x\"",
            "@$\"x\"",
            "r#\"a\\q\"#",
            "r##\"a\"#b\"##",
            "#\"x\"#",
            "##\"x\"##",
            "\"\"\"a\"b\"\"\"",
            "\"\"\"\"\"\"",
            "'''x'''",
            "`a${1}b`",
        ] {
            assert_eq!(texts(src), vec![(ForeignStr, src), (Eof, "")], "{src}");
            assert!(errors(src).is_empty(), "{src}");
        }
        assert_eq!(texts("r#\"a\"#b\"#")[..2], [(ForeignStr, "r#\"a\"#"), (Ident, "b")]);
        // No closing delimiter on the line: the token goes to its end.
        let line: Vec<TokenKind> = texts("$\"ab \\q\nx").into_iter().map(|t| t.0).collect();
        assert_eq!(line, vec![ForeignStr, Newline, Ident, Eof]);
        assert_eq!(texts("`a\r\nb`")[0], (ForeignStr, "`a"));
        // A character written nowhere is its E0001 (S-454).
        assert_eq!(errors("`a\u{2028}b`"), vec![(Code::E0001, "\u{2028}")]);
        // No delimiter: `$` alone, `@param`, the name `r#x`, `#[`, a string, a character.
        assert_eq!(kinds("$ x").0, vec![Error, Ident, Eof]);
        assert_eq!(kinds("@param r#x #[a]").0[..6], [At, Ident, Ident, Hash, Ident, Hash]);
        assert!(!kinds("\"\" 'a' '\\'' br\"x\"").0.contains(&ForeignStr));
        // A name before a delimiter is a name, and the delimiter opens (S-458).
        let both = kinds("br#\"x\"# f`x` r\"\"\"x\"\"\"").0;
        assert_eq!(both, vec![Ident, ForeignStr, Ident, ForeignStr, Ident, ForeignStr, Eof]);
        // A run of `#` that opens no delimiter is a `#` each; a delimiter
        // after a closing one opens (`"#` then `#"`).
        assert_eq!(kinds("### x").0, vec![Hash, Hash, Hash, Ident, Eof]);
        assert_eq!(kinds("r#\"a\"##\"b\"#").0, vec![ForeignStr, ForeignStr, Eof]);
        // A delimiter after a literal is no name against it (`r` of `r#"…"#`).
        let l = lex(FileId(0), "\"a\"r#\"b\"#");
        assert!(l.literals.touches().is_empty(), "{:?}", l.literals.touches());
    }

    #[test]
    fn a_character_literal_of_several_characters_notes_the_string() {
        let d = lex(FileId(0), "'abc'").diagnostics;
        assert_eq!(d.len(), 1);
        assert!(d[0].notes.iter().any(|n| n.message.contains("a string is written")), "{d:?}");
        assert!(lex(FileId(0), "'ab").diagnostics.iter().all(|d| d.notes.is_empty()));
    }

    #[test]
    fn line_comments_by_their_slashes() {
        assert_eq!(
            kinds("//! m\n/// d\n// c\n//// c\n////// c\n").0,
            vec![ModuleDoc, Newline, DocComment, Newline, Comment, Newline, Comment, Newline, Comment, Newline, Eof]
        );
    }

    #[test]
    fn the_reserved_words_are_keywords() {
        assert_eq!(kinds("clock when reset_if ser").0, vec![KwClock, KwWhen, KwResetIf, KwSer, Eof]);
        assert!(KwClock.reserved().is_some() && KwSer.reserved().is_some());
    }

    #[test]
    fn the_power_and_the_strict_equalities_are_one_token() {
        assert_eq!(kinds("a ** b === c !== d").0, vec![Ident, StarStar, Ident, EqEqEq, Ident, NotEqEq, Ident, Eof]);
        assert_eq!(kinds("a ==== b").0, vec![Ident, EqEqEq, Eq, Ident, Eof]);
        assert_eq!(kinds("x.f!=y").0, vec![Ident, Dot, Ident, NotEq, Ident, Eof]);
        // A block comment is read before `**` (§2.1).
        assert_eq!(kinds("/**/ a **/").0, vec![BlockComment, Ident, StarStar, Slash, Eof]);
    }

    #[test]
    fn escapes_are_one_grammar() {
        assert_eq!(errors(r#""\u{0}\u{10FFFF}\u{41}\n\t\r\0\\\"\'""#), vec![]);
        for bad in [r#""\u{1234567}""#, r#""\u{0000041}""#, r#""\u{D800}""#, r#""\u{}""#, r#""\u{41""#, r#""\u41""#] {
            assert_eq!(errors(bad).first().map(|e| e.0), Some(Code::E0001), "{bad}");
        }
        // An unknown escape takes the character after the `\` whole.
        assert_eq!(errors("\"\\音\""), vec![(Code::E0001, "\\音")]);
        assert_eq!(crate::literal::escape("u{41}x"), (Some('A'), 5));
        assert_eq!(crate::literal::escape("u{0000041}"), (None, 10));
        assert_eq!(crate::literal::escape("音"), (None, 3));
        assert_eq!(crate::literal::escape("\nx"), (None, 0));
        assert_eq!(crate::literal::char_value("'\\u{0000041}'"), '\u{FFFD}');
    }

    #[test]
    fn a_hole_holds_a_name_path() {
        for ok in
            ["{x}", "{p.x}", "{self.gain}", "{t.0}", "{MAX_VOICES}", "{cfg.N}", "{F32.PI}", "{Self.N}", "{s.type}"]
        {
            assert!(errors(&format!("\"{ok}\"")).is_empty(), "{ok}");
        }
        for bad in [
            "{}", "{ x }", "{x .y}", "{x + 1}", "{f(x)}", "{xs[0]}", "{1}", "{true}", "{_}", "{x.}", "{.x}", "{é}",
            "{if}",
        ] {
            let src = format!("\"{bad}\"");
            assert_eq!(errors(&src), vec![(Code::E0001, bad)], "{bad}");
        }
        let format = lex(FileId(0), "\"{x:.2}\"").diagnostics;
        assert!(format[0].notes[0].message.contains("no format"), "{format:?}");
        // A reserved word at the head is E0200 at the word (S-371); after a `.` it is a name.
        assert_eq!(errors("\"a{clock}b\""), vec![(Code::E0200, "clock")]);
        assert!(errors("\"{s.clock}\"").is_empty());
        // The lexer keeps the path of each hole.
        let l = lex(FileId(0), "\"a{t.0}b{x}\"");
        let paths: Vec<Vec<&str>> = l
            .literals
            .holes()
            .iter()
            .map(|h| h.path.iter().flatten().map(|s| &"\"a{t.0}b{x}\""[s.start as usize..s.end as usize]).collect())
            .collect();
        assert_eq!(paths, vec![vec!["t", "0"], vec!["x"]]);
    }

    /// Each line of each file of the repository, and the lines of a tuple
    /// index after a `.`, a `#` after a `#` and a name before a literal,
    /// lexed anew from its first token ([`line_of`]) to its line break: the
    /// tokens are those of the file. The same pairs over a line break too
    /// (a `.`, a `#` or a name that ends a line, and a number, a `#"` or a
    /// string that starts the next): the lexer does not look back over it.
    #[test]
    fn a_line_lexed_anew_reads_its_tokens() {
        let mut files = crate::cst_tests::repo_files();
        let own = [
            "  t.0 .1\n  t.0.0 .1 .2\n",
            "  ##\"a\"##\n x\n",
            "  f\"{x}\"\n  \"a\"_s\n",
            // Over a line break, the line after with and without its indentation.
            "  t.\n  1.5\n  t.\n1.5\n  t .\n0x1F\n",
            "  #\n#\"a\"#\n  #\n  ##\"b\"##\n",
            "  f\n\"x\"\n  f\n  'c'\n  r\n\"{y}\"\n",
        ];
        for (k, src) in own.iter().enumerate() {
            files.push((format!("own {k}"), src.to_string()));
        }
        let mut lines = 0;
        for (name, text) in &files {
            let tokens = lex(FileId(0), text).tokens;
            let mut k = 0;
            while k < tokens.len() {
                assert_eq!(line_of(&tokens, k), k, "{name}");
                let n = (k..tokens.len()).find(|&n| matches!(tokens[n].kind, Newline | Eof)).unwrap();
                let (a, b) = (tokens[k].span.start, tokens[n].span.end);
                let anew = lex(FileId(0), &text[a as usize..b as usize]).tokens;
                let moved: Vec<(TokenKind, u32, u32)> =
                    anew.iter().map(|t| (t.kind, t.span.start + a, t.span.end + a)).collect();
                let own: Vec<(TokenKind, u32, u32)> =
                    tokens[k..=n].iter().map(|t| (t.kind, t.span.start, t.span.end)).collect();
                let len = own.len() - usize::from(tokens[n].kind == Eof);
                assert_eq!(
                    moved.iter().take(len).collect::<Vec<_>>(),
                    own[..len].iter().collect::<Vec<_>>(),
                    "{name}: the line at {a} read anew (left) and in the file"
                );
                lines += 1;
                k = n + 1;
            }
        }
        assert!(lines > 10_000, "only {lines} lines");
    }
}
