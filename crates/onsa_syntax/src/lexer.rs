//! Lexer (spec §2). Never stops: invalid input yields `Error` tokens and
//! E0001 diagnostics, and lexing continues. A form of another language
//! (a block comment, `1.`, `1u8`, `++`, `::`, ...) is a token of its own and
//! no diagnostic here: the parser accepts it nowhere, and the table of those
//! forms ([`crate::foreign`]) says what the failure is (E0020 or E0002).

use onsa_diag::{Code, Diagnostic, FileId, Span, Stage};

use crate::token::{Token, TokenKind};

/// Result of lexing one file.
#[derive(Debug, Default)]
pub struct Lexed {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
    /// The holes of the string literals that a `}` closes (`{x}`, also of a
    /// form an interpolation may not have, `{X}`), from the `{` to after the
    /// `}`: the parser tells an interpolation in the name of a `test` by them
    /// (spec §11.8, S-244).
    pub holes: Vec<Span>,
}

pub fn lex(file: FileId, text: &str) -> Lexed {
    let mut lx = Lexer { file, text, bytes: text.as_bytes(), pos: 0, out: Lexed::default() };
    lx.run();
    lx.out
}

struct Lexer<'a> {
    file: FileId,
    text: &'a str,
    bytes: &'a [u8],
    pos: usize,
    out: Lexed,
}

impl<'a> Lexer<'a> {
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn peek_at(&self, n: usize) -> Option<u8> {
        self.bytes.get(self.pos + n).copied()
    }

    fn span(&self, start: usize) -> Span {
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
            match b {
                b'\n' => {
                    self.pos += 1;
                    self.push(TokenKind::Newline, start);
                }
                b' ' | b'\t' | b'\r' => {
                    while matches!(self.peek(), Some(b' ' | b'\t' | b'\r')) {
                        self.pos += 1;
                    }
                    self.push(TokenKind::Whitespace, start);
                }
                b'/' if self.peek_at(1) == Some(b'/') => self.comment(start),
                b'/' if self.peek_at(1) == Some(b'*') => self.block_comment(start),
                b'"' => self.string(start),
                b'\'' => self.char_lit(start),
                b'0'..=b'9' => self.number(start),
                _ if is_ident_start(b) => self.ident(start),
                _ => self.punct(start),
            }
        }
        let end = self.text.len();
        self.push(TokenKind::Eof, end);
    }

    fn comment(&mut self, start: usize) {
        let doc = self.peek_at(2) == Some(b'/') && self.peek_at(3) != Some(b'/');
        while let Some(b) = self.peek() {
            if b == b'\n' {
                break;
            }
            self.pos += 1;
        }
        self.push(if doc { TokenKind::DocComment } else { TokenKind::Comment }, start);
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
            } else {
                self.pos += 1;
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
        let text = &self.text[start..self.pos];
        let kind =
            if text == "_" { TokenKind::Underscore } else { TokenKind::keyword(text).unwrap_or(TokenKind::Ident) };
        self.push(kind, start);
    }

    fn number(&mut self, start: usize) {
        // After `.`, a digit run is a tuple index (§4.1): no float, no base prefix.
        let after_dot =
            self.out.tokens.last().is_some_and(|t| t.kind == TokenKind::Dot && t.span.end as usize == start);
        if after_dot {
            self.digits(|b| b.is_ascii_digit());
            self.push(TokenKind::Int, start);
            return;
        }
        if self.peek() == Some(b'0') && matches!(self.peek_at(1), Some(b'x' | b'b')) {
            let hex = self.peek_at(1) == Some(b'x');
            self.pos += 2;
            let n = if hex {
                self.digits(|b| b.is_ascii_hexdigit() || b == b'_')
            } else {
                self.digits(|b| matches!(b, b'0' | b'1' | b'_'))
            };
            if n == 0 {
                let span = self.span(start);
                self.error(Code::E0001, span, "number prefix without digits");
            }
            let kind = if self.suffix() { TokenKind::ForeignLit } else { TokenKind::Int };
            self.push(kind, start);
            return;
        }
        self.digits(|b| b.is_ascii_digit() || b == b'_');
        let mut float = false;
        if self.peek() == Some(b'.') {
            match self.peek_at(1) {
                Some(b) if b.is_ascii_digit() => {
                    self.pos += 1;
                    self.digits(|b| b.is_ascii_digit() || b == b'_');
                    float = true;
                }
                // `1..<n`, `1..=n`, `1...n`, `1.abs()`: the int ends here.
                Some(b'.') => {}
                Some(b) if is_ident_start(b) => {}
                _ => {
                    // `1.`: a form of another language.
                    self.pos += 1;
                    self.push(TokenKind::ForeignLit, start);
                    return;
                }
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            let save = self.pos;
            self.pos += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.pos += 1;
            }
            if self.digits(|b| b.is_ascii_digit()) == 0 {
                self.pos = save;
            } else {
                float = true;
            }
        }
        let kind = if self.suffix() {
            TokenKind::ForeignLit
        } else if float {
            TokenKind::Float
        } else {
            TokenKind::Int
        };
        self.push(kind, start);
    }

    /// `1u8`, `1.0f32`: a suffix is never valid (no typed literals, §2.4).
    /// The letters after the digits are read into the number, which is then
    /// a form of another language (`ForeignLit`) when the table of those
    /// forms knows the suffix ([`crate::foreign::is_type_suffix`]), and
    /// E0001 when it does not (`123abc`).
    fn suffix(&mut self) -> bool {
        if !self.peek().is_some_and(is_ident_start) {
            return false;
        }
        let start = self.pos;
        while self.peek().is_some_and(is_ident_continue) {
            self.pos += 1;
        }
        if crate::foreign::is_type_suffix(&self.text[start..self.pos]) {
            return true;
        }
        let span = Span::new(self.file, start as u32, self.pos as u32);
        self.error(Code::E0001, span, "a number has no suffix");
        false
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

    fn string(&mut self, start: usize) {
        self.pos += 1;
        loop {
            let Some(b) = self.peek() else {
                let span = self.span(start);
                self.error(Code::E0001, span, "unterminated string literal");
                break;
            };
            match b {
                b'"' => {
                    self.pos += 1;
                    break;
                }
                b'\n' => {
                    let span = self.span(start);
                    self.error(Code::E0001, span, "unterminated string literal");
                    break;
                }
                b'\\' => self.escape(),
                b'{' if self.peek_at(1) == Some(b'{') => self.pos += 2,
                b'}' if self.peek_at(1) == Some(b'}') => self.pos += 2,
                b'{' => {
                    // Interpolation: `{name}` or `{name.field...}` (§2.4)
                    let open = self.pos;
                    self.pos += 1;
                    let ok = self.interp_path();
                    if self.peek() == Some(b'}') {
                        self.pos += 1;
                        self.out.holes.push(Span::new(self.file, open as u32, self.pos as u32));
                        if !ok {
                            let span = Span::new(self.file, open as u32, self.pos as u32);
                            self.error(
                                Code::E0001,
                                span,
                                "interpolation must be `{name}` or `{name.field}`; expressions are not allowed",
                            );
                        }
                    } else {
                        let span = Span::new(self.file, open as u32, self.pos as u32);
                        self.error(Code::E0001, span, "unterminated interpolation; write `{{` for a literal brace");
                    }
                }
                b'}' => {
                    let span = Span::new(self.file, self.pos as u32, self.pos as u32 + 1);
                    self.error(Code::E0001, span, "lone `}` in string; write `}}` for a literal brace");
                    self.pos += 1;
                }
                _ => self.pos += 1,
            }
        }
        self.push(TokenKind::Str, start);
    }

    /// `name(.name)*` with snake_case names. Consumes up to `}` or an invalid byte.
    fn interp_path(&mut self) -> bool {
        let mut ok = true;
        loop {
            let seg = self.pos;
            while self.peek().is_some_and(is_ident_continue) {
                self.pos += 1;
            }
            let text = &self.text[seg..self.pos];
            if text.is_empty() || !text.bytes().next().is_some_and(|b| b.is_ascii_lowercase() || b == b'_') {
                ok = false;
            }
            match self.peek() {
                Some(b'.') => self.pos += 1,
                Some(b'}') | None => return ok,
                Some(b'\n') | Some(b'"') => return false,
                Some(_) => {
                    ok = false;
                    self.pos += 1;
                }
            }
        }
    }

    fn char_lit(&mut self, start: usize) {
        self.pos += 1;
        match self.peek() {
            Some(b'\\') => self.escape(),
            Some(b'\'') | Some(b'\n') | None => {
                let span = self.span(start);
                self.error(Code::E0001, span, "empty char literal");
            }
            Some(_) => {
                let c = self.text[self.pos..].chars().next().unwrap();
                self.pos += c.len_utf8();
            }
        }
        if self.peek() == Some(b'\'') {
            self.pos += 1;
        } else {
            // Possibly a lifetime or a multi-char literal from another language.
            while let Some(b) = self.peek() {
                if b == b'\'' {
                    self.pos += 1;
                    break;
                }
                if b == b'\n' {
                    break;
                }
                self.pos += 1;
            }
            let span = self.span(start);
            self.error(Code::E0001, span, "char literal must hold exactly one Unicode scalar value");
        }
        self.push(TokenKind::Char, start);
    }

    /// Escapes (S-19): `\n \t \r \0 \\ \" \' \u{XXXX}`.
    fn escape(&mut self) {
        let start = self.pos;
        self.pos += 1;
        match self.peek() {
            Some(b'n' | b't' | b'r' | b'0' | b'\\' | b'"' | b'\'') => self.pos += 1,
            Some(b'u') if self.peek_at(1) == Some(b'{') => {
                self.pos += 2;
                let n = self.digits(|b| b.is_ascii_hexdigit());
                let close = self.peek() == Some(b'}');
                if close {
                    self.pos += 1;
                }
                let valid = close && (1..=6).contains(&n) && {
                    let hex = &self.text[start + 3..self.pos - 1];
                    u32::from_str_radix(hex, 16).ok().and_then(char::from_u32).is_some()
                };
                if !valid {
                    let span = self.span(start);
                    self.error(Code::E0001, span, "invalid `\\u{...}` escape");
                }
            }
            _ => {
                if self.peek().is_some_and(|b| b != b'\n') {
                    self.pos += 1;
                }
                let span = self.span(start);
                self.error(Code::E0001, span, "unknown escape; allowed: \\n \\t \\r \\0 \\\\ \\\" \\' \\u{...}");
            }
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
            _ => {
                let c = self.text[self.pos..].chars().next().unwrap();
                self.pos += c.len_utf8();
                let span = self.span(start);
                self.error(Code::E0001, span, format!("invalid character `{}`", c.escape_default()));
                self.push(Error, start);
                return;
            }
        };
        self.pos += len;
        self.push(kind, start);
    }
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
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
        assert_eq!(kinds("0x").1, vec![Code::E0001]);
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
}
