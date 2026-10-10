//! The lines and blanks of the tokens the parser reads (§2.5): what
//! separates each token from the tokens around it and whether a line break
//! goes on with its line ([`Lines`]), found once after the lexer and read by
//! the parser, its recovery and the table of the forms of other languages
//! ([`crate::foreign`]) alike (D-13, D-15); the one judgement of a line that
//! goes on ([`continues`]). It reads the tokens only: what a token starts is
//! [`crate::starts`], and nothing here reads the lexer, the parser or the
//! table.

use crate::starts::ends_operand;
use crate::token::{Gap, Token, TokenKind};

/// The line facts of each token the parser reads (the lexer's without the
/// whitespace), computed once ([`code_tokens`]): what separates it from the
/// token before and from the token after, and, for a newline, whether it
/// goes on with its line. The parser, its recovery and the table ask these
/// and judge no gap again.
#[derive(Debug, Clone, Default)]
pub(crate) struct Lines {
    line: Vec<Line>,
}

#[derive(Debug, Clone, Copy)]
struct Line {
    /// What separates the token from the token before it ([`crate::token::gap_before`]).
    before: Gap,
    /// What separates the token from the token after it: a newline or a line
    /// comment after it is a line break.
    after: Gap,
    /// A newline that goes on with its line ([`continues`]).
    goes_on: bool,
}

/// The tokens the parser reads (the lexer's `all` without the whitespace),
/// the index in `all` of each, and their line facts ([`Lines`]): one pass
/// over the full list, then one each way over the tokens, so the line facts
/// are linear in the file however long a run of comment lines and blank
/// lines is.
pub(crate) fn code_tokens(all: &[Token]) -> (Vec<Token>, Vec<u32>, Lines) {
    let mut tokens = Vec::with_capacity(all.len());
    let mut full = Vec::with_capacity(all.len());
    let mut line = Vec::with_capacity(all.len());
    // The gap before each token ([`Gap::then`], as `gap_before` reads it).
    let mut gap = Gap::None;
    for (i, t) in all.iter().enumerate() {
        if t.kind != TokenKind::Whitespace {
            tokens.push(*t);
            full.push(i as u32);
            line.push(Line { before: gap, after: Gap::None, goes_on: false });
        }
        gap = gap.then(t.kind);
    }
    let lines = Lines::of(&tokens, line);
    (tokens, full, lines)
}

impl Lines {
    /// The facts of `tokens`, whose gaps before them are in `line`.
    fn of(tokens: &[Token], mut line: Vec<Line>) -> Lines {
        // Backwards: the gap after each token, and the first code token from
        // each token on.
        let mut next = vec![TokenKind::Eof; tokens.len()];
        let mut next_code = TokenKind::Eof;
        for (k, t) in tokens.iter().enumerate().rev() {
            line[k].after = match tokens.get(k + 1).map(|t| t.kind) {
                Some(TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment) => Gap::Newline,
                Some(_) => line[k + 1].before,
                None => Gap::None,
            };
            if t.kind.is_code() {
                next_code = t.kind;
            }
            next[k] = next_code;
        }
        // Forwards: the last two code tokens before each newline.
        let (mut two_back, mut prev) = (None, None);
        for (k, t) in tokens.iter().enumerate() {
            if t.kind == TokenKind::Newline {
                line[k].goes_on = prev.is_some_and(|p| continues(two_back, p, next[k]));
            } else if t.kind.is_code() {
                two_back = prev;
                prev = Some(t.kind);
            }
        }
        Lines { line }
    }

    /// What separates `tokens[i]` from the token before it.
    #[inline]
    pub(crate) fn before(&self, i: usize) -> Gap {
        self.line[i].before
    }

    /// What separates `tokens[i]` from the token after it (§2.5: a newline or
    /// a line comment after it is a line break).
    #[inline]
    pub(crate) fn after(&self, i: usize) -> Gap {
        self.line[i].after
    }

    /// Whether `tokens[i]` is at the head of its line: a line break, and no
    /// other token, is before it (blanks aside). The one test of a symbol at
    /// the head of a line (§2.5, S-124, S-335, S-374, S-380).
    #[inline]
    pub(crate) fn at_line_head(&self, i: usize) -> bool {
        self.line[i].before == Gap::Newline
    }

    /// Whether `tokens[i]` is a newline that goes on with its line
    /// ([`continues`]).
    #[inline]
    pub(crate) fn goes_on(&self, i: usize) -> bool {
        self.line[i].goes_on
    }

    /// The mark `::[` of type arguments in an expression at `tokens[i]`
    /// (§2.5, §4.5): `::` and `[` with no space or newline before either. The
    /// one test of the mark, for the parser and the table of the forms.
    pub(crate) fn type_args_mark(&self, tokens: &[Token], i: usize) -> bool {
        tokens.get(i).is_some_and(|t| t.kind == TokenKind::ColonColon)
            && tokens.get(i + 1).is_some_and(|t| t.kind == TokenKind::LBracket)
            && self.before(i) == Gap::None
            && self.before(i + 1) == Gap::None
    }
}

/// Whether a line break goes on with the line (§2.5, S-47, R-58, S-124,
/// S-335, S-374): `prev` is the last code token of the line (`before` the one
/// before it) and `next` the first of the next line, the lines of comments
/// and the blank lines passed. The line goes on after a binary operator (a
/// `-` / `^` only after an operand: a prefix one at the end of a line is the
/// error of S-369), `..<` / `..=`, `=` or `->`, and before a `.` or `uses`. A
/// line of attributes goes on too, which the tokens do not show
/// (`Parser::parse_attrs`, S-121). The one judgement, which [`code_tokens`]
/// makes for every newline: the parser (`Parser::peek_index`), its recovery
/// (S-47) and the table read [`Lines::goes_on`].
pub fn continues(before: Option<TokenKind>, prev: TokenKind, next: TokenKind) -> bool {
    use TokenKind::*;
    let binary = match prev {
        Minus | Caret => before.is_some_and(ends_operand),
        k => k.binop().is_some(),
    };
    binary || prev.range_end().is_some() || matches!(prev, Eq | Arrow) || matches!(next, Dot | KwUses)
}
