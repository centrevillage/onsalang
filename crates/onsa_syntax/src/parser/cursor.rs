//! The cursor of the parser: the tokens it reads and skips under the
//! newline context (§2.5), the openers written apart (S-89) and the empty
//! brackets (S-513).

use super::*;

/// The rule of the empty brackets (§2.5, S-513, [`Parser::empty_brackets`]).
const EMPTY_BRACKETS_RULE: &str = "a variant with no fields, a declaration with no type parameters and a handler with no parameters are written without brackets, and so are their uses in `with` and in a pattern: `A`, `fn f()`, `handler h: Ask`, `with h`, `E.A` (§2.5)";

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ cursor

    pub(super) fn significant(&self) -> bool {
        *self.nl.last().unwrap()
    }

    pub(super) fn with_nl<T>(&mut self, significant: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        self.nl.push(significant);
        let r = f(self);
        self.nl.pop();
        r
    }

    /// Index of the next token that is not trivia under the current context:
    /// where a newline is significant, a newline that goes on with the line
    /// is trivia too ([`Lines::goes_on`], §2.5).
    pub(super) fn peek_index(&self) -> usize {
        self.skip_trivia(self.pos)
    }

    /// The first token from `i` that is not trivia under the current context.
    pub(super) fn skip_trivia(&self, mut i: usize) -> usize {
        loop {
            match self.tokens[i].kind {
                k if k.is_line_comment() => i += 1,
                TokenKind::Newline if !self.significant() || self.lines.goes_on(i) => i += 1,
                _ => return i,
            }
        }
    }

    pub(super) fn peek(&self) -> Token {
        self.tokens[self.peek_index()]
    }

    pub(super) fn peek_kind(&self) -> TokenKind {
        self.peek().kind
    }

    /// What separates the next token from the token before it.
    pub(super) fn peek_gap(&self) -> Gap {
        self.gap(self.peek_index())
    }

    /// The next token is a member `.` with a blank before it, or a blank or a
    /// line break after it (§2.5, S-203, S-353): the one test, for the chain
    /// of an expression and for a path (a type, a pattern, a `use`, an
    /// `impl`). The parser fails at it ([`Want::Postfix`]), and the table names
    /// the form (`space_around_dot`, `newline_after_dot`).
    pub(super) fn dot_apart(&self) -> bool {
        let i = self.peek_index();
        self.tokens[i].kind == TokenKind::Dot && (self.gap(i) == Gap::Space || self.gap_after(i).is_some())
    }

    /// The token after `tokens[i]`, newlines and comments skipped.
    pub(super) fn next_code(&self, i: usize) -> usize {
        let mut j = i + 1;
        while j + 1 < self.tokens.len()
            && (self.tokens[j].kind == TokenKind::Newline || self.tokens[j].kind.is_line_comment())
        {
            j += 1;
        }
        j.min(self.tokens.len() - 1)
    }

    /// What separates `tokens[i]` from the token after it ([`Lines::after`]).
    pub(super) fn gap_after(&self, i: usize) -> Gap {
        self.lines.after(i)
    }

    /// What separates `tokens[i]` from the token before it ([`Lines::before`]).
    pub(super) fn gap(&self, i: usize) -> Gap {
        self.lines.before(i)
    }

    /// Index of the token after `peek()` (same skipping rules).
    pub(super) fn peek2_index(&self) -> usize {
        let i = self.peek_index();
        if self.tokens[i].kind == TokenKind::Eof { i } else { self.skip_trivia(i + 1) }
    }

    /// The token after `peek()` (same skipping rules).
    pub(super) fn peek2(&self) -> Token {
        self.tokens[self.peek2_index()]
    }

    /// The next token ignoring newlines regardless of context.
    pub(super) fn peek_past_newlines(&self) -> Token {
        self.tokens[self.past_newlines()]
    }

    /// Index of [`Parser::peek_past_newlines`].
    pub(super) fn past_newlines(&self) -> usize {
        let mut i = self.pos;
        loop {
            match self.tokens[i].kind {
                k if k == TokenKind::Newline || k.is_line_comment() => i += 1,
                _ => return i,
            }
        }
    }

    pub(super) fn bump(&mut self) -> Token {
        let i = self.peek_index();
        let t = self.tokens[i];
        if t.kind != TokenKind::Eof {
            self.pos = i + 1;
            self.last_end = t.span.end;
            self.closed.clear();
            self.events.push(Event::Token(self.full[i]));
            if is_opening(t.kind) {
                self.braces.push(i);
            } else if is_closing(t.kind) {
                close_bracket(&mut self.braces, &self.tokens, t.kind, 0);
            }
        } else {
            self.pos = i;
        }
        t
    }

    pub(super) fn at(&self, kind: TokenKind) -> bool {
        self.peek_kind() == kind
    }

    pub(super) fn eat(&mut self, kind: TokenKind) -> Option<Token> {
        if self.at(kind) { Some(self.bump()) } else { None }
    }

    /// Whether the next token is the postfix opener `open` (`(`, `[`, or the
    /// mark `!` / `~` of a call) written right after the token before it
    /// (§2.5, S-89: the arguments of a call, an index, type arguments, the
    /// parameters of a declaration and of an anonymous function, a function
    /// type, a pattern, an attribute, the fields of a variant, the arguments
    /// of a handler, S-412). An opener after a blank or a line break is not
    /// read on: it is recorded with whether the token before ends a path of
    /// names (`by_name`, S-399) and whether an expression is before it
    /// (`expr`), and the grammar fails at it where it fails; the table names
    /// the form there ([`Detached`]). Two openers are not asked here: the
    /// `(` after `pub` (a visibility of another language whatever the blank,
    /// [`Parser::parse_vis`], S-248, S-417), and the `(` of the tuple struct
    /// `struct P (I32)` (the table's `tuple_struct`, S-39).
    pub(super) fn touches(&mut self, open: TokenKind, by_name: bool, expr: bool) -> bool {
        let at = self.peek_index();
        if self.tokens[at].kind != open {
            return false;
        }
        if !self.gap(at).is_some() {
            return true;
        }
        // The site that read the opener first judges it: after `with h`,
        // the `handle` expression is no callee, but `h` takes the list.
        if self.detached.is_none_or(|d| d.at != at) {
            self.detached = Some(Detached { at, by_name, expr, required: false });
        }
        false
    }

    /// The opener `open` of a list that is required here (the parameters of
    /// a declaration or an anonymous function, a function type): one that a
    /// blank or a line break keeps apart from the token before it is the
    /// E0020 of [`Parser::touches`], with the gap taken out (S-89, S-412).
    pub(super) fn opens(&mut self, open: TokenKind) -> PResult<Token> {
        if self.touches(open, true, false) {
            return Ok(self.bump());
        }
        let at = self.peek_index();
        if let Some(d) = self.detached.as_mut().filter(|d| d.at == at) {
            d.required = true;
        }
        Err(self.unexpected(open.describe()))
    }

    /// [`Parser::touches`] for the list that `open` opens at a place that
    /// writes no empty list (§2.5, S-513: the fields of a variant, the type
    /// parameters of a declaration, the arguments of `with h(…)`, the
    /// elements of a pattern `E.A(…)`), after [`Parser::refuse_empty`].
    pub(super) fn touches_bare(&mut self, open: TokenKind) -> PResult<bool> {
        self.refuse_empty(open)?;
        Ok(self.touches(open, true, false))
    }

    /// The E0002 of [`Parser::empty_brackets`] for the empty brackets
    /// ([`crate::scan::empty_brackets`]) that `open` opens right after the
    /// token before it, at a place that writes no empty list (§2.5, S-513;
    /// also the parameters of a handler). Empty brackets after a gap are the
    /// gap's E0020 first ([`Parser::touches`]; two errors, §18.1).
    pub(super) fn refuse_empty(&mut self, open: TokenKind) -> PResult<()> {
        let at = self.peek_index();
        match crate::scan::empty_brackets(&self.tokens, at) {
            Some(close) if self.tokens[at].kind == open && !self.gap(at).is_some() => {
                Err(self.empty_brackets(at, close))
            }
            _ => Ok(()),
        }
    }

    /// The E0002 of the empty brackets from token `open` to token `close`
    /// (§2.5, S-513): the candidate takes them out, and with a comment
    /// between them there is none, the note giving the rule.
    pub(super) fn empty_brackets(&mut self, open: usize, close: usize) -> ParseError {
        let span = Span::new(self.file, self.tokens[open].span.start, self.tokens[close].span.end);
        let mut d = Diagnostic::new(Stage::Syntax, Code::E0002, span, "empty brackets are not written here")
            .with_found(self.src(span).to_string())
            .with_rule(EMPTY_BRACKETS_RULE);
        if !(open + 1..close).any(|k| self.tokens[k].kind.is_comment()) {
            d = d.with_fix(Fix::delete("remove the empty brackets", span));
        }
        self.report(d);
        ParseError
    }

    /// The closing bracket `close` of a list of `list` after its elements:
    /// any other token is the E0002 of the missing `,` or of what does not go
    /// there ([`Want::Separator`], S-384).
    pub(super) fn close_list(&mut self, list: NodeKind, close: TokenKind) -> PResult<Token> {
        if self.at(close) {
            return Ok(self.bump());
        }
        Err(self.fail(Want::Separator(list), &format!("`,` or {}", close.describe())))
    }

    pub(super) fn skip_newlines(&mut self) {
        while matches!(self.peek_kind(), TokenKind::Newline) {
            self.bump();
        }
    }

    pub(super) fn token_text(&self, t: Token) -> &'a str {
        &self.text[t.span.start as usize..t.span.end as usize]
    }

    pub(super) fn is_ident(&self, t: Token, text: &str) -> bool {
        t.kind == TokenKind::Ident && self.token_text(t) == text
    }

    pub(super) fn span_from(&self, start: u32) -> Span {
        Span::new(self.file, start, self.last_end.max(start))
    }

    pub(super) fn src(&self, span: Span) -> &'a str {
        &self.text[span.start as usize..span.end as usize]
    }
}
