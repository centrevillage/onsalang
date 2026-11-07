//! The guard reading of a pattern ([`reads_as_pattern`], §7, §18.1): the
//! parser's own grammar of the patterns, with the guard forms read as
//! `Error` nodes where a reading of the file fails at them.

use super::*;

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ guard reading

    /// Close `m`, a guard form from the token at `first`, as an `Error` node.
    pub(super) fn guarded(&mut self, m: Marker, first: u32, form: Guarded) -> Completed {
        let c = self.complete(m, NodeKind::Error);
        if let Some(g) = &mut self.guard {
            g.forms.push((first, form));
        }
        c
    }

    /// A range (§7): its tokens to the end of the alternative, `sym` and
    /// `end` its symbol and its end among the tokens that are no trivia
    /// ([`pattern_alternative`]). `..` alone is no form.
    pub(super) fn guard_range(&mut self, sym: usize, end: usize) -> PResult<Completed> {
        let code: Vec<usize> =
            (self.pos..self.tokens.len()).filter(|&k| !self.tokens[k].kind.is_trivia()).take(end).collect();
        if sym == 0 && end == 1 {
            return Err(self.fail(Want::Pattern, "a pattern"));
        }
        let (first, symbol) = (self.tokens[code[0]].span.start, self.tokens[code[sym]].span.start);
        let m = self.start(NodeKind::Error)?;
        while self.peek_index() <= code[end - 1] {
            self.bump();
        }
        Ok(self.guarded(m, first, Guarded::Range { sym: symbol }))
    }

    /// A float (`1.5`, `1.`, `.5`, `-(1.5)`) or a `-` before a constant
    /// (`-LIMIT`, `-(I64.MAX)`): `-`, `(`s, the number or the path and as
    /// many `)`s.
    pub(super) fn guard_number(&mut self) -> PResult<Completed> {
        let first = self.peek().span.start;
        let m = self.start(NodeKind::Error)?;
        let minus = self.eat(TokenKind::Minus).is_some();
        let mut opens = 0;
        while minus && self.eat(TokenKind::LParen).is_some() {
            opens += 1;
        }
        let t = self.peek();
        let i = self.peek_index();
        match t.kind {
            TokenKind::Float => {
                self.bump();
            }
            TokenKind::ForeignLit if self.literals.number(t.span).is_some_and(|n| n.number.is_float()) => {
                self.bump();
            }
            TokenKind::Dot if self.tokens[i + 1].kind == TokenKind::Int && !self.gap(i + 1).is_some() => {
                self.bump();
                self.bump();
            }
            TokenKind::Ident | TokenKind::KwSelfType if minus => {
                let path = self.parse_path("a pattern")?;
                if !crate::naming::reads_constant(self.token_text(path.last)) {
                    return Err(self.fail(Want::Pattern, "a pattern"));
                }
            }
            _ => return Err(self.fail(Want::Pattern, "a pattern")),
        }
        for _ in 0..opens {
            if self.eat(TokenKind::RParen).is_none() {
                return Err(self.fail(Want::Pattern, "a pattern"));
            }
        }
        Ok(self.guarded(m, first, Guarded::Number))
    }

    /// `n @ p` (§7): the binding, the `@` and the pattern after it, if one
    /// reads there (`a @ ..` is still the form).
    pub(super) fn guard_at(&mut self) -> PResult<Completed> {
        // An `@` counts a level, as a form of a pattern (§2.5): a chain of
        // them nests no deeper than the limit (the `Error` node counts none).
        let ats = self.guard.as_ref().map_or(0, |g| g.ats);
        if self.level() + ats >= NESTING_LIMIT {
            return Err(self.fail(Want::Pattern, "a pattern"));
        }
        let first = self.peek().span.start;
        let m = self.start(NodeKind::Error)?;
        let b = self.start(NodeKind::BindPat)?;
        self.bump();
        self.complete(b, NodeKind::BindPat);
        self.bump();
        let s = self.snapshot();
        self.guard.iter_mut().for_each(|g| g.ats += 1);
        let read = self.parse_pattern_alt();
        self.guard.iter_mut().for_each(|g| g.ats -= 1);
        match read {
            Ok(_) => self.end_trial(),
            Err(_) => self.restore(s),
        }
        Ok(self.guarded(m, first, Guarded::At))
    }
}

/// The state of a guard reading ([`reads_as_pattern`]).
#[derive(Default)]
pub(super) struct GuardReading {
    /// The guard forms read as `Error` nodes, by the start of their first
    /// token; a trial undone drops its own ([`Parser::restore`]).
    pub(super) forms: Vec<(u32, Guarded)>,
    /// The `@`s whose right side is being read: each counts a level (§2.5).
    ats: u32,
}

/// A guard form of a guard reading ([`reads_as_pattern`]): an `Error` node.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Guarded {
    /// A range; `sym` is the start of its symbol.
    Range { sym: u32 },
    /// A float, or a `-` before a constant.
    Number,
    /// A string literal with holes.
    Str,
    /// `n @ p`: a `BindPat`, the `@`, and the pattern if one reads.
    At,
}

/// `f` on a cursor over `tokens`, a run of the full list of the tokens of
/// `text` ([`lexed_run`]), at no failure: what a later stage reads with the
/// guard forms' reader, from the tokens of its CST.
pub(crate) fn with_cursor<T>(
    file: FileId,
    text: &str,
    tokens: Vec<Token>,
    literals: &Literals,
    f: impl FnOnce(&crate::foreign::Cursor) -> T,
) -> Option<T> {
    Some(f(&Parser::new(file, text, lexed_run(file, tokens, literals)?).cursor(0, Want::Other)))
}

/// The run `tokens` of the full list of the tokens of a file, with the facts
/// of `literals` in it, as a lexer's output that ends at an `Eof` (its
/// positions are those of the file); `None` for no token.
fn lexed_run(file: FileId, mut tokens: Vec<Token>, literals: &Literals) -> Option<crate::Lexed> {
    let (first, end) = (tokens.first()?.span.start, tokens.last()?.span.end);
    if tokens.last().is_some_and(|t| t.kind != TokenKind::Eof) {
        tokens.push(Token { kind: TokenKind::Eof, span: Span::new(file, end, end) });
    }
    Some(crate::Lexed { tokens, diagnostics: Vec::new(), literals: literals.within(first, end) })
}

/// The guard reading of a pattern (§7, §18.1): the tokens `tokens` of a
/// file (a run of its full list) read by the parser's own grammar, the guard
/// forms read as `Error` nodes ([`Guarded`]) where the parser fails at them.
/// One alternative from the first token when not `whole`, else the whole
/// run as a pattern. Its diagnostics are not kept; `None` when it does not
/// read. The tree's root is a `SourceFile` whose first node is the pattern.
pub(crate) fn reads_as_pattern(
    file: FileId,
    text: &str,
    tokens: Vec<Token>,
    literals: &Literals,
    whole: bool,
) -> Option<(crate::cst::Cst, Vec<(u32, Guarded)>)> {
    let first = tokens.first()?.span.start;
    let mut p = Parser::new(file, text, lexed_run(file, tokens, literals)?);
    p.nl = vec![false];
    p.guard = Some(GuardReading::default());
    let root = p.enter_unit(NodeKind::SourceFile, first);
    let read = if whole { p.parse_pattern() } else { p.parse_pattern_alt() };
    if read.is_err() || (whole && !p.at(TokenKind::Eof)) {
        return None;
    }
    p.complete(root, NodeKind::SourceFile);
    let goes_on = vec![false; p.all.len()];
    let forms = p.guard.take().unwrap_or_default().forms;
    Some((crate::cst::build(p.all, goes_on, p.events), forms))
}
