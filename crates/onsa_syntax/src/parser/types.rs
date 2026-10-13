//! The types, their clocks and type arguments.

use super::*;

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ types

    /// A type and the clock written after it (`F32 at sample`, §11.3): the
    /// clock is read at every type position but the type of `as`
    /// ([`Parser::parse_bare_type`]); after the result of a function type it
    /// is the result's (S-367). Where it goes (the input or output of a
    /// flow or a function) and where it does not (a binding, a type: E0020)
    /// is decided on the tree after parsing (`crate::foreign`, S-356).
    pub(super) fn parse_type(&mut self) -> PResult<Completed> {
        let c = self.parse_type_ex()?.0;
        self.parse_clock_opt()?;
        Ok(c)
    }

    /// A type with no clock after it: the type of `as`, whose `at` is the
    /// clock of the cast (E0011, §3.1).
    pub(super) fn parse_bare_type(&mut self) -> PResult<Completed> {
        Ok(self.parse_type_ex()?.0)
    }

    pub(super) fn parse_clock_opt(&mut self) -> PResult<()> {
        if self.at(TokenKind::KwAt) {
            self.parse_clock()?;
        }
        Ok(())
    }

    /// `at name`: a clock (§11.3). The name is read as it is; which names
    /// are clocks W3-10 looks up (S-359: an unknown one is the names stage's
    /// E0302).
    pub(super) fn parse_clock(&mut self) -> PResult<()> {
        let m = self.start(NodeKind::Clock)?;
        self.bump();
        self.parse_ident("the name of a clock")?;
        self.complete(m, NodeKind::Clock);
        Ok(())
    }

    /// A type, and the number of its type arguments when it is a path type.
    pub(super) fn parse_type_ex(&mut self) -> PResult<(Completed, usize)> {
        let mut nargs = 0;
        let c = match self.peek_kind() {
            TokenKind::LParen => {
                let m = self.start(NodeKind::TupleType)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    if p.eat(TokenKind::RParen).is_some() {
                        return Ok(NodeKind::UnitType);
                    }
                    p.parse_type()?;
                    let Some(comma) = p.eat(TokenKind::Comma) else {
                        p.close_list(NodeKind::TupleType, TokenKind::RParen)?;
                        return Ok(NodeKind::ParenType);
                    };
                    if p.at(TokenKind::RParen) {
                        return Err(p.one_element(comma));
                    }
                    while !p.at(TokenKind::RParen) {
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::TupleType, TokenKind::RParen)?;
                    Ok(NodeKind::TupleType)
                })?;
                self.complete(m, kind)
            }
            TokenKind::LBracket => {
                let m = self.start(NodeKind::ArrayType)?;
                self.bump();
                self.with_nl(false, |p| {
                    p.parse_type()?;
                    p.expect(TokenKind::Semi)?;
                    p.parse_expr()?;
                    p.expect(TokenKind::RBracket)?;
                    Ok(())
                })?;
                self.complete(m, NodeKind::ArrayType)
            }
            TokenKind::KwRt | TokenKind::KwFn => {
                let m = self.start(NodeKind::FnType)?;
                self.eat(TokenKind::KwRt);
                self.expect(TokenKind::KwFn)?;
                let l = self.start(NodeKind::FnTypeParams)?;
                // S-412: the `(` after `fn` in a function type follows the
                // rule of the postfix `(` (a blank before it is E0020).
                self.opens(TokenKind::LParen)?;
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RParen) {
                        p.parse_mode();
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::FnTypeParams, TokenKind::RParen)?;
                    Ok(())
                })?;
                self.complete(l, NodeKind::FnTypeParams);
                if self.at_line_end(TokenKind::Arrow) {
                    self.bump();
                    // A clock after the result belongs to the result, as
                    // `uses` does (S-367): a clock in a type, E0020.
                    self.parse_type()?;
                }
                self.parse_effect_row_opt()?;
                self.complete(m, NodeKind::FnType)
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let m = self.start(NodeKind::PathType)?;
                let path = self.parse_path("a type")?;
                // A type name of another language that reads as a name (`i32`):
                // the one form the parser does not fail at by itself.
                if path.segments == 1
                    && let Some(d) = foreign::type_name(self.text, path.first)
                {
                    self.report(d);
                    return Err(ParseError);
                }
                if self.touches(TokenKind::LBracket, true, false) {
                    let a = self.start(NodeKind::TypeArgs)?;
                    self.bump();
                    nargs = self.with_nl(false, |p| p.parse_type_args())?;
                    self.complete(a, NodeKind::TypeArgs);
                }
                self.complete(m, NodeKind::PathType)
            }
            _ => return Err(self.fail(Want::Type, "a type")),
        };
        Ok((c, nargs))
    }

    /// The elements of a list of type arguments after its `[`, and its `]`:
    /// the one reading of the lists of a type position and of `::[…]` in an
    /// expression (§4.5). An empty list is E0002.
    pub(super) fn parse_type_args(&mut self) -> PResult<usize> {
        let close = TokenKind::RBracket;
        if self.at(close) {
            return Err(self.fail(Want::Type, "a type argument"));
        }
        let mut n = 0;
        while !self.at(close) {
            self.parse_type_arg()?;
            n += 1;
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.close_list(NodeKind::TypeArgs, close)?;
        Ok(n)
    }

    /// A type argument: a type, or a const argument written as a constant
    /// expression (`Ring[F32, 4]`, `Ring[F32, N * 2]`, spec §4.5, S-24,
    /// R-192). The element is a type when it reads as a type and no operator
    /// or postfix goes on after it ([`continues_an_expression`]); else it is
    /// read as an expression, whose constant rules are the later stages'
    /// (E0417, E0401). A constant's name (`TABLE_SIZE`, `cfg.N`) reads as a
    /// type; the later stages take it by the kind of the parameter. What
    /// follows a type is the list's error (`Option[I32 Bool]`: the missing
    /// `,` of a list of type arguments, S-384), and so is the error inside a
    /// list of type arguments the type opened (`Option[Option[I32 Bool]]`;
    /// the expression would read the brackets as an index and lose the list). A type that fails
    /// with a diagnostic of its own (a form of the table, E0020; E0006) keeps
    /// it too.
    fn parse_type_arg(&mut self) -> PResult<()> {
        let s = self.snapshot();
        let as_type = self.parse_type();
        // A type followed by `::` keeps its reading: `Option::[I32]` in a
        // list is the mark in a type position (E0020), and a constant
        // expression with `::[…]` waits for S-329.
        let next = self.peek_index();
        let ends = self.tokens[next].kind == TokenKind::ColonColon
            || !continues_an_expression(self.tokens[next].kind, self.gap(next));
        // A list of type arguments the type opened (`Option[…]`): an
        // expression reads its brackets as an index, so its error stays the
        // type's. Parentheses are not: `(1 + 2) * 3` is a constant.
        let opened_a_list =
            || self.events[s.events..].iter().any(|e| matches!(e, Event::Start { kind: Some(NodeKind::TypeArgs), .. }));
        match as_type {
            Ok(_) if ends => {
                self.end_trial();
                return Ok(());
            }
            // `_` is no type (§2.2) and no constant: `pair::[U8, _]` is E0002 (§4.5).
            Err(ParseError)
                if self.diagnostics[s.diagnostics..].iter().any(|d| d.code != Code::E0002)
                    || opened_a_list()
                    || self.tokens[s.pos..]
                        .iter()
                        .find(|t| !t.kind.is_trivia())
                        .is_some_and(|t| t.kind == TokenKind::Underscore) =>
            {
                self.end_trial();
                return Err(ParseError);
            }
            _ => self.restore(s),
        }
        let m = self.start(NodeKind::ConstArg)?;
        self.parse_expr()?;
        self.complete(m, NodeKind::ConstArg);
        Ok(())
    }

    /// Whether the tokens from the `[` at `open` read as a list of type
    /// arguments with two or more elements (a `[…]` that is no index, §4.5):
    /// a trial reading, undone whatever its result. Not inside another trial.
    pub(super) fn type_list_next(&mut self) -> bool {
        if self.trials > 0 {
            return false;
        }
        let s = self.snapshot();
        self.bump();
        let n = self.with_nl(false, |p| p.parse_type_args());
        self.restore(s);
        matches!(n, Ok(n) if n >= 2)
    }
}

/// Whether a token of `kind` after `gap` goes on with an expression before
/// it: a binary operator, a range symbol (whose place the table judges,
/// `range_outside_header`), `as`, a member `.`, `?`, or a postfix opener
/// written right after it (a type argument, [`Parser::parse_type_arg`]).
fn continues_an_expression(kind: TokenKind, gap: Gap) -> bool {
    use TokenKind::*;
    binop(kind)
        || !kind.range_readings().is_empty()
        || matches!(kind, KwAs | Dot | Question)
        || (matches!(kind, LParen | LBracket | Bang | Tilde) && gap == Gap::None)
}

/// Whether the tokens `all[first..=last]` of a file, a list in angle
/// brackets with its brackets written as `[ ]` (`swaps`: the index in `all`
/// of each bracket and what it becomes, `paths::angle_tokens`), read as a list
/// of type parameters (`params`) or of type arguments (R-193): read by the
/// parser's own grammar (one reading), as `reads_as_expr` reads an
/// expression. Its diagnostics are not kept.
pub(crate) fn reads_as_type_list(
    file: FileId,
    text: &str,
    all: &[Token],
    literals: &Literals,
    run: (usize, usize),
    swaps: &[(usize, &str)],
    params: bool,
) -> bool {
    let mut p = trial(file, text, all, literals, run, swaps);
    p.bump();
    let read = if params { p.parse_generic_list() } else { p.parse_type_args().map(|_| ()) };
    read.is_ok() && p.at(TokenKind::Eof) && p.diagnostics.is_empty()
}

/// Whether the tokens `all[first..=last]` of a file read as one type (the
/// element of a tuple struct, `tuple_struct`), by the parser's own grammar
/// as [`reads_as_type_list`] reads a list. Its diagnostics are not kept.
pub(crate) fn reads_as_type(file: FileId, text: &str, all: &[Token], literals: &Literals, run: (usize, usize)) -> bool {
    let mut p = trial(file, text, all, literals, run, &[]);
    p.parse_type().is_ok() && p.at(TokenKind::Eof) && p.diagnostics.is_empty()
}

/// A parser of the tokens `all[first..=last]` alone, the brackets of
/// `swaps` written as `[ ]`, newlines not significant.
fn trial<'a>(
    file: FileId,
    text: &'a str,
    all: &[Token],
    literals: &Literals,
    (first, last): (usize, usize),
    swaps: &[(usize, &str)],
) -> Parser<'a> {
    let mut tokens = Vec::new();
    for (i, t) in all.iter().enumerate().take(last + 1).skip(first) {
        let bracket = |kind, start: u32, end: u32| Token { kind, span: Span::new(file, start, end) };
        match swaps.iter().find(|s| s.0 == i).map(|s| s.1) {
            // `>>` closes two lists, `>=` one before its `=` (the end of the run).
            Some("]]") => {
                tokens.push(bracket(TokenKind::RBracket, t.span.start, t.span.start + 1));
                tokens.push(bracket(TokenKind::RBracket, t.span.start + 1, t.span.end));
            }
            Some(s) if s.starts_with(']') => tokens.push(bracket(TokenKind::RBracket, t.span.start, t.span.start + 1)),
            Some(_) => tokens.push(bracket(TokenKind::LBracket, t.span.start, t.span.end)),
            None => tokens.push(*t),
        }
    }
    let end = all[last].span.end;
    tokens.push(Token { kind: TokenKind::Eof, span: Span::new(file, end, end) });
    let literals = literals.within(all[first].span.start, end);
    let mut p = Parser::new(file, text, crate::Lexed { tokens, diagnostics: Vec::new(), literals });
    p.nl = vec![false];
    p
}
