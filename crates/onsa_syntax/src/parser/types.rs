//! The types, their clocks and type arguments.

use super::*;

/// Whether the clock written after a type is read with it
/// ([`Parser::parse_type_with`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ClockAfter {
    /// `F32 at sample` (§11.3): at every type position but the type of `as`.
    Read,
    /// The type of `as`, whose `at` is the clock of the cast (E0011, §3.1).
    Skip,
}

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ types

    /// A type and the clock written after it ([`ClockAfter::Read`]).
    pub(super) fn parse_type(&mut self) -> PResult<Completed> {
        Ok(self.parse_type_with(ClockAfter::Read)?.0)
    }

    /// A type with no clock after it ([`ClockAfter::Skip`]).
    pub(super) fn parse_bare_type(&mut self) -> PResult<Completed> {
        Ok(self.parse_type_with(ClockAfter::Skip)?.0)
    }

    /// A type, the clock after it when `clock` reads it, and the number of
    /// its type arguments when it is a path type. After the result of a
    /// function type the clock is the result's (S-367). Where a clock goes
    /// (the input or output of a flow or a function) and where it does not
    /// (a binding, a type: E0020) is decided on the tree after parsing
    /// (`crate::foreign`, S-356).
    pub(super) fn parse_type_with(&mut self, clock: ClockAfter) -> PResult<(Completed, usize)> {
        let read = self.parse_type_and_args()?;
        if clock == ClockAfter::Read && self.at(TokenKind::KwAt) {
            self.parse_clock()?;
        }
        Ok(read)
    }

    /// `at name`: a clock (§11.3). The name is read as it is; which names
    /// are clocks the names stage looks up (S-359: an unknown one is its
    /// E0302).
    pub(super) fn parse_clock(&mut self) -> PResult<()> {
        let m = self.start(NodeKind::Clock)?;
        self.bump();
        self.parse_ident("the name of a clock")?;
        self.complete(m, NodeKind::Clock);
        Ok(())
    }

    /// A type, and the number of its type arguments when it is a path type.
    fn parse_type_and_args(&mut self) -> PResult<(Completed, usize)> {
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
                // `fn name` declares a function, which no type is: the error
                // is at the `fn` (its `rt`), so that the recovery may start
                // the next unit there (§18.1, S-947, R-396).
                let f = if self.at(TokenKind::KwRt) { self.peek2_index() } else { self.peek_index() };
                if self.tokens[f].kind == TokenKind::KwFn
                    && declares_a_function(TokenKind::KwFn, self.tokens[self.skip_trivia(f + 1)].kind)
                {
                    return Err(self.unexpected_fn("a type"));
                }
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
    /// expression (§4.5). An empty list is E0002, whose candidate takes it
    /// out with the `::` before it (§2.5, S-548).
    pub(super) fn parse_type_args(&mut self) -> PResult<usize> {
        let close = TokenKind::RBracket;
        if self.at(close) {
            let open = self.pos - 1;
            let before = (0..open).rev().find(|&k| !self.tokens[k].kind.is_trivia());
            let from = before.filter(|&k| self.tokens[k].kind == TokenKind::ColonColon).unwrap_or(open);
            let what = ("an empty list of type arguments", EMPTY_TYPE_ARGS_RULE, "remove the empty list");
            self.report_empty((open, self.peek_index()), from, what);
            return Err(ParseError);
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
    /// it too. An element that the tokens show to be an expression
    /// ([`Parser::goes_on_as_expression`]) is not tried as a type (R-417).
    fn parse_type_arg(&mut self) -> PResult<()> {
        if !self.goes_on_as_expression(self.peek_index()) {
            return self.try_type_arg();
        }
        let m = self.start(NodeKind::ConstArg)?;
        self.parse_expr()?;
        self.complete(m, NodeKind::ConstArg);
        Ok(())
    }

    /// [`Parser::parse_type_arg`] of an element that may be a type: a trial
    /// reading as a type, then as an expression.
    fn try_type_arg(&mut self) -> PResult<()> {
        let s = self.snapshot();
        let as_type = self.parse_type();
        // A type followed by `::` keeps its reading: `Option::[I32]` in a
        // list is the mark in a type position (E0020).
        let next = self.peek_index();
        let ends = !continues_an_expression(self.tokens[next].kind, self.gap(next));
        // A list of type arguments the type opened (`Option[…]`): an
        // expression reads its brackets as an index, so its error stays the
        // type's. Parentheses are not: `(1 + 2) * 3` is a constant.
        let opened_a_list =
            || self.events[s.events..].iter().any(|e| matches!(e, Event::Start { kind: Some(NodeKind::TypeArgs), .. }));
        match as_type {
            Ok(_) if ends => return Ok(()),
            // `_` is no type (§2.2) and no constant: `pair::[U8, _]` is E0002 (§4.5).
            Err(ParseError)
                if self.diagnostics[s.diagnostics..].iter().any(|d| d.code != Code::E0002)
                    || opened_a_list()
                    || self.tokens[s.pos..]
                        .iter()
                        .find(|t| !t.kind.is_trivia())
                        .is_some_and(|t| t.kind == TokenKind::Underscore) =>
            {
                return Err(ParseError);
            }
            _ => self.restore(s),
        }
        let m = self.start(NodeKind::ConstArg)?;
        self.parse_expr()?;
        self.complete(m, NodeKind::ConstArg);
        Ok(())
    }

    /// Whether the type argument at `at` is an expression by its tokens
    /// alone (§4.5, R-417): a token that starts an expression and no type (a
    /// number, `-`, a string, `if`), or a head (a path of names with the
    /// `[…]` or `::[…]` after it, or a bracket) and its clock with an
    /// operator or a postfix after them ([`continues_an_expression`]). A
    /// bracket with nothing after it asks the same of the first element in
    /// it (`(Rg[F32, 4].CAP)`). Else the element may be a type, and is tried.
    /// The two spellings of a list read alike, so that no candidate turns
    /// one reading into the other; each token is passed by one lookahead.
    fn goes_on_as_expression(&self, mut at: usize) -> bool {
        use TokenKind::*;
        let brackets = crate::scan::Brackets::of(&self.brackets, &self.tokens);
        loop {
            let kind = self.tokens[at].kind;
            if !crate::starts::starts_type(kind) {
                return kind == ForeignLit || (starts_operand(kind) && kind != Underscore);
            }
            // The head ends at its last name, or at the bracket that closes
            // the one it opens (a bracket that does not close: maybe a type).
            let (mut last, mut open) = (at, matches!(kind, LParen | LBracket).then_some(at));
            if matches!(kind, Ident | KwSelfType) {
                while let Some(name) = self.path_goes_on(last + 1) {
                    last = name;
                }
                let colons = self.skip_trivia(last + 1);
                let o = if self.tokens[colons].kind == ColonColon { self.skip_trivia(colons + 1) } else { colons };
                open = (self.tokens[o].kind == LBracket && (o != colons || self.gap(o) == Gap::None)).then_some(o);
            } else if open.is_none() {
                return false;
            }
            let end = match open {
                Some(o) => match brackets.closing(o) {
                    Some(close) => close,
                    None => return false,
                },
                None => last,
            };
            let mut next = self.skip_trivia(end + 1);
            if self.tokens[next].kind == KwAt && self.tokens[self.skip_trivia(next + 1)].kind == Ident {
                next = self.skip_trivia(self.skip_trivia(next + 1) + 1);
            }
            if continues_an_expression(self.tokens[next].kind, self.gap(next)) {
                return true;
            }
            if !matches!(kind, LParen | LBracket) {
                return false;
            }
            at = self.skip_trivia(at + 1);
        }
    }
}

/// The rule of an empty list of type arguments (§2.5, §4.5, S-548).
const EMPTY_TYPE_ARGS_RULE: &str = "a name with no type arguments is written without the list, and without its `::` in an expression: `f(1)`, `Buf.zeroed(4)`, `P` (§2.5, §4.5)";

/// Whether a token of `kind` after `gap` goes on with an expression before
/// it: a binary operator, a range symbol (whose place the table judges,
/// `range_outside_header`), `as`, a member `.`, `?`, or a postfix opener
/// written right after it (a type argument, [`Parser::parse_type_arg`]).
fn continues_an_expression(kind: TokenKind, gap: Gap) -> bool {
    use TokenKind::*;
    kind.binop().is_some()
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
