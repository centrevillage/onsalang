//! The expressions: the binary chains, prefixes, postfixes, primaries,
//! `if` and its branches, and the reading of a range end ([`reads_as_expr`]).

use super::*;

/// The rule of a `^` with no name right after it (§2.6, S-358).
const CARET_RULE: &str = "a prefix `^` is the mark of a name, written right before the name of a `let` of the flow (`prev~(^y)`), and no operator; the binary `^` is the exclusive or (§2.6)";

/// The rule of an `if~` with no `else` (§11.5, S-355).
const IF_TILDE_ELSE_RULE: &str =
    "`if~` evaluates every branch and takes one, so its chain ends with an `else` block (§11.5)";

/// The note of a handler written in place with no body (§8.3, S-421).
const HANDLER_BODY_RULE: &str = "after the name of an effect, the body `{ ... }` of a handler written in place follows on its line (§8.3); a named handler is a `snake_case` name (§2.3)";

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ expressions

    pub(super) fn parse_expr(&mut self) -> PResult<Completed> {
        self.parse_expr_inner(false)
    }

    /// Binary chain, flat in the CST (§3.1: the AST reads it as a tree,
    /// `lower.rs`; the groups are checked in `groups.rs`).
    /// Its height is the one of the tree of §3.1 ([`ChainHeight`]).
    pub(super) fn parse_expr_inner(&mut self, allow_range: bool) -> PResult<Completed> {
        let first = self.parse_cast()?;
        let mut expr = first;
        if self.binary_here() {
            let m = self.precede(first, NodeKind::BinaryExpr)?;
            let base = self.level();
            let mut chain = ChainHeight::new(first.height);
            while let Some(op) = self.peek_kind().binop().filter(|_| self.binary_here()) {
                let (pending, left) = chain.operator(op.group());
                self.chain_operator(base, pending, left)?;
                self.bump();
                let right = self.parse_cast()?;
                chain.operand(right.height);
            }
            let top = self.open.len() - 1;
            self.open[top].children = chain.height();
            self.open[top].level = base;
            expr = self.complete(m, NodeKind::BinaryExpr);
        }
        if allow_range {
            return self.parse_range_rest(expr);
        }
        Ok(expr)
    }

    /// The next token is a binary operator read as one here. One at the head
    /// of a line is not (§2.5, S-124, S-370: a line ends at its end), nor a
    /// `-`, `^` or `+` with a blank before it and its operand touching it
    /// (`a -b`, `[1 -1]`, `[1 +1]`; S-398, S-405). The grammar fails at it,
    /// and the table names the form (`leading_operator`, `leading_minus`,
    /// `asymmetric_binary_space`). `a - -b` has blanks on both sides.
    fn binary_here(&self) -> bool {
        let i = self.peek_index();
        let asymmetric = matches!(self.tokens[i].kind, TokenKind::Minus | TokenKind::Caret | TokenKind::Plus)
            && self.gap(i) == Gap::Space
            && self.gap_after(i) == Gap::None
            && starts_operand(self.tokens[i + 1].kind);
        self.tokens[i].kind.binop().is_some() && !asymmetric && !self.lines.at_line_head(i)
    }

    /// The rest of a head whose start `expr` is read: a range when a range
    /// symbol follows, else `expr`. A range is the whole expression of a head
    /// and is weaker than the binary operators (§3.1, S-257). Its other
    /// symbols (`..`, `...`) fail at the symbol: the table of the forms of
    /// other languages says what they are (`range_dots`; a range anywhere
    /// else, `range_outside_header`).
    pub(super) fn parse_range_rest(&mut self, expr: Completed) -> PResult<Completed> {
        // A range symbol at the head of a line (in brackets, where a line
        // break is a blank) is not read: the table names it (`leading_range`, S-335).
        if !self.peek_kind().range_readings().is_empty() && self.lines.at_line_head(self.peek_index()) {
            return Err(self.unexpected("`{`"));
        }
        if self.peek_kind().range_end().is_some() {
            let m = self.precede(expr, NodeKind::RangeExpr)?;
            self.bump();
            // A `{` after the symbol starts the body (S-338): `parse_primary` says so.
            self.parse_expr_inner(false)?;
            return Ok(self.complete(m, NodeKind::RangeExpr));
        }
        if self.peek_kind().is_foreign_range() {
            return Err(self.unexpected("`..<` or `..=`"));
        }
        Ok(expr)
    }

    /// The next operator of a chain whose node is at the level `base`: in the
    /// tree of §3.1 it is under `pending - 1` operators that wait for their
    /// right operand, and its left operand is `left` high (one level per
    /// operator, [`ChainHeight`]). E0006 at the operator when that is over the limit,
    /// before the chain is read on (spec §2.5); else its right operand is read
    /// at its level.
    fn chain_operator(&mut self, base: u32, pending: u32, left: u32) -> PResult<()> {
        let at = self.peek().span;
        self.limit(base + pending + left, at, NodeKind::BinaryExpr)?;
        let top = self.open.len() - 1;
        self.open[top].level = base + pending;
        Ok(())
    }

    /// `prefix [as Type | at Clock]*`: a prefix binds tighter than `as` and
    /// `at` (§3.1). A chain of them is read whole and is E0011 (`groups.rs`).
    fn parse_cast(&mut self) -> PResult<Completed> {
        let mut expr = self.parse_prefix()?;
        loop {
            match self.peek_kind() {
                TokenKind::KwAs => {
                    let m = self.precede(expr, NodeKind::CastExpr)?;
                    self.bump();
                    self.parse_bare_type()?;
                    expr = self.complete(m, NodeKind::CastExpr);
                }
                TokenKind::KwAt => {
                    let m = self.precede(expr, NodeKind::AtExpr)?;
                    self.parse_clock()?;
                    expr = self.complete(m, NodeKind::AtExpr);
                }
                _ => return Ok(expr),
            }
        }
    }

    // The tokens `parse_prefix` reads as the start of an operand are those of
    // `starts_operand` (a `debug_assert` in `parse_primary` and the test
    // `operand_starts` hold the two together).
    fn parse_prefix(&mut self) -> PResult<Completed> {
        self.parse_prefix_in(false)
    }

    /// [`Parser::parse_prefix`], `in_a_stack` under another prefix operator.
    fn parse_prefix_in(&mut self, in_a_stack: bool) -> PResult<Completed> {
        let t = self.peek();
        if matches!(t.kind, TokenKind::Minus | TokenKind::Bang) {
            // The prefix `-` / `!` touches its operand (§2.5, S-123, S-369):
            // after a blank or a line break the parser fails at it
            // ([`Want::Prefix`]), and the table names the form
            // (`space_after_prefix`, `newline_after_prefix`). A stack of
            // prefix operators with blanks or line breaks between them
            // (`- - x`, `-` and `-a` on the next line) is one form, the
            // E0012 of the stack (S-410, S-248).
            let i = self.peek_index();
            let stacked = matches!(self.tokens[self.next_code(i)].kind, TokenKind::Minus | TokenKind::Bang);
            let gap = self.gap_after(i);
            if gap.is_some() && !(stacked || in_a_stack) {
                return Err(self.fail(Want::Prefix, "an operand right after the prefix operator"));
            }
            let m = self.start(NodeKind::PrefixExpr)?;
            self.bump();
            if gap == Gap::Newline {
                self.skip_newlines();
            }
            self.parse_prefix_in(true)?;
            return Ok(self.complete(m, NodeKind::PrefixExpr));
        }
        self.parse_postfix()
    }

    pub(super) fn parse_postfix(&mut self) -> PResult<Completed> {
        let first = self.peek();
        let mut expr = self.parse_primary()?;
        // The last name of a chain `a.b.C` of names (a struct literal path, S-08).
        let mut chain: Option<Token> = (expr.kind == NodeKind::PathExpr).then_some(first);
        // What the chain is so far, for the callee of a `(` (§6.1).
        let mut callee = Callee::start(expr.kind);
        loop {
            // A `.` on the next line continues the expression (§2.5,
            // [`Parser::peek_index`]).
            let t = self.peek();
            match t.kind {
                TokenKind::LParen => {
                    // A callee not written by name is no item: E0020 here,
                    // `.(` (§6.1, S-191).
                    let by_name = callee.by_name();
                    if !self.touches(TokenKind::LParen, by_name, true) {
                        break;
                    }
                    if !by_name {
                        return Err(self.fail(Want::Callee, "an operator or the end of the expression"));
                    }
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
                }
                TokenKind::Tilde | TokenKind::Bang
                    if self.tokens[self.next_code(self.peek_index())].kind == TokenKind::LParen
                        && callee.last().takes_a_mark() =>
                {
                    // The mark touches the name and the `(` touches the mark
                    // (S-123, S-412): a gap after the mark makes the call's
                    // list the required one of `Parser::opens`.
                    let mark = self.peek_index();
                    let after = self.gap_after(mark);
                    if !self.touches(t.kind, true, true) || after.is_some() {
                        if after.is_some() {
                            let kept = self.detached.filter(|d| d.at == mark);
                            let d = kept.unwrap_or(Detached { at: mark, by_name: true, expr: true, required: false });
                            self.detached = Some(Detached { required: true, ..d });
                        }
                        break;
                    }
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.bump();
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
                }
                TokenKind::Tilde => {
                    return Err(self.fail(Want::Other, "the flow-call mark `name~(args)`, written without spaces"));
                }
                // Type arguments after a path of names (§4.5, S-239): `::[`
                // with no space on either side of `::`. Elsewhere `::` is not
                // read (the forms of other languages, `crate::foreign`).
                TokenKind::ColonColon
                    if self.lines.type_args_mark(&self.tokens, self.peek_index()) && callee.last().names_a_path() =>
                {
                    let m = self.precede(expr, NodeKind::TypeArgsExpr)?;
                    self.bump();
                    let a = self.start(NodeKind::TypeArgs)?;
                    self.bump();
                    self.with_nl(false, |p| p.parse_type_args())?;
                    self.complete(a, NodeKind::TypeArgs);
                    // The name before the list stays the last name of a chain
                    // (`Pr::[U8] { a: 1 }`).
                    expr = self.complete(m, NodeKind::TypeArgsExpr);
                }
                // The member `.` takes no space on either side inside a line (§2.5, S-203).
                TokenKind::Dot if self.dot_apart() => {
                    return Err(self.fail(Want::Postfix, "a member `.` without spaces around it"));
                }
                // `v.(x)`: a call through a function value (§6.1, S-191).
                TokenKind::Dot if self.peek2().kind == TokenKind::LParen => {
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.bump();
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
                }
                TokenKind::Dot => {
                    let m = self.precede(expr, NodeKind::FieldExpr)?;
                    self.bump();
                    let n = self.peek();
                    match n.kind {
                        // A keyword is a field name here; `.(` is read above.
                        k if !(crate::starts::starts_member(k) || k.is_keyword()) => {
                            return Err(self.unexpected("a field name or tuple index after `.`"));
                        }
                        TokenKind::Int => {
                            if crate::literal::tuple_index_value(self.token_text(n)).is_some()
                                && crate::literal::tuple_index_unpadded(self.token_text(n)).is_some()
                            {
                                return Err(self.fail(Want::TupleIndex, "a tuple index without a leading `0`"));
                            }
                            self.bump();
                            if crate::literal::tuple_index_value(self.token_text(n)).is_none() {
                                return Err(self.error(Code::E0408, n.span, "tuple index is too large"));
                            }
                            expr = self.complete(m, NodeKind::TupleIndexExpr);
                            chain = None;
                        }
                        _ => {
                            let name = self.parse_name_after_dot("a field name")?;
                            expr = self.complete(m, NodeKind::FieldExpr);
                            chain = chain.map(|_| name);
                        }
                    }
                }
                // Type arguments of other languages before a call, `f<T>(x)`
                // and `f[A, B](x)` (§4.5): the table says from the tokens
                // whether the brackets are such a list ([`foreign::type_list_ahead`]);
                // the parser fails at them, so `<` is not read as a comparison
                // nor `[A, B]` as an index.
                // In a type (a const argument, an array's length) no `::[` is
                // written, so a `[…]` with `,` is read as an index (R-196).
                TokenKind::Lt | TokenKind::LBracket
                    if foreign::type_list_ahead(&self.tokens, &self.lines, self.peek_index(), expr.kind)
                        && (self.peek_kind() == TokenKind::Lt || (!self.in_type() && self.type_list_next())) =>
                {
                    return Err(self.fail(Want::Other, "an operator or the end of the expression"));
                }
                TokenKind::LBracket if self.touches(TokenKind::LBracket, callee.by_name(), true) => {
                    let m = self.precede(expr, NodeKind::IndexExpr)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        p.parse_expr()?;
                        p.expect(TokenKind::RBracket)?;
                        Ok(())
                    })?;
                    expr = self.complete(m, NodeKind::IndexExpr);
                    chain = None;
                }
                // A `?` after a blank or a line break is not read on: the
                // grammar fails at it, and the table names the form
                // (`space_before_question`, `newline_before_question`).
                TokenKind::Question if self.peek_gap().is_some() => break,
                TokenKind::Question => {
                    let m = self.precede(expr, NodeKind::TryExpr)?;
                    self.bump();
                    expr = self.complete(m, NodeKind::TryExpr);
                    chain = None;
                }
                TokenKind::LBrace
                    if !self.no_struct_lit
                        && chain.is_some_and(|c| self.token_text(c).starts_with(|c: char| c.is_ascii_uppercase())) =>
                {
                    // In brackets the `{` is on the line of the name (E0003, S-413).
                    self.e0003_unless_on_the_line(TokenKind::LBrace);
                    let m = self.precede(expr, NodeKind::StructLit)?;
                    let l = self.start(NodeKind::StructLitFields)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RBrace) {
                            let f = p.start(NodeKind::StructLitField)?;
                            p.parse_ident("field name")?;
                            p.expect(TokenKind::Colon)?;
                            p.parse_consumed()?;
                            p.complete(f, NodeKind::StructLitField);
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.close_list(NodeKind::StructLitFields, TokenKind::RBrace)?;
                        Ok(())
                    })?;
                    self.complete(l, NodeKind::StructLitFields);
                    expr = self.complete(m, NodeKind::StructLit);
                    chain = None;
                }
                _ => break,
            }
            callee = callee.then(expr.kind);
        }
        // A postfix `?` after a blank or a line break, where the chain would
        // read it: the grammar fails at it, and the table's candidate writes
        // it against the chain (§2.5, R-214); elsewhere a `?` has none.
        let next = (self.pos..self.tokens.len())
            .find(|&k| self.tokens[k].kind != TokenKind::Newline && !self.tokens[k].kind.is_comment());
        if let Some(at) = next.filter(|&k| self.tokens[k].kind == TokenKind::Question && self.gap(k).is_some()) {
            self.detached = Some(Detached { at, by_name: false, expr: true, required: false });
        }
        Ok(expr)
    }

    /// `( args )`.
    fn parse_arg_list(&mut self) -> PResult<()> {
        let m = self.start(NodeKind::ArgList)?;
        self.bump(); // `(`
        self.with_nl(false, |p| {
            let saved = std::mem::replace(&mut p.no_struct_lit, false);
            while !p.at(TokenKind::RParen) {
                let a = p.start(NodeKind::Arg)?;
                if p.at(TokenKind::KwMove) {
                    // `f(move x)`: `move x` is the form `move` (§5.2).
                    p.parse_move(MoveAs::Level, |p, mv| p.parse_marked(mv))?;
                } else if p.at(TokenKind::KwInout) {
                    let mark = p.bump();
                    p.parse_marked(mark)?;
                } else {
                    p.parse_expr()?;
                }
                p.complete(a, NodeKind::Arg);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.no_struct_lit = saved;
            p.close_list(NodeKind::ArgList, TokenKind::RParen)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::ArgList);
        Ok(())
    }

    fn parse_primary(&mut self) -> PResult<Completed> {
        let t = self.peek();
        let kind = match t.kind {
            TokenKind::KwMove => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "`move` is written only where a value is consumed: let/var initializers, assignment, literal elements, `match move x`, call arguments, and the last expression of a block (§5.2)",
                ));
            }
            TokenKind::KwRt => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "an anonymous function cannot be `rt`; its `rt` comes from the expected type",
                ));
            }
            TokenKind::Int => {
                let m = self.start(NodeKind::Literal)?;
                self.bump();
                self.check_int(t);
                return Ok(self.complete(m, NodeKind::Literal));
            }
            TokenKind::Float | TokenKind::Char | TokenKind::Str | TokenKind::KwTrue | TokenKind::KwFalse => {
                NodeKind::Literal
            }
            TokenKind::Underscore => NodeKind::HoleExpr,
            TokenKind::Ident | TokenKind::KwSelf | TokenKind::KwSelfType => NodeKind::PathExpr,
            // `^name` (§2.6): a mark of the name, no operator; the `^` after
            // an operand is the binary one. A `^` with no name right after it
            // is E0002 with the rule (S-358).
            TokenKind::Caret => {
                if self.peek2().kind != TokenKind::Ident || self.gap(self.peek2_index()).is_some() {
                    let next = self.peek2();
                    return Err(self.fail_noting(Want::Expr, "a name right after `^`", next, CARET_RULE));
                }
                let m = self.start(NodeKind::FeedbackExpr)?;
                self.bump();
                self.bump();
                return Ok(self.complete(m, NodeKind::FeedbackExpr));
            }
            TokenKind::LParen => {
                let m = self.start(NodeKind::TupleExpr)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    let saved = std::mem::replace(&mut p.no_struct_lit, false);
                    let r = p.parse_paren_rest();
                    p.no_struct_lit = saved;
                    r
                })?;
                return Ok(self.complete(m, kind));
            }
            TokenKind::LBracket => {
                let m = self.start(NodeKind::ArrayExpr)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    let saved = std::mem::replace(&mut p.no_struct_lit, false);
                    let r = p.parse_array_rest();
                    p.no_struct_lit = saved;
                    r
                })?;
                return Ok(self.complete(m, kind));
            }
            // In a header, a `{` at the start of an expression outside
            // parentheses starts the body (§4.4, S-338), as the `{` of a
            // struct literal does (S-08): a block is written in parentheses.
            TokenKind::LBrace if self.no_struct_lit => {
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0002,
                    t.span,
                    "a `{` at the start of an expression in a header starts the body",
                )
                .with_found("{")
                .with_rule("in the header of `if`, `while`, `match`, `for` and `par`, a `{` at the start of an expression outside parentheses starts the body: a block expression there is written in parentheses, `({ … })`, and a range has both ends, `0..<n` (§3.1, §4.4, §7)");
                self.report(d);
                return Err(ParseError);
            }
            TokenKind::LBrace => return self.parse_block_expr(),
            TokenKind::KwIf => return self.parse_if(None),
            TokenKind::KwMatch => {
                let m = self.start(NodeKind::MatchExpr)?;
                self.bump();
                self.branch_tilde()?;
                if self.at(TokenKind::KwMove) {
                    // `match move x` consumes the value (§7, S-21).
                    self.parse_move(MoveAs::Node, |p, mv| {
                        let saved = std::mem::replace(&mut p.no_struct_lit, true);
                        let inner = p.parse_marked(mv);
                        p.no_struct_lit = saved;
                        inner
                    })?;
                } else {
                    self.parse_head_expr(false)?;
                }
                let arms = self.start(NodeKind::MatchArms)?;
                self.e0003_unless_on_the_line(TokenKind::LBrace);
                self.expect(TokenKind::LBrace)?;
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RBrace) {
                        let a = p.start(NodeKind::MatchArm)?;
                        p.parse_pattern()?;
                        if p.eat(TokenKind::KwIf).is_some() {
                            p.parse_expr()?;
                        }
                        p.expect(TokenKind::FatArrow)?;
                        p.parse_consumed()?;
                        p.complete(a, NodeKind::MatchArm);
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::MatchArms, TokenKind::RBrace)?;
                    Ok(())
                })?;
                self.complete(arms, NodeKind::MatchArms);
                return Ok(self.complete(m, NodeKind::MatchExpr));
            }
            // `fn name` declares a function, which is written at the top level
            // or in a list of members: the error is at the `fn`, so that the
            // recovery may start the next unit there (an unclosed `{`, §18.1).
            TokenKind::KwFn if declares_a_function(t.kind, self.peek2().kind) => {
                return Err(self.unexpected("an expression (a function is declared at the top level)"));
            }
            TokenKind::KwFn => {
                let m = self.start(NodeKind::ClosureExpr)?;
                self.bump();
                self.parse_params(false, NodeKind::ClosureExpr)?;
                if self.at_line_end(TokenKind::Arrow) {
                    self.bump();
                    self.parse_type()?;
                }
                self.parse_effect_row_opt()?;
                self.parse_body()?;
                return Ok(self.complete(m, NodeKind::ClosureExpr));
            }
            TokenKind::KwHandle => {
                let m = self.start(NodeKind::HandleExpr)?;
                self.bump();
                self.parse_body()?;
                self.e0003_unless_on_the_line(TokenKind::KwWith);
                self.expect(TokenKind::KwWith)?;
                let path = self.parse_path("a handler")?;
                // S-421: after the name of an effect (`UpperCamel`, §2.3) the
                // body of a handler written in place follows, on the line of
                // the name in brackets and out of them (E0003 else); with no
                // `{` there is no body (E0002). A named handler (`snake_case`)
                // is read as before (S-480).
                if crate::naming::is_type_name(self.token_text(path.last)) {
                    if !self.e0003_unless_on_the_line(TokenKind::LBrace) {
                        let found = self.peek();
                        let expected = "the body `{ ... }` of the handler";
                        return Err(self.fail_noting(Want::Other, expected, found, HANDLER_BODY_RULE));
                    }
                    self.parse_item_body(ItemCtx::InlineHandler)?;
                } else if self.at(TokenKind::LBrace) {
                    self.parse_item_body(ItemCtx::InlineHandler)?;
                // S-412: the `(` after the handler of `with` follows the rule of
                // the postfix `(` (a blank before it is E0020).
                } else if self.touches_bare(TokenKind::LParen)? {
                    self.parse_arg_list()?;
                }
                return Ok(self.complete(m, NodeKind::HandleExpr));
            }
            TokenKind::KwUnsafe => {
                let m = self.start(NodeKind::UnsafeExpr)?;
                self.bump();
                self.parse_body()?;
                return Ok(self.complete(m, NodeKind::UnsafeExpr));
            }
            TokenKind::KwPar => {
                let m = self.start(NodeKind::ParExpr)?;
                self.bump();
                self.parse_name("replication index")?;
                self.expect(TokenKind::KwIn)?;
                let range = self.parse_head_expr(true)?;
                // A range symbol at the head of the next line: the table names
                // it (`leading_range`, S-335).
                let next = self.past_newlines();
                if range.kind != NodeKind::RangeExpr
                    && !self.tokens[next].kind.range_readings().is_empty()
                    && self.lines.at_line_head(next)
                {
                    return Err(self.unexpected("`{`"));
                }
                if range.kind != NodeKind::RangeExpr {
                    return Err(self.error(Code::E0002, range.span, "`par` needs a range `a..<b` or `a..=b`"));
                }
                self.parse_body()?;
                return Ok(self.complete(m, NodeKind::ParExpr));
            }
            _ => {
                debug_assert!(!starts_operand(t.kind), "{:?} starts an operand", t.kind);
                return Err(self.fail(Want::Expr, "an expression"));
            }
        };
        let m = self.start(kind)?;
        let t = self.bump();
        if t.kind == TokenKind::Str {
            self.interpolation_levels(t)?;
        }
        Ok(self.complete(m, kind))
    }

    /// The holes of the string literal `t`, the innermost open node (spec
    /// §2.5): a hole `{a.b.c}` counts as the path `a.b.c` written as an
    /// expression, one level per `.`. E0006 at the `.` over the limit.
    fn interpolation_levels(&mut self, t: Token) -> PResult<()> {
        let level = self.level();
        let mut height = 0;
        let paths: Vec<Vec<Span>> = self.literals.holes_in(t.span).iter().filter_map(|h| h.path.clone()).collect();
        for path in paths {
            for (i, name) in path.iter().enumerate().skip(1) {
                let dot = Span::new(self.file, name.start - 1, name.start);
                self.limit(level + Self::height(NodeKind::FieldExpr, i as u32 - 1), dot, NodeKind::FieldExpr)?;
            }
            height = height.max(path.len().saturating_sub(1) as u32);
        }
        let top = self.open.len() - 1;
        self.open[top].children = self.open[top].children.max(height);
        Ok(())
    }

    /// After `(`: `()`, `(e)` or `(a, b, ...)`.
    fn parse_paren_rest(&mut self) -> PResult<NodeKind> {
        if self.eat(TokenKind::RParen).is_some() {
            return Ok(NodeKind::TupleExpr);
        }
        let first = self.parse_consumed()?;
        let Some(comma) = self.eat(TokenKind::Comma) else {
            if first.kind == NodeKind::MoveExpr {
                let mv = Span::new(self.file, first.span.start, first.span.start + "move".len() as u32);
                return Err(self.error(
                    Code::E0002,
                    mv,
                    "a marked expression stands where it is consumed; it is parenthesized only as an element of a tuple of two or more (§5.2)",
                ));
            }
            self.close_list(NodeKind::TupleExpr, TokenKind::RParen)?;
            return Ok(NodeKind::ParenExpr);
        };
        if self.at(TokenKind::RParen) {
            return Err(self.one_element(comma));
        }
        while !self.at(TokenKind::RParen) {
            self.parse_consumed()?;
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.close_list(NodeKind::TupleExpr, TokenKind::RParen)?;
        Ok(NodeKind::TupleExpr)
    }

    /// E0002 at the `,` after the only element of a parenthesis (`(e,)`,
    /// `(I32,)`, `(p,)`, §2.4, R-43): a tuple has two or more elements.
    pub(super) fn one_element(&mut self, comma: Token) -> ParseError {
        self.error(
            Code::E0002,
            comma.span,
            "a tuple has two or more elements; `(e)` is a group, and a `,` after the only element is not written (§2.4)",
        )
    }

    /// After `[`: `[]`, `[a, b]` or `[e; N]`.
    fn parse_array_rest(&mut self) -> PResult<NodeKind> {
        if self.eat(TokenKind::RBracket).is_some() {
            return Ok(NodeKind::ArrayExpr);
        }
        self.parse_consumed()?;
        if self.eat(TokenKind::Semi).is_some() {
            self.parse_expr()?;
            self.expect(TokenKind::RBracket)?;
            return Ok(NodeKind::RepeatExpr);
        }
        while self.eat(TokenKind::Comma).is_some() {
            if self.at(TokenKind::RBracket) {
                break;
            }
            self.parse_consumed()?;
        }
        self.close_list(NodeKind::ArrayExpr, TokenKind::RBracket)?;
        Ok(NodeKind::ArrayExpr)
    }

    /// `if [~] cond { } [else (if … | { })]` (§11.5). `chain` is `None` for
    /// the first `if` of a chain and, for an `if` after `else`, whether the
    /// first one has the `~`: the `~` is written on the first `if` only (a
    /// later one is `else_if_tilde` of the table, S-355), and the chain of an
    /// `if~` ends with an `else` block (E0002 with the rule, S-355).
    fn parse_if(&mut self, chain: Option<bool>) -> PResult<Completed> {
        let m = self.start(NodeKind::IfExpr)?;
        self.expect(TokenKind::KwIf)?;
        let tilde = match chain {
            None => self.branch_tilde()?,
            Some(_) if self.at(TokenKind::Tilde) => {
                return Err(self.fail(Want::Expr, "the condition of `else if`"));
            }
            Some(tilde) => tilde,
        };
        self.parse_head_expr(false)?;
        self.parse_body()?;
        let close_brace_end = self.last_end;
        // `else` is on the line of the `}`, and the `if` after it on its line (E0003).
        if self.e0003_unless_on_the_line(TokenKind::KwElse) {
            self.bump();
            if self.e0003_unless_on_the_line(TokenKind::KwIf) {
                self.parse_if(Some(tilde))?;
            } else {
                self.parse_body()?;
            }
        } else if tilde {
            // The chain of an `if~` ends without `else` (S-355): E0002 at the
            // `}` of its last block, after which the `else` goes.
            let close = Span::new(self.file, close_brace_end - 1, close_brace_end);
            let d =
                Diagnostic::new(Stage::Syntax, Code::E0002, close, "expected `else` after the last block of an `if~`")
                    .with_found("}")
                    .with_rule(IF_TILDE_ELSE_RULE);
            self.report(d);
            return Err(ParseError);
        }
        Ok(self.complete(m, NodeKind::IfExpr))
    }

    /// The `~` of `if~` and `match~` (§2.6), read when it touches the
    /// keyword. With a blank between them the parser fails at it, and the
    /// table names the form (`space_after_branch_keyword`, S-354).
    fn branch_tilde(&mut self) -> PResult<bool> {
        if !self.at(TokenKind::Tilde) {
            return Ok(false);
        }
        if self.peek_gap().is_some() {
            return Err(self.fail(Want::Expr, "the condition, after a `~` written without a blank"));
        }
        self.bump();
        Ok(true)
    }
}

/// Whether the tokens `all[first..=last]` of a file are one expression,
/// read as an end of a range in a header (no struct literal and no block
/// at its start, §4.4, S-338; newlines not significant): the ends of a
/// range pattern (§7, S-341), read by the parser's own grammar (one
/// reading). Its diagnostics are not kept.
pub(crate) fn reads_as_expr(
    file: FileId,
    text: &str,
    all: &[Token],
    literals: &Literals,
    first: usize,
    last: usize,
) -> bool {
    let mut tokens = all[first..=last].to_vec();
    let end = all[last].span.end;
    tokens.push(Token { kind: TokenKind::Eof, span: Span::new(file, end, end) });
    // The holes and the lexer's errors of the literals in the run read as
    // they do in the file; its diagnostics are not this reading's.
    let literals = literals.within(all[first].span.start, end);
    let mut p = Parser::new(file, text, crate::Lexed { tokens, diagnostics: Vec::new(), literals });
    p.nl = vec![false];
    p.no_struct_lit = true;
    p.parse_expr_inner(false).is_ok() && p.at(TokenKind::Eof) && p.diagnostics.is_empty()
}
