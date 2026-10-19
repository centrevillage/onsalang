//! The blocks and the statements.

use super::*;

/// How the form `move` is in the tree ([`Parser::parse_move`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MoveAs {
    /// A `MoveExpr` node: an expression in a consuming position, the
    /// scrutinee of `match move x`.
    Node,
    /// No node: only the level is counted ([`Parser::without_node`]): an
    /// argument (`f(move x)`) and the iterated value of `for`.
    Level,
}

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ blocks and statements

    /// The body of a declaration or a head (`fn`, `if`, `while`, ...): a block
    /// whose `{` is on the line of the head's last token ([`Parser::e0003_unless_on_the_line`]).
    pub(super) fn parse_body(&mut self) -> PResult<Completed> {
        self.e0003_unless_on_the_line(TokenKind::LBrace);
        self.parse_block_expr()
    }

    /// Whether the next code token is `kind` (an `else`, a `with`, the `if`
    /// after `else`, the `{` of a body, a struct literal or pattern, an
    /// effect row), looked for past the line breaks whatever the context. A
    /// line break before it is the E0003 of §2.5 (S-47, S-202, R-62, S-413 to
    /// S-415): at the token (R-160), with the candidate that moves it and the
    /// rest of its line up to the end of the code before it, before the
    /// comment there (S-216, [`crate::edits::move_up`]); the reading goes on
    /// past the line breaks, as if it were on the line.
    pub(super) fn e0003_unless_on_the_line(&mut self, kind: TokenKind) -> bool {
        let i = (self.pos..self.tokens.len()).find(|&k| !self.tokens[k].kind.is_trivia()).unwrap_or(self.pos);
        let t = self.tokens[i];
        if t.kind != kind {
            return false;
        }
        if self.tokens[self.pos..i].iter().any(|t| t.kind == TokenKind::Newline) {
            let word = self.token_text(t).to_string();
            let title = format!("move `{word}` to the end of the line before");
            let fix = crate::edits::move_up(self.file, self.text, &self.all, &title, self.last_end, t, " ");
            let message = match kind {
                TokenKind::KwElse | TokenKind::KwWith => {
                    format!("`{word}` must be on the same line as the closing `}}`")
                }
                TokenKind::KwIf => "the `if` after `else` must be on the line of the `else`".to_string(),
                _ => format!("`{word}` must be on the line of the last token of what it belongs to"),
            };
            let d = Diagnostic::new(Stage::Syntax, Code::E0003, t.span, message).with_found(word).with_fix(fix);
            self.report(d);
            self.with_nl(true, |p| p.skip_newlines());
        }
        true
    }

    /// `{ stmts }` as an expression (newlines significant inside).
    pub(super) fn parse_block_expr(&mut self) -> PResult<Completed> {
        let m = self.start(NodeKind::Block)?;
        self.expect(TokenKind::LBrace)?;
        let saved = std::mem::replace(&mut self.no_struct_lit, false);
        let block = self.with_nl(true, |p| p.parse_block_body());
        self.no_struct_lit = saved;
        block?;
        Ok(self.complete(m, NodeKind::Block))
    }

    fn parse_block_body(&mut self) -> PResult<()> {
        loop {
            self.skip_newlines();
            if self.at(TokenKind::RBrace) {
                break;
            }
            if self.at(TokenKind::Eof) {
                return Err(self.unexpected("`}`"));
            }
            self.parse_stmt()?;
            match self.peek_kind() {
                TokenKind::Newline | TokenKind::RBrace => {}
                _ => return Err(self.unexpected("newline or `}`")),
            }
        }
        self.expect(TokenKind::RBrace)?;
        Ok(())
    }

    /// A `let` after its keyword (the node `m` is open): `pat[: T] = e`.
    fn parse_let_rest(&mut self, m: Marker) -> PResult<Completed> {
        self.parse_pattern()?;
        if self.eat(TokenKind::Colon).is_some() {
            self.parse_type()?;
        }
        self.expect(TokenKind::Eq)?;
        self.parse_consumed()?;
        Ok(self.complete(m, NodeKind::LetStmt))
    }

    fn parse_stmt(&mut self) -> PResult<Completed> {
        // The attributes before a statement (§6.5, §12.4: `@mem(bulk) let`):
        // an `@` with a name right after it. A line break may come before the
        // statement, as before a declaration (fmt puts them on its line). Only
        // a `let` takes one (`@mem`); before any other statement, the table's
        // E0005, and the statement is read on.
        let i = self.peek_index();
        if self.tokens[i].kind == TokenKind::At
            && self.tokens[i + 1].kind == TokenKind::Ident
            && self.gap(i + 1) == Gap::None
        {
            let attrs = self.parse_attrs(false)?;
            self.skip_newlines();
            if self.at(TokenKind::KwLet) {
                let m = self.precede(attrs[0].node, NodeKind::LetStmt)?;
                self.check_attrs(&attrs, Place::Let, None);
                self.bump();
                return self.parse_let_rest(m);
            }
            self.check_attrs(&attrs, Place::Other("a statement other than `let`"), None);
        }
        let t = self.peek();
        match t.kind {
            TokenKind::KwLet => {
                let m = self.start(NodeKind::LetStmt)?;
                self.bump();
                self.parse_let_rest(m)
            }
            TokenKind::KwVar => {
                let m = self.start(NodeKind::VarStmt)?;
                self.bump();
                self.parse_var_rest(m)
            }
            TokenKind::KwFor => {
                let m = self.start(NodeKind::ForStmt)?;
                self.bump();
                self.parse_pattern()?;
                self.expect(TokenKind::KwIn)?;
                if self.at(TokenKind::KwMove) {
                    // `for s in move xs`: `move xs` is the form `move` (§5.2).
                    // A range after its start (`for i in move 0..<n`) is read
                    // on, the `move` over the whole range (§7: E0703, of
                    // the modes stage, W4-09); the start is a postfix
                    // expression as any operand of `move` (§5.2).
                    // SPEC-GAP(S-362): `move lo + 1..<hi` is the E0002 of
                    // §5.2, which §7's E0703 for a range does not settle.
                    self.parse_move(MoveAs::Level, |p, mv| {
                        let saved = std::mem::replace(&mut p.no_struct_lit, true);
                        let r = p.parse_marked(mv).and_then(|start| p.parse_range_rest(start));
                        p.no_struct_lit = saved;
                        r
                    })?;
                } else {
                    self.parse_head_expr(true)?;
                }
                self.parse_body()?;
                Ok(self.complete(m, NodeKind::ForStmt))
            }
            TokenKind::KwWhile => {
                let m = self.start(NodeKind::WhileStmt)?;
                self.bump();
                self.parse_head_expr(false)?;
                self.parse_body()?;
                Ok(self.complete(m, NodeKind::WhileStmt))
            }
            TokenKind::KwBreak => {
                let m = self.start(NodeKind::BreakStmt)?;
                self.bump();
                Ok(self.complete(m, NodeKind::BreakStmt))
            }
            TokenKind::KwContinue => {
                let m = self.start(NodeKind::ContinueStmt)?;
                self.bump();
                Ok(self.complete(m, NodeKind::ContinueStmt))
            }
            TokenKind::KwReturn => {
                let m = self.start(NodeKind::ReturnStmt)?;
                self.bump();
                if !matches!(self.peek_kind(), TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof) {
                    self.parse_consumed()?;
                }
                Ok(self.complete(m, NodeKind::ReturnStmt))
            }
            // `move a` on the last expression of a block (§5.2, S-100): where
            // the block stands decides the rest (the modes stage).
            TokenKind::KwMove => {
                let expr = self.parse_consumed()?;
                if self.peek_past_newlines().kind != TokenKind::RBrace {
                    return Err(self.error(
                        Code::E0002,
                        t.span,
                        "a `move` statement is written only as the last expression of a block (§5.2)",
                    ));
                }
                let m = self.precede(expr, NodeKind::ExprStmt)?;
                Ok(self.complete(m, NodeKind::ExprStmt))
            }
            TokenKind::KwAssert => {
                let m = self.start(NodeKind::AssertStmt)?;
                self.bump();
                self.parse_expr()?;
                Ok(self.complete(m, NodeKind::AssertStmt))
            }
            _ => {
                let expr = self.parse_expr()?;
                if self.at(TokenKind::Eq) {
                    let m = self.precede(expr, NodeKind::AssignStmt)?;
                    self.bump();
                    self.parse_consumed()?;
                    return Ok(self.complete(m, NodeKind::AssignStmt));
                }
                let m = self.precede(expr, NodeKind::ExprStmt)?;
                Ok(self.complete(m, NodeKind::ExprStmt))
            }
        }
    }

    fn parse_var_rest(&mut self, m: Marker) -> PResult<Completed> {
        self.parse_name("variable name")?;
        if self.eat(TokenKind::Colon).is_some() {
            self.parse_type()?;
        }
        self.expect(TokenKind::Eq)?;
        self.parse_consumed()?;
        Ok(self.complete(m, NodeKind::VarStmt))
    }

    /// An expression in a consuming position (§5.2, S-21) or where the
    /// function returns (S-100): `move <place>` or a plain expression.
    pub(super) fn parse_consumed(&mut self) -> PResult<Completed> {
        if !self.at(TokenKind::KwMove) {
            return self.parse_expr();
        }
        self.parse_move(MoveAs::Node, |p, mv| p.parse_marked(mv))
    }

    /// The form `move` at the next token (§5.2): the `move`, then `rest`
    /// reads its operand (given the `move`). It is a `MoveExpr` node or
    /// a level without one ([`MoveAs`]). The one reading of the form.
    pub(super) fn parse_move(
        &mut self,
        node: MoveAs,
        rest: impl FnOnce(&mut Self, Token) -> PResult<Completed>,
    ) -> PResult<Completed> {
        match node {
            MoveAs::Node => {
                let m = self.start(NodeKind::MoveExpr)?;
                let mv = self.bump();
                rest(self, mv)?;
                Ok(self.complete(m, NodeKind::MoveExpr))
            }
            MoveAs::Level => {
                let mv = self.bump();
                self.without_node(NodeKind::MoveExpr, mv.span, |p| rest(p, mv))
            }
        }
    }

    /// The operand of the mark `move` or `inout` (§5.2, R-42): a postfix
    /// expression, never the operand of a binary operator, `as` or `at`
    /// (`move y + 1` is E0002 at the `+`, not `move (y + 1)`).
    pub(super) fn parse_marked(&mut self, mark: Token) -> PResult<Completed> {
        let prefix = matches!(self.peek_kind(), TokenKind::Minus | TokenKind::Bang);
        let operand = if prefix { None } else { Some(self.parse_postfix()?) };
        let t = self.peek();
        match operand {
            Some(e) if t.kind.binop().is_none() && !matches!(t.kind, TokenKind::KwAs | TokenKind::KwAt) => Ok(e),
            _ => {
                let (mark, op) = (self.token_text(mark), self.token_text(t));
                let what = if prefix { "a prefix" } else { "the operand of" };
                Err(self.error(
                    Code::E0002,
                    t.span,
                    format!("the operand of `{mark}` is a postfix expression (a name and its fields, indexes and calls), not {what} `{op}` (§5.2)"),
                ))
            }
        }
    }

    /// Head expression of `if` / `while` / `match` / `for` / `par`: no struct
    /// literal (S-08); ranges allowed only when `allow_range`.
    pub(super) fn parse_head_expr(&mut self, allow_range: bool) -> PResult<Completed> {
        let saved = std::mem::replace(&mut self.no_struct_lit, true);
        let r = self.parse_expr_inner(allow_range);
        self.no_struct_lit = saved;
        r
    }
}
