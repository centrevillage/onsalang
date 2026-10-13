//! The names, paths, generic parameters, parameters, modes and effect rows
//! of the signatures.

use super::*;

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ signatures

    /// The name a declaration introduces, in a `Name` node.
    pub(super) fn parse_name(&mut self, what: &str) -> PResult<Token> {
        let m = self.start(NodeKind::Name)?;
        let t = self.parse_ident(what)?;
        self.complete(m, NodeKind::Name);
        Ok(t)
    }

    pub(super) fn parse_ident(&mut self, what: &str) -> PResult<Token> {
        let t = self.peek();
        if t.kind == TokenKind::Ident {
            self.bump();
            Ok(t)
        } else {
            Err(self.unexpected(what))
        }
    }

    /// `a.b.c` (also accepts `Self` as a segment).
    pub(super) fn parse_path(&mut self, what: &str) -> PResult<PathInfo> {
        let m = self.start(NodeKind::Path)?;
        let first = self.parse_path_segment(what)?;
        let mut last = first;
        let mut segments = 1;
        loop {
            // A `.` on the next line continues the path, as an expression's
            // chain (§2.5, [`Parser::peek_index`]); the member `.` of a path takes
            // no blank and no line break after it (S-203, S-353, the one test,
            // [`Parser::dot_apart`]).
            if self.dot_apart() {
                return Err(self.fail(Want::Postfix, "a member `.` without spaces around it"));
            }
            if self.at(TokenKind::Dot) && (self.peek2().kind == TokenKind::Ident || self.peek2().kind.is_keyword()) {
                self.bump();
            } else {
                break;
            }
            last = self.parse_name_after_dot(what)?;
            segments += 1;
        }
        self.complete(m, NodeKind::Path);
        Ok(PathInfo { segments, first, last })
    }

    /// After `.` and at the head of the path of a `use`, a keyword is an
    /// ordinary name (`std.test`, `x.type`, `use test.{Gen}`; §2.2).
    pub(super) fn parse_name_after_dot(&mut self, what: &str) -> PResult<Token> {
        let t = self.peek();
        if t.kind == TokenKind::Ident || t.kind.is_keyword() {
            self.bump();
            Ok(t)
        } else {
            Err(self.unexpected(what))
        }
    }

    fn parse_path_segment(&mut self, what: &str) -> PResult<Token> {
        let t = self.peek();
        match t.kind {
            TokenKind::Ident | TokenKind::KwSelfType => {
                self.bump();
                Ok(t)
            }
            _ => Err(self.unexpected(what)),
        }
    }

    pub(super) fn parse_generics_opt(&mut self) -> PResult<()> {
        if !self.touches(TokenKind::LBracket, true, false) {
            return Ok(());
        }
        let m = self.start(NodeKind::GenericParams)?;
        self.bump();
        self.with_nl(false, |p| p.parse_generic_list())?;
        self.complete(m, NodeKind::GenericParams);
        Ok(())
    }

    pub(super) fn parse_generic_list(&mut self) -> PResult<()> {
        let close = TokenKind::RBracket;
        while !self.at(close) {
            let m = self.start(NodeKind::TypeParam)?;
            if self.eat(TokenKind::KwConst).is_some() {
                self.parse_name("const parameter name")?;
                self.expect(TokenKind::Colon)?;
                self.parse_type()?;
                self.complete(m, NodeKind::ConstParam);
            } else {
                let name = self.parse_name("type parameter")?;
                if self.token_text(name).starts_with(|c: char| c.is_ascii_lowercase()) {
                    self.complete(m, NodeKind::EffectParam);
                } else {
                    if self.eat(TokenKind::Colon).is_some() {
                        loop {
                            let b = self.start(NodeKind::Bound)?;
                            self.eat(TokenKind::Question);
                            self.parse_path("trait bound")?;
                            self.complete(b, NodeKind::Bound);
                            if self.eat(TokenKind::Plus).is_none() {
                                break;
                            }
                        }
                    }
                    self.complete(m, NodeKind::TypeParam);
                }
            }
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.close_list(NodeKind::GenericParams, close)?;
        Ok(())
    }

    /// `(params)` of the node `around` (`Flow`, `Fn`, `Handler`,
    /// `ClosureExpr`); `require_types` is false for anonymous functions
    /// (§6.1). The inputs of a flow take doc comments (§2.1,
    /// [`crate::docs::elements_take_docs`]) and `@param` (§6.5).
    pub(super) fn parse_params(&mut self, require_types: bool, around: NodeKind) -> PResult<()> {
        let inputs = around == NodeKind::Flow;
        let docs_taken = crate::docs::elements_take_docs(NodeKind::ParamList, around);
        let m = self.start(NodeKind::ParamList)?;
        // S-412: the `(` after `fn` of an anonymous function follows
        // the rule of the parameters of a declaration (a blank before it is E0020).
        self.opens(TokenKind::LParen)?;
        self.with_nl(false, |p| {
            while !p.at(TokenKind::RParen) {
                let docs = if docs_taken { p.element_docs() } else { None };
                let param = p.start(NodeKind::Param)?;
                p.attach_docs(docs);
                let attrs = p.parse_attrs(false)?;
                // `@param` goes on an input of a flow (§6.5, §11.7).
                let place = if inputs { Place::FlowInput } else { Place::Other("a parameter of a function") };
                p.check_attrs(&attrs, place, None);
                p.parse_mode();
                let t = p.peek();
                let is_self = match t.kind {
                    TokenKind::KwSelf | TokenKind::Underscore => {
                        let n = p.start(NodeKind::Name)?;
                        p.bump();
                        p.complete(n, NodeKind::Name);
                        t.kind == TokenKind::KwSelf
                    }
                    TokenKind::Ident => {
                        p.parse_name("parameter name")?;
                        false
                    }
                    _ => return Err(p.unexpected("a parameter name")),
                };
                if p.eat(TokenKind::Colon).is_some() {
                    p.parse_type()?;
                } else if require_types && !is_self {
                    return Err(p.unexpected("`:` (parameter types are always written, P1)"));
                }
                p.complete(param, NodeKind::Param);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.close_list(NodeKind::ParamList, TokenKind::RParen)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::ParamList);
        Ok(())
    }

    pub(super) fn parse_mode(&mut self) {
        if self.eat(TokenKind::KwInout).is_none() {
            self.eat(TokenKind::KwMove);
        }
    }

    pub(super) fn parse_effect_row_opt(&mut self) -> PResult<()> {
        if self.eat(TokenKind::KwUses).is_none() {
            return Ok(());
        }
        let m = self.start(NodeKind::EffectRow)?;
        // In brackets the `{` is on the line of `uses` (E0003, S-413); out of
        // them the line ends at `uses`.
        if !self.significant() {
            self.e0003_unless_on_the_line(TokenKind::LBrace);
        }
        self.expect(TokenKind::LBrace)?;
        self.with_nl(false, |p| {
            while !p.at(TokenKind::RBrace) {
                p.parse_path("effect name")?;
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.close_list(NodeKind::EffectRow, TokenKind::RBrace)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::EffectRow);
        Ok(())
    }
}
