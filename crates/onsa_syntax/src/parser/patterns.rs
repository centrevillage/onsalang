//! The patterns.

use super::*;

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ patterns

    pub(super) fn parse_pattern(&mut self) -> PResult<Completed> {
        let first = self.parse_pattern_alt()?;
        if !self.at_line_end(TokenKind::Pipe) {
            return Ok(first);
        }
        let m = self.precede(first, NodeKind::OrPat)?;
        while self.at_line_end(TokenKind::Pipe) {
            self.bump();
            self.parse_pattern_alt()?;
        }
        Ok(self.complete(m, NodeKind::OrPat))
    }

    /// After a `-` in a pattern: `(`s, an integer and as many `)`s (the negative
    /// literal `-(128)`, S-185). Comments and newlines inside are skipped.
    fn parenthesised_int_after_minus(&self) -> bool {
        let mut i = self.peek2_index();
        let next = |i: &mut usize| loop {
            let t = self.tokens[*i];
            if t.kind != TokenKind::Eof {
                *i += 1;
            }
            match t.kind {
                k if k == TokenKind::Newline || k.is_line_comment() => {}
                k => return k,
            }
        };
        let mut opens = 0;
        let mut k = next(&mut i);
        while k == TokenKind::LParen {
            opens += 1;
            k = next(&mut i);
        }
        if opens == 0 || k != TokenKind::Int {
            return false;
        }
        (0..opens).all(|_| next(&mut i) == TokenKind::RParen)
    }

    /// Whether `t` is a number written as in other languages that is an
    /// integer in Onsa (`017`, `1u8`, `0o17`; [`crate::literal::Number::is_float`]).
    fn foreign_integer(&self, t: Token) -> bool {
        t.kind == TokenKind::ForeignLit && self.literals.number(t.span).is_some_and(|n| !n.number.is_float())
    }

    /// After a `-` in a pattern: `(`s and a `-` (`-(-1)`, S-227).
    fn negated_negative(&self) -> bool {
        let mut kinds = self.tokens[self.peek_index() + 1..].iter().map(|t| t.kind).filter(|k| !k.is_trivia());
        let mut opens = 0;
        loop {
            match kinds.next() {
                Some(TokenKind::LParen) => opens += 1,
                Some(TokenKind::Minus) => return opens > 0,
                _ => return false,
            }
        }
    }

    /// What follows the pattern being read: `=>` in an arm of `match`, `=`
    /// in a `let`, `in` in a `for` (the words of a failure in it).
    fn pattern_end(&self) -> &'static str {
        let owner = self.open.iter().rev().find_map(|o| match self.events[o.event as usize] {
            Event::Start { kind: Some(k @ (NodeKind::MatchArm | NodeKind::LetStmt | NodeKind::ForStmt)), .. } => {
                Some(k)
            }
            _ => None,
        });
        match owner {
            Some(NodeKind::LetStmt) => "`=`",
            Some(NodeKind::ForStmt) => "`in`",
            _ => "`=>`",
        }
    }

    /// Whether the string literal `t` interpolates (`{x}`, §2.4,
    /// [`Literals::interpolated`]).
    fn has_holes(&self, t: Token) -> bool {
        self.literals.interpolated(t.span)
    }

    fn parse_pattern_alt(&mut self) -> PResult<Completed> {
        let t = self.peek();
        // A range (`1..<3`, `..=5`, `lo..<n + 1`; spec §7): no pattern. The
        // table of the forms reads it from its first token (the guard form).
        let rest =
            self.tokens[self.pos..].iter().map(|t| t.kind).filter(|k| !k.is_trivia() || *k == TokenKind::Newline);
        if pattern_alternative(rest).1.is_some() {
            return Err(self.fail(Want::Pattern, "a pattern"));
        }
        let kind = match t.kind {
            TokenKind::Underscore => NodeKind::WildPat,
            // `-1`, and `-(1)` / `-((1))`: the parentheses between `-` and the integer are not
            // seen (§7, §4.7; S-184, S-185). `-(-1)` is no literal (S-227) and stays E0002.
            // The `-` of a negative literal touches it, as every prefix `-` does
            // (§2.5, S-411): the table names the form ([`Want::Prefix`],
            // `space_after_prefix`, `newline_after_prefix`). Only the `-` of a
            // negative literal: a range, a float or a constant after it is the
            // form of its own row (read above and below), and another operand
            // is no pattern whatever the blank (the general E0002).
            TokenKind::Minus
                if self.gap_after(self.peek_index()).is_some()
                    && (self.tokens[self.next_code(self.peek_index())].kind == TokenKind::Int
                        || self.parenthesised_int_after_minus()) =>
            {
                return Err(self.fail(Want::Prefix, "a pattern"));
            }
            // `-017`, `-1u8`: an integer written as in other languages, whose
            // row the table names at the number, as in an expression (§2.4,
            // §18.1); a float after the `-` is the float pattern's (S-248),
            // and a blank after the `-` the general E0002, as before a name.
            TokenKind::Minus if !self.gap_after(self.peek_index()).is_some() && self.foreign_integer(self.peek2()) => {
                let _negative = self.start(NodeKind::NegLitPat)?;
                self.bump();
                return Err(self.fail(Want::Pattern, "a pattern"));
            }
            TokenKind::Minus if self.peek2().kind == TokenKind::Int || self.parenthesised_int_after_minus() => {
                let m = self.start(NodeKind::NegLitPat)?;
                self.bump();
                self.with_nl(false, |p| {
                    let mut opens = 0;
                    while p.eat(TokenKind::LParen).is_some() {
                        opens += 1;
                    }
                    let n = p.bump();
                    p.check_int(n);
                    for _ in 0..opens {
                        p.bump();
                    }
                });
                return Ok(self.complete(m, NodeKind::NegLitPat));
            }
            // `-(-1)` is no literal (S-227, R-156).
            TokenKind::Minus if self.negated_negative() => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "a pattern's `-` is on an integer literal or a constant; `-(-1)` is neither (§7)",
                ));
            }
            TokenKind::Int => {
                let m = self.start(NodeKind::LitPat)?;
                self.bump();
                self.check_int(t);
                return Ok(self.complete(m, NodeKind::LitPat));
            }
            // A string with an interpolation makes a value: no pattern (§7, S-225).
            TokenKind::Str if self.has_holes(t) => return Err(self.fail(Want::Pattern, "a pattern")),
            k if crate::starts::literal_pattern(k) => NodeKind::LitPat,
            // `()`, `(p)` (a group, §2.4, R-43) or `(p, q, ...)`.
            TokenKind::LParen => {
                let m = self.start(NodeKind::TuplePat)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    if p.eat(TokenKind::RParen).is_some() {
                        return Ok(NodeKind::TuplePat);
                    }
                    p.parse_pattern()?;
                    let Some(comma) = p.eat(TokenKind::Comma) else {
                        p.close_list(NodeKind::TuplePat, TokenKind::RParen)?;
                        return Ok(NodeKind::ParenPat);
                    };
                    if p.at(TokenKind::RParen) {
                        return Err(p.one_element(comma));
                    }
                    while !p.at(TokenKind::RParen) {
                        p.parse_pattern()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::TuplePat, TokenKind::RParen)?;
                    Ok(NodeKind::TuplePat)
                })?;
                return Ok(self.complete(m, kind));
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let m = self.start(NodeKind::PathPat)?;
                let path = self.parse_path("a pattern")?;
                if self.touches_bare(TokenKind::LParen)? {
                    self.reshape(NodeKind::TupleStructPat)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RParen) {
                            p.parse_pattern()?;
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.close_list(NodeKind::TupleStructPat, TokenKind::RParen)?;
                        Ok(())
                    })?;
                    return Ok(self.complete(m, NodeKind::TupleStructPat));
                }
                // The `{` of a struct pattern is on the line of its name, in
                // brackets and in a `let` alike (E0003, S-413).
                if crate::naming::is_type_name(self.token_text(path.last))
                    && self.e0003_unless_on_the_line(TokenKind::LBrace)
                {
                    self.reshape(NodeKind::StructPat)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RBrace) {
                            // The rest `..`, last (§7: the stage that counts the
                            // fields reports it, S-109, S-366).
                            if p.at(TokenKind::DotDot) {
                                let r = p.start(NodeKind::StructPatRest)?;
                                p.bump();
                                p.complete(r, NodeKind::StructPatRest);
                                break;
                            }
                            let f = p.start(NodeKind::StructPatField)?;
                            p.parse_ident("field name")?;
                            p.expect(TokenKind::Colon)?;
                            p.parse_pattern()?;
                            p.complete(f, NodeKind::StructPatField);
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.close_list(NodeKind::StructPat, TokenKind::RBrace)?;
                        Ok(())
                    })?;
                    return Ok(self.complete(m, NodeKind::StructPat));
                }
                // `n @ p` (§7, S-186): no pattern; the table reads it at `@`.
                if self.at(TokenKind::At) {
                    let after = self.pattern_end();
                    return Err(self.fail(Want::Pattern, after));
                }
                let bind = path.segments == 1 && crate::naming::is_binding_name(self.token_text(path.first));
                return Ok(self.complete(m, if bind { NodeKind::BindPat } else { NodeKind::PathPat }));
            }
            _ => return Err(self.fail(Want::Pattern, "a pattern")),
        };
        let m = self.start(kind)?;
        self.bump();
        Ok(self.complete(m, kind))
    }
}
