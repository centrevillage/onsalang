//! The file and the recovery: the top level of a file, the units (S-59), and
//! the skipping of a unit after a parse error with where it ends.

use super::*;

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ file

    #[cfg(test)]
    pub(crate) fn parse_file(self) -> ParseOutput {
        self.parse_units(ItemCtx::Top)
    }

    /// The declarations of the text read as those of a list of `ctx` (the
    /// top level of a file, or the members of an `impl`, a `trait`, ...),
    /// under a `SourceFile` node: a file, or the text of one unit read again
    /// in the context of its list (`crate::operands`).
    pub(crate) fn parse_units(mut self, ctx: ItemCtx) -> ParseOutput {
        let root = self.enter_unit(NodeKind::SourceFile, 0);
        if ctx == ItemCtx::Top {
            self.module_docs();
        }
        loop {
            let doc = self.collect_docs();
            if self.at(TokenKind::Eof) {
                break; // trailing doc comments without a declaration are dropped
            }
            let start = self.peek().span.start;
            let (depth, reported) = (self.open.len(), self.diagnostics.len());
            let m = self.start_item(doc);
            match self.parse_item(ctx, m) {
                Ok(item) => {
                    self.levels.push(item.height);
                    // Terminator: newline or end of file.
                    match self.peek_kind() {
                        TokenKind::Newline | TokenKind::Eof => {}
                        _ => {
                            // The tokens after the item on its line are of its
                            // unit (`crate::units`, S-274).
                            let _ = self.unexpected("newline after the declaration");
                            self.skip_unit(start, 0, false, true);
                        }
                    }
                }
                Err(ParseError) => {
                    // The item node stays open: the skipped tokens go inside it.
                    self.close_open(depth + 1);
                    self.skip_unit(start, 0, false, false);
                    self.close_open(depth);
                    self.failed_unit_reported(start, reported);
                }
            }
        }
        self.complete(root, NodeKind::SourceFile);
        self.release_held();
        let mut goes_on = vec![false; self.all.len()];
        for (k, &f) in self.full.iter().enumerate() {
            goes_on[f as usize] = self.lines.goes_on(k);
        }
        ParseOutput {
            goes_on,
            tokens: self.all,
            events: self.events,
            diagnostics: self.diagnostics,
            levels: self.levels,
            literals: self.literals,
            #[cfg(test)]
            height: self.height,
            items: self.items,
        }
    }

    /// Skip to the end of the unit that starts at `unit_start` after a syntax
    /// error in it (spec §18.1, S-59): the skipped tokens form an `Error` node
    /// in the open node. `base` is the number of brackets open around the
    /// unit (0 for a top-level item, the list's for a `member`). The unit ends:
    ///
    /// - at the start of an item at the beginning of a line, once the
    ///   brackets of the unit are closed ([`Parser::starts_an_item`]);
    /// - for a member, before the `}` that closes the list;
    /// - with a bracket that may stay open, at such a start on a line no deeper
    ///   than the brackets of the unit open there ([`Parser::ends_open`]); a
    ///   `{` that a `}` closes may not, and `(` and `[` have no such record;
    /// - at the end of the file; a member with brackets open also at that `}`.
    ///
    /// Brackets of the unit open where it ends get an E0002 whatever stopped
    /// its reading (§18.1 for `{`; `(` and `[` alike, S-280; R-371): the
    /// innermost has it, and the others open there, around the unit too, have
    /// notes (S-943, S-948). A unit whose brackets cannot be counted gets
    /// none ([`Parser::uncounted`]).
    ///
    /// With `line`, the unit is a finished item and the tokens after it on
    /// its line (S-274): the skip also ends at the end of that line, outside
    /// the brackets it opens.
    pub(super) fn skip_unit(&mut self, unit_start: u32, base: usize, member: bool, line: bool) {
        let mut braces = self.braces.clone();
        let from = self.peek_index();
        let mut i = from;
        // Where in `braces` the lowest bracket that may stay open is, kept
        // as they change: reading them at every item is quadratic.
        let mut stays_open = braces.iter().position(|&b| !self.brace_closed[b]);
        loop {
            let t = self.tokens[i];
            if t.kind == TokenKind::Eof || (line && t.kind == TokenKind::Newline && braces.len() <= base) {
                break;
            }
            if t.span.start > unit_start
                && self.starts_a_line(i)
                && self.starts_an_item(i)
                && (braces.len() <= base || (stays_open.is_some() && self.ends_open(i, &braces[base..])))
            {
                break;
            }
            // A `}` that closes no `{` of the member closes the list.
            let closed = crate::scan::pair(&mut braces, &self.tokens, i, base);
            stays_open = stays_open
                .filter(|&k| k < braces.len())
                .or_else(|| (braces.last() == Some(&i) && !self.brace_closed[i]).then(|| braces.len() - 1));
            if closed.is_none() && t.kind == TokenKind::RBrace && member {
                break;
            }
            i += 1;
        }
        // An error found at the token where the unit ends (the next item, the
        // end of the file) is this unit's, though that token is not.
        let stop = self.tokens[i].span.start;
        let mut first_at_stop = self.diagnostics.len();
        while first_at_stop > self.lexed && self.diagnostics[first_at_stop - 1].span.start >= stop {
            first_at_stop -= 1;
        }
        if braces.len() > base {
            // It is the unclosed bracket: reported at the bracket, not at that
            // token; once for all the units that end there. E0006 stays.
            let at_stop = self.diagnostics.split_off(first_at_stop);
            let uncounted = self.uncounted(unit_start, stop) || at_stop.iter().any(|d| d.code == Code::E0006);
            self.diagnostics.extend(at_stop.into_iter().filter(|d| d.code == Code::E0006));
            self.prefixed.retain(|s| s.start < stop);
            if !uncounted && self.reported_stop != Some(i) {
                self.reported_stop = Some(i);
                self.unclosed_brace(&braces, unit_start);
            }
        } else if self.tokens[i].kind != TokenKind::Eof {
            // It is reported where the unit stops (`fn f(` before the next
            // `fn`), so that it is of the unit (`crate::units`).
            // SPEC-GAP(S-276): the position of an error found at the token that
            // starts the next item: the end of the unit, as an empty span.
            let end = Span::new(self.file, self.last_end, self.last_end);
            for d in &mut self.diagnostics[first_at_stop..] {
                d.span = end;
                d.found = None;
            }
        }
        let first = (from..i).find(|&k| !self.tokens[k].kind.is_trivia());
        let last = (from..i).rev().find(|&k| !self.tokens[k].kind.is_trivia());
        if let (Some(first), Some(last)) = (first, last) {
            let m = self.enter_unit(NodeKind::Error, self.tokens[first].span.start);
            for k in first..=last {
                self.events.push(Event::Token(self.full[k]));
            }
            self.complete(m, NodeKind::Error);
            self.last_end = self.tokens[last].span.end.max(self.last_end);
        }
        self.pos = i;
        self.braces.truncate(base);
        if !member {
            self.nl.truncate(1);
        }
        self.no_struct_lit = false;
    }

    /// Whether the next token ends the unit being read where a `{` is never
    /// closed, at a statement or an element of a list (§18.1, S-487, S-593):
    /// the unit fails there with no diagnostic of its own, for the recovery
    /// stops at the same token ([`Parser::skip_unit`]) and reports the `{`.
    /// A correct program closes every `{`, so its reading does not change.
    pub(super) fn unit_ends_unclosed(&self) -> bool {
        let i = self.peek_index();
        self.starts_a_line(i)
            && self.starts_an_item(i)
            && self.braces.iter().any(|&b| self.tokens[b].kind == TokenKind::LBrace && !self.brace_closed[b])
            && self.ends_open(i, &self.braces[self.unit_brackets..])
    }

    /// Whether an item that starts `tokens[i]` ends a unit with the brackets
    /// `open`, those of the unit: its line is indented as much as or less than
    /// every line that opened one (§18.1). A deeper line ends nothing (S-943).
    /// The one judgment of the reading and the recovery; the indentation is
    /// read only in a file with an error, and never to pair the brackets (S-948).
    fn ends_open(&self, i: usize, open: &[usize]) -> bool {
        let indent = self.indent(self.tokens[i].span.start);
        open.iter().all(|&b| self.indent(self.tokens[b].span.start) >= indent)
    }

    /// Whether the brackets of the unit from `from` to `to` cannot be
    /// counted (§18.1, S-859): it has an E0006, or a literal or a `/*` that
    /// does not close, which a closing bracket may be in. By their place: the
    /// unit of an `impl` holds its members.
    fn uncounted(&self, from: u32, to: u32) -> bool {
        let mut own = self.diagnostics[self.lexed..].iter().rev().take_while(|d| d.span.start >= from);
        self.literals.unclosed_in(from, to) || own.any(|d| d.code == Code::E0006)
    }

    /// A unit that failed has a diagnostic: its reading, its brackets or the
    /// lexer's, `before` being the number of them when it started at `start`.
    pub(super) fn failed_unit_reported(&self, start: u32, before: usize) {
        let end = self.tokens[self.pos].span.start;
        if self.diagnostics.len() <= before && !self.literals.errors_in(start, end) {
            let span = Span::new(self.file, start, end);
            onsa_diag::internal::bug(Some(span), "a unit failed with no diagnostic");
        }
    }

    /// Whether `tokens[i]` starts an item, the one definition of it (§18.1,
    /// S-593): what starts its head ([`starts_heading`]), a doc comment, or
    /// the words before a head on the line, whatever else is read at the
    /// token.
    fn starts_an_item(&self, i: usize) -> bool {
        let kind = self.tokens[i].kind;
        starts_heading(kind) || kind.is_doc() || self.words_before_head_at(i).is_some()
    }

    /// Whether the next token is `kind` written at the end of a line, not at
    /// the head of the next one (`->`, the `|` of a pattern, §2.5, S-374,
    /// S-380): the one at the head is not read, and the table names it.
    pub(super) fn at_line_end(&self, kind: TokenKind) -> bool {
        let i = self.peek_index();
        self.tokens[i].kind == kind && !self.lines.at_line_head(i)
    }

    /// Whether `tokens[i]` starts a line that does not go on with the line
    /// before it: the recovery takes an item keyword there as the start of
    /// the next unit (S-47: `fn(I32) -> I32` after `type Op =` does not start one).
    fn starts_a_line(&self, i: usize) -> bool {
        i == 0 || (self.tokens[i - 1].kind == TokenKind::Newline && !self.lines.goes_on(i - 1))
    }

    /// The number of blanks before the first token of the line of `at`; a
    /// tab counts as one blank, as a space does (§18.1, S-943).
    fn indent(&self, at: u32) -> usize {
        crate::lexer::indent(self.text, at).len()
    }

    /// E0002 at the innermost of the brackets `open` where the unit starting
    /// at `unit_start` ends, with a note on the declaration it is in and one
    /// on each of the others, in order (§18.1, S-943, S-948).
    fn unclosed_brace(&mut self, open: &[usize], unit_start: u32) {
        let (&b, others) = open.split_last().expect("the unit has a bracket open");
        let brace = self.tokens[b];
        let first = self.tokens.partition_point(|t| t.span.start < unit_start);
        let keyword = (first..b).find(|&k| is_declaration_keyword(self.tokens[k].kind));
        // An `impl` and an `extern` block have no name of their own.
        let named = keyword.filter(|&k| !matches!(self.tokens[k].kind, TokenKind::KwImpl | TokenKind::KwExtern));
        let name = named.and_then(|k| (k + 1..b).find(|&n| self.tokens[n].kind == TokenKind::Ident));
        let open = self.token_text(brace).to_string();
        let close = match brace.kind {
            TokenKind::LParen => ")",
            TokenKind::LBracket => "]",
            _ => "}",
        };
        let mut d = Diagnostic::new(Stage::Syntax, Code::E0002, brace.span, format!("this `{open}` is never closed"))
            .with_rule(format!("every `{open}` is closed by a `{close}`; one that is not ends at the next item on a line indented as much as or less than the line of the `{open}`, or at the end of the file (§18.1)"));
        let place = if brace.kind == TokenKind::LBrace { "in the body of" } else { "in" };
        match (keyword, name) {
            (_, Some(n)) => {
                let t = self.tokens[n];
                d = d.with_note(t.span, format!("it is {place} `{}`", self.token_text(t)));
            }
            (Some(k), None) => {
                let t = self.tokens[k];
                d = d.with_note(t.span, format!("it is {place} this `{}`", self.token_text(t)));
            }
            (None, None) => {}
        }
        for &o in others {
            let t = self.tokens[o];
            d = d.with_note(t.span, format!("this `{}` is never closed either", self.token_text(t)));
        }
        self.report(d);
    }
}
