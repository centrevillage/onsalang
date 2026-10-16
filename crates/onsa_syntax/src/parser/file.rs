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
            let depth = self.open.len();
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
                }
            }
        }
        self.complete(root, NodeKind::SourceFile);
        self.release_held();
        ParseOutput {
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
    /// - at a token that may start an item at the beginning of a line, once
    ///   the brackets of the unit are closed;
    /// - for a member, before the `}` that closes the list;
    /// - at a keyword that starts an item at the beginning of a line indented
    ///   as much as or less than every line that opened a bracket of the unit
    ///   still open: that bracket is never closed, and the innermost of them
    ///   gets the E0002 (§18.1 for `{`; `(` and `[` alike, S-280). The
    ///   indentation is read only here, in a file with an error. At the end
    ///   of the file, likewise when the reading stopped there (`expected `}`,
    ///   found end of file`); when another error stopped it earlier (E0006,
    ///   ...), the open brackets follow from that error and get no diagnostic
    ///   (2026-10-08, the parent's decision).
    ///
    /// With `line`, the unit is a finished item and the tokens after it on
    /// its line (S-274): the skip also ends at the end of that line, outside
    /// the brackets it opens.
    pub(super) fn skip_unit(&mut self, unit_start: u32, base: usize, member: bool, line: bool) {
        let mut braces = self.braces.clone();
        let from = self.peek_index();
        let mut i = from;
        let mut unclosed = None;
        loop {
            let t = self.tokens[i];
            if t.kind == TokenKind::Eof {
                // A `{` of the unit still open at the end of the file: it is the
                // error when the reading stopped at the end (below).
                if braces.len() > base {
                    unclosed = braces.last().copied();
                }
                break;
            }
            if line && t.kind == TokenKind::Newline && braces.len() <= base {
                break;
            }
            // SPEC-GAP(S-487): a line that starts with words before a head
            // (`export "C" fn h`, S-459) starts a declaration too, once the
            // brackets of the unit are closed; the head is read on after
            // the words.
            if t.span.start > unit_start
                && braces.len() <= base
                && self.starts_a_line(i)
                && self.words_before_head_at(i).is_some()
            {
                break;
            }
            if t.span.start > unit_start && self.starts_a_line(i) && is_item_start(t.kind) {
                if braces.len() <= base {
                    break;
                }
                let indent = self.indent(t.span.start);
                if braces[base..].iter().all(|&b| self.indent(self.tokens[b].span.start) >= indent) {
                    unclosed = braces.last().copied();
                    break;
                }
            }
            if is_opening(t.kind) {
                braces.push(i);
            } else if is_closing(t.kind) && !close_bracket(&mut braces, &self.tokens, t.kind, base) {
                // A `}` that closes no `{` of the member closes the list.
                if t.kind == TokenKind::RBrace && member {
                    break;
                }
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
        let at_end = self.tokens[i].kind == TokenKind::Eof;
        if at_end && first_at_stop == self.diagnostics.len() {
            unclosed = None;
        }
        if let Some(b) = unclosed {
            // It is the unclosed bracket: reported at the bracket, not at that
            // token; once for all the units that end there.
            self.diagnostics.truncate(first_at_stop);
            self.prefixed.retain(|s| s.start < stop);
            if self.reported_stop != Some(i) {
                self.reported_stop = Some(i);
                self.unclosed_brace(b, unit_start);
            }
        } else if !at_end {
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

    /// The next token starts an item at the beginning of a line indented as
    /// much as or less than the line of the `{` of the list of members open
    /// around it (`base` brackets), and that `{` is never closed.
    pub(super) fn list_ends_unclosed(&self, base: usize) -> bool {
        let i = self.peek_index();
        let t = self.tokens[i];
        let Some(&brace) = self.braces[..base].last() else { return false };
        self.starts_a_line(i)
            && is_item_start(t.kind)
            && !self.brace_closed[brace]
            && self.indent(t.span.start) <= self.indent(self.tokens[brace].span.start)
    }

    /// The last token read ends a statement or a declaration that is no
    /// operand ([`Parser::ends`]).
    pub(super) fn end_no_operand(&mut self) {
        self.end_with(End::NoOperand);
    }

    pub(super) fn end_with(&mut self, end: End) {
        if let Some(last) = (0..self.pos).rev().find(|&k| !self.tokens[k].kind.is_trivia()) {
            // In order (the table searches them): a statement ends after the
            // ones before it, and a declaration after its own statements.
            debug_assert!(self.ends.last().is_none_or(|e| e.0 <= last), "the ends out of order");
            if self.ends.last().is_some_and(|e| e.0 == last) {
                // A declaration ends where its last statement did (`fn f() { for … { } }`
                // does not end there): the outer one says what follows.
                self.ends.pop();
            }
            self.ends.push((last, end));
        }
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

    /// The number of blanks before the first token of the line of `at`.
    fn indent(&self, at: u32) -> usize {
        let line = self.text[..at as usize].rfind('\n').map_or(0, |i| i + 1);
        self.text[line..].chars().take_while(|c| *c == ' ' || *c == '\t').count()
    }

    /// E0002 at the bracket (token `b`) that the unit starting at `unit_start`
    /// never closes, with a note on the declaration it is in (§18.1).
    fn unclosed_brace(&mut self, b: usize, unit_start: u32) {
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
        self.report(d);
    }
}

/// A token that starts an item: what starts its head ([`starts_heading`]) or a doc comment.
fn is_item_start(kind: TokenKind) -> bool {
    starts_heading(kind) || kind.is_doc()
}
