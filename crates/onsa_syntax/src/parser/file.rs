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
                            let breaks = ctx == ItemCtx::Top && self.starts_only_a_line(self.peek_index(), true);
                            let _ = self.fail(Want::LineEnd { breaks }, "newline after the declaration");
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
            item_starts: self.item_starts,
            apart: self.apart.into_inner(),
        }
    }

    /// Skip to the end of the unit that starts at `unit_start` after a syntax
    /// error in it (spec §18.1, S-59): the skipped tokens form an `Error` node
    /// in the open node. `base` is the number of brackets open around the
    /// unit (0 for a top-level item, the list's for a `member`). The unit ends:
    ///
    /// - at the start of an item at the head of a line, also of one that goes
    ///   on with the line before it (S-947), once the brackets of the unit
    ///   are closed ([`Parser::starts_an_item`]);
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
    /// its line (S-274), as it is once a `}` closes the brackets of the unit
    /// (the body, §18.1, R-421) and after a form of `static` (S-620): the
    /// skip also ends at the end of that line, outside
    /// the brackets it opens, the line going on as §2.5 reads (S-950) and
    /// after a `::` of a path at its end, when the unit failed at a path's `::`
    /// ([`crate::foreign::path_colons`]), with the name after it (S-963: `use std::`
    /// and `math` on the next line, as `use std.` and `math`).
    pub(super) fn skip_unit(&mut self, unit_start: u32, base: usize, member: bool, line: bool) {
        let form = self.static_line.take();
        let first = self.tokens.partition_point(|t| t.span.start < unit_start);
        // A reading that failed after a `}` closed the brackets of the unit
        // (a `use` list read whole, S-696) is as the skip past that `}` below.
        let closed = (first..self.pos).rev().find(|&k| self.tokens[k].kind.is_code());
        let closed = closed.is_some_and(|k| self.tokens[k].kind == TokenKind::RBrace) && self.braces.len() <= base;
        let mut line = line || form.is_some() || closed;
        // A function of C goes on to the body its next line opens (S-620).
        let mut body = form == Some(true);
        let mut braces = self.braces.clone();
        // Where in `braces` the lowest bracket that may stay open is, kept
        // as they change: reading them at every item is quadratic.
        let mut stays_open = braces.iter().position(|&b| !self.brace_closed[b]);
        // An item that starts at the head of the line of the failure, or of
        // the lines of its doc comments and attributes alone right before it,
        // which the reading read on from (`export` of `export fn h`, S-947),
        // on a line that goes on with the one before or in a bracket (not the
        // line of the head after its attributes): the unit ends there, the
        // reading of it undone.
        let mut head = (first..=self.peek_index()).rev().find(|&k| self.lines.at_line_head(k));
        while let Some(line) = head.and_then(|h| self.line_before(h, first))
            && (self.tokens[line].kind.is_doc() || self.attributes_alone(line).is_some())
        {
            head = Some(line);
        }
        if let Some(head) = head.filter(|&h| h < self.pos)
            && crate::scan::balanced(&self.tokens[head..self.pos])
            && self.unit_ends_at(head, unit_start, base, &braces, stays_open.is_some())
            && (braces.len() > base || self.lines.goes_on(head - 1))
        {
            self.unread_from(head, first);
        }
        // From the cursor: a doc comment that the reading passed as trivia
        // (on a line that goes on with the one before) starts an item (S-947).
        let from = self.pos;
        let mut i = from;
        // The last attribute that closes on its line: a line that ends with
        // it goes on (§2.5).
        let mut attribute = None;
        let (mut last, path) = (None, crate::foreign::path_colons(&self.tokens, from));
        loop {
            let t = self.tokens[i];
            let line_ends = t.kind == TokenKind::Newline
                && braces.len() <= base
                && !self.lines.goes_on(i)
                && !(path && last.is_some_and(|l| crate::foreign::path_colons(&self.tokens, l)))
                && !attribute.is_some_and(|e: usize| self.tokens[e + 1..i].iter().all(|c| c.kind.is_comment()));
            let opens = || self.tokens[i..].iter().find(|c| !c.kind.is_comment() && !c.kind.is_trivia());
            if line && line_ends && std::mem::take(&mut body) && opens().is_some_and(|c| c.kind == TokenKind::LBrace) {
                line = false;
            } else if t.kind == TokenKind::Eof || (line && line_ends) {
                break;
            }
            body &= t.kind != TokenKind::LBrace;
            if line && matches!(t.kind, TokenKind::At | TokenKind::Hash) {
                attribute = self.attribute_end(i);
            }
            last = Some(i).filter(|_| !t.kind.is_trivia() && !t.kind.is_comment()).or(last);
            if self.unit_ends_at(i, unit_start, base, &braces, stays_open.is_some()) {
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
            line |= closed.is_some() && t.kind == TokenKind::RBrace && braces.len() <= base;
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
            // `fn`), so that it is of the unit (`crate::units`): at the end of
            // the unit, as an empty span (§18.1, S-276): the general E0002,
            // though the token that starts the next unit is a reserved word
            // (R-400, S-952). Failed at that token or after comments only, it
            // is what the unit wants after its last token. E0006 stays.
            let end = Span::new(self.file, self.last_end, self.last_end);
            let general = self.diagnostics[first_at_stop..].iter().any(|d| d.code != Code::E0006);
            let last = (first..i).rev().find(|&k| !self.tokens[k].kind.is_trivia());
            let failed = self.wanted.take().filter(|w| {
                let at = self.tokens[w.0].span.start;
                w.0 >= i
                    && self.tokens[i..w.0].iter().all(|t| t.kind.is_trivia())
                    && self.diagnostics[first_at_stop..].iter().any(|d| d.span.start == at)
            });
            if let (Some(last), Some((_, expected)), true) = (last, failed, general) {
                let at_stop = self.diagnostics.split_off(first_at_stop);
                self.diagnostics.extend(at_stop.into_iter().filter(|d| d.code == Code::E0006));
                let message = format!("expected {expected} after {}", self.tokens[last].kind.describe());
                self.report(Diagnostic::new(Stage::Syntax, Code::E0002, end, message));
            }
            for d in &mut self.diagnostics[first_at_stop..] {
                d.span = end;
                d.found = None;
                if d.code != Code::E0006 {
                    d.code = Code::E0002;
                }
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

    /// The first token of the line of code before the line of `tokens[h]`
    /// (blank lines passed), from `first` on.
    fn line_before(&self, h: usize, first: usize) -> Option<usize> {
        let last = (first..h).rev().find(|&k| self.tokens[k].kind != TokenKind::Newline)?;
        (first..=last).rev().find(|&k| self.lines.at_line_head(k))
    }

    /// Whether the unit from `unit_start` ends at `tokens[i]`, with `braces`
    /// open there, `base` of them around the unit, and one that may stay
    /// open among them if `stays_open` ([`Parser::skip_unit`]).
    fn unit_ends_at(&self, i: usize, unit_start: u32, base: usize, braces: &[usize], stays_open: bool) -> bool {
        self.tokens[i].span.start > unit_start
            && self.lines.at_line_head(i)
            && self.starts_an_item(i)
            && (braces.len() <= base || (stays_open && self.ends_open(i, &braces[base..])))
    }

    /// Whether the next token ends the unit being read where a `{` is never
    /// closed, at a statement or an element of a list (§18.1, S-487, S-593):
    /// the unit fails there with no diagnostic of its own, for the recovery
    /// stops at the same token ([`Parser::skip_unit`]) and reports the `{`.
    /// A correct program closes every `{`, so its reading does not change.
    pub(super) fn unit_ends_unclosed(&self) -> bool {
        let i = self.peek_index();
        self.lines.at_line_head(i)
            && self.starts_an_item(i)
            && self.braces.iter().any(|&b| self.tokens[b].kind == TokenKind::LBrace && !self.brace_closed[b])
            && self.ends_open(i, &self.braces[self.unit_brackets..])
    }

    /// Whether the unit from `unit_start` ends at `tokens[i]` with the
    /// brackets open now, as its skip ends it ([`Parser::unit_ends_at`]): for
    /// a reading that passes tokens of the unit (a `use` element, S-696).
    pub(super) fn unit_ends_here(&self, i: usize, unit_start: u32) -> bool {
        self.lines.at_line_head(i) && self.starts_an_item(i) && {
            let stays_open = self.braces.iter().any(|&b| !self.brace_closed[b]);
            self.unit_ends_at(i, unit_start, self.unit_brackets, &self.braces, stays_open)
        }
    }

    /// [`Parser::unit_ends_unclosed`] with the brackets of the unit around
    /// the member read (those of the file: a list of members is of a
    /// top-level item), as the list asks it at the start of a member.
    pub(super) fn list_ends_unclosed(&mut self) -> bool {
        let member = std::mem::replace(&mut self.unit_brackets, 0);
        let ends = self.unit_ends_unclosed();
        self.unit_brackets = member;
        ends
    }

    /// Whether an item that starts `tokens[i]` ends a unit with the brackets
    /// `open`, those of the unit: its line is indented as much as or less than
    /// every line that opened one (§18.1). A deeper line ends nothing (S-943).
    /// The one judgment of the reading and the recovery; the indentation is
    /// read only in a file with an error, and never to pair the brackets (S-948).
    fn ends_open(&self, i: usize, open: &[usize]) -> bool {
        let indent = self.indent(self.tokens[self.item_line(i)].span.start);
        // The brackets are in order (outermost first): the text is read back
        // to the start of each line once, not for each bracket on it (R-446).
        let (mut from, mut start) = (0, 0);
        open.iter().all(|&b| {
            let at = self.tokens[b].span.start as usize;
            start = self.text[from..at].rfind('\n').map_or(start, |k| from + k + 1);
            from = at;
            self.indent(start as u32) >= indent
        })
    }

    /// The first token of the line that an item starting at `tokens[i]`, at
    /// the head of a line, is measured at (§18.1, S-947): past the lines of
    /// attributes alone (`@name`, `@name(…)` and `#[…]`, closed on their
    /// line), that of the item they are of. The last run walked is kept, so
    /// a skip asks at each of its lines in linear time.
    fn item_line(&self, i: usize) -> usize {
        let (from, line) = self.attribute_lines.get();
        if (from..line).contains(&i) {
            return line;
        }
        let mut line = i;
        while let Some(end) = self.attributes_alone(line) {
            line = self.next_past_line_ends(end);
        }
        self.attribute_lines.set((i, line));
        line
    }

    /// The last token of the line of `tokens[k]` when from `k` on it has
    /// attributes alone, each closed on the line ([`Parser::attribute_end`]).
    fn attributes_alone(&self, mut k: usize) -> Option<usize> {
        loop {
            let end = self.attribute_end(k)?;
            match self.on_line_after(end) {
                Some(next) => k = next,
                None => return Some(end),
            }
        }
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
    /// S-593): what starts its head ([`starts_heading`]) but `fn(` and `rt
    /// fn(` (S-947), a doc comment, or the words before a head on the line,
    /// whatever else is read at the token.
    pub(super) fn starts_an_item(&self, i: usize) -> bool {
        (self.heading_at(i) && !self.function_value_at(i))
            || self.tokens[i].kind.is_doc()
            || self.words_before_head_at(i).is_some()
    }

    /// Whether `tokens[i]` starts a head ([`starts_heading`]), a `#` only
    /// with the `[` of `#[` right after it (§18.1, R-399, R-423).
    pub(super) fn heading_at(&self, i: usize) -> bool {
        let t = self.tokens[i];
        let bracket = |n: &Token| n.kind == TokenKind::LBracket && n.span.start == t.span.end;
        starts_heading(t.kind) && (t.kind != TokenKind::Hash || self.tokens.get(i + 1).is_some_and(bracket))
    }

    /// Whether the token `i` after a statement on its line (`top`: after an
    /// item of the top level) starts only a statement (an item) there, so a
    /// line break before it makes the line right (§2.5, S-401): a keyword of
    /// a statement that is no expression but `move` (which marks the value
    /// of one), or attributes before a `let`; at the top level, the start of
    /// an item but `fn(`, or attributes (`@`, `#[`) before one. An attribute
    /// is looked at to its end on its line, without a trial reading (§18.1:
    /// else a line break leaves its error).
    pub(super) fn starts_only_a_line(&self, i: usize, top: bool) -> bool {
        use TokenKind::*;
        let mut k = i;
        while matches!(self.tokens[k].kind, At | Hash) {
            let Some(end) = self.attribute_end(k) else { return false };
            k = self.next_past_line_ends(end);
        }
        let kind = self.tokens[k].kind;
        match top {
            true => starts_heading(kind) && !self.function_value_at(k),
            false if k > i => kind == KwLet,
            false => crate::starts::starts_statement(kind) && kind != KwMove,
        }
    }

    /// Whether `fn` at `tokens[i]`, or after the `rt` there on its line, opens
    /// a function type or an anonymous function ([`opens_a_function_value`]).
    fn function_value_at(&self, i: usize) -> bool {
        let f = if self.tokens[i].kind == TokenKind::KwRt { self.on_line_after(i) } else { Some(i) };
        let next = |f| self.on_line_after(f).map(|n| self.tokens[n].kind);
        f.is_some_and(|f| opens_a_function_value(self.tokens[f].kind, next(f)))
    }

    /// Whether the next token is `kind` written at the end of a line, not at
    /// the head of the next one (`->`, the `|` of a pattern, §2.5, S-374,
    /// S-380): the one at the head is not read, and the table names it.
    pub(super) fn at_line_end(&self, kind: TokenKind) -> bool {
        let i = self.peek_index();
        self.tokens[i].kind == kind && !self.lines.at_line_head(i)
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
            d = d.with_note(t.span, format!("this `{}` is open here too", self.token_text(t)));
        }
        self.report(d);
    }
}
