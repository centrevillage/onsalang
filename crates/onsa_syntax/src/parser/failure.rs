//! The failures of the parser: its diagnostics, and the questions to the
//! table of the forms of other languages at a failure ([`crate::foreign`]).

use super::*;

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ diagnostics

    pub(super) fn report(&mut self, d: Diagnostic) {
        self.diagnostics.push(d);
    }

    pub(super) fn error(&mut self, code: Code, span: Span, message: impl Into<String>) -> ParseError {
        let found = self.src(span).to_string();
        let mut d = Diagnostic::new(Stage::Syntax, code, span, message);
        if !found.is_empty() && !found.contains('\n') {
            d = d.with_found(found);
        }
        self.report(d);
        ParseError
    }

    pub(super) fn unexpected(&mut self, expected: &str) -> ParseError {
        self.fail(Want::Other, expected)
    }

    /// [`Parser::unexpected`] at a `fn` that declares a function, where
    /// `expected` goes: the message says where a function is declared, and
    /// what the unit wanted there, if it ends at that `fn`, is `expected`
    /// alone ([`Parser::skip_unit`], R-400).
    pub(super) fn unexpected_fn(&mut self, expected: &str) -> ParseError {
        let at = self.peek_index();
        self.unexpected(&format!("{expected} (a function is declared at the top level)"));
        if let Some((k, wanted)) = &mut self.wanted
            && *k == at
        {
            *wanted = expected.to_string();
        }
        ParseError
    }

    /// The one entry of the failures of the parser at the next token, where
    /// it wanted `want` (`expected`, for the message). The table of the forms
    /// of other languages says first whether the token starts such a form
    /// ([`foreign::at_failure`]); else, and also when the form is in a place
    /// where nothing of its kind goes (a literal `1.` among the items), the
    /// failure is the general E0002 (both are reported; the driver chooses
    /// one per unit, S-281).
    pub(super) fn fail(&mut self, want: Want, expected: &str) -> ParseError {
        self.fail_with(want, expected, None)
    }

    /// [`Parser::fail`], where the general E0002 says what came instead
    /// (`found`, a token after the failure: what follows a `^`) and gives the
    /// correct rule as its note (§18.1: a form of no row whose rule is known,
    /// S-358).
    pub(super) fn fail_noting(&mut self, want: Want, expected: &str, found: Token, rule: &str) -> ParseError {
        self.fail_with(want, expected, Some((found, rule)))
    }

    pub(super) fn fail_with(&mut self, want: Want, expected: &str, noted: Option<(Token, &str)>) -> ParseError {
        self.fail_at(want, expected, noted, None);
        ParseError
    }

    /// [`Parser::fail_with`], in the head of a declaration: the general
    /// E0002 is `own` when the parser knows the form (a run of words before
    /// the head, a keyword before a keyword, the modifiers out of order;
    /// §18.1, S-459, S-464). The token to read on from, if the head may be
    /// read on: after the form a row found when it ends on its line
    /// ([`foreign::Hit::resume`]), else `own`'s.
    pub(super) fn fail_at(
        &mut self,
        want: Want,
        expected: &str,
        noted: Option<(Token, &str)>,
        own: Option<Own>,
    ) -> Option<usize> {
        let named = self.named.take();
        // A guard reading only says whether the tokens read (no diagnostics).
        if self.guard.is_some() {
            return None;
        }
        let at = self.peek_index();
        let named = named.filter(|&(k, _)| k == at).map(|(_, kind)| kind);
        let t = self.tokens[at];
        self.wanted = Some((at, expected.to_string()));
        // The number of a literal written as in other languages (`1u8`,
        // `0o17`, `017`) is checked as any integer literal (E0408): two
        // errors of one token, of which the driver reports one.
        if t.kind == TokenKind::ForeignLit
            && let Some(n) = self.literals.number(t.span)
            && let Some(number) = n.number.int_body(self.token_text(t))
            && crate::literal::int_value(number).is_none()
        {
            self.report(Diagnostic::new(
                Stage::Syntax,
                Code::E0408,
                t.span,
                "integer literal is larger than any integer type holds",
            ));
        }
        let cursor = self.cursor(at, want);
        let foreign::Failure { rows, general, prefixed, resume } = foreign::at_failure(&cursor);
        self.prefixed.extend(prefixed);
        let read_by_a_row = !rows.is_empty();
        for d in rows {
            self.report(d);
        }
        let resume = resume.or(own.as_ref().map(|o| o.resume));
        if let (Some(_), Some(own)) = (&general, own) {
            let mut d = Diagnostic::new(Stage::Syntax, Code::E0002, own.span, own.message)
                .with_found(self.src(own.span).to_string())
                .with_rule(own.rule);
            for f in own.fixes {
                d = d.with_fix(f);
            }
            self.report(d);
            return resume;
        }
        // A `!(` after a value that is no name, where no `,` of a list goes
        // before it (R-339, S-631).
        let value_bang = self.value_bang == Some(at) && general.as_ref().is_some_and(Vec::is_empty);
        let noted = noted.or(value_bang.then_some((t, super::expressions::MARK_RULE)));
        // A reserved word, where nothing of this version takes it: its E0200
        // where it is read, instead of the general E0002 (§2.2, S-169, S-371).
        // `static` at the head of an item is read before (S-620,
        // `Parser::static_head`): here it is out of that place.
        let shown = noted.map_or(t, |(found, _)| found);
        if let Some(feature) = shown.kind.reserved() {
            let word = self.token_text(shown);
            let mut d = feature.diagnostic(Stage::Syntax, shown.span, &[]).with_found(word.to_string());
            // A path of a body that starts with it, where an operand is read
            // (`static.tick()`, S-674): a module of that name is read through
            // a `use` of its first name, and the path goes on from that name.
            let is = |k: Option<usize>, kind| k.filter(|&k| self.tokens[k].kind == kind);
            let link =
                |k| is(is(self.on_line_after(k), TokenKind::Dot).and_then(|d| self.on_line_after(d)), TokenKind::Ident);
            if let Some(name) = link(at).filter(|_| shown == t && want == Want::Expr) {
                let last = std::iter::successors(Some(name), |&k| link(k)).last().unwrap_or(name);
                let call = if is(self.on_line_after(last), TokenKind::LParen).is_some() { "()" } else { "" };
                let (first, path) =
                    (self.token_text(self.tokens[name]), self.src(self.tokens[name].span.to(self.tokens[last].span)));
                d = d.with_rule(format!("a path in a body does not start with the reserved word `{word}`; a module of that name is reached through a `use`: `use {word}.{first}`, then `{path}{call}` (§2.2, §15.1)"));
            }
            self.report(d);
            return resume;
        }
        if let Some(fixes) = general {
            let msg = format!("expected {expected}, found {}", shown.kind.describe());
            // A line that ends where it cannot: the main position is the end
            // of its code, before its comment, and the range is empty, so no
            // `found` (§18.1).
            let span = match t.kind {
                TokenKind::Newline => {
                    let code = (0..at).rev().find(|&k| !self.tokens[k].kind.is_trivia());
                    let end = code.map_or(t.span.start, |k| self.tokens[k].span.end);
                    Span::new(self.file, end, end)
                }
                _ => t.span,
            };
            let mut d = Diagnostic::new(Stage::Syntax, Code::E0002, span, msg);
            let found = self.src(shown.span);
            if !span.is_empty() && !found.is_empty() && !found.contains('\n') {
                d = d.with_found(found);
            } else if !span.is_empty() && noted.is_some() {
                // What came after the failure is no text (a line break, the
                // end of the file): it is named as the message names it.
                d = d.with_found(shown.kind.describe());
            }
            if let Some((_, rule)) = noted {
                d = d.with_rule(rule);
            }
            for f in fixes {
                d = d.with_fix(f);
            }
            // A keyword written as a name, of no form a row reads (S-654).
            if d.fixes.is_empty()
                && !read_by_a_row
                && noted.is_none()
                && let Some(to) = self.keyword_name(at, want, named)
            {
                d = d.with_fix(Fix::replace("write the name with a `_` at its end", t.span, to));
            }
            self.report(d);
        }
        resume
    }

    /// The candidate of the keyword at token `at` written as a name (§2.3,
    /// S-654): where a name of `named` is declared, or where an operand is
    /// (`want`), when the token after it goes on after a name; the name of
    /// an item with `@export` takes none (§14.2).
    fn keyword_name(&self, at: usize, want: Want, named: Option<Declared>) -> Option<String> {
        let t = self.tokens[at];
        if named.is_none() && want != Want::Expr {
            return None;
        }
        let next = self.on_line_after(at).map(|k| self.tokens[k].kind);
        if !crate::starts::keyword_as_name(t.kind, named.is_none())
            || !crate::starts::follows_a_name(next, named.is_some(), self.no_struct_lit)
        {
            return None;
        }
        let function = matches!(named, Some(Declared::Function | Declared::Flow));
        // SPEC-GAP(S-985): the name of a member of an `extern` block is the
        // symbol of C it binds, which a `_` at its end would change: none.
        if function && self.innermost(NodeKind::Extern).is_some() {
            return None;
        }
        let exported = function && self.exported_head(at);
        crate::naming::keyword_candidate(self.token_text(t), named, exported)
    }

    /// Where the innermost open node of `kind` starts.
    fn innermost(&self, kind: NodeKind) -> Option<u32> {
        let open = self.open.iter().rev();
        open.map(|o| (&self.events[o.event as usize], o.start))
            .find(|(e, _)| matches!(e, Event::Start { kind: Some(k), .. } if *k == kind))
            .map(|(_, start)| start)
    }

    /// Whether the head of the item being read, before token `at`, has the
    /// attribute `@export` (§14.2).
    fn exported_head(&self, at: usize) -> bool {
        let Some(start) = self.innermost(NodeKind::Item) else { return false };
        let first = self.tokens.partition_point(|t| t.span.start < start);
        (first..at).any(|k| {
            self.tokens[k].kind == TokenKind::At
                && self.tokens.get(k + 1).is_some_and(|n| self.token_text(*n) == crate::attrs::EXPORT)
        })
    }

    /// Read on to token `to` after a failure in the head of a declaration
    /// (§18.1, S-435): the tokens from the cursor up to it go into the node
    /// open, the part of the head that was not read.
    pub(super) fn read_on(&mut self, to: usize) {
        for k in self.pos..to {
            let t = self.tokens[k];
            if t.kind.is_trivia() {
                continue;
            }
            self.events.push(Event::Token(self.full[k]));
            self.last_end = t.span.end;
            crate::scan::pair(&mut self.braces, &self.tokens, k, 0);
        }
        self.pos = to;
        self.closed.clear();
    }

    /// The token after `tokens[k]` on its line, comments passed over; `None`
    /// at the end of the line or of the file.
    pub(super) fn on_line_after(&self, k: usize) -> Option<usize> {
        let j = (k + 1..self.tokens.len()).find(|&j| !self.tokens[j].kind.is_comment())?;
        (!matches!(self.tokens[j].kind, TokenKind::Newline | TokenKind::Eof)).then_some(j)
    }

    /// What the table of the forms of other languages reads of the parser
    /// at token `at` (a failure, or a form read whole), wanting `want`; the
    /// place of an attribute read there is set by the caller that knows it.
    pub(super) fn cursor(&self, at: usize, want: Want) -> foreign::Cursor<'_> {
        foreign::Cursor {
            file: self.file,
            text: self.text,
            tokens: &self.tokens,
            all: &self.all,
            full: &self.full,
            lines: &self.lines,
            literals: &self.literals,
            names: &self.names,
            apart: &self.apart,
            brackets: &self.brackets,
            at,
            open: self
                .open
                .iter()
                .map(|o| match self.events[o.event as usize] {
                    Event::Start { kind: Some(k), .. } => (k, o.start),
                    _ => (NodeKind::Error, o.start),
                })
                .collect(),
            closed: &self.closed,
            want,
            detached: self.detached.filter(|d| d.at == at),
            ends: &self.ends,
            reach: self.open.iter().map(|o| o.level + o.children).max().unwrap_or(0),
            place: None,
            declaration: None,
            word: None,
        }
    }

    /// A form of another language or a redundant mark that the parser reads
    /// whole, starting at token `at` (an old attribute, a redundant
    /// visibility; [`foreign::Detect::Read`]), at `place` (an attribute's,
    /// and the keyword of the declaration whose head holds it, if any): the
    /// table's diagnostics are reported, and whether there was one. The
    /// reading goes on (the unit has the syntax error, so its body is not
    /// checked).
    pub(super) fn read_form(&mut self, at: usize, place: Option<Place>, declaration: Option<usize>) -> bool {
        self.read_at(at, |c| (c.place, c.declaration) = (place, declaration))
    }

    /// The visibility word at token `word` in a place that takes none, on
    /// what `on` says (§15.1, S-491): its row is reported, and the reading
    /// goes on, as at [`Parser::read_form`].
    pub(super) fn read_word(&mut self, word: usize, on: foreign::WordOn) {
        if !self.read_at(word, |c| c.word = Some(on)) {
            onsa_diag::internal::bug(Some(self.tokens[word].span), "a visibility word that no row reads");
        }
    }

    /// [`Parser::read_form`] with what the parser knows set on the cursor by `set`.
    fn read_at(&mut self, at: usize, set: impl FnOnce(&mut foreign::Cursor)) -> bool {
        let mut cursor = self.cursor(at, Want::Other);
        set(&mut cursor);
        let found = foreign::at_read(&cursor);
        let any = !found.is_empty();
        for d in found {
            self.report(d);
        }
        any
    }

    pub(super) fn expect(&mut self, kind: TokenKind) -> PResult<Token> {
        if self.at(kind) { Ok(self.bump()) } else { Err(self.unexpected(kind.describe())) }
    }

    /// E0408 when an integer literal does not fit any integer type (the
    /// value is read by the same function when the AST is made). A number
    /// with the lexer's E0001 (`123abc`, `0x_`) has that error alone.
    pub(super) fn check_int(&mut self, t: Token) {
        if crate::literal::int_value(self.token_text(t)).is_none() && self.literals.ok(t.span) {
            self.report(Diagnostic::new(
                Stage::Syntax,
                Code::E0408,
                t.span,
                "integer literal is larger than any integer type holds",
            ));
        }
    }

    /// The held errors of the content of the literals of each run that no
    /// row reported ([`foreign::held_errors`]), after the whole file is read
    /// (S-400, [`crate::literal::Run`]).
    pub(super) fn release_held(&mut self) {
        if self.literals.runs().is_empty() {
            return;
        }
        let held: Vec<Diagnostic> = foreign::held_errors(&self.literals, &self.prefixed).cloned().collect();
        self.diagnostics.extend(held);
    }
}

/// The general E0002 of a failure in the head of a declaration whose form
/// the parser knows ([`Parser::fail_at`]): its range, message, rule and
/// candidates, and the token the head is read on from.
pub(super) struct Own {
    pub(super) span: Span,
    pub(super) message: String,
    pub(super) rule: &'static str,
    pub(super) fixes: Vec<Fix>,
    pub(super) resume: usize,
}
