//! The head of a declaration before its keyword (§18.1): its attributes, its
//! visibility and its modifiers, and the reading on after a form that the
//! head does not take (S-435, S-459, S-464, S-481, S-492, S-593).
//!
//! What was not read stays in the head, before the declaration's node: an
//! incomplete `Attr` (an attribute that was not read, S-460) or `Vis` node
//! (a visibility of another language), or an `Error` node (a run of words, a
//! keyword before a keyword, the modifiers out of order, an `rt` before a
//! form), whose `pub`, `priv` and `rt` are the modifiers written
//! ([`crate::lower`]). The tokens of a head of an `extern` block that does
//! not read stay in its node (S-477). The unit has
//! the syntax error, so the declaration is a read one whose body is not
//! checked (`crate::units`, `Failed::Unit`).

use onsa_diag::{Edit, Note};

use super::items::{SeenAttr, VisRead};
use super::*;

/// The head of a declaration as read ([`Parser::parse_heading`]).
pub(super) struct Heading {
    /// The attributes of Onsa read whole.
    pub attrs: Vec<SeenAttr>,
    /// The index of the visibility word read whole.
    pub vis: Option<usize>,
    /// The keyword of the declaration (the next token).
    pub keyword: Token,
    pub declaration: &'static Declaration,
    /// Where its attributes are (§6.5), in the list of declarations read.
    pub place: crate::attrs::Place,
}

/// Why the head of a declaration did not read ([`Parser::read_heading`]):
/// where it fails, an attribute of another language read on before it has
/// no place the parser knows ([`foreign::at_heading_hash`]).
pub(super) enum Unread {
    /// A form of the head failed (an attribute of Onsa, a visibility, a
    /// keyword before a keyword): a declaration was begun.
    Failed,
    /// No declaration where the head looks for its keyword (`let`, a name,
    /// a `#[…]` that fails after it: the end of the list or of the file).
    NoDeclaration,
}

impl From<ParseError> for Unread {
    fn from(_: ParseError) -> Self {
        Unread::Failed
    }
}

impl<'a> Parser<'a> {
    /// The head of the item in the node open, up to the keyword of its
    /// declaration: the attributes read whole, the index of the visibility
    /// word read whole, and the declaration. After a form before the name
    /// that ends on its line, the head is read on from the token after it
    /// (attributes, visibility, declaration): a visibility of another
    /// language ([`Parser::parse_vis`]), an attribute of another language
    /// ([`Parser::foreign_attribute`]) or one whose arguments do not read
    /// ([`Parser::parse_attrs`]), the words before the head
    /// ([`Parser::words_before_head`]), a keyword before a keyword
    /// ([`Parser::keyword_before_keyword`]), the modifiers out of order
    /// ([`Parser::modifiers_out_of_order`]) and an attribute after a
    /// visibility or `rt` ([`Parser::late_attribute`]). Any other token is the failure of
    /// the head. The attributes of other languages read on are asked about
    /// at the place of the declaration read, as those of Onsa are
    /// ([`Parser::check_attrs`]): the parser read the head, and the table
    /// reads it no more (§6.5, D-15).
    pub(super) fn parse_heading(&mut self, ctx: ItemCtx) -> PResult<Heading> {
        let mut hashes = Vec::new();
        let read = self.read_heading(&mut hashes, ctx);
        let place = read.as_ref().ok().map(|h| h.place);
        let keyword = read.is_ok().then(|| self.peek_index());
        let failed = matches!(read, Err(Unread::Failed));
        for at in hashes {
            // After `rt` it is the error of its place (§18.1): asked with no
            // place, it has no candidate.
            let before = self.tokens[..at].iter().rev().find(|t| !t.kind.is_comment());
            let after_rt = before.is_some_and(|t| t.kind == TokenKind::KwRt);
            let mut cursor = self.cursor(at, Want::Other);
            if !after_rt {
                (cursor.place, cursor.declaration) = (place, keyword);
            }
            let (row, mut d) = foreign::at_heading_hash(&cursor, failed).unwrap_or_else(|| {
                onsa_diag::internal::bug(Some(self.tokens[at].span), "a `#[` read on that the table does not name")
            });
            // The head of the `extern` block is of its form (S-601).
            if row == foreign::RowId::LinkAttribute {
                self.linked = keyword;
            }
            if after_rt {
                d.notes = vec![Note::rule(ATTRIBUTE_RULE)];
            }
            self.report(d);
        }
        read.map_err(|_| ParseError)
    }

    /// The head of [`Parser::parse_heading`]; the `#` of each attribute of
    /// another language read on go to `hashes`; a member when `ctx` is the
    /// list of a declaration (the place of its attributes, §6.5).
    fn read_heading(&mut self, hashes: &mut Vec<usize>, ctx: ItemCtx) -> Result<Heading, Unread> {
        let member = ctx != ItemCtx::Top;
        let mut attrs = Vec::new();
        let mut vis = None;
        loop {
            let read = self.parse_attrs(true)?;
            if !read.is_empty() {
                self.skip_newlines();
                // The line after them goes on (§2.5): an item at its head
                // ends the list of a `{` never closed, as at a member (§18.1;
                // `x @a`, then `fn f`), and the attributes have none.
                if ctx != ItemCtx::InlineHandler && self.list_ends_unclosed() {
                    self.unexpected("the declaration of the attributes");
                    return Err(Unread::NoDeclaration);
                }
            }
            attrs.extend(read);
            if self.modifiers_out_of_order() {
                continue;
            }
            match self.parse_vis("a declaration")? {
                VisRead::ReadOn => continue,
                VisRead::Word(w) => vis = Some(w),
                VisRead::Absent => {}
            }
            // In this order: the attribute after `rt` is not for `parse_attrs`.
            let rt = self.rt_before_form();
            if self.late_attribute()? || rt {
                continue;
            }
            let t = self.peek();
            if let Some(declaration) = declaration(t.kind) {
                if self.keyword_before_keyword(t)? {
                    continue;
                }
                let place = crate::attrs::place_of_declaration(t.kind, member);
                return Ok(Heading { attrs, vis, keyword: t, declaration, place });
            }
            // Another attribute that fails (not closed on its line, or no
            // declaration after it): no declaration was begun.
            if self.foreign_attribute(hashes).map_err(|_| Unread::NoDeclaration)? || self.words_before_head() {
                continue;
            }
            if let Some(unread) = self.static_head(ctx) {
                return Err(unread);
            }
            self.unexpected("a declaration");
            return Err(Unread::NoDeclaration);
        }
    }

    /// The attribute `@name(…)` that failed in its arguments at the cursor,
    /// its `@` at `at` (§18.1): when its `(` closes on its line, the rest is
    /// read on into its node, which closes incomplete (an attribute that was
    /// not read), and `true`. `depth` is the number of nodes open around it.
    // An attribute of Onsa whose arguments do not read, and that closes on
    // its line, is read on as a form before the name (S-435, S-481).
    pub(super) fn read_on_after_attribute(&mut self, at: usize, depth: usize) -> bool {
        let open = at + 2;
        if self.pos <= open || self.tokens[open].kind != TokenKind::LParen {
            return false;
        }
        let Some(close) = crate::scan::closing_on_line(&self.tokens, open).filter(|&c| self.pos <= c) else {
            return false;
        };
        self.close_open(depth + 1);
        self.read_on(close + 1);
        self.finish(None, false);
        true
    }

    /// `#[…]` of other languages at the cursor, in an `Attr` node opened
    /// there: one whose `[` closes on its line, before a declaration may
    /// come (not before the `}` of the list or the end of the file), is read
    /// on after, on the line of the declaration or on a line of its own; its
    /// node is incomplete, an attribute that was not read (S-460), and its
    /// `#` goes to `hashes`: the table names its form when the head is read
    /// ([`Parser::parse_heading`]). At any other, the parser fails, and the
    /// table names the form (`hash_attribute`). `Ok(false)` when no `#` is
    /// next.
    fn foreign_attribute(&mut self, hashes: &mut Vec<usize>) -> PResult<bool> {
        if !self.at(TokenKind::Hash) {
            return Ok(false);
        }
        let at = self.peek_index();
        self.start(NodeKind::Attr)?;
        let close = self
            .hash_end(at)
            .filter(|&e| !matches!(self.tokens[self.next_code(e)].kind, TokenKind::RBrace | TokenKind::Eof));
        let Some(close) = close else { return Err(self.fail(Want::Other, "a declaration")) };
        self.read_on(close + 1);
        self.finish(None, false);
        self.skip_newlines();
        hashes.push(at);
        Ok(true)
    }

    /// The `]` on its line of the `#[` at `at`.
    fn hash_end(&self, at: usize) -> Option<usize> {
        let bracket = Some(at + 1).filter(|&b| self.tokens[b].kind == TokenKind::LBracket)?;
        crate::scan::closing_on_line(&self.tokens, bracket)
    }

    /// The words before a head on its line (S-459): names, and the keywords
    /// `unsafe` and `static` (§18.1, S-615), which start no item, with the strings after them (the old
    /// `export "C" fn`, S-464), right before a token that starts a head
    /// ([`starts_heading`]). The run is one E0002 (or the row of its form,
    /// `export_c`), and the head is read on after it, the run in an `Error`
    /// node. `false` when no such run is next (`print(1)`, `proc name`, a
    /// word at the end of its line).
    fn words_before_head(&mut self) -> bool {
        let first = self.peek_index();
        let Some((last, next)) = self.words_before_head_at(first) else { return false };
        let span = Span::new(self.file, self.tokens[first].span.start, self.tokens[last].span.end);
        let message = format!("`{}` is no part of the head of a declaration", self.src(span));
        self.read_into_error(first, Own { span, message, rule: WORDS_RULE, fixes: Vec::new(), resume: next });
        true
    }

    /// `const` or `extern` and its string at the cursor (the keyword `t`),
    /// right before the keyword of another declaration on its line (`const
    /// fn h`, `extern "C" fn h`, S-464): the declaration fails at that
    /// keyword, where the grammar of `t` fails; the keyword and its string
    /// are one E0002 (or the row of the form, `const_fn`, `extern_fn`), and
    /// the head is read on from the keyword after. The node of `t` turns an
    /// `Error` node.
    fn keyword_before_keyword(&mut self, t: Token) -> PResult<bool> {
        let node = match t.kind {
            TokenKind::KwConst => NodeKind::Const,
            TokenKind::KwExtern => NodeKind::Extern,
            _ => return Ok(false),
        };
        let first = self.peek_index();
        let mut last = first;
        let Some(mut next) = self.on_line_after(first) else { return Ok(false) };
        if t.kind == TokenKind::KwExtern && self.tokens[next].kind == TokenKind::Str {
            last = next;
            let Some(n) = self.on_line_after(next) else { return Ok(false) };
            next = n;
        }
        let keyword = self.tokens[next];
        if !is_declaration_keyword(keyword.kind) {
            return Ok(false);
        }
        self.start(node)?;
        while self.peek_index() < next {
            self.bump();
        }
        let span = Span::new(self.file, self.tokens[first].span.start, self.tokens[last].span.end);
        let message = format!("`{}` cannot be written before `{}`", self.src(span), self.token_text(keyword));
        let own = Own { span, message, rule: KEYWORD_RULE, fixes: Vec::new(), resume: next };
        self.fail_at(Want::Other, "a declaration", None, Some(own));
        self.finish(Some(NodeKind::Error), false);
        Ok(true)
    }

    /// The modifiers `pub`, `priv` and `rt` on the line at the cursor, twice or
    /// out of order before the head goes on (`pub pub fn`, `rt pub fn`, `pub
    /// pub export fn`, S-464), or with an `rt` before the keyword of a
    /// declaration other than `fn` (`rt struct P`, `pub rt impl P {`, S-492):
    /// one E0002, and the head is read on from the token after, the modifiers
    /// in an `Error` node. Its candidate writes the right order (the
    /// visibility, then `rt` before `fn`, each once), and there is none when
    /// `pub` and `priv` are both written, or when no keyword is next: whether
    /// an `rt` stays is not known at the run. An `rt` in order before a form
    /// that is no keyword is left to [`Parser::rt_before_form`].
    fn modifiers_out_of_order(&mut self) -> bool {
        use TokenKind::{KwFn, KwPriv, KwPub, KwRt};
        let first = self.peek_index();
        let mut run = Vec::new();
        let mut next = first;
        while matches!(self.tokens[next].kind, KwPub | KwPriv | KwRt) {
            run.push(next);
            let Some(n) = self.on_line_after(next) else { return false };
            next = n;
        }
        let kinds: Vec<TokenKind> = run.iter().map(|&k| self.tokens[k].kind).collect();
        let vis: Vec<TokenKind> = kinds.iter().copied().filter(|&k| k != KwRt).collect();
        let rt = kinds.len() - vis.len();
        let ordered = vis.len() <= 1 && rt <= 1 && (vis.is_empty() || kinds[0] != KwRt);
        let keyword = is_declaration_keyword(self.tokens[next].kind).then_some(self.tokens[next].kind);
        // S-492: `rt` has a place only before `fn` (§10), so no order makes the
        // head right; the `rt` is not recorded ([`crate::lower`]).
        let no_place = rt > 0 && keyword.is_some_and(|k| k != KwFn);
        if (ordered && !no_place) || !self.head_goes_on(next) {
            return false;
        }
        let fixes = if keyword.is_none() || (vis.contains(&KwPub) && vis.contains(&KwPriv)) {
            Vec::new()
        } else {
            let keep_rt = rt > 0 && !no_place;
            let right: Vec<TokenKind> = vis.first().copied().into_iter().chain(keep_rt.then_some(KwRt)).collect();
            let edits = run
                .iter()
                .enumerate()
                .filter_map(|(i, &k)| match right.get(i) {
                    Some(&w) if w == kinds[i] => None,
                    Some(&w) => Some(Edit::replace(self.tokens[k].span, modifier(w))),
                    None => Some(Edit::delete(self.with_blank_after(k))),
                })
                .collect();
            let title =
                if no_place { "write the head without `rt`" } else { "write the visibility, then `rt`, once each" };
            vec![Fix::new(title, edits)]
        };
        let last = *run.last().unwrap_or(&first);
        let span = Span::new(self.file, self.tokens[first].span.start, self.tokens[last].span.end);
        let right = if no_place { "`rt` is written only before `fn`" } else { "a visibility and then `rt`, once each" };
        let message = format!("`{}` is no head of a declaration: {right}", self.src(span));
        self.read_into_error(first, Own { span, message, rule: MODIFIERS_RULE, fixes, resume: next });
        true
    }

    /// `rt` at the cursor, right before a form on its line that the head is
    /// read on after (`rt @fp(relaxed) fn h`, `rt #[inline] fn h`, `rt export
    /// fn h`, S-593): it goes into an `Error` node, a modifier written
    /// ([`crate::lower`]) with no report of its own: the form is the error,
    /// reported in this round of [`Parser::read_heading`]. Before any other
    /// token, `rt` is the head of a function, which fails there.
    fn rt_before_form(&mut self) -> bool {
        let rt = self.peek_index();
        if self.tokens[rt].kind != TokenKind::KwRt {
            return false;
        }
        let form = self.on_line_after(rt).filter(|&next| match self.tokens[next].kind {
            TokenKind::At => self.late_attribute_end(next).is_some(),
            TokenKind::Hash => {
                self.hash_end(next).and_then(|e| self.on_line_after(e)).is_some_and(|n| self.head_goes_on(n))
            }
            _ => self.words_before_head_at(next).is_some(),
        });
        let Some(form) = form else { return false };
        let m = self.enter_unit(NodeKind::Error, self.tokens[rt].span.start);
        self.read_on(form);
        self.complete(m, NodeKind::Error);
        true
    }

    /// An attribute at the cursor after a visibility or `rt`, where the head
    /// takes none (`pub @fp(relaxed) fn h`, S-593), when
    /// [`Parser::late_attribute_end`] finds its end: one E0002 for its place,
    /// whose candidate moves it ([`Parser::moved_attribute`], S-600), and the
    /// head is read on after it. Its node is incomplete, an attribute that
    /// was not read (S-460): what is in it is not looked at.
    // S-949: an old attribute here (`pub @derive(Eq) struct P`, `pub @relaxed
    // fn h`) is this E0002 too, whatever its name: its place is the first error.
    fn late_attribute(&mut self) -> PResult<bool> {
        let at = self.peek_index();
        if self.tokens[at].kind != TokenKind::At {
            return Ok(false);
        }
        let Some(last) = self.late_attribute_end(at) else { return Ok(false) };
        let fixes = self.moved_attribute(at, last).into_iter().collect();
        self.start(NodeKind::Attr)?;
        let span = Span::new(self.file, self.tokens[at].span.start, self.tokens[last].span.end);
        let message = format!("`{}` cannot be written here: attributes come first in a head", self.src(span));
        let own = Own { span, message, rule: ATTRIBUTE_RULE, fixes, resume: last + 1 };
        self.fail_at(Want::Other, "a declaration", None, Some(own));
        self.read_on(last + 1);
        self.finish(None, false);
        Ok(true)
    }

    /// The last token of the form `@name` or `@name(…)` at `at`, when its `(`
    /// closes on its line and the head goes on after it on that line (§18.1).
    fn late_attribute_end(&self, at: usize) -> Option<usize> {
        let last = self.attribute_end(at)?;
        self.on_line_after(last).filter(|&n| self.head_goes_on(n)).map(|_| last)
    }

    /// The candidate of the attribute from `at` to `last` after the
    /// visibility and `rt` right before it: it goes before them, after the
    /// attributes there (§18.1, S-600). None when what is in it does not
    /// read as the arguments of an attribute (`pub @fp(relaxed, 1 +) fn h`),
    /// tried at the cursor and undone; when the check of the head would take
    /// it out (`@fp(strict)`, [`crate::attrs::unset`]); or when no modifier is
    /// right before it.
    fn moved_attribute(&mut self, at: usize, last: usize) -> Option<Fix> {
        let modifier = |k: usize| {
            let b = self.tokens[..k].iter().rposition(|t| !t.kind.is_comment())?;
            matches!(self.tokens[b].kind, TokenKind::KwPub | TokenKind::KwPriv | TokenKind::KwRt).then_some(b)
        };
        let first = std::iter::successors(modifier(at), |&k| modifier(k)).last()?;
        let trial = self.snapshot();
        // SPEC-GAP(S-990): what is in it "reads" when the general reading of the arguments of an
        // attribute reads it (not the value of S-834): `pub @fp(1) fn h` has no candidate.
        let read = self.parse_attr(false).ok().filter(|_| self.diagnostics.len() == trial.diagnostics);
        let reads = read.is_some_and(|a| crate::attrs::unset(self.text, &self.written(&a)).is_none());
        self.restore(trial);
        let span = Span::new(self.file, self.tokens[at].span.start, self.tokens[last].span.end);
        let gone = Edit::delete(Span::new(self.file, span.start, self.with_blank_after(last).end));
        let put = Edit::insert(self.file, self.tokens[first].span.start, format!("{} ", self.src(span)));
        reads.then(|| Fix::new("write the attribute before the visibility and `rt`", vec![gone, put]))
    }

    /// The last token of the attribute at `at` that closes on its line: of the
    /// form `@name` or `@name(…)`, or `#[…]` of other languages.
    pub(super) fn attribute_end(&self, at: usize) -> Option<usize> {
        if self.tokens[at].kind == TokenKind::Hash {
            return self.hash_end(at);
        }
        let at_name = |n: &usize| self.tokens[at].kind == TokenKind::At && self.tokens[*n].kind == TokenKind::Ident;
        let name = self.on_line_after(at).filter(at_name)?;
        let open = self.on_line_after(name).filter(|&o| self.tokens[o].kind == TokenKind::LParen);
        open.map_or(Some(name), |o| crate::scan::closing_on_line(&self.tokens, o))
    }

    /// The head of an `extern` block at the cursor, when it does not read
    /// before the `{` on its line (`extern "C" {`, `extern {`, S-477): from
    /// `extern` to before the `{` is one E0002 at the token the grammar fails
    /// at (a row of that token, a run of a literal, is the error instead), and
    /// `true`, the members being read on. The name of the library is the
    /// writer's: no candidate. After `#[link(name = "m")]`, the attribute's
    /// diagnostic is of the head too (S-601): the head has none of its own.
    pub(super) fn extern_head_read_on(&mut self) -> bool {
        let first = self.peek_index();
        let linked = self.linked.take() == Some(first);
        let Some((head, brace)) = self.extern_head_on_line(first) else { return false };
        let string = |&t: &usize| self.tokens[t].kind == TokenKind::Str;
        let fits =
            |k: usize, t: &usize| if k == 1 { self.is_ident(self.tokens[*t], "lib") } else { k < 3 && string(t) };
        let failing = head.iter().enumerate().find(|&(k, t)| !fits(k, t)).map(|(k, _)| k);
        if failing.is_none() && head.len() == 3 {
            return false;
        }
        let end = self.tokens[*head.last().unwrap_or(&first)].span.end;
        let span = Span::new(self.file, self.tokens[first].span.start, end);
        let message = format!("`{}` is no head of an `extern` block", self.src(span));
        let at = failing.map_or(brace, |k| head[k]);
        while self.peek_index() < at {
            self.bump();
        }
        let own = Own { span, message, rule: EXTERN_RULE, fixes: Vec::new(), resume: brace };
        if !linked {
            self.fail_at(Want::Other, "a declaration", None, Some(own));
        }
        self.read_on(brace);
        true
    }

    /// The tokens between `extern` at `first` and the first `{` on its line,
    /// and that `{`; `None` when there is none, or when the brackets before
    /// it do not close (the range of the form closes on its line, §18.1).
    fn extern_head_on_line(&self, first: usize) -> Option<(Vec<usize>, usize)> {
        let (mut head, mut open) = (Vec::new(), Vec::new());
        let mut at = first;
        loop {
            at = self.on_line_after(at)?;
            let kind = self.tokens[at].kind;
            if kind == TokenKind::LBrace {
                return open.is_empty().then_some((head, at));
            }
            let closed = crate::scan::pair(&mut open, &self.tokens, at, 0);
            if closed.is_none() && matches!(kind, TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
                return None;
            }
            head.push(at);
        }
    }

    /// Whether the head goes on at `tokens[i]`: a token that starts a head,
    /// or the words before one (§18.1, S-593).
    fn head_goes_on(&self, i: usize) -> bool {
        starts_heading(self.tokens[i].kind) || self.words_before_head_at(i).is_some()
    }

    /// The run of words from token `first` before a head on its line
    /// ([`Parser::words_before_head`]): its last token, and the token after
    /// it that starts the head.
    pub(super) fn words_before_head_at(&self, first: usize) -> Option<(usize, usize)> {
        let word = |k: TokenKind| matches!(k, TokenKind::Ident | TokenKind::KwUnsafe | TokenKind::KwStatic);
        if !word(self.tokens[first].kind) {
            return None;
        }
        let mut last = first;
        loop {
            let n = self.on_line_after(last)?;
            match self.tokens[n].kind {
                k if word(k) || k == TokenKind::Str => last = n,
                k if starts_heading(k) => return Some((last, n)),
                _ => return None,
            }
        }
    }

    /// Report the failure at the cursor whose form the parser knows (`own`)
    /// and read on into an `Error` node from token `first`.
    fn read_into_error(&mut self, first: usize, own: Own) {
        let resume = self.fail_at(Want::Other, "a declaration", None, Some(own));
        let m = self.enter_unit(NodeKind::Error, self.tokens[first].span.start);
        if let Some(r) = resume {
            self.read_on(r);
        }
        self.complete(m, NodeKind::Error);
    }

    /// The span of token `k` with the blanks after it.
    fn with_blank_after(&self, k: usize) -> Span {
        let span = self.tokens[k].span;
        let end = self.all.get(self.full[k] as usize + 1).filter(|w| w.kind == TokenKind::Whitespace);
        Span::new(self.file, span.start, end.map_or(span.end, |w| w.span.end))
    }
}

/// The text of a modifier.
fn modifier(kind: TokenKind) -> &'static str {
    match kind {
        TokenKind::KwPub => "pub",
        TokenKind::KwPriv => "priv",
        _ => "rt",
    }
}

/// The note of the words before a head (S-459).
const WORDS_RULE: &str = "the head of a declaration starts with its visibility (`pub`, `priv` or none) and its keyword; there are no modifiers of other languages (§18.1)";

/// The note of a keyword before a keyword (S-464).
const KEYWORD_RULE: &str =
    "the keyword of a declaration is followed by its name, not by the keyword of another declaration (§18.1)";

/// The note of an attribute after a visibility or `rt` (S-593).
const ATTRIBUTE_RULE: &str = "the attributes of a declaration are written before its visibility and `rt`: `@fp(relaxed) pub rt fn h` (§6.5, §18.1)";

/// The note of the head of an `extern` block that does not read (S-477).
const EXTERN_RULE: &str =
    "an `extern` block is written `extern \"C\" lib \"…\" {`, with the name of its library (§14.1)";

/// The note of the modifiers out of order (S-464).
const MODIFIERS_RULE: &str = "the head of a declaration is its visibility (`pub` or `priv`, or none), then `rt` before `fn`, each written once, then its keyword (§10, §15.1, §18.1)";
