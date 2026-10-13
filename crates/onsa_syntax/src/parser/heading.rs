//! The head of a declaration before its keyword (§18.1): its attributes, its
//! visibility and its modifiers, and the reading on after a form that the
//! head does not take (S-435, S-459, S-464, S-481).
//!
//! What was not read stays in the head, before the declaration's node: an
//! incomplete `Attr` (an attribute that was not read, S-460) or `Vis` node
//! (a visibility of another language), or an `Error` node (a run of words, a
//! keyword before a keyword, the modifiers out of order), whose `pub`,
//! `priv` and `rt` are the modifiers written ([`crate::lower`]). The unit has
//! the syntax error, so the declaration is a read one whose body is not
//! checked (`crate::units`, `Failed::Unit`).

use onsa_diag::Edit;

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
    /// ([`Parser::keyword_before_keyword`]) and the modifiers out of order
    /// ([`Parser::modifiers_out_of_order`]). Any other token is the failure of
    /// the head. The attributes of other languages read on are asked about
    /// at the place of the declaration read, as those of Onsa are
    /// ([`Parser::check_attrs`]): the parser read the head, and the table
    /// reads it no more (§6.5, D-15).
    pub(super) fn parse_heading(&mut self) -> PResult<Heading> {
        let mut hashes = Vec::new();
        let read = self.read_heading(&mut hashes);
        let place = read.as_ref().ok().map(|h| crate::attrs::place_of_declaration(h.keyword.kind));
        let keyword = read.is_ok().then(|| self.peek_index());
        for at in hashes {
            let mut cursor = self.cursor(at, Want::Other);
            (cursor.place, cursor.declaration) = (place, keyword);
            let d = foreign::at_heading_hash(&cursor).unwrap_or_else(|| {
                onsa_diag::internal::bug(Some(self.tokens[at].span), "a `#[` read on that the table does not name")
            });
            self.report(d);
        }
        read
    }

    /// The head of [`Parser::parse_heading`]; the `#` of each attribute of
    /// another language read on go to `hashes`.
    fn read_heading(&mut self, hashes: &mut Vec<usize>) -> PResult<Heading> {
        let mut attrs = Vec::new();
        let mut vis = None;
        loop {
            let read = self.parse_attrs(true)?;
            if !read.is_empty() {
                self.skip_newlines();
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
            let t = self.peek();
            if let Some(declaration) = declaration(t.kind) {
                if self.keyword_before_keyword(t)? {
                    continue;
                }
                return Ok(Heading { attrs, vis, keyword: t, declaration });
            }
            if self.foreign_attribute(hashes)? || self.words_before_head() {
                continue;
            }
            return Err(self.unexpected("a declaration"));
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
        let close = Some(at + 1)
            .filter(|&b| self.tokens[b].kind == TokenKind::LBracket)
            .and_then(|b| crate::scan::closing_on_line(&self.tokens, b))
            .filter(|&e| !matches!(self.tokens[self.next_code(e)].kind, TokenKind::RBrace | TokenKind::Eof));
        let Some(close) = close else { return Err(self.fail(Want::Other, "a declaration")) };
        self.read_on(close + 1);
        self.finish(None, false);
        self.skip_newlines();
        hashes.push(at);
        Ok(true)
    }

    /// The words before a head on its line (S-459): names, and `unsafe`,
    /// which starts no item, with the strings after them (the old
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

    /// The modifiers `pub`, `priv` and `rt` on the line at the cursor before
    /// the keyword of a declaration, twice or out of order (`pub pub fn`,
    /// `rt pub fn`, S-464): one E0002 whose candidate writes the right order
    /// (the visibility, then `rt`, each once; none when `pub` and `priv` are
    /// both written), and the head is read on from the keyword, the
    /// modifiers in an `Error` node. An `rt` before a keyword other than `fn`
    /// is the grammar's failure at the keyword, as are the modifiers in order.
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
        let keyword = self.tokens[next].kind;
        // SPEC-GAP(S-492): `rt` before the keyword of a declaration other than
        // `fn` (`rt pub struct P`) is not read as the modifiers out of order:
        // no order of them makes the head right, and the grammar fails at it.
        if ordered || !is_declaration_keyword(keyword) || (rt > 0 && keyword != KwFn) {
            return false;
        }
        let fixes = if vis.contains(&KwPub) && vis.contains(&KwPriv) {
            Vec::new()
        } else {
            let right: Vec<TokenKind> = vis.first().copied().into_iter().chain((rt > 0).then_some(KwRt)).collect();
            let edits = run
                .iter()
                .enumerate()
                .filter_map(|(i, &k)| match right.get(i) {
                    Some(&w) if w == kinds[i] => None,
                    Some(&w) => Some(Edit::replace(self.tokens[k].span, modifier(w))),
                    None => Some(Edit::delete(self.with_blank_after(k))),
                })
                .collect();
            vec![Fix::new("write the visibility, then `rt`, once each", edits)]
        };
        let last = *run.last().unwrap_or(&first);
        let span = Span::new(self.file, self.tokens[first].span.start, self.tokens[last].span.end);
        let message =
            format!("`{}` is no head of a declaration: a visibility and then `rt`, once each", self.src(span));
        self.read_into_error(first, Own { span, message, rule: MODIFIERS_RULE, fixes, resume: next });
        true
    }

    /// The run of words from token `first` before a head on its line
    /// ([`Parser::words_before_head`]): its last token, and the token after
    /// it that starts the head.
    pub(super) fn words_before_head_at(&self, first: usize) -> Option<(usize, usize)> {
        if !matches!(self.tokens[first].kind, TokenKind::Ident | TokenKind::KwUnsafe) {
            return None;
        }
        let mut last = first;
        loop {
            let n = self.on_line_after(last)?;
            match self.tokens[n].kind {
                TokenKind::Ident | TokenKind::KwUnsafe | TokenKind::Str => last = n,
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

/// The note of the modifiers out of order (S-464).
const MODIFIERS_RULE: &str = "the head of a declaration is its visibility (`pub` or `priv`, or none), then `rt` before `fn`, each written once, then its keyword (§10, §15.1, §18.1)";
