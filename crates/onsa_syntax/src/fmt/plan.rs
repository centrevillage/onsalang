//! The plan of `onsa fmt`: the decisions about single tokens that the
//! printer (`fmt/print.rs`) reads as it walks (W3-11).
//!
//! The plan is made once, before the walk, from the tree and the tables of
//! `fmt/shape.rs`. Its decisions are those of `docs/onsa-tools.md` §3.2 and
//! §3.3 that drop, add or respell a token or add or remove a line break; the
//! printer keeps every other line break of the writer's.
//!
//! - **Dropped tokens:** the rewrites of §3.3 (`fmt/rewrites.rs`); the `,`
//!   after the last element of a list on one line or in the continuation
//!   form; a `,` at the head of a line, which moves to the end of the element
//!   before it (the comment at the end of that line goes after it, §3.4).
//! - **Added `,`:** after the last element of a list in the block form. The
//!   `..` of a struct pattern is no element and gets none (S-500).
//! - **Respelled tokens:** the numbers (S-62, S-126; not the index of a
//!   tuple, S-508).
//! - **Forms:** the form of each list and enclosure (`shape::forms`), by its
//!   opening bracket; the printer reads it from here.
//! - **Added line breaks:** before the closing bracket of a list in the
//!   block form; round the attributes of an item and of an input of a list in
//!   the block form (S-501); after the `{` and before the `}` of a block or a
//!   body of items over more than one line. None between the elements of a
//!   list (S-520, S-521).
//! - **Removed line breaks:** before the closing bracket of a list on one
//!   line or in the continuation form (S-507), and between brackets with
//!   nothing in them (S-496); inside an element of a list or an enclosure,
//!   but at a place of a continuation (S-497, S-505); between the attribute
//!   of a `let` and the `let` (§3.2). The printer keeps them when a comment
//!   is between (§3.4, S-497).

use super::rewrites::{REWRITES, all_nodes};
use super::shape::{self, Form, Shape};
use crate::cst::{Cst, NodeId, NodeKind, TokenIdx};
use crate::layout::continues;
use crate::literal;
use crate::token::TokenKind;

/// The printer leaves the token out.
const DROP: u8 = 1;
/// The printer writes a `,` right after the token.
const COMMA_AFTER: u8 = 2;
/// A line break goes before the token.
const BREAK_BEFORE: u8 = 4;
/// No line break goes before the token.
const JOIN: u8 = 8;

pub(super) struct Plan {
    /// The decisions of each token, by its index.
    flags: Vec<u8>,
    /// The tokens with another text, in the order of the tokens.
    texts: Vec<(TokenIdx, String)>,
    /// The opening bracket of each list and enclosure and its form, in the order of the tokens.
    forms: Vec<(TokenIdx, Form)>,
}

impl Plan {
    /// The plan of `cst`, the tree of `src` (without a syntax error).
    pub(super) fn new(cst: &Cst, src: &str) -> Plan {
        let mut plan = Plan { flags: vec![0; cst.tokens().len()], texts: Vec::new(), forms: Vec::new() };
        let nodes = all_nodes(cst);
        let mut dropped = Vec::new();
        for &n in &nodes {
            REWRITES.iter().for_each(|rewrite| (rewrite.cst)(cst, n, &mut dropped));
        }
        dropped.into_iter().for_each(|t| plan.set(t, DROP));
        plan.numbers(cst, src);
        for &n in &nodes {
            let forms = shape::forms(cst, n);
            for &(pair, form) in &forms {
                plan.list(cst, n, pair, form);
            }
            plan.attributes(cst, n, forms.first().map(|&(_, form)| form));
            plan.forms.extend(forms.into_iter().map(|((open, _), form)| (open, form)));
        }
        plan.forms.sort_unstable_by_key(|&(open, _)| open);
        // After the line breaks round the attributes, which can make a body one of more than one line.
        nodes.iter().for_each(|&n| plan.brackets(cst, n));
        plan.inside_elements(cst, &nodes);
        plan
    }

    /// The form of the list or the enclosure whose opening bracket is `open`.
    pub(super) fn form(&self, open: TokenIdx) -> Option<Form> {
        let i = self.forms.binary_search_by_key(&open, |&(t, _)| t).ok()?;
        Some(self.forms[i].1)
    }

    /// Whether the printer writes the code token `t` (a token left out is
    /// passed over like trivia).
    pub(super) fn kept(&self, t: TokenIdx) -> bool {
        !self.has(t, DROP)
    }

    /// The text the printer writes for the code token `t`, when it is not
    /// the text of the source.
    pub(super) fn text(&self, t: TokenIdx) -> Option<&str> {
        let i = self.texts.binary_search_by_key(&t, |(t, _)| *t).ok()?;
        Some(&self.texts[i].1)
    }

    /// Whether a `,` goes right after the code token `t`, before the comment at the end of its line.
    pub(super) fn comma_after(&self, t: TokenIdx) -> bool {
        self.has(t, COMMA_AFTER)
    }

    /// Whether a line break goes before the code token `t` where the writer has none.
    pub(super) fn breaks_before(&self, t: TokenIdx) -> bool {
        self.has(t, BREAK_BEFORE)
    }

    /// Whether the line breaks of the writer before the code token `t` go
    /// (unless a comment is between it and the code token before it).
    pub(super) fn joins(&self, t: TokenIdx) -> bool {
        self.has(t, JOIN)
    }

    fn has(&self, t: TokenIdx, flag: u8) -> bool {
        self.flags[t.index()] & flag != 0
    }

    fn set(&mut self, t: TokenIdx, flag: u8) {
        self.flags[t.index()] |= flag;
    }

    /// The numbers in their canonical spelling (§3.2, S-62, S-126).
    fn numbers(&mut self, cst: &Cst, src: &str) {
        for (i, tok) in cst.tokens().iter().enumerate() {
            let t = TokenIdx(i as u32);
            let literal =
                matches!(cst.kind(cst.token_parent(t)), NodeKind::Literal | NodeKind::LitPat | NodeKind::NegLitPat);
            if !matches!(tok.kind, TokenKind::Int | TokenKind::Float) || !literal {
                continue;
            }
            let text = &src[tok.span.start as usize..tok.span.end as usize];
            let Some(canonical) = literal::canonical_number(text) else {
                onsa_diag::internal::bug(Some(tok.span), "fmt met a number a syntax error left unread")
            };
            if canonical != text {
                self.texts.push((t, canonical));
            }
        }
    }

    /// The `,` and the closing bracket of the list or the enclosure `n`, of
    /// its pair of brackets `(open, close)` of the form `form` (§3.2, S-500,
    /// S-507, S-522).
    fn list(&mut self, cst: &Cst, n: NodeId, (open, close): (TokenIdx, TokenIdx), form: Form) {
        for c in cst.child_tokens(n).filter(|&c| open < c && c < close && cst.token(c).kind == TokenKind::Comma) {
            let before = self.previous(cst, c);
            if form != Form::Block && source_next(cst, c) == Some(close) {
                self.set(c, DROP);
            } else if let Some(before) = before.filter(|&b| on_another_line(cst, b, c)) {
                self.set(c, DROP);
                self.set(before, COMMA_AFTER);
            }
        }
        if form != Form::Block {
            self.set(close, JOIN);
            return;
        }
        let element = shape::elements(cst, n).last().map(|e| TokenIdx(e.end.0 - 1));
        let rest = shape::rest(cst, n).map(|r| r.start);
        if let Some(element) = element.filter(|&e| rest.is_none_or(|r| r < e))
            && source_next(cst, element).is_none_or(|t| cst.token(t).kind != TokenKind::Comma)
        {
            self.set(element, COMMA_AFTER);
        }
        let last = self.previous(cst, close).expect("a closing bracket has its opening one before it");
        if !on_another_line(cst, last, close) {
            self.set(close, BREAK_BEFORE);
        }
    }

    /// The line breaks round the attributes of an item and of the inputs in
    /// a list in the block form (`n` of the form `form`): each on a line of
    /// its own (§3.2, S-501).
    fn attributes(&mut self, cst: &Cst, n: NodeId, form: Option<Form>) {
        match cst.kind(n) {
            NodeKind::Item => self.own_lines(cst, n),
            NodeKind::ParamList if form == Some(Form::Block) => cst.child_nodes(n).for_each(|p| self.own_lines(cst, p)),
            _ => {}
        }
    }

    /// Line breaks before the first attribute of `n` and after each.
    fn own_lines(&mut self, cst: &Cst, n: NodeId) {
        let attrs = cst.child_nodes(n).filter(|&c| cst.kind(c) == NodeKind::Attr);
        for (i, (first, last)) in attrs.filter_map(|a| cst.significant_tokens(a)).enumerate() {
            if i == 0 && self.previous(cst, first).is_some_and(|b| !on_another_line(cst, b, first)) {
                self.set(first, BREAK_BEFORE);
            }
            if let Some(after) = self.next(cst, last).filter(|&a| !on_another_line(cst, last, a)) {
                self.set(after, BREAK_BEFORE);
            }
        }
    }

    /// The line breaks inside the brackets of `n`: none in an empty pair
    /// (S-496), and one after the `{` and before the `}` of a block or a body
    /// of items over more than one line (§3.2).
    fn brackets(&mut self, cst: &Cst, n: NodeId) {
        let (Some(row), Some((open, close))) = (shape::shape(cst.kind(n)), shape::brackets(cst, n)) else { return };
        let inside = open.index() + 1..close.index();
        let content = |i: usize| cst.tokens()[i].kind.is_comment() || self.written(cst, TokenIdx(i as u32));
        if !inside.clone().any(content) {
            self.set(close, JOIN);
            return;
        }
        let lines = |i: usize| cst.tokens()[i].kind == TokenKind::Newline || self.has(TokenIdx(i as u32), BREAK_BEFORE);
        if row.shape != Shape::Container || !(inside.start..=close.index()).any(lines) {
            return;
        }
        let first = self.next(cst, open).expect("a body has its closing bracket");
        if !on_another_line(cst, open, first) {
            self.set(first, BREAK_BEFORE);
        }
        let last = self.previous(cst, close).expect("a body has its opening bracket");
        if !on_another_line(cst, last, close) {
            self.set(close, BREAK_BEFORE);
        }
    }

    /// The line breaks of the writer that go (§3.2, S-497, S-505): the
    /// line breaks inside an element of a list or inside an enclosure, but
    /// those at a place of a continuation (§2.5), and the line breaks between
    /// the attributes of a `let` and the `let`. A `JOIN` goes on the code
    /// token after them, which the printer reads only when no comment is
    /// between (S-497 (β), §3.4).
    ///
    /// One walk over the tokens with the stack of the pairs of brackets the
    /// token is in (of the nodes of `nodes`, [`shape::pairs`]). A line break
    /// between `prev` and `t`, two code tokens written one after the other,
    /// is inside an element when the innermost pair round it is that of a
    /// list or an enclosure (not a block or a body of items, and none at the
    /// top of the file: there the line breaks end statements and items) and
    /// it is neither right after the opening bracket nor right before the
    /// closing one (the form of the list, [`Plan::list`]) nor before the first
    /// token of an element (between two elements). A place of a continuation
    /// is the one judgement [`continues`] on the last two code tokens before
    /// the line break and the first after it, and the end of an attribute
    /// (§2.5: an attribute ends no line, which the tokens do not show).
    fn inside_elements(&mut self, cst: &Cst, nodes: &[NodeId]) {
        const STARTS_ELEMENT: u8 = 1;
        const ENDS_ATTRIBUTE: u8 = 2;
        const ENDS_LET_ATTRIBUTE: u8 = 4;
        let tokens = cst.tokens();
        let mut marks = vec![0u8; tokens.len()];
        // (opening, closing, whether the pair holds statements or items), in the order of the tokens.
        let mut pairs = Vec::new();
        for &n in nodes {
            match cst.kind(n) {
                NodeKind::Attr => {
                    let let_attribute = cst.parent(n).is_some_and(|p| cst.kind(p) == NodeKind::LetStmt);
                    if let Some((_, last)) = cst.significant_tokens(n) {
                        marks[last.index()] |= if let_attribute { ENDS_LET_ATTRIBUTE } else { ENDS_ATTRIBUTE };
                    }
                }
                kind => {
                    let Some(row) = shape::shape(kind) else { continue };
                    let container = row.shape == Shape::Container;
                    pairs.extend(shape::pairs(cst, n).into_iter().map(|(open, close)| (open, close, container)));
                    if row.shape == Shape::List {
                        shape::part_starts(cst, n).into_iter().for_each(|t| marks[t.index()] |= STARTS_ELEMENT);
                    }
                }
            }
        }
        pairs.sort_unstable_by_key(|&(open, _, _)| open);
        let mut pairs = pairs.into_iter().peekable();
        let mut stack: Vec<(TokenIdx, TokenIdx, bool)> = Vec::new();
        // The last two code tokens of the source (the written ones or not, as `continues` reads them).
        let (mut before, mut last) = (None, None);
        // The last code token written, and whether a line break follows it.
        let (mut prev, mut breaks): (Option<TokenIdx>, bool) = (None, false);
        for (i, tok) in tokens.iter().enumerate() {
            let t = TokenIdx(i as u32);
            if tok.kind == TokenKind::Newline {
                breaks = true;
            }
            if !tok.kind.is_code() {
                continue;
            }
            if let (Some(p), true, true) = (prev, breaks, self.kept(t)) {
                let joins = match marks[p.index()] {
                    m if m & ENDS_LET_ATTRIBUTE != 0 => true,
                    m if m & ENDS_ATTRIBUTE != 0 => false,
                    _ => stack.last().is_some_and(|&(open, close, container)| {
                        !container
                            && p != open
                            && t != close
                            && marks[i] & STARTS_ELEMENT == 0
                            && last.is_none_or(|l| !continues(before, l, tok.kind))
                    }),
                };
                if joins {
                    self.set(t, JOIN);
                }
            }
            if stack.last().is_some_and(|&(_, close, _)| close == t) {
                stack.pop();
            }
            while let Some(pair) = pairs.next_if(|&(open, _, _)| open == t) {
                stack.push(pair);
            }
            (before, last) = (last, Some(tok.kind));
            if self.kept(t) {
                (prev, breaks) = (Some(t), false);
            }
        }
    }

    /// The code token before `t` that the printer writes.
    fn previous(&self, cst: &Cst, t: TokenIdx) -> Option<TokenIdx> {
        (0..t.index()).rev().map(|i| TokenIdx(i as u32)).find(|&c| self.written(cst, c))
    }

    /// The code token after `t` that the printer writes (the `Eof` at the end).
    fn next(&self, cst: &Cst, t: TokenIdx) -> Option<TokenIdx> {
        (t.index() + 1..cst.tokens().len()).map(|i| TokenIdx(i as u32)).find(|&c| self.written(cst, c))
    }

    fn written(&self, cst: &Cst, t: TokenIdx) -> bool {
        !cst.token(t).kind.is_trivia() && !self.has(t, DROP)
    }
}

/// The code token after `t` in the source, written or not ([`Plan::next`] is the one written).
fn source_next(cst: &Cst, t: TokenIdx) -> Option<TokenIdx> {
    let i = cst.tokens()[t.index() + 1..].iter().position(|t| !t.kind.is_trivia())?;
    Some(TokenIdx((t.index() + 1 + i) as u32))
}

/// Whether the token `b` is on a line after that of the token `a`: a line
/// break, or a comment (which a line break follows), is between them
/// (`shape.rs` reads the line breaks alone).
fn on_another_line(cst: &Cst, a: TokenIdx, b: TokenIdx) -> bool {
    cst.tokens()[a.index() + 1..b.index()].iter().any(|t| t.kind == TokenKind::Newline || t.kind.is_comment())
}
