//! The `static` of other languages at the head of an item (§2.2, §18.1,
//! S-620): Rust's `static NAME: T = e` and `static mut NAME: T = e`, and the
//! declarations of C (`static int x = 4;`, `static int f(void) {`).
//!
//! Each is read as far as its name, so that the module has the name: the
//! words before it go into an `Error` node of the head, and the name into a
//! declaration node that the unit's recovery cuts after it
//! ([`Parser::skip_unit`]) at the end of its line, outside the brackets it
//! opens, the line going on as §2.5 reads (as after an item read whole, the
//! form starting no item, §18.1). `static NAME: T` is a `Const` node with its type,
//! a constant of the type `T` whose value is not read (`Failed::Body`); the
//! others are a `Fn` node with the name alone, a declaration whose heading
//! is not read (`Failed::Heading`), whose uses get no diagnostic. The
//! initializer and the body of a function of C (its `{` on the line of the
//! head or the next) are skipped by the recovery, which pairs the brackets as
//! it goes (one pass forward), and are not checked.

use onsa_diag::{Edit, Note};

use super::*;

/// A form of `static` at the head of an item ([`Parser::static_form`]).
#[derive(Clone, Copy, PartialEq)]
enum Static {
    /// `static NAME: T = e`.
    Item,
    /// `static mut NAME: T = e`.
    Mut,
    /// Two names or more after `static`, the last the name, then a token
    /// that starts no head; a function when that token is `(`.
    C { function: bool },
}

impl<'a> Parser<'a> {
    /// `static` at the cursor, at the head of an item in the list of `ctx`
    /// (§2.2, §18.1): a form of [`Parser::static_form`] is the diagnostic of
    /// its row and is read as far as its name (the module's documentation);
    /// any other (`static X = 4`) is the general E0002, not the E0200 of the
    /// reserved word. How the head did not read; `None` when no `static` is
    /// next.
    pub(super) fn static_head(&mut self, ctx: ItemCtx) -> Option<super::heading::Unread> {
        let first = self.peek_index();
        if self.tokens[first].kind != TokenKind::KwStatic {
            return None;
        }
        let Some((form, words, name)) = self.static_form(first) else {
            let t = self.tokens[first];
            let message = format!("expected a declaration, found {}", t.kind.describe());
            let own = Own { span: t.span, message, rule: STATIC_RULE, fixes: Vec::new(), resume: first };
            self.fail_at(Want::Other, "a declaration", None, Some(own));
            return Some(super::heading::Unread::NoDeclaration);
        };
        let span = self.tokens[first].span.to(self.tokens[words].span);
        // `const` is written where an associated constant is (§18.1).
        let constant = declaration(TokenKind::KwConst).is_some_and(|d| d.places.of(TokenKind::Ident).0.contains(&ctx));
        let (row, fixes) = match form {
            Static::Item if constant => {
                (foreign::RowId::StaticItem, vec![Fix::new("write `const`", vec![Edit::replace(span, "const")])])
            }
            Static::Item => (foreign::RowId::StaticItem, Vec::new()),
            Static::Mut => (foreign::RowId::StaticMutItem, Vec::new()),
            Static::C { .. } => (foreign::RowId::CStaticItem, Vec::new()),
        };
        let mut d = foreign::report(row, self.text, span, fixes);
        if form == (Static::C { function: true }) {
            d.notes = vec![Note::rule(C_FUNCTION_RULE)];
        }
        self.report(d);
        // The handler written in an expression is of the unit around it.
        self.static_line = (ctx != ItemCtx::InlineHandler).then_some(form == Static::C { function: true });
        let m = self.enter_unit(NodeKind::Error, self.tokens[first].span.start);
        self.read_on(name);
        self.complete(m, NodeKind::Error);
        let node = if form == Static::Item { NodeKind::Const } else { NodeKind::Fn };
        if self.start(node).is_ok() && self.parse_name(Declared::Constant, "a name").is_ok() && form == Static::Item {
            let _ = self.expect(TokenKind::Colon).and_then(|_| self.parse_type());
        }
        Some(super::heading::Unread::Failed)
    }

    /// The form of the `static` at `first` (§2.2): with the last token before
    /// its name and the name. The one judgment of the three forms.
    fn static_form(&self, first: usize) -> Option<(Static, usize, usize)> {
        let ident = |k: &usize| self.tokens[*k].kind == TokenKind::Ident;
        let next = |k: usize| self.on_line_after(k);
        let colon = |k: usize| next(k).is_some_and(|c| self.tokens[c].kind == TokenKind::Colon);
        let a = next(first).filter(ident)?;
        if colon(a) {
            return Some((Static::Item, first, a));
        }
        let b = next(a).filter(ident)?;
        if self.is_ident(self.tokens[a], "mut") && colon(b) {
            return Some((Static::Mut, a, b));
        }
        let (mut before, mut last) = (a, b);
        loop {
            match next(last) {
                Some(n) if ident(&n) => (before, last) = (last, n),
                // The words before a head (`static int fn`) are read before.
                Some(n) if self.heading_at(n) => return None,
                n => {
                    let function = n.is_some_and(|n| self.tokens[n].kind == TokenKind::LParen);
                    return Some((Static::C { function }, before, last));
                }
            }
        }
    }
}

/// The note of the general E0002 at `static` at the head of an item.
const STATIC_RULE: &str = "`static` is reserved (§2.2); a constant of the module is written `const NAME: T = e`, a declaration starts with its visibility and its keyword (§18.1)";

/// The note of a function of C declared `static` (§2.2).
const C_FUNCTION_RULE: &str = "a function is written `fn name(x: T) -> R { … }` (§6.1)";
