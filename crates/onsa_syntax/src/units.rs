//! The units of the diagnostics of one file (spec §18.1, S-59, R-71): made
//! once here, from the CST, and read by the later stages (sema skips the body
//! of an item whose unit failed in the syntax stage, `fmt` and `diff --ast`
//! report one diagnostic per unit, the driver chooses one per unit and keeps
//! the table for the tests, D-15). The choice of the diagnostic of a unit is
//! `onsa_driver::reduce`'s alone.
//!
//! A unit is:
//!
//! - a top-level item, and each member of an `impl`, `trait`, `effect`,
//!   `handler` or `extern` (a unit whose `parent` is the item's unit; the
//!   item's own unit is then its heading and its braces);
//! - with the item, the `;` and the other tokens after it on the line where it
//!   ends (`const A: I32 = 1;`, S-254, S-274);
//! - a run of tokens that belong to no item, up to the next item, over lines
//!   (S-259).

use std::collections::HashMap;
use std::ops::Range;

use onsa_diag::{Diagnostic, Span, Stage};

use crate::ast::{Ast, Failed, ItemId};
use crate::cst::{Cst, Elem, NodeId, NodeKind};
use crate::lower::AstMap;
use crate::token::TokenKind;

/// One unit of the diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unit {
    /// From its first to its last token (doc comments and attributes
    /// included, and what is of the unit after the item on its line).
    pub span: Span,
    /// The item, when it has an AST (its name was read).
    pub item: Option<ItemId>,
    /// The unit of the `impl`, `trait`, ... a member belongs to.
    pub parent: Option<usize>,
    /// The units of its members (they follow it in the table).
    pub members: Range<usize>,
    /// For an item with members: its heading, from its start to the `{` of
    /// its members (not included: the E0002 of a `{` never closed is of the
    /// item's unit, and does not take its members). A diagnostic there makes the whole item one unit
    /// (§18.1, `onsa_driver::reduce`).
    pub heading: Option<Span>,
    /// The unit has a diagnostic of the syntax stage (its own, not one of a
    /// member's).
    pub syntax_failed: bool,
}

impl Unit {
    /// The heading of the unit holds the offset `at`: a diagnostic there
    /// makes the whole item one unit (§18.1). The one place of that test.
    pub fn heading_holds(&self, at: u32) -> bool {
        self.heading.is_some_and(|h| h.start <= at && at < h.end)
    }
}

/// The units of a file, in the order of the file (a member after the unit of
/// its item).
#[derive(Debug, Clone, Default)]
pub struct Units {
    pub list: Vec<Unit>,
    /// The top-level units, in the order of the file.
    top: Vec<usize>,
    /// The end of the file: a diagnostic there (an unclosed item at the end
    /// of the file) is of the last unit.
    end: u32,
}

impl Units {
    /// The unit a diagnostic at `span` is of: the innermost unit that holds
    /// its start (its end included), or the last unit for the end of the
    /// file. `None` for a place outside every unit (another file, the
    /// blanks between units).
    pub fn of(&self, span: Span) -> Option<usize> {
        let at = span.start;
        let top = self.top.partition_point(|&u| self.list[u].span.start <= at);
        let &u = self.top[..top].last()?;
        let unit = &self.list[u];
        if unit.span.file != span.file {
            return None;
        }
        if at > unit.span.end {
            return (at >= self.end && top == self.top.len()).then_some(u);
        }
        let members = &self.list[unit.members.clone()];
        let inner = members.partition_point(|m| m.span.start <= at);
        match inner.checked_sub(1) {
            Some(k) if at <= members[k].span.end => Some(unit.members.start + k),
            _ => Some(u),
        }
    }
}

/// The units of the file of `cst` (`text` is its source), the syntax
/// diagnostics among `diagnostics` marked on them, and the items of the
/// units that failed marked in `ast` ([`crate::ast::Item::failed`]).
pub(crate) fn build(cst: &Cst, map: &AstMap, text: &str, diagnostics: &[Diagnostic], ast: &mut Ast) -> Units {
    let item_of: HashMap<NodeId, ItemId> = map.items.iter().enumerate().map(|(i, &n)| (n, ItemId(i as u32))).collect();
    let mut starts: Vec<u32> = diagnostics.iter().filter(|d| d.stage == Stage::Syntax).map(|d| d.span.start).collect();
    starts.sort_unstable();
    let mut b = Builder { cst, text, item_of, starts, list: Vec::new() };
    b.list(cst.root(), None);
    let list = b.list;
    let top = (0..list.len()).filter(|&u| list[u].parent.is_none()).collect();
    let mut units = Units { list, top, end: text.len() as u32 };
    let mut heading_failed = vec![false; units.list.len()];
    for d in diagnostics.iter().filter(|d| d.stage == Stage::Syntax) {
        if let Some(u) = units.of(d.span) {
            units.list[u].syntax_failed = true;
            if units.list[u].heading_holds(d.span.start) {
                heading_failed[u] = true;
            }
        }
    }
    // A unit with a syntax error: the later stages do not check its body. The
    // members of an item whose heading failed are in its unit (§18.1).
    for u in 0..units.list.len() {
        let unit = &units.list[u];
        let failed = unit.syntax_failed || unit.parent.is_some_and(|p| heading_failed[p]);
        if failed && let Some(item) = unit.item {
            ast.items[item.index()].failed.get_or_insert(Failed::Unit);
        }
    }
    units
}

struct Builder<'a> {
    cst: &'a Cst,
    text: &'a str,
    item_of: HashMap<NodeId, ItemId>,
    /// Where the syntax diagnostics start, in order.
    starts: Vec<u32>,
    list: Vec<Unit>,
}

impl Builder<'_> {
    /// The units of the children of `container` (the file, or a list of
    /// members whose unit is `parent`).
    fn list(&mut self, container: NodeId, parent: Option<usize>) {
        // The last unit made in this container, and whether it is a run of
        // tokens of no item.
        let mut last: Option<(usize, bool)> = None;
        for e in self.cst.children(container).to_vec() {
            match e {
                Elem::Node(n) if self.cst.kind(n) == NodeKind::Item => match self.declaration(n) {
                    Some(decl) => {
                        let u = self.push(self.item_span(n), self.item_of.get(&n).copied(), parent);
                        last = Some((u, false));
                        if matches!(
                            self.cst.kind(decl),
                            NodeKind::Impl | NodeKind::Trait | NodeKind::Effect | NodeKind::Handler | NodeKind::Extern
                        ) && let Some(members) =
                            self.cst.child_nodes(decl).find(|&c| self.cst.kind(c) == NodeKind::ItemList)
                        {
                            let start = self.list[u].span.start;
                            let brace =
                                self.cst.child_tokens(members).find(|&t| self.cst.token(t).kind == TokenKind::LBrace);
                            // The heading ends before the `{`: a `{` never closed is
                            // not an error of the heading (§18.1).
                            let end = brace.map_or(self.list[u].span.end, |t| self.cst.token(t).span.start);
                            self.list[u].heading = Some(Span::new(self.list[u].span.file, start, end));
                            let first = self.list.len();
                            self.list(members, Some(u));
                            self.list[u].members = first..self.list.len();
                        }
                    }
                    None => self.stray(self.cst.span(n), parent, &mut last),
                },
                Elem::Node(n) => {
                    let span = self.cst.span(n);
                    if !span.is_empty() {
                        self.after(span, parent, &mut last);
                    }
                }
                Elem::Token(t) => {
                    let token = self.cst.token(t);
                    // A `;`, and trivia with a diagnostic of the lexer: tokens
                    // of no item (S-259).
                    let diagnosed = || {
                        let k = self.starts.partition_point(|&s| s < token.span.start);
                        self.starts.get(k).is_some_and(|&s| s < token.span.end.max(token.span.start + 1))
                    };
                    if token.kind == TokenKind::Semi || (token.kind.is_trivia() && diagnosed()) {
                        self.after(token.span, parent, &mut last);
                    }
                }
            }
        }
    }

    /// The span of an item, its doc comments included.
    fn item_span(&self, n: NodeId) -> Span {
        let span = self.cst.span(n);
        match self.cst.child_nodes(n).find(|&c| self.cst.kind(c) == NodeKind::Docs) {
            Some(docs) => Span::new(span.file, self.cst.full_span(docs).start.min(span.start), span.end),
            None => span,
        }
    }

    /// The declaration node of an `Item` node; `None` when the parser found
    /// none (tokens of no item).
    fn declaration(&self, n: NodeId) -> Option<NodeId> {
        self.cst
            .child_nodes(n)
            .find(|&c| !matches!(self.cst.kind(c), NodeKind::Docs | NodeKind::Attr | NodeKind::Vis | NodeKind::Error))
    }

    fn push(&mut self, span: Span, item: Option<ItemId>, parent: Option<usize>) -> usize {
        let u = self.list.len();
        self.list.push(Unit { span, item, parent, members: u + 1..u + 1, heading: None, syntax_failed: false });
        u
    }

    /// Tokens outside the items: of the unit before them when they are on
    /// the line where it ends (S-254, S-274), else a run of their own.
    // SPEC-GAP(S-274): the tokens other than `;` after an item on its line are
    // of the item's unit, like the `;` of S-254.
    fn after(&mut self, span: Span, parent: Option<usize>, last: &mut Option<(usize, bool)>) {
        if let Some((u, _)) = *last {
            let end = self.list[u].span.end;
            if end <= span.start && !self.text[end as usize..span.start as usize].contains('\n') {
                self.list[u].span = Span::new(span.file, self.list[u].span.start, span.end.max(end));
                return;
            }
        }
        self.stray(span, parent, last);
    }

    /// Tokens of no item: one unit for a run of them up to the next item,
    /// over lines.
    // SPEC-GAP(S-259): a run of tokens of no item over several lines is one
    // unit, and so is trivia with a diagnostic of the lexer among them (a
    // block comment between items).
    fn stray(&mut self, span: Span, parent: Option<usize>, last: &mut Option<(usize, bool)>) {
        if let Some((u, true)) = *last {
            let s = self.list[u].span;
            self.list[u].span = Span::new(s.file, s.start, span.end.max(s.end));
            return;
        }
        let u = self.push(span, None, parent);
        *last = Some((u, true));
    }
}

#[cfg(test)]
mod tests {
    use onsa_diag::FileId;

    /// The text of each unit and its parent.
    fn units(src: &str) -> Vec<(String, Option<usize>)> {
        let p = crate::parse(FileId(0), src);
        p.units.list.iter().map(|u| (src[u.span.start as usize..u.span.end as usize].to_string(), u.parent)).collect()
    }

    fn s(text: &str, parent: Option<usize>) -> (String, Option<usize>) {
        (text.to_string(), parent)
    }

    #[test]
    fn items_and_members_are_units() {
        let src = "/// d\nfn a() {}\nimpl P {\n  fn b(self) {}\n  const C: I32 = 1\n}\n";
        assert_eq!(
            units(src),
            [
                s("/// d\nfn a() {}", None),
                s("impl P {\n  fn b(self) {}\n  const C: I32 = 1\n}", None),
                s("fn b(self) {}", Some(1)),
                s("const C: I32 = 1", Some(1)),
            ]
        );
    }

    #[test]
    fn what_follows_an_item_on_its_line_is_of_its_unit() {
        // S-254: the `;`; S-274: the other tokens; a `;` on a line of its own is a run of its own.
        let src = "fn a() {};\nfn b() {} ) ]\n;\nfn c() {}\n";
        assert_eq!(units(src), [s("fn a() {};", None), s("fn b() {} ) ]", None), s(";", None), s("fn c() {}", None)]);
    }

    #[test]
    fn a_run_of_tokens_of_no_item_is_one_unit_over_lines() {
        // S-259.
        let src = "fn a() {}\n) )\n] ]\n;\nfn b() {}\n";
        assert_eq!(units(src), [s("fn a() {}", None), s(") )\n] ]\n;", None), s("fn b() {}", None)]);
    }

    #[test]
    fn block_comments_between_items_join_the_run_of_tokens_of_no_item() {
        // S-259: block comments between items (E0020) and the tokens after them are one unit.
        let src = "fn a() {}\n/* x */\n/* y */\n$\nfn b() {}\n";
        assert_eq!(units(src), [s("fn a() {}", None), s("/* x */\n/* y */\n$", None), s("fn b() {}", None)]);
    }

    #[test]
    fn a_diagnostic_is_of_the_innermost_unit_and_the_end_of_the_file_of_the_last() {
        let src = "impl P {\n  fn b(self) {\n    let = 1\n  }\n}\nfn c() {\n  1 +";
        let p = crate::parse(FileId(0), src);
        let at = |s: &str| {
            let at = src.find(s).unwrap() as u32;
            p.units.of(onsa_diag::Span::new(FileId(0), at, at))
        };
        assert_eq!(at("impl"), Some(0));
        assert_eq!(at("= 1"), Some(1));
        assert_eq!(at("fn c"), Some(2));
        let end = src.len() as u32;
        assert_eq!(p.units.of(onsa_diag::Span::new(FileId(0), end, end)), Some(2));
        // The member's syntax error marks the member, and its item fails; the `impl` does not.
        assert!(p.units.list[1].syntax_failed && !p.units.list[0].syntax_failed);
        let failed: Vec<bool> = p.ast.items.iter().map(|i| i.failed.is_some()).collect();
        assert_eq!(failed.iter().filter(|f| **f).count(), 2, "`b` and `c`: {failed:?}");
    }
}
