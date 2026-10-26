//! The units of the diagnostics of one file (spec §18.1, S-59, R-71): made
//! once here, from the CST, and read by the later stages (sema skips the body
//! of an item whose unit failed in the syntax stage, `fmt` and `diff --ast`
//! report one diagnostic per unit, the driver chooses one per unit and keeps
//! the table for the tests, D-15). The choice of the diagnostic of a unit is
//! [`Units::choose`] alone: `onsa_driver::reduce` reports with it, and
//! `crate::operands` completes the candidates of what it chooses.
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

use std::collections::{BTreeSet, HashMap};
use std::ops::Range;

use onsa_diag::{Diagnostic, Edit, FileId, Span, Stage};

use crate::ast::{Ast, Failed, ItemId};
use crate::cst::{Cst, Elem, NodeId, NodeKind};
use crate::lower::AstMap;
use crate::parser::ItemCtx;
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
    /// The list it is read in: the top level, or the members of its parent
    /// ([`ItemCtx::of_members`]).
    pub(crate) list: ItemCtx,
    /// Its height in levels (spec §2.5) as the parser read it (none for
    /// tokens of no item).
    pub(crate) height: u32,
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

    /// For each of `diagnostics` (of the file of these units, among any
    /// others), its unit and whether a check reports it there (spec §18.1,
    /// S-59, S-214, S-281): the one choice of a unit's diagnostic. A
    /// diagnostic of a member goes to the unit of its `impl` (`trait`, ...)
    /// when the heading of the item has one (a heading with an error makes
    /// the whole item one unit). In a unit, the diagnostic of the earliest
    /// check stage is reported, and among those the first in the order of the
    /// diagnostics (start, end, code, message), then of `diagnostics`. A
    /// diagnostic of no check stage or outside every unit has none.
    pub fn choose(&self, diagnostics: &[&Diagnostic]) -> Vec<(Option<usize>, bool)> {
        let mut assigned: Vec<Option<usize>> = diagnostics
            .iter()
            .map(|d| {
                d.stage.check_rank()?;
                self.of(d.span)
            })
            .collect();
        let mut heading_error = vec![false; self.list.len()];
        for (d, a) in diagnostics.iter().zip(&assigned) {
            if let Some(u) = *a
                && self.list[u].heading_holds(d.span.start)
            {
                heading_error[u] = true;
            }
        }
        for a in assigned.iter_mut() {
            if let Some(u) = *a
                && let Some(p) = self.list[u].parent
                && heading_error[p]
            {
                *a = Some(p);
            }
        }
        // Both the E0020 of a form and the E0002 of its place may be found at
        // one token (`1.` among the items): the order chooses, here alone.
        let key = |i: usize| (diagnostics[i].unit_order(), i);
        let mut best: Vec<Option<usize>> = vec![None; self.list.len()];
        for (i, a) in assigned.iter().enumerate() {
            if let Some(u) = *a
                && best[u].is_none_or(|b| key(i) < key(b))
            {
                best[u] = Some(i);
            }
        }
        assigned.iter().enumerate().map(|(i, &a)| (a, a.is_some_and(|u| best[u] == Some(i)))).collect()
    }

    /// What a check reads again for the edits at `spans` (§18.1, S-537): the
    /// units of one list that they touch (overlap, or meet at an end), from
    /// the first to the last with the text between them and the blanks and
    /// comments the spans reach round them, in that list. The spans go to
    /// the members of an item when they are inside its braces and touch
    /// members only. `None` when a span touches no unit, when they are of two
    /// lists, and when a unit between the first and the last is not touched:
    /// the reading is no longer than the units touched and the text between
    /// and round them that the spans reach.
    pub(crate) fn reading(&self, spans: &[Span]) -> Option<Within> {
        let (first, last) = self.run(self.top.len(), |k| self.top[k], spans)?;
        let unit = &self.list[first];
        let inside = |s: &Span| unit.heading.is_some_and(|h| h.end <= s.start);
        let members = unit.members.clone();
        let (first, last) = match first == last && spans.iter().all(inside) {
            true => self.run(members.len(), |k| members.start + k, spans).unwrap_or((first, last)),
            false => (first, last),
        };
        let (a, b) = (&self.list[first], &self.list[last]);
        // The blanks and comments that a span takes out round them too.
        let start = spans.iter().map(|s| s.start).fold(a.span.start, u32::min);
        let end = spans.iter().map(|s| s.end).fold(b.span.end, u32::max);
        Some(Within {
            span: Span::new(a.span.file, start, end),
            ctx: a.list,
            height: self.list[first..=last].iter().map(|u| u.height).max().unwrap_or(0),
        })
    }

    /// The first and the last of the units of a list (its `n` units, the
    /// `k`th of which is `unit(k)`, in the order of the text) that `spans`
    /// touch, when they touch a run of them.
    fn run(&self, n: usize, unit: impl Fn(usize) -> usize, spans: &[Span]) -> Option<(usize, usize)> {
        let span = |k: usize| self.list[unit(k)].span;
        // The first `k` where `before` no longer holds (it holds up to there).
        let point = |before: &dyn Fn(Span) -> bool| {
            let (mut lo, mut hi) = (0, n);
            while lo < hi {
                let mid = (lo + hi) / 2;
                if before(span(mid)) { lo = mid + 1 } else { hi = mid }
            }
            lo
        };
        let mut touched = BTreeSet::new();
        for s in spans {
            let a = point(&|u| u.end < s.start);
            let b = point(&|u| u.start <= s.end);
            if a >= b || (a..b).any(|k| span(k).file != s.file) {
                return None;
            }
            touched.extend(a..b);
        }
        let (&first, &last) = (touched.first()?, touched.last()?);
        (last - first + 1 == touched.len()).then(|| (unit(first), unit(last)))
    }
}

/// A text that a check reads again as the declarations of a list (a unit,
/// a run of units, or the whole file): its span in the file, the list, and
/// the height (§2.5) the parser read of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Within {
    pub span: Span,
    pub ctx: ItemCtx,
    pub height: u32,
}

impl Within {
    /// The whole of `text`, at the top level, `height` levels high.
    pub(crate) fn file(file: FileId, text: &str, height: u32) -> Within {
        Within { span: Span::new(file, 0, text.len() as u32), ctx: ItemCtx::Top, height }
    }

    /// Its part of the text of the file.
    pub(crate) fn of<'t>(&self, text: &'t str) -> &'t str {
        &text[self.span.start as usize..self.span.end as usize]
    }

    /// The edit `e` of the file as one of its text (from its start), and
    /// back ([`Within::global`]).
    pub(crate) fn local(&self, e: &Edit) -> Edit {
        let s = Span::new(e.span.file, e.span.start - self.span.start, e.span.end - self.span.start);
        Edit::replace(s, e.replace.clone())
    }

    pub(crate) fn global(&self, e: &Edit) -> Edit {
        let s = Span::new(e.span.file, e.span.start + self.span.start, e.span.end + self.span.start);
        Edit::replace(s, e.replace.clone())
    }
}

/// The units of the file of `cst` (`text` is its source; `heights` the
/// height of each item node by its start, `ParseOutput::items`). A run of
/// tokens of no item takes the trivia with a diagnostic of the syntax stage
/// in `diagnostics` (S-259): those of the lexer and of the doc comments,
/// which are reported before the units are made; the later checks report
/// on code.
pub(crate) fn build(cst: &Cst, map: &AstMap, text: &str, heights: &[(u32, u32)], diagnostics: &[Diagnostic]) -> Units {
    let item_of: HashMap<NodeId, ItemId> = map.items.iter().enumerate().map(|(i, &n)| (n, ItemId(i as u32))).collect();
    let mut starts: Vec<u32> = diagnostics.iter().filter(|d| d.stage == Stage::Syntax).map(|d| d.span.start).collect();
    starts.sort_unstable();
    let heights = heights.iter().copied().collect();
    let mut b = Builder { cst, text, item_of, heights, starts, ctx: ItemCtx::Top, list: Vec::new() };
    b.list(cst.root(), None);
    let list = b.list;
    let top = (0..list.len()).filter(|&u| list[u].parent.is_none()).collect();
    Units { list, top, end: text.len() as u32 }
}

impl Units {
    /// The syntax diagnostics among `diagnostics` marked on the units, and
    /// the items of the units that failed marked in `ast`
    /// ([`crate::ast::Item::failed`]).
    pub(crate) fn mark_failed(&mut self, diagnostics: &[Diagnostic], ast: &mut Ast) {
        let mut heading_failed = vec![false; self.list.len()];
        for d in diagnostics.iter().filter(|d| d.stage == Stage::Syntax) {
            if let Some(u) = self.of(d.span) {
                self.list[u].syntax_failed = true;
                if self.list[u].heading_holds(d.span.start) {
                    heading_failed[u] = true;
                }
            }
        }
        // A unit with a syntax error: the later stages do not check its body. The
        // members of an item whose heading failed are in its unit (§18.1).
        for unit in &self.list {
            let failed = unit.syntax_failed || unit.parent.is_some_and(|p| heading_failed[p]);
            if failed && let Some(item) = unit.item {
                ast.items[item.index()].failed.get_or_insert(Failed::Unit);
            }
        }
    }
}

/// The declaration node of the `Item` node `n`; `None` when the parser
/// found none (tokens of no item).
pub(crate) fn declaration(cst: &Cst, n: NodeId) -> Option<NodeId> {
    cst.child_nodes(n)
        .find(|&c| !matches!(cst.kind(c), NodeKind::Docs | NodeKind::Attr | NodeKind::Vis | NodeKind::Error))
}

struct Builder<'a> {
    cst: &'a Cst,
    text: &'a str,
    item_of: HashMap<NodeId, ItemId>,
    /// The height of each item node, by its start.
    heights: HashMap<u32, u32>,
    /// Where the syntax diagnostics start, in order.
    starts: Vec<u32>,
    /// The list whose units are made ([`Unit::list`]).
    ctx: ItemCtx,
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
                Elem::Node(n) if self.cst.kind(n) == NodeKind::Item => match declaration(self.cst, n) {
                    Some(decl) => {
                        let u = self.push(self.item_span(n), self.item_of.get(&n).copied(), parent);
                        self.list[u].height = self.heights.get(&self.cst.span(n).start).copied().unwrap_or(0);
                        last = Some((u, false));
                        if let Some(inner) = ItemCtx::of_members(self.cst.kind(decl))
                            && let Some(members) =
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
                            let outer = std::mem::replace(&mut self.ctx, inner);
                            self.list(members, Some(u));
                            self.ctx = outer;
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

    fn push(&mut self, span: Span, item: Option<ItemId>, parent: Option<usize>) -> usize {
        let u = self.list.len();
        let (members, list) = (u + 1..u + 1, self.ctx);
        self.list.push(Unit { span, item, parent, members, heading: None, syntax_failed: false, list, height: 0 });
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
    // Plan S-259: a run of tokens of no item over several lines is one
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
