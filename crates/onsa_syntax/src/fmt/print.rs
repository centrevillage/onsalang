//! The printer of `onsa fmt` (`spec/tools.md` §3.2, §3.4; W3-11 unit
//! U3a): it walks the tokens of the CST and writes the code tokens and the
//! comments in their order, deciding only what goes between two of them. The
//! plan (`fmt/plan.rs`, W3-11 unit U3b) says which code tokens it leaves out,
//! respells or follows with a `,`.
//!
//! The walk does not recurse (as in `cst.rs`); it keeps a stack of the nodes
//! it is in ([`Frame`]). Between two code tokens the gap is read from the
//! trivia between them and from the deepest node that holds both (the top
//! of the stack that began before the second token):
//!
//! - **No line break:** the space of the table (`space::space`, S-496).
//! - **Line breaks:** every line break of the writer is kept (R-143), as
//!   `\n` (S-201), but for those the plan removes; the plan adds others
//!   (`fmt/plan.rs`, read at the head of [`Printer::token`]). Where the deepest node holds statements or items, or the
//!   gap lies between the elements of a list, the gap separates two parts and
//!   keeps one blank line of the writer's (S-122, S-499); not before the first
//!   or after the last line of content (a code or comment line; the comment
//!   at the end of the line of the opening bracket is none, S-502). Every
//!   other gap is inside one part and keeps no blank line.
//! - **Indentation** (S-498, S-335), two spaces a level: a statement or an
//!   item is one level deeper than the base line of its block (none in the
//!   file); an element of a list in the block form one level deeper than the
//!   base line of the list, in the continuation form at the column of the
//!   first element; a closing bracket at its base line. The base line is
//!   the line of a `(` or a `[` and, for a `{`, the line where the form that
//!   holds it starts (`shape::holder`). Any other line (a continuation of
//!   §2.5, a line break inside an element) is one level deeper than the
//!   line where its owner starts: the innermost statement or item, element of
//!   a list, or content of an enclosure that holds the line break. Levels do
//!   not add up over continuations. The line after a line that starts with
//!   an attribute has the indentation of that line; the line after another
//!   attribute of an element of a list in the continuation form is at the
//!   column of the first element (S-524).
//! - **Comments** stay where they are written (§3.4): a comment after code
//!   at the end of that line, a comment on a line of its own with the
//!   indentation of the next line (inside the brackets when that line is a
//!   closing bracket), and the line break after a comment is always kept.
//!
//! The indentation of a line is read from the stack; the output is not read
//! back. The comments at the ends of lines are aligned after the walk
//! (`fmt/align.rs`).

use super::align;
use super::plan::Plan;
use super::rewrites::Choices;
use super::shape::{self, Form, Shape};
use super::space::{self, Space};
use crate::cst::{Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// One level of indentation.
const STEP: usize = 2;

/// The source written in the canonical form of the printer (see the module
/// documentation). `cst` is the tree of `src`, without a syntax error, and
/// `choices` its rewrites.
pub(super) fn print(cst: &Cst, src: &str, choices: &Choices) -> String {
    let plan = Plan::new(cst, src, choices);
    let mut p = Printer {
        cst,
        src,
        plan: &plan,
        frames: Vec::new(),
        begun: 0,
        out: String::new(),
        line: 0,
        col: 0,
        indent: 0,
        line_head: None,
        comment_marks: Vec::new(),
        comment_lines: Vec::new(),
        attribute: None,
    };
    p.walk();
    align::finish(p.out, p.comment_marks, &p.comment_lines)
}

/// A node the walk is in.
struct Frame {
    node: NodeId,
    /// The next child to walk.
    next: usize,
    /// The indentation of the line of its first code token, once it is written.
    start: Option<usize>,
    /// The output line of its first code token, once it is written.
    line: usize,
    /// Whether its first code token began a line.
    heads_line: bool,
    /// A statement or an item: a child of the file or of a container (`shape::holds_statements`).
    statement: bool,
    brackets: Option<Brackets>,
}

/// The brackets of a node in the table of `fmt/shape.rs`.
struct Brackets {
    /// The pairs, the outermost first (`shape::pairs`: more than one only
    /// in an enclosure with nested pairs, `-((1))`).
    pairs: Vec<Pair>,
    what: What,
}

struct Pair {
    open: TokenIdx,
    close: TokenIdx,
    /// The indentation of the base line, once the opening bracket is written.
    base: Option<usize>,
}

impl Brackets {
    fn outermost(&self) -> &Pair {
        &self.pairs[0]
    }

    /// The pair whose opening bracket is `prev` or whose closing bracket is `t`, else the outermost.
    fn pair_round(&self, prev: Option<TokenIdx>, t: TokenIdx) -> &Pair {
        self.pairs.iter().find(|p| prev == Some(p.open) || t == p.close).unwrap_or(self.outermost())
    }
}

enum What {
    /// A block or a body of items.
    Container,
    /// Any other enclosure: the indentation of the line where its content starts.
    Enclosure { content: Option<usize> },
    /// A list: its form, the first tokens of its elements (and of the rest
    /// of a struct pattern), the indentation of the line where the current
    /// element starts, and the column of the first element.
    List { form: Form, starts: Vec<TokenIdx>, element: Option<usize>, first_col: Option<usize> },
}

/// Where the line breaks of a gap put the next line.
struct Place {
    /// The indentation of the line of the next code token.
    indent: usize,
    /// The indentation of the comments on lines of their own in the gap.
    comments: usize,
    /// Whether the gap separates two parts and keeps a blank line.
    separates: bool,
    /// The gap starts right after an opening bracket (or at the head of the file).
    head: bool,
    /// The gap ends right before a closing bracket (or at the end of the file).
    tail: bool,
}

/// The trivia between two code tokens.
struct Gap {
    /// A comment at the end of the line of the first token.
    trailing: Option<TokenIdx>,
    /// The comments on lines of their own, each with the number of blank lines before it.
    lines: Vec<(usize, TokenIdx)>,
    /// The number of blank lines before the second token.
    blanks: usize,
    /// Whether there is a line break.
    breaks: bool,
}

struct Printer<'a> {
    cst: &'a Cst,
    src: &'a str,
    plan: &'a Plan,
    frames: Vec<Frame>,
    /// The number of frames, from the root, whose first code token is written.
    begun: usize,
    out: String,
    /// The index of the output line, its column and its indentation.
    line: usize,
    col: usize,
    indent: usize,
    /// The first code token of the output line.
    line_head: Option<TokenIdx>,
    comment_marks: Vec<(usize, String)>,
    /// The output lines of the comments on lines of their own.
    comment_lines: Vec<usize>,
    /// The attributes the walk left last ([`Printer::leave`]).
    attribute: Option<Attributes>,
}

/// Attributes one after the other on a line: the last token of the last one,
/// the output lines of the first token of the first one and of that last
/// token, and the indentation of the line when the first one starts it.
struct Attributes {
    end: TokenIdx,
    first: usize,
    line: usize,
    indent: Option<usize>,
}

impl<'a> Printer<'a> {
    fn walk(&mut self) {
        let cst = self.cst;
        let mut prev = None;
        self.enter(cst.root());
        while let Some(top) = self.frames.last_mut() {
            let Some(&child) = cst.children(top.node).get(top.next) else {
                let f = self.frames.pop().expect("a frame");
                self.begun = self.begun.min(self.frames.len());
                self.leave(f, prev);
                continue;
            };
            top.next += 1;
            match child {
                Elem::Node(c) => self.enter(c),
                Elem::Token(t) if !cst.token(t).kind.is_trivia() && self.plan.kept(t) => {
                    self.token(prev, t);
                    prev = Some(t);
                }
                Elem::Token(_) => {}
            }
        }
    }

    fn enter(&mut self, n: NodeId) {
        let cst = self.cst;
        let kind = cst.kind(n);
        let pairs: Vec<Pair> =
            shape::pairs(cst, n).into_iter().map(|(open, close)| Pair { open, close, base: None }).collect();
        let brackets = shape::shape(kind).filter(|_| !pairs.is_empty()).map(|row| {
            let what = match row.shape {
                Shape::Container => What::Container,
                Shape::List => {
                    let starts = shape::part_starts(cst, n);
                    let form = self.plan.form(pairs[0].open).expect("the plan has the form of a list");
                    What::List { form, starts, element: None, first_col: None }
                }
                Shape::Enclosure => What::Enclosure { content: None },
            };
            Brackets { pairs, what }
        });
        let statement = cst.parent(n).is_some_and(|p| shape::holds_statements(cst.kind(p)));
        self.frames.push(Frame { node: n, next: 0, start: None, line: 0, heads_line: false, statement, brackets });
    }

    /// Leave the frame `f`; `last` is the last code token written.
    fn leave(&mut self, f: Frame, last: Option<TokenIdx>) {
        if self.cst.kind(f.node) == NodeKind::Attr
            && let (Some(last), Some(indent)) = (last, f.start)
        {
            let (first, line, indent) = (f.line, self.line, f.heads_line.then_some(indent));
            match &mut self.attribute {
                Some(a) if !f.heads_line && a.line == line => a.end = last,
                _ => self.attribute = Some(Attributes { end: last, first, line, indent }),
            }
        }
    }

    /// Write the code token `t` after the gap from `prev`.
    fn token(&mut self, prev: Option<TokenIdx>, t: TokenIdx) {
        let cst = self.cst;
        // The deepest node that holds both tokens; the nodes above it start at `t`.
        let deepest = self.begun.max(1) - 1;
        let mut gap = self.gap(prev, t);
        // After the attributes of a `let`, the `let` is on their line when they are on one line of the output
        // and no comment is between, else on the next line (§3.2, S-527). Then the line breaks of the plan.
        let comment = gap.trailing.is_some() || !gap.lines.is_empty();
        let of_let = self.attribute.as_ref().filter(|a| prev == Some(a.end));
        if let Some(a) = of_let.filter(|_| cst.kind(self.frames[deepest].node) == NodeKind::LetStmt) {
            if a.first == self.line && !comment {
                (gap.breaks, gap.blanks) = (false, 0);
            } else {
                gap.breaks = true;
            }
        } else if self.plan.joins(t) && !comment {
            (gap.breaks, gap.blanks) = (false, 0);
        } else if self.plan.breaks_before(t) {
            gap.breaks = true;
        }
        let eof = cst.token(t).kind == TokenKind::Eof;
        if let (Some(prev), false) = (prev, gap.breaks) {
            if eof {
                return;
            }
            if space::space(cst, prev, t) == Space::One {
                self.write(" ");
            }
        } else {
            let place = self.place(deepest, prev, t);
            if let Some(c) = gap.trailing {
                self.write(" ");
                let text = self.comment(c);
                self.comment_marks.push((self.line, text.to_string()));
                self.write(text);
            }
            let mut content_before = !place.head;
            for &(blanks, c) in &gap.lines {
                self.new_line(place.separates && content_before && blanks > 0, place.comments);
                self.comment_lines.push(self.line);
                self.write(self.comment(c));
                content_before = true;
            }
            if eof {
                return;
            }
            self.new_line(place.separates && content_before && !place.tail && gap.blanks > 0, place.indent);
        }
        let col = self.col;
        let heads_line = self.line_head.is_none();
        if heads_line {
            self.line_head = Some(t);
        }
        let span = cst.token(t).span;
        let plan: &'a Plan = self.plan;
        self.write(plan.text(t).unwrap_or(&self.src[span.start as usize..span.end as usize]));
        self.started(deepest, prev, t, col, heads_line);
        if plan.comma_after(t) {
            self.write(",");
        }
    }

    /// Record what the token `t`, written at `col`, starts.
    fn started(&mut self, deepest: usize, prev: Option<TokenIdx>, t: TokenIdx, col: usize, heads_line: bool) {
        let (indent, line) = (self.indent, self.line);
        for f in &mut self.frames[deepest + 1..] {
            f.start = Some(indent);
            f.line = line;
            f.heads_line = heads_line;
        }
        self.begun = self.frames.len();
        if let Some(b) = &mut self.frames[deepest].brackets {
            let outermost = b.pairs[0].open;
            match &mut b.what {
                What::List { starts, element, first_col, .. } if starts.binary_search(&t).is_ok() => {
                    *element = Some(indent);
                    if starts[0] == t {
                        *first_col = Some(col);
                    }
                }
                What::Enclosure { content } if prev == Some(outermost) => *content = Some(indent),
                _ => {}
            }
        }
        // The opening bracket of a pair of the node on the top (an inner pair of `-((1))` too).
        let top = self.frames.len() - 1;
        let Some(pair) = self.frames[top].brackets.as_ref().and_then(|b| b.pairs.iter().position(|p| p.open == t))
        else {
            return;
        };
        let base = match shape::holder(self.cst, self.frames[top].node) {
            None => indent,
            Some(h) => {
                self.frames.iter().rev().find(|f| f.node == h).and_then(|f| f.start).expect("the holder has begun")
            }
        };
        self.frames[top].brackets.as_mut().expect("brackets").pairs[pair].base = Some(base);
    }

    /// The trivia between `prev` (none at the head of the file) and `t`,
    /// two code tokens the printer writes one after the other.
    ///
    /// A blank line is a line of the source with nothing on it: a code token
    /// the plan leaves out between the two (a `,` at the head of a line that
    /// moves to the element before it, a rewrite of §3.3) is something on its
    /// line, so the line breaks before and after it make no blank line (§3.2,
    /// S-499: only the blank lines of the writer are kept). The line breaks
    /// still count as a line break of the writer's.
    fn gap(&self, prev: Option<TokenIdx>, t: TokenIdx) -> Gap {
        let from = prev.map_or(0, |p| p.index() + 1);
        let mut gap = Gap { trailing: None, lines: Vec::new(), blanks: 0, breaks: false };
        // The line breaks after the last thing on a line, and the blank lines before that thing.
        let (mut breaks, mut blanks) = (0, 0);
        for (i, tok) in self.cst.tokens()[from..t.index()].iter().enumerate() {
            let c = TokenIdx((from + i) as u32);
            // A line break that goes with a token a rewrite drops (§3.4) is none.
            if tok.kind == TokenKind::Newline && self.plan.kept(c) {
                breaks += 1;
                gap.breaks = true;
                continue;
            }
            if !tok.kind.is_comment() && !tok.kind.is_code() {
                continue;
            }
            blanks += breaks.max(1) - 1;
            breaks = 0;
            if tok.kind.is_comment() {
                if !gap.breaks && prev.is_some() {
                    gap.trailing = Some(c);
                } else {
                    gap.lines.push((blanks, c));
                }
                (gap.breaks, blanks) = (true, 0);
            }
        }
        gap.blanks = blanks + breaks.max(1) - 1;
        gap
    }

    /// Where the line breaks between `prev` and `t` put the next line; the
    /// frame `deepest` holds both tokens.
    fn place(&self, deepest: usize, prev: Option<TokenIdx>, t: TokenIdx) -> Place {
        let cst = self.cst;
        let f = &self.frames[deepest];
        if shape::holds_statements(cst.kind(f.node)) {
            let (head, tail, base, inner) = match f.brackets.as_ref().map(Brackets::outermost) {
                Some(b) => {
                    let base = b.base.expect("the opening bracket is written");
                    (prev == Some(b.open), t == b.close, base, base + STEP)
                }
                None => (prev.is_none(), cst.token(t).kind == TokenKind::Eof, 0, 0), // the file
            };
            return Place { indent: if tail { base } else { inner }, comments: inner, separates: true, head, tail };
        }
        let pair = f.brackets.as_ref().map(|b| (b.pair_round(prev, t), &b.what));
        if let Some((Pair { open, close, base: Some(base) }, what)) = pair {
            let (head, tail) = (prev == Some(*open), t == *close);
            let inner = base + STEP;
            let at = |inner: usize, separates| Place {
                indent: if tail { *base } else { inner },
                comments: inner,
                separates,
                head,
                tail,
            };
            match what {
                What::Enclosure { .. } if head || tail => return at(inner, false),
                What::List { form, starts, first_col, .. } => {
                    if head || tail || starts.binary_search(&t).is_ok() {
                        // A comment before the closing bracket is one level deeper than the base line (S-531).
                        let inner = match (form, first_col) {
                            (Form::Continuation, Some(col)) if !tail => *col,
                            _ => inner,
                        };
                        return at(inner, true);
                    }
                }
                What::Enclosure { .. } | What::Container => {}
            }
        }
        // After attributes that start their line, their indentation; after others of an element of a list in
        // the continuation form, the column of its first element (S-524).
        let indent = match &self.attribute {
            Some(a) if prev == Some(a.end) => a.indent.or_else(|| self.continuation(deepest)),
            _ => None,
        };
        let indent = indent.unwrap_or_else(|| self.owner(deepest) + STEP);
        Place { indent, comments: indent, separates: false, head: false, tail: false }
    }

    /// The column of the first element of the list in the continuation form
    /// whose element is the frame `deepest`.
    fn continuation(&self, deepest: usize) -> Option<usize> {
        match &self.frames[..deepest].last()?.brackets.as_ref()?.what {
            What::List { form: Form::Continuation, first_col, .. } => *first_col,
            _ => None,
        }
    }

    /// The indentation of the line where the owner of a line break in the
    /// frame `deepest` starts: the innermost statement or item, element of a
    /// list or content of an enclosure.
    fn owner(&self, deepest: usize) -> usize {
        for f in self.frames[..=deepest].iter().rev() {
            match f.brackets.as_ref().map(|b| &b.what) {
                Some(What::List { element: Some(at), .. } | What::Enclosure { content: Some(at) }) => return *at,
                _ if f.statement => return f.start.expect("a statement that holds a line break has begun"),
                _ => {}
            }
        }
        unreachable!("a line break inside no statement, element or enclosure")
    }

    /// The text of the comment `c`, without blanks at its end.
    fn comment(&self, c: TokenIdx) -> &'a str {
        crate::lexer::comment_text(self.src, self.cst.token(c).span)
    }

    /// End the output line (and add a blank line when `blank`), and indent the next.
    fn new_line(&mut self, blank: bool, indent: usize) {
        if !self.out.is_empty() {
            self.out.push('\n');
            self.line += 1;
            if blank {
                self.out.push('\n');
                self.line += 1;
            }
        }
        self.out.extend(std::iter::repeat_n(' ', indent));
        self.col = indent;
        self.indent = indent;
        self.line_head = None;
    }

    fn write(&mut self, s: &str) {
        self.out.push_str(s);
        self.col += s.chars().count();
    }
}
