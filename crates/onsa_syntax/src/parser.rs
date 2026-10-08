//! Hand-written recursive-descent parser (D-01) over the token list from the
//! lexer. It builds the CST ([`crate::cst`]) through a list of events; the
//! AST is made from the CST in one stage ([`crate::lower`], R-86).
//!
//! Newlines (spec §2.5): inside a block a `Newline` token ends a statement
//! unless the line ends with a binary operator, `=`, `->` or `=>`, or the next
//! line starts with `.`. Inside parentheses, brackets, struct literals, match
//! arm lists, generic lists and `uses { }` rows, newlines are whitespace. The
//! parser keeps a stack of "newline significant" flags; `peek` skips newlines
//! whenever the top of the stack says they are insignificant.
//!
//! The parser reads the tokens without the whitespace tokens (what separates
//! two tokens is [`crate::token::gap_before`]). A token it consumes is an
//! event `Token`; the tokens it skips (comments, insignificant newlines,
//! whitespace) are placed in the tree by [`crate::cst::build`].
//!
//! Errors: at most one diagnostic per top-level item is kept (P-01, §18.1).
//! Parse errors are fatal for the item; the parser closes the nodes it was in
//! as incomplete, puts the tokens up to the next item start in an `Error`
//! node, and continues.

use onsa_diag::{Code, Diagnostic, Edit, FileId, Fix, Span, Stage};

use crate::ast::Ast;
use crate::cst::{Cst, Event, NodeKind};
use crate::lower::AstMap;
use crate::token::{Gap, Token, TokenKind};

/// Result of [`crate::parse`].
#[derive(Debug)]
pub struct Parsed {
    pub ast: Ast,
    /// The CST the AST was made from.
    pub cst: Cst,
    /// From each AST node to the CST node it was made from.
    pub map: AstMap,
    pub diagnostics: Vec<Diagnostic>,
    /// Every diagnostic of the lexer and the parser (stage `Syntax`), taken
    /// before the diagnostics were reduced to one per item (S-56): what
    /// [`Parsed::syntax_errors`] reads, and what `fmt` and `diff --ast` report.
    pub syntax: Vec<Diagnostic>,
    /// The levels (spec §2.5) of each top-level item the parser finished, in
    /// the order of the file (`onsa dump --levels`; the fmt properties check
    /// that `fmt` makes no item deeper, `tools/fmt_props.py`).
    pub levels: Vec<u32>,
}

impl Parsed {
    /// The lexer or the parser reported a diagnostic: `onsa fmt` does not
    /// rewrite the file and `onsa diff --ast` does not compare it, since the
    /// parser may have left an item out of the AST, whatever the code (R-146).
    /// The one place of that decision (`fmt`, `diff --ast`, the test tools).
    // SPEC-GAP(S-214): §18.2 and S-120 say "the E00xx of the lexer and the
    // parser"; the parser also fails items with E0408. Until S-214 is decided,
    // every diagnostic of the syntax stage stops them (the conservative reading).
    pub fn syntax_errors(&self) -> bool {
        !self.syntax.is_empty()
    }

    /// What `fmt` and `diff --ast` report for a file they do not take: every
    /// diagnostic of the syntax stage (the reduction per item would hide some
    /// behind a diagnostic of a later stage, §18.2 "report them all"), then
    /// the reduced diagnostics of the later stages (E0320), by position.
    pub fn syntax_report(&self) -> Vec<Diagnostic> {
        let mut out = self.syntax.clone();
        out.extend(self.diagnostics.iter().filter(|d| d.stage != onsa_diag::Stage::Syntax).cloned());
        out.sort_by_key(|d| (d.span.file, d.span.start, d.code));
        out
    }
}

/// What the parser gives the later stages of [`crate::parse`].
pub(crate) struct ParseOutput {
    pub tokens: Vec<Token>,
    pub events: Vec<Event>,
    pub diagnostics: Vec<Diagnostic>,
    /// Spans of every top-level item attempt (successful or not), for P-01.
    pub item_ranges: Vec<Span>,
    /// The levels of each top-level item that parsed ([`Parsed::levels`]).
    pub levels: Vec<u32>,
    /// The height of the tree in levels (spec §2.5), as the parser counted
    /// it (`Parser::height`): the deepest declaration unit. The tests compare
    /// it with the tree.
    #[cfg_attr(not(test), allow(dead_code))]
    pub height: u32,
}

/// Marker for "a diagnostic was reported; abandon this item".
#[derive(Debug, Clone, Copy)]
pub(crate) struct ParseError;

pub(crate) type PResult<T> = Result<T, ParseError>;

/// What kind of declaration list we are inside; decides whether `fn` bodies
/// are required / allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ItemCtx {
    Top,
    Trait,
    Impl,
    Effect,
    Handler,
    Extern,
    InlineHandler,
}

const BUILTIN_TYPE_FIXES: &[(&str, &str)] = &[
    ("i8", "I8"),
    ("i16", "I16"),
    ("i32", "I32"),
    ("i64", "I64"),
    ("u8", "U8"),
    ("u16", "U16"),
    ("u32", "U32"),
    ("u64", "U64"),
    ("f32", "F32"),
    ("f64", "F64"),
    ("bool", "Bool"),
    ("usize", "U32"),
    ("isize", "I32"),
];

/// An open node. It is closed by [`Parser::complete`]; a syntax error leaves
/// it open and `parse_file` closes it as incomplete (no check on drop: `?`
/// drops markers).
#[derive(Debug, Clone, Copy)]
struct Marker {
    /// Index of its `Start` event.
    event: u32,
    /// Start offset of its span (the first token the parser saw in it).
    start: u32,
}

/// A closed node.
#[derive(Debug, Clone, Copy)]
struct Completed {
    kind: NodeKind,
    event: u32,
    /// Where the node starts (a node that wraps it starts there too).
    start: u32,
    /// The span of the AST node it gives (for a `RefExpr`, the inner expression).
    span: Span,
    /// The height of its subtree ([`Parser::height`]).
    height: u32,
}

/// An open node: its `Start` event, the greatest height of its children so
/// far, and its level.
#[derive(Debug, Clone, Copy)]
struct Open {
    event: u32,
    children: u32,
    /// The levels (spec §2.5) from the root of the declaration unit down to
    /// this node, this node included: a child of `height(kind, 0)` levels is
    /// at `level + height(kind, 0)`. Items, lists and statements count no
    /// level, so every unit starts from 0. In a binary chain it is the level
    /// of the operator whose right operand is read ([`Parser::chain_operator`]).
    level: u32,
}

/// The deepest nesting of the syntax (spec §2.5, S-183, S-221): a form at a
/// level above it is E0006 ([`Parser::too_deep`]).
pub const NESTING_LIMIT: u32 = 256;

/// A parsed path: its node, the number of segments and the first and last segment.
#[derive(Debug, Clone, Copy)]
struct PathInfo {
    segments: usize,
    first: Token,
    last: Token,
}

pub(crate) struct Parser<'a> {
    file: FileId,
    text: &'a str,
    /// The full token list of the lexer.
    all: Vec<Token>,
    /// The tokens the parser reads: the full list without whitespace.
    tokens: Vec<Token>,
    /// Index in `all` of each token of `tokens`.
    full: Vec<u32>,
    /// Index of the next raw token.
    pos: usize,
    /// End offset of the last consumed token.
    last_end: u32,
    /// Stack of "newlines are significant" flags.
    nl: Vec<bool>,
    /// S-08: no struct literal in the head expression of `if` / `while` / ...
    no_struct_lit: bool,
    /// Brace depth of the cursor (for recovery).
    depth: i32,
    events: Vec<Event>,
    /// The open nodes, innermost last.
    open: Vec<Open>,
    /// The height of the tree, once the root closed.
    height: u32,
    diagnostics: Vec<Diagnostic>,
    /// Spans of every top-level item attempt (successful or not), for P-01.
    item_ranges: Vec<Span>,
    /// The levels of each top-level item that parsed.
    levels: Vec<u32>,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(file: FileId, text: &'a str, all: Vec<Token>, diagnostics: Vec<Diagnostic>) -> Parser<'a> {
        let full: Vec<u32> = (0..all.len() as u32).filter(|&i| all[i as usize].kind != TokenKind::Whitespace).collect();
        let tokens = full.iter().map(|&i| all[i as usize]).collect();
        Parser {
            file,
            text,
            all,
            tokens,
            full,
            pos: 0,
            last_end: 0,
            nl: vec![true],
            no_struct_lit: false,
            depth: 0,
            events: Vec::new(),
            open: Vec::new(),
            height: 0,
            diagnostics,
            item_ranges: Vec::new(),
            levels: Vec::new(),
        }
    }

    // ------------------------------------------------------------ nodes

    /// The one place where nodes open (`start`, `precede`, the recovery,
    /// the doc comments of an item). `children` is the height of what the
    /// node wraps already (for `precede`). A node whose subtree reaches a
    /// level over [`NESTING_LIMIT`] is E0006 at the next token, the token that
    /// makes the level (spec §2.5); nothing is opened then.
    fn enter(&mut self, kind: NodeKind, start: u32, children: u32) -> PResult<Marker> {
        let base = self.level();
        self.limit(base + Self::height(kind, children), self.peek().span, kind)?;
        let event = self.events.len() as u32;
        self.events.push(Event::Start { kind: Some(kind), forward_parent: None });
        self.open.push(Open { event, children, level: base + Self::height(kind, 0) });
        Ok(Marker { event, start })
    }

    /// Open a node of no level (an item, its doc comments, the skipped
    /// tokens of the recovery, the file): it never reaches the limit.
    fn enter_unit(&mut self, kind: NodeKind, start: u32) -> Marker {
        debug_assert_eq!(Self::height(kind, 0), 0, "{kind:?} is not a node of no level");
        self.enter(kind, start, 0).unwrap_or_else(|ParseError| {
            onsa_diag::internal::bug(Some(self.peek().span), format!("{kind:?} counts a level"))
        })
    }

    /// Open a node at the next token.
    fn start(&mut self, kind: NodeKind) -> PResult<Marker> {
        let start = self.peek().span.start;
        self.enter(kind, start, 0)
    }

    /// The level of the innermost open node (0 outside every node).
    fn level(&self) -> u32 {
        self.open.last().map_or(0, |o| o.level)
    }

    /// The height of the subtree of a node of `kind` whose highest child has
    /// height `children`: the one function that counts the depth of the
    /// syntax (spec §2.5, S-221). Each form of an expression, a type or a
    /// pattern and each block is one level; names, literals, `_`, lists,
    /// statements and the headers of declarations are none, so a node of no
    /// level never nests in another without a node of one level between
    /// them. No wildcard: a new kind of node decides its level here.
    pub(crate) fn height(kind: NodeKind, children: u32) -> u32 {
        use NodeKind::*;
        let level = match kind {
            // The file, the items and their headers: a unit starts from 0.
            SourceFile | Error | Name | Item | Docs | Attr | HashAttr | AttrArgs | AttrNamedArg | Vis | Fn | Flow
            | Struct | FieldList | Field | TupleStructBody | Enum | VariantList | Variant | VariantFields
            | TypeAlias | OpaqueType | Trait | Impl | Effect | Handler | Const | Use | UseTree | UseNames | Extern
            | Target | Test | ItemList | GenericParams | TypeParam | ConstParam | EffectParam | Bound | ParamList
            | Param | EffectRow | Path => 0,
            // Types: a type with arguments counts at its `[` (the `TypeArgs`), a name none.
            PathType | ConstArg | FnTypeParams => 0,
            TypeArgs | UnitType | TupleType | ArrayType | FnType => 1,
            // Statements are none, the loops one (and their blocks one more).
            LetStmt | VarStmt | BreakStmt | ContinueStmt | ReturnStmt | AssertStmt | AssignStmt | ExprStmt => 0,
            ForStmt | WhileStmt | LoopStmt | Block => 1,
            // Expressions. A binary chain is flat in the tree: its height is
            // the one of the tree of §3.1, one level per operator ([`Chain`]).
            Literal | LeadingDotFloat | HoleExpr | PathExpr | BinaryExpr | MatchArms | MatchArm | ArgList | Arg
            | StructLitFields | StructLitField => 0,
            ParenExpr | TupleExpr | ArrayExpr | RepeatExpr | IfExpr | MatchExpr | ClosureExpr | HandleExpr
            | UnsafeExpr | ParExpr | MoveExpr | RangeExpr | CastExpr | PrefixExpr | RefExpr | CallExpr | FieldExpr
            | TupleIndexExpr | IndexExpr | TryExpr | StructLit => 1,
            // Patterns: `|` is one level for all its alternatives.
            WildPat | LitPat | NegLitPat | BindPat | PathPat | StructPatField => 0,
            TuplePat | TupleStructPat | StructPat | OrPat => 1,
        };
        children + level
    }

    /// E0006 when a form whose subtree reaches level `total` is over the
    /// limit; `at` is the token that makes its level.
    fn limit(&mut self, total: u32, at: Span, kind: NodeKind) -> PResult<()> {
        if total <= NESTING_LIMIT {
            return Ok(());
        }
        Err(self.too_deep(at, kind))
    }

    /// E0006 at `at`, the token of a form of `kind` over the limit (spec §2.5).
    /// The note says how to split the form: an expression into a `let`, a
    /// type into a `type` alias, a block into a function. The unit is not
    /// read further: the error goes up to the recovery.
    fn too_deep(&mut self, at: Span, kind: NodeKind) -> ParseError {
        use crate::lower::Class;
        use NodeKind::*;
        let split = match (kind, crate::lower::class(kind)) {
            (Block | ForStmt | WhileStmt | LoopStmt, _) => {
                "move the inner blocks into a function and call it; a function starts again from level 0"
            }
            (TypeArgs | FnTypeParams, _) | (_, Class::Type) => "name an inner part of the type with a `type` alias",
            (StructPatField, _) | (_, Class::Pat) => "bind an inner part to a name and match that name on its own",
            _ => "bind an inner part to a name with `let`, or move it into a function",
        };
        let message =
            format!("the syntax is nested deeper than {NESTING_LIMIT} levels, counted from the declaration (§2.5)");
        let d = Diagnostic::new(Stage::Syntax, Code::E0006, at, message)
            .with_found(self.src(at).to_string())
            .with_rule(split);
        self.report(d);
        ParseError
    }

    /// The innermost open node becomes a node of `kind` at the next token: a
    /// pattern that starts with a name is an enum or struct pattern from its
    /// `(` or `{` on (spec §2.5: the level is made by the bracket after the name).
    fn reshape(&mut self, kind: NodeKind) -> PResult<()> {
        let n = self.open.len();
        let Some(top) = self.open.last().copied() else {
            onsa_diag::internal::bug(Some(self.peek().span), "the parser reshapes a node it did not open");
        };
        let base = if n >= 2 { self.open[n - 2].level } else { 0 };
        self.limit(base + Self::height(kind, top.children), self.peek().span, kind)?;
        if let Event::Start { kind: k, .. } = &mut self.events[top.event as usize] {
            *k = Some(kind);
        }
        self.open[n - 1].level = base + Self::height(kind, 0);
        Ok(())
    }

    /// Count a form written without a node of its own (`move x` as an
    /// argument or the iterated value of `for`, spec §5.2: the form `move`)
    /// at the token `at`: what `f` reads is one form of `kind` deeper.
    fn without_node(
        &mut self,
        kind: NodeKind,
        at: Span,
        f: impl FnOnce(&mut Self) -> PResult<Completed>,
    ) -> PResult<Completed> {
        let n = self.open.len();
        let saved = self.open[n - 1].level;
        self.limit(saved + Self::height(kind, 0), at, kind)?;
        self.open[n - 1].level = saved + Self::height(kind, 0);
        let inner = f(self)?;
        self.open[n - 1].level = saved;
        let top = &mut self.open[n - 1];
        top.children = top.children.max(Self::height(kind, inner.height));
        Ok(inner)
    }

    /// Close the innermost open node; its height goes to its parent.
    fn finish(&mut self, kind: Option<NodeKind>, complete: bool) -> (u32, u32) {
        let Some(top) = self.open.pop() else {
            onsa_diag::internal::bug(Some(self.peek().span), "the parser closes a node it did not open");
        };
        if let Some(kind) = kind
            && let Event::Start { kind: k, .. } = &mut self.events[top.event as usize]
        {
            *k = Some(kind);
        }
        let kind = match self.events[top.event as usize] {
            Event::Start { kind: Some(k), .. } => k,
            _ => NodeKind::Error,
        };
        let h = Self::height(kind, top.children);
        match self.open.last_mut() {
            Some(parent) => parent.children = parent.children.max(h),
            None => self.height = h,
        }
        self.events.push(Event::Finish { complete });
        (top.event, h)
    }

    /// Close the innermost open node `m` as `kind`.
    fn complete(&mut self, m: Marker, kind: NodeKind) -> Completed {
        debug_assert_eq!(self.open.last().map(|o| o.event), Some(m.event), "nodes close in order");
        let (event, height) = self.finish(Some(kind), true);
        Completed { kind, event, start: m.start, span: self.span_from(m.start), height }
    }

    /// Open a node that wraps the closed node `c` (a postfix, a chain, a
    /// cast): the left of a chain is counted too, so the first postfix that
    /// makes the chain too deep is the E0006, before the chain is read on.
    fn precede(&mut self, c: Completed, kind: NodeKind) -> PResult<Marker> {
        let m = self.enter(kind, c.start, c.height)?;
        if let Event::Start { forward_parent, .. } = &mut self.events[c.event as usize] {
            *forward_parent = Some(m.event);
        }
        Ok(m)
    }

    /// Close every node opened above `depth` as incomplete (after an error).
    fn close_open(&mut self, depth: usize) {
        while self.open.len() > depth {
            self.finish(None, false);
        }
    }

    // ------------------------------------------------------------ cursor

    fn significant(&self) -> bool {
        *self.nl.last().unwrap()
    }

    fn with_nl<T>(&mut self, significant: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        self.nl.push(significant);
        let r = f(self);
        self.nl.pop();
        r
    }

    /// Index of the next token that is not trivia under the current context.
    fn peek_index(&self) -> usize {
        let mut i = self.pos;
        loop {
            let t = self.tokens[i];
            match t.kind {
                TokenKind::Comment | TokenKind::DocComment => i += 1,
                TokenKind::Newline if !self.significant() => i += 1,
                _ => return i,
            }
        }
    }

    fn peek(&self) -> Token {
        self.tokens[self.peek_index()]
    }

    fn peek_kind(&self) -> TokenKind {
        self.peek().kind
    }

    /// What separates the next token from the token before it.
    fn peek_gap(&self) -> Gap {
        self.gap(self.peek_index())
    }

    /// What separates `tokens[i]` from the token before it in the source.
    fn gap(&self, i: usize) -> Gap {
        crate::token::gap_before(&self.all, self.full[i] as usize)
    }

    /// Index of the token after `peek()` (same skipping rules).
    fn peek2_index(&self) -> usize {
        let mut i = self.peek_index();
        if self.tokens[i].kind != TokenKind::Eof {
            i += 1;
        }
        loop {
            let t = self.tokens[i];
            match t.kind {
                TokenKind::Comment | TokenKind::DocComment => i += 1,
                TokenKind::Newline if !self.significant() => i += 1,
                _ => return i,
            }
        }
    }

    /// The token after `peek()` (same skipping rules).
    fn peek2(&self) -> Token {
        self.tokens[self.peek2_index()]
    }

    /// The next token ignoring newlines regardless of context.
    fn peek_past_newlines(&self) -> Token {
        let mut i = self.pos;
        loop {
            let t = self.tokens[i];
            match t.kind {
                TokenKind::Comment | TokenKind::DocComment | TokenKind::Newline => i += 1,
                _ => return t,
            }
        }
    }

    fn bump(&mut self) -> Token {
        let i = self.peek_index();
        let t = self.tokens[i];
        if t.kind != TokenKind::Eof {
            self.pos = i + 1;
            self.last_end = t.span.end;
            self.events.push(Event::Token(self.full[i]));
            match t.kind {
                TokenKind::LBrace => self.depth += 1,
                TokenKind::RBrace => self.depth -= 1,
                _ => {}
            }
        } else {
            self.pos = i;
        }
        t
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.peek_kind() == kind
    }

    fn eat(&mut self, kind: TokenKind) -> Option<Token> {
        if self.at(kind) { Some(self.bump()) } else { None }
    }

    fn skip_newlines(&mut self) {
        while matches!(self.peek_kind(), TokenKind::Newline) {
            self.bump();
        }
    }

    fn token_text(&self, t: Token) -> &'a str {
        &self.text[t.span.start as usize..t.span.end as usize]
    }

    fn is_ident(&self, t: Token, text: &str) -> bool {
        t.kind == TokenKind::Ident && self.token_text(t) == text
    }

    fn span_from(&self, start: u32) -> Span {
        Span::new(self.file, start, self.last_end.max(start))
    }

    fn src(&self, span: Span) -> &'a str {
        &self.text[span.start as usize..span.end as usize]
    }

    // ------------------------------------------------------------ diagnostics

    fn report(&mut self, d: Diagnostic) {
        self.diagnostics.push(d);
    }

    fn error(&mut self, code: Code, span: Span, message: impl Into<String>) -> ParseError {
        let found = self.src(span).to_string();
        let mut d = Diagnostic::new(Stage::Syntax, code, span, message);
        if !found.is_empty() && !found.contains('\n') {
            d = d.with_found(found);
        }
        self.report(d);
        ParseError
    }

    fn unexpected(&mut self, expected: &str) -> ParseError {
        let t = self.peek();
        let msg = format!("expected {expected}, found {}", t.kind.describe());
        self.error(Code::E0002, t.span, msg)
    }

    fn expect(&mut self, kind: TokenKind) -> PResult<Token> {
        if self.at(kind) { Ok(self.bump()) } else { Err(self.unexpected(kind.describe())) }
    }

    /// E0020 with one candidate that replaces `span`, and the note with the
    /// correct rule (S-114), non-fatal (§18.1). W3-15 moves these into the
    /// table of `onsa_syntax::foreign`.
    fn foreign(&mut self, span: Span, message: &str, title: &str, replace: &str, rule: &str) {
        let found = self.src(span).to_string();
        let d = Diagnostic::new(Stage::Syntax, Code::E0020, span, message)
            .with_found(found)
            .with_fix(Fix::replace(title, span, replace))
            .with_rule(rule);
        self.report(d);
    }

    /// E0408 when an integer literal does not fit any integer type (the
    /// value is read by the same function when the AST is made).
    fn check_int(&mut self, t: Token) {
        if crate::lower::int_value(self.token_text(t)).is_none() {
            self.report(Diagnostic::new(
                Stage::Syntax,
                Code::E0408,
                t.span,
                "integer literal is larger than any integer type holds",
            ));
        }
    }

    // ------------------------------------------------------------ file

    pub(crate) fn parse_file(mut self) -> ParseOutput {
        let root = self.enter_unit(NodeKind::SourceFile, 0);
        loop {
            let doc = self.collect_docs();
            if self.at(TokenKind::Eof) {
                break; // trailing doc comments without a declaration are dropped
            }
            if self.at(TokenKind::Semi) {
                let t = self.bump();
                self.foreign(
                    t.span,
                    "`;` is not used in Onsa; statements end at the newline",
                    "remove the `;`",
                    "",
                    "a statement or declaration ends at the end of its line; there is no `;` (§2.5)",
                );
                continue;
            }
            let start = self.peek().span.start;
            let depth = self.open.len();
            let m = self.start_item(doc);
            match self.parse_item(ItemCtx::Top, m) {
                Ok(item) => {
                    self.item_ranges.push(item.span);
                    self.levels.push(item.height);
                    // Terminator: newline, `;` (E0020), or end of file.
                    match self.peek_kind() {
                        TokenKind::Newline | TokenKind::Eof => {}
                        TokenKind::Semi => {
                            let t = self.bump();
                            self.foreign(
                                t.span,
                                "`;` is not used in Onsa; statements end at the newline",
                                "remove the `;`",
                                "",
                                "a statement or declaration ends at the end of its line; there is no `;` (§2.5)",
                            );
                        }
                        _ => {
                            let _ = self.unexpected("newline after the declaration");
                            self.recover(start);
                        }
                    }
                }
                Err(ParseError) => {
                    // The item node stays open: the skipped tokens go inside it.
                    self.close_open(depth + 1);
                    self.recover(start);
                    self.close_open(depth);
                }
            }
        }
        self.complete(root, NodeKind::SourceFile);
        ParseOutput {
            tokens: self.all,
            events: self.events,
            diagnostics: self.diagnostics,
            item_ranges: self.item_ranges,
            levels: self.levels,
            height: self.height,
        }
    }

    /// Skip to the next item start at the beginning of a line, outside braces
    /// (T1-7). The skipped tokens form an `Error` node. Records the skipped
    /// range for P-01 grouping.
    fn recover(&mut self, item_start: u32) {
        let mut depth = self.depth;
        let from = self.peek_index();
        let mut i = from;
        while self.tokens[i].kind != TokenKind::Eof {
            let t = self.tokens[i];
            let line_start = i == 0 || self.tokens[i - 1].kind == TokenKind::Newline;
            if i > self.pos && depth <= 0 && line_start && is_item_start(t.kind) {
                break;
            }
            match t.kind {
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace => depth -= 1,
                _ => {}
            }
            i += 1;
        }
        let first = (from..i).find(|&k| !self.tokens[k].kind.is_trivia());
        let last = (from..i).rev().find(|&k| !self.tokens[k].kind.is_trivia());
        if let (Some(first), Some(last)) = (first, last) {
            let m = self.enter_unit(NodeKind::Error, self.tokens[first].span.start);
            for k in first..=last {
                self.events.push(Event::Token(self.full[k]));
            }
            self.complete(m, NodeKind::Error);
        }
        let end = if i > 0 { self.tokens[i - 1].span.end } else { item_start };
        self.pos = i;
        self.last_end = end.max(self.last_end);
        self.depth = 0;
        self.nl.truncate(1);
        self.no_struct_lit = false;
        self.item_ranges.push(Span::new(self.file, item_start, end.max(item_start)));
    }

    // ------------------------------------------------------------ items

    /// Skip the blank lines and plain comments before an item; return the
    /// first and the last doc comment directly before it (blank lines and
    /// plain comments may come between the doc comments). This is where a
    /// doc comment is taken for the item (the `Docs` node).
    fn collect_docs(&mut self) -> Option<(usize, usize)> {
        let mut docs = None;
        loop {
            let t = self.tokens[self.pos];
            match t.kind {
                TokenKind::Newline | TokenKind::Comment => self.pos += 1,
                TokenKind::DocComment => {
                    let first = docs.map_or(self.pos, |(f, _)| f);
                    docs = Some((first, self.pos));
                    self.pos += 1;
                }
                _ => break,
            }
        }
        docs
    }

    /// Open the `Item` node; its doc comments (from `collect_docs`) are its
    /// first child, `Docs`. The trivia before them belong to the enclosing list.
    fn start_item(&mut self, docs: Option<(usize, usize)>) -> Marker {
        let start = self.peek().span.start;
        let m = self.enter_unit(NodeKind::Item, start);
        if let Some((first, last)) = docs {
            let d = self.enter_unit(NodeKind::Docs, self.tokens[first].span.start);
            for k in first..=last {
                self.events.push(Event::Token(self.full[k]));
            }
            self.complete(d, NodeKind::Docs);
        }
        m
    }

    /// The attributes before a declaration or a parameter; returns how many.
    fn parse_attrs(&mut self) -> PResult<usize> {
        let mut n = 0;
        loop {
            self.skip_newlines_if_followed_by(|k| matches!(k, TokenKind::At | TokenKind::Hash));
            if self.at(TokenKind::At) {
                self.parse_attr()?;
                n += 1;
            } else if self.at(TokenKind::Hash) && self.peek2().kind == TokenKind::LBracket {
                // `#[derive(...)]` → `@derive(...)`
                let m = self.start(NodeKind::HashAttr)?;
                let hash = self.bump();
                self.bump(); // `[`
                let inner_start = self.peek().span.start;
                self.with_nl(false, |p| p.parse_attr_body())?;
                let inner_end = self.last_end;
                self.expect(TokenKind::RBracket)?;
                let span = self.span_from(hash.span.start);
                let fix = format!("@{}", &self.text[inner_start as usize..inner_end as usize]);
                self.foreign(
                    span,
                    "attributes are written `@name(...)`",
                    "write the attribute with `@`",
                    &fix,
                    "an attribute is written `@name(...)` (§6.5)",
                );
                self.complete(m, NodeKind::HashAttr);
                n += 1;
            } else {
                break;
            }
        }
        Ok(n)
    }

    /// In a significant context, skip newlines only when the next real token satisfies `f`.
    fn skip_newlines_if_followed_by(&mut self, f: impl Fn(TokenKind) -> bool) {
        if self.at(TokenKind::Newline) && f(self.peek_past_newlines().kind) {
            self.skip_newlines();
        }
    }

    fn parse_attr(&mut self) -> PResult<()> {
        let m = self.start(NodeKind::Attr)?;
        self.expect(TokenKind::At)?;
        self.parse_attr_body()?;
        self.complete(m, NodeKind::Attr);
        Ok(())
    }

    fn parse_attr_body(&mut self) -> PResult<()> {
        self.parse_ident("attribute name")?;
        if self.at(TokenKind::LParen) && !self.peek_gap().is_some() {
            let m = self.start(NodeKind::AttrArgs)?;
            self.bump();
            self.with_nl(false, |p| {
                while !p.at(TokenKind::RParen) {
                    if p.at(TokenKind::Ident) && p.peek2().kind == TokenKind::Colon {
                        let a = p.start(NodeKind::AttrNamedArg)?;
                        p.parse_ident("key")?;
                        p.bump();
                        p.parse_expr()?;
                        p.complete(a, NodeKind::AttrNamedArg);
                    } else if p.at(TokenKind::Str) {
                        p.expect(TokenKind::Str)?;
                    } else {
                        p.parse_path("attribute argument")?;
                    }
                    if p.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                p.expect(TokenKind::RParen)
            })?;
            self.complete(m, NodeKind::AttrArgs);
        }
        Ok(())
    }

    fn parse_vis(&mut self) -> PResult<()> {
        if !self.at(TokenKind::KwPub) {
            return Ok(());
        }
        let m = self.start(NodeKind::Vis)?;
        let public = self.bump();
        if self.at(TokenKind::LParen) && !self.peek_gap().is_some() {
            self.bump();
            let t = self.peek();
            let is_crate = self.is_ident(t, "crate");
            if self.is_ident(t, "pkg") || is_crate {
                self.bump();
            } else {
                return Err(self.unexpected("`pkg`"));
            }
            let close = self.expect(TokenKind::RParen)?;
            if is_crate {
                // `pub(crate)` is visibility within the package, the default
                // (§15.1): the candidate removes it with the spaces after it.
                // (`pub(pkg)` is E0020 too, S-36: W3-08.)
                let span = Span::new(self.file, public.span.start, close.span.end);
                let at = self.all.partition_point(|x| x.span.start < close.span.end);
                let end = match self.all.get(at) {
                    Some(w) if w.kind == TokenKind::Whitespace => w.span.end,
                    _ => close.span.end,
                };
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0020,
                    span,
                    "`pub(crate)` is visibility within the package, which is the default; remove it",
                )
                .with_found(self.src(span).to_string())
                .with_fix(Fix::delete("remove the visibility", Span::new(self.file, span.start, end)))
                .with_rule("visibility is `pub` (outside the package), nothing (the package), or `priv` (§15.1)");
                self.report(d);
            }
        }
        self.complete(m, NodeKind::Vis);
        Ok(())
    }

    /// The item whose node `m` is open (doc comments, attributes, visibility, declaration).
    fn parse_item(&mut self, ctx: ItemCtx, m: Marker) -> PResult<Completed> {
        if self.parse_attrs()? > 0 {
            self.skip_newlines();
        }
        self.parse_vis()?;
        let t = self.peek();
        // `proc name` is the E0020 spelling of `flow name`: it is placed as a flow.
        let proc = t.kind == TokenKind::Ident && self.token_text(t) == "proc" && self.peek2().kind == TokenKind::Ident;
        let keyword = if proc { TokenKind::KwFlow } else { t.kind };
        if let Some((_, _, places)) = DECLARATIONS.iter().find(|(k, _, _)| *k == keyword)
            && !places.contains(&ctx)
        {
            return Err(self.not_a_member(t, ctx));
        }
        if let Some((_, parse, _)) = DECLARATIONS.iter().find(|(k, _, _)| *k == t.kind) {
            parse(self, ctx)?;
        } else if proc {
            let d = self.start(NodeKind::Flow)?;
            self.bump();
            self.foreign(
                t.span,
                "a signal-processing node is declared with `flow`",
                "write `flow`",
                "flow",
                "a stateful signal-processing node is declared with `flow` (§11)",
            );
            self.parse_flow_after_keyword(d)?;
        } else {
            return Err(self.unexpected("a declaration"));
        }
        Ok(self.complete(m, NodeKind::Item))
    }

    /// E0002 for the declaration at `t` in the list of declarations of
    /// `ctx`, where it is not a member: the members are a closed list
    /// (§18.1: methods and associated constants; the operations of an
    /// `effect`, the functions of a `handler` and of an `extern`, and the
    /// opaque types of an `extern`, §14.1). A declaration with a list of its
    /// own is never a member, so declarations do not nest without bound
    /// (they count no level, spec §2.5).
    // SPEC-GAP(S-263): the closed list of the declarations a declaration holds is not written in the spec; the conservative reading of §18.1, §8.1 and §14.1.
    fn not_a_member(&mut self, t: Token, ctx: ItemCtx) -> ParseError {
        let (owner, members) = match ctx {
            ItemCtx::Trait => ("a `trait`", "functions and `const`s"),
            ItemCtx::Impl => ("an `impl`", "functions and `const`s"),
            ItemCtx::Effect => ("an `effect`", "its operations, declared as functions"),
            ItemCtx::Handler | ItemCtx::InlineHandler => ("a handler", "functions"),
            ItemCtx::Extern => ("an `extern` block", "functions and opaque `type`s"),
            ItemCtx::Top => onsa_diag::internal::bug(Some(t.span), "a declaration of the top level is refused there"),
        };
        let word = self.token_text(t).to_string();
        let d = Diagnostic::new(
            Stage::Syntax,
            Code::E0002,
            t.span,
            format!("`{word}` cannot be declared in {owner}; declare it at the top level of the module"),
        )
        .with_found(word)
        .with_rule(format!("the members of {owner} are {members} (§18.1)"));
        self.report(d);
        ParseError
    }

    fn parse_flow(&mut self, _: ItemCtx) -> PResult<()> {
        let d = self.start(NodeKind::Flow)?;
        self.bump();
        self.parse_flow_after_keyword(d)
    }

    /// `[rt] fn name[generics](params) [-> T] [uses {..}] [body]`
    fn parse_fn(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Fn)?;
        self.eat(TokenKind::KwRt);
        self.expect(TokenKind::KwFn)?;
        self.parse_name("function name")?;
        self.parse_generics_opt()?;
        self.parse_params(true)?;
        if self.eat(TokenKind::Arrow).is_some() {
            self.parse_type()?;
        }
        self.parse_effect_row_opt()?;
        match ctx {
            ItemCtx::Effect | ItemCtx::Extern => {
                if self.at(TokenKind::LBrace) {
                    let t = self.peek();
                    return Err(self.error(Code::E0002, t.span, "this declaration is a signature and takes no body"));
                }
            }
            ItemCtx::Trait => {
                if self.at(TokenKind::LBrace) {
                    self.parse_block_expr()?;
                }
            }
            _ => {
                if !self.at(TokenKind::LBrace) {
                    return Err(self.unexpected("`{` (a function body)"));
                }
                self.parse_block_expr()?;
            }
        }
        self.complete(m, NodeKind::Fn);
        Ok(())
    }

    fn parse_flow_after_keyword(&mut self, m: Marker) -> PResult<()> {
        self.parse_name("flow name")?;
        self.parse_params(true)?;
        self.expect(TokenKind::Arrow)?;
        self.parse_type()?;
        self.parse_block_expr()?;
        self.complete(m, NodeKind::Flow);
        Ok(())
    }

    fn parse_struct(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Struct)?;
        self.expect(TokenKind::KwStruct)?;
        self.parse_name("struct name")?;
        self.parse_generics_opt()?;
        if self.at(TokenKind::LParen) {
            let b = self.start(NodeKind::TupleStructBody)?;
            self.bump();
            self.with_nl(false, |p| {
                p.parse_type()?;
                p.expect(TokenKind::RParen)?;
                Ok(())
            })?;
            self.complete(b, NodeKind::TupleStructBody);
        } else {
            let l = self.start(NodeKind::FieldList)?;
            self.expect(TokenKind::LBrace)?;
            self.with_nl(false, |p| {
                while !p.at(TokenKind::RBrace) {
                    let f = p.start(NodeKind::Field)?;
                    p.parse_vis()?;
                    p.parse_name("field name")?;
                    p.expect(TokenKind::Colon)?;
                    p.parse_type()?;
                    p.complete(f, NodeKind::Field);
                    if p.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                p.expect(TokenKind::RBrace)?;
                Ok(())
            })?;
            self.complete(l, NodeKind::FieldList);
        }
        self.complete(m, NodeKind::Struct);
        Ok(())
    }

    fn parse_enum(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Enum)?;
        self.expect(TokenKind::KwEnum)?;
        self.parse_name("enum name")?;
        self.parse_generics_opt()?;
        let l = self.start(NodeKind::VariantList)?;
        self.expect(TokenKind::LBrace)?;
        self.with_nl(false, |p| {
            while !p.at(TokenKind::RBrace) {
                let v = p.start(NodeKind::Variant)?;
                p.parse_name("variant name")?;
                if p.at(TokenKind::LParen) {
                    let f = p.start(NodeKind::VariantFields)?;
                    p.bump();
                    while !p.at(TokenKind::RParen) {
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                    p.complete(f, NodeKind::VariantFields);
                } else if p.at(TokenKind::LBrace) {
                    let t = p.peek();
                    return Err(p.error(
                        Code::E0002,
                        t.span,
                        "enum variants are tuple-like or unit; wrap named fields in a struct (§4.4)",
                    ));
                }
                p.complete(v, NodeKind::Variant);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.expect(TokenKind::RBrace)?;
            Ok(())
        })?;
        self.complete(l, NodeKind::VariantList);
        self.complete(m, NodeKind::Enum);
        Ok(())
    }

    /// `type Name = T` (alias) or `type Name` (opaque, in `extern` / `target`).
    fn parse_type_item(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::TypeAlias)?;
        self.expect(TokenKind::KwType)?;
        let name = self.parse_name("type name")?;
        if self.eat(TokenKind::Eq).is_some() {
            if ctx == ItemCtx::Extern {
                return Err(self.error(Code::E0002, name.span, "an opaque type in `extern` has no definition"));
            }
            self.parse_type()?;
            self.complete(m, NodeKind::TypeAlias);
            Ok(())
        } else if ctx == ItemCtx::Extern {
            self.complete(m, NodeKind::OpaqueType);
            Ok(())
        } else {
            Err(self.unexpected("`=` (a type alias needs a definition)"))
        }
    }

    fn parse_trait(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Trait)?;
        self.expect(TokenKind::KwTrait)?;
        self.parse_name("trait name")?;
        self.parse_generics_opt()?;
        self.parse_item_body(ItemCtx::Trait)?;
        self.complete(m, NodeKind::Trait);
        Ok(())
    }

    fn parse_impl(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Impl)?;
        self.expect(TokenKind::KwImpl)?;
        self.parse_generics_opt()?;
        let (first, args) = self.parse_type_ex()?;
        if self.eat(TokenKind::KwFor).is_some() {
            if !(first.kind == NodeKind::PathType && args == 0) {
                return Err(self.error(Code::E0002, first.span, "expected a trait name before `for`"));
            }
            self.parse_type()?;
        }
        self.parse_item_body(ItemCtx::Impl)?;
        self.complete(m, NodeKind::Impl);
        Ok(())
    }

    fn parse_effect(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Effect)?;
        self.eat(TokenKind::KwBlocking);
        self.expect(TokenKind::KwEffect)?;
        self.parse_name("effect name")?;
        self.parse_item_body(ItemCtx::Effect)?;
        self.complete(m, NodeKind::Effect);
        Ok(())
    }

    fn parse_handler(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Handler)?;
        self.expect(TokenKind::KwHandler)?;
        self.parse_name("handler name")?;
        if self.at(TokenKind::LParen) {
            self.parse_params(true)?;
        }
        self.expect(TokenKind::Colon)?;
        self.parse_path("effect name")?;
        self.parse_item_body(ItemCtx::Handler)?;
        self.complete(m, NodeKind::Handler);
        Ok(())
    }

    fn parse_const(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Const)?;
        self.expect(TokenKind::KwConst)?;
        self.parse_name("constant name")?;
        self.expect(TokenKind::Colon)?;
        self.parse_type()?;
        if self.eat(TokenKind::Eq).is_some() {
            self.skip_newlines();
            self.parse_expr()?;
        } else if ctx != ItemCtx::Trait {
            return Err(self.unexpected("`=` (a constant needs a value)"));
        }
        self.complete(m, NodeKind::Const);
        Ok(())
    }

    fn parse_use(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Use)?;
        self.expect(TokenKind::KwUse)?;
        let tree = self.start(NodeKind::UseTree)?;
        self.parse_ident("module path")?;
        loop {
            if self.at(TokenKind::ColonColon) {
                let t = self.bump();
                self.foreign(
                    t.span,
                    "paths are separated with `.`",
                    "write `.`",
                    ".",
                    "the separator of a path is `.` (`F32.PI`, `std.math`, §15.1)",
                );
            } else if self.eat(TokenKind::Dot).is_none() {
                break;
            }
            if self.at(TokenKind::LBrace) {
                let n = self.start(NodeKind::UseNames)?;
                self.bump();
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RBrace) {
                        p.parse_ident("imported name")?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RBrace)?;
                    Ok(())
                })?;
                self.complete(n, NodeKind::UseNames);
                break;
            }
            if self.at(TokenKind::Star) {
                let t = self.peek();
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "there is no glob import; list the names in `{ }` (§15.1)",
                ));
            }
            self.parse_name_after_dot("module path")?;
        }
        self.complete(tree, NodeKind::UseTree);
        self.complete(m, NodeKind::Use);
        Ok(())
    }

    fn parse_extern(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Extern)?;
        self.expect(TokenKind::KwExtern)?;
        self.expect(TokenKind::Str)?;
        let t = self.peek();
        if !self.is_ident(t, "lib") {
            return Err(self.unexpected("`lib`"));
        }
        self.bump();
        self.expect(TokenKind::Str)?;
        self.parse_item_body(ItemCtx::Extern)?;
        self.complete(m, NodeKind::Extern);
        Ok(())
    }

    fn parse_target(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Target)?;
        self.expect(TokenKind::KwTarget)?;
        match self.peek_kind() {
            TokenKind::KwType => {
                let o = self.start(NodeKind::OpaqueType)?;
                self.bump();
                self.parse_name("type name")?;
                self.complete(o, NodeKind::OpaqueType);
            }
            TokenKind::KwFn | TokenKind::KwRt => self.parse_fn(ItemCtx::Extern)?,
            _ => return Err(self.unexpected("`fn` or `type` after `target`")),
        }
        self.complete(m, NodeKind::Target);
        Ok(())
    }

    fn parse_test(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Test)?;
        self.expect(TokenKind::KwTest)?;
        self.expect(TokenKind::Str)?;
        self.parse_block_expr()?;
        self.complete(m, NodeKind::Test);
        Ok(())
    }

    /// `{ item NL item NL ... }` for trait / impl / effect / handler / extern bodies.
    fn parse_item_body(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::ItemList)?;
        self.expect(TokenKind::LBrace)?;
        self.with_nl(true, |p| {
            loop {
                let doc = p.collect_docs();
                if p.at(TokenKind::RBrace) {
                    break;
                }
                if p.at(TokenKind::Eof) {
                    return Err(p.unexpected("`}`"));
                }
                let item = p.start_item(doc);
                p.parse_item(ctx, item)?;
                match p.peek_kind() {
                    TokenKind::Newline | TokenKind::RBrace => {}
                    TokenKind::Semi => {
                        let t = p.bump();
                        p.foreign(
                            t.span,
                            "`;` is not used in Onsa; declarations end at the newline",
                            "remove the `;`",
                            "",
                            "a statement or declaration ends at the end of its line; there is no `;` (§2.5)",
                        );
                    }
                    _ => return Err(p.unexpected("newline or `}`")),
                }
            }
            p.expect(TokenKind::RBrace)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::ItemList);
        Ok(())
    }

    // ------------------------------------------------------------ signatures

    /// The name a declaration introduces, in a `Name` node.
    fn parse_name(&mut self, what: &str) -> PResult<Token> {
        let m = self.start(NodeKind::Name)?;
        let t = self.parse_ident(what)?;
        self.complete(m, NodeKind::Name);
        Ok(t)
    }

    fn parse_ident(&mut self, what: &str) -> PResult<Token> {
        let t = self.peek();
        if t.kind == TokenKind::Ident {
            self.bump();
            Ok(t)
        } else {
            Err(self.unexpected(what))
        }
    }

    /// `a.b.c` (also accepts `Self` as a segment). `::` is E0020.
    fn parse_path(&mut self, what: &str) -> PResult<PathInfo> {
        let m = self.start(NodeKind::Path)?;
        let first = self.parse_path_segment(what)?;
        let mut last = first;
        let mut segments = 1;
        loop {
            if self.at(TokenKind::ColonColon) {
                let t = self.bump();
                self.foreign(
                    t.span,
                    "paths are separated with `.`",
                    "write `.`",
                    ".",
                    "the separator of a path is `.` (`F32.PI`, `std.math`, §15.1)",
                );
            } else if self.at(TokenKind::Dot)
                && (self.peek2().kind == TokenKind::Ident || self.peek2().kind.is_keyword())
            {
                self.bump();
            } else {
                break;
            }
            last = self.parse_name_after_dot(what)?;
            segments += 1;
        }
        self.complete(m, NodeKind::Path);
        Ok(PathInfo { segments, first, last })
    }

    /// After `.`, a keyword is an ordinary name (`std.test`, `x.type`).
    fn parse_name_after_dot(&mut self, what: &str) -> PResult<Token> {
        let t = self.peek();
        if t.kind == TokenKind::Ident || t.kind.is_keyword() {
            self.bump();
            Ok(t)
        } else {
            Err(self.unexpected(what))
        }
    }

    fn parse_path_segment(&mut self, what: &str) -> PResult<Token> {
        let t = self.peek();
        match t.kind {
            TokenKind::Ident | TokenKind::KwSelfType => {
                self.bump();
                Ok(t)
            }
            _ => Err(self.unexpected(what)),
        }
    }

    fn parse_generics_opt(&mut self) -> PResult<()> {
        if self.at(TokenKind::Lt) && !self.peek_gap().is_some() {
            // `fn f<T>` → `[T]`
            let m = self.start(NodeKind::GenericParams)?;
            let lt = self.bump();
            self.with_nl(false, |p| p.parse_generic_list(TokenKind::Gt))?;
            let span = self.span_from(lt.span.start);
            let inner = &self.text[lt.span.end as usize..self.last_end as usize - 1];
            let fix = format!("[{inner}]");
            self.foreign(
                span,
                "generic parameters are written in `[ ]`",
                "write the type parameters in `[ ]`",
                &fix,
                "type parameters and type arguments are written in `[ ]` (§4.5)",
            );
            self.complete(m, NodeKind::GenericParams);
            return Ok(());
        }
        if !self.at(TokenKind::LBracket) || self.peek_gap().is_some() {
            return Ok(());
        }
        let m = self.start(NodeKind::GenericParams)?;
        self.bump();
        self.with_nl(false, |p| p.parse_generic_list(TokenKind::RBracket))?;
        self.complete(m, NodeKind::GenericParams);
        Ok(())
    }

    fn parse_generic_list(&mut self, close: TokenKind) -> PResult<()> {
        while !self.at(close) {
            let m = self.start(NodeKind::TypeParam)?;
            if self.eat(TokenKind::KwConst).is_some() {
                self.parse_name("const parameter name")?;
                self.expect(TokenKind::Colon)?;
                self.parse_type()?;
                self.complete(m, NodeKind::ConstParam);
            } else {
                let name = self.parse_name("type parameter")?;
                if self.token_text(name).starts_with(|c: char| c.is_ascii_lowercase()) {
                    self.complete(m, NodeKind::EffectParam);
                } else {
                    if self.eat(TokenKind::Colon).is_some() {
                        loop {
                            let b = self.start(NodeKind::Bound)?;
                            self.eat(TokenKind::Question);
                            self.parse_path("trait bound")?;
                            self.complete(b, NodeKind::Bound);
                            if self.eat(TokenKind::Plus).is_none() {
                                break;
                            }
                        }
                    }
                    self.complete(m, NodeKind::TypeParam);
                }
            }
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(close)?;
        Ok(())
    }

    /// `(params)`; `require_types` is false for anonymous functions (§6.1).
    fn parse_params(&mut self, require_types: bool) -> PResult<()> {
        let m = self.start(NodeKind::ParamList)?;
        self.expect(TokenKind::LParen)?;
        self.with_nl(false, |p| {
            while !p.at(TokenKind::RParen) {
                let param = p.start(NodeKind::Param)?;
                p.parse_attrs()?;
                p.parse_mode();
                let t = p.peek();
                // `mut self` → `inout self`
                if p.is_ident(t, "mut") && p.peek2().kind == TokenKind::KwSelf {
                    p.bump();
                    let span = p.span_from(t.span.start).to(p.peek().span);
                    p.foreign(
                        span,
                        "a receiver that changes is written `inout self`",
                        "write `inout self`",
                        "inout self",
                        "the mode comes before the name; a receiver that changes is `inout self` (§5.2)",
                    );
                }
                let t = p.peek();
                let is_self = match t.kind {
                    TokenKind::KwSelf | TokenKind::Underscore => {
                        let n = p.start(NodeKind::Name)?;
                        p.bump();
                        p.complete(n, NodeKind::Name);
                        t.kind == TokenKind::KwSelf
                    }
                    TokenKind::Ident => {
                        p.parse_name("parameter name")?;
                        false
                    }
                    TokenKind::Amp => return Err(p.borrow_param_error()),
                    _ => return Err(p.unexpected("a parameter name")),
                };
                if p.eat(TokenKind::Colon).is_some() {
                    p.parse_type()?;
                } else if require_types && !is_self {
                    return Err(p.unexpected("`:` (parameter types are always written, P1)"));
                }
                p.complete(param, NodeKind::Param);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.expect(TokenKind::RParen)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::ParamList);
        Ok(())
    }

    /// `&mut x` / `&x` from Rust (E0020): the mode goes before the name (§5.2).
    fn borrow_param_error(&mut self) -> ParseError {
        let t = self.peek();
        let is_mut = self.tokens.get(self.peek_index() + 1).is_some_and(|n| {
            n.kind == TokenKind::Ident && &self.text[n.span.start as usize..n.span.end as usize] == "mut"
        });
        let (span, msg) = if is_mut {
            let end = self.tokens[self.peek_index() + 1].span.end;
            (
                Span::new(t.span.file, t.span.start, end),
                "`&mut T` is written as `inout name: T`; the mode comes before the name (§5.2)",
            )
        } else {
            (t.span, "`&T` is the default borrow; write `name: T` (§5.2)")
        };
        let found = self.text[span.start as usize..span.end as usize].to_string();
        let d = Diagnostic::new(Stage::Syntax, Code::E0020, span, msg)
            .with_found(found)
            .with_fix(Fix::delete("remove the reference mark", span))
            .with_rule("there are no references; an argument is borrowed by default and changed with `inout` before the name (§5.2)");
        self.diagnostics.push(d);
        ParseError
    }

    fn parse_mode(&mut self) {
        if self.eat(TokenKind::KwInout).is_none() {
            self.eat(TokenKind::KwMove);
        }
    }

    fn parse_effect_row_opt(&mut self) -> PResult<()> {
        if self.eat(TokenKind::KwUses).is_none() {
            return Ok(());
        }
        let m = self.start(NodeKind::EffectRow)?;
        self.expect(TokenKind::LBrace)?;
        self.with_nl(false, |p| {
            while !p.at(TokenKind::RBrace) {
                p.parse_path("effect name")?;
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.expect(TokenKind::RBrace)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::EffectRow);
        Ok(())
    }

    // ------------------------------------------------------------ types

    fn parse_type(&mut self) -> PResult<Completed> {
        Ok(self.parse_type_ex()?.0)
    }

    /// A type, and the number of its type arguments when it is a path type.
    fn parse_type_ex(&mut self) -> PResult<(Completed, usize)> {
        let mut nargs = 0;
        let c = match self.peek_kind() {
            TokenKind::LParen => {
                let m = self.start(NodeKind::TupleType)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    if p.eat(TokenKind::RParen).is_some() {
                        return Ok(NodeKind::UnitType);
                    }
                    let first = p.parse_type()?;
                    if p.eat(TokenKind::Comma).is_none() {
                        p.expect(TokenKind::RParen)?;
                        return Err(p.error(
                            Code::E0002,
                            first.span,
                            "a parenthesized type is not a tuple; tuples have two or more elements",
                        ));
                    }
                    while !p.at(TokenKind::RParen) {
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                    Ok(NodeKind::TupleType)
                })?;
                self.complete(m, kind)
            }
            TokenKind::LBracket => {
                let m = self.start(NodeKind::ArrayType)?;
                self.bump();
                self.with_nl(false, |p| {
                    p.parse_type()?;
                    p.expect(TokenKind::Semi)?;
                    p.parse_expr()?;
                    p.expect(TokenKind::RBracket)?;
                    Ok(())
                })?;
                self.complete(m, NodeKind::ArrayType)
            }
            TokenKind::KwRt | TokenKind::KwFn => {
                let m = self.start(NodeKind::FnType)?;
                self.eat(TokenKind::KwRt);
                self.expect(TokenKind::KwFn)?;
                let l = self.start(NodeKind::FnTypeParams)?;
                self.expect(TokenKind::LParen)?;
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RParen) {
                        p.parse_mode();
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                    Ok(())
                })?;
                self.complete(l, NodeKind::FnTypeParams);
                if self.eat(TokenKind::Arrow).is_some() {
                    self.parse_type()?;
                }
                self.parse_effect_row_opt()?;
                self.complete(m, NodeKind::FnType)
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let m = self.start(NodeKind::PathType)?;
                let path = self.parse_path("a type")?;
                if path.segments == 1 {
                    let name = self.token_text(path.first);
                    if let Some((_, fix)) = BUILTIN_TYPE_FIXES.iter().find(|(from, _)| *from == name) {
                        self.foreign(
                            path.first.span,
                            "built-in types are written in UpperCamel (`I32`, `F32`, `Bool`)",
                            "write the built-in type name",
                            fix,
                            "type names are UpperCamel, the built-in ones too (`I32`, `F32`, `Bool`, §2.3)",
                        );
                    }
                }
                if self.at(TokenKind::LBracket) && !self.peek_gap().is_some() {
                    let a = self.start(NodeKind::TypeArgs)?;
                    self.bump();
                    nargs = self.with_nl(false, |p| p.parse_type_args(TokenKind::RBracket))?;
                    self.complete(a, NodeKind::TypeArgs);
                } else if self.at(TokenKind::Lt) && !self.peek_gap().is_some() {
                    let a = self.start(NodeKind::TypeArgs)?;
                    let lt = self.bump();
                    nargs = self.with_nl(false, |p| p.parse_type_args(TokenKind::Gt))?;
                    let span = self.span_from(lt.span.start);
                    let inner = &self.text[lt.span.end as usize..self.last_end as usize - 1];
                    let fix = format!("[{inner}]");
                    self.foreign(
                        span,
                        "type arguments are written in `[ ]`",
                        "write the type arguments in `[ ]`",
                        &fix,
                        "type parameters and type arguments are written in `[ ]` (§4.5)",
                    );
                    self.complete(a, NodeKind::TypeArgs);
                }
                self.complete(m, NodeKind::PathType)
            }
            TokenKind::Amp => return Err(self.borrow_param_error()),
            _ => return Err(self.unexpected("a type")),
        };
        Ok((c, nargs))
    }

    fn parse_type_args(&mut self, close: TokenKind) -> PResult<usize> {
        let mut n = 0;
        while !self.at(close) {
            self.parse_type_arg()?;
            n += 1;
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(close)?;
        Ok(n)
    }

    /// A type argument: a type, or a const argument written as an integer
    /// literal, optionally negated (`Ring[F32, 4]`, S-24 / spec §4.5).
    fn parse_type_arg(&mut self) -> PResult<()> {
        if !matches!(self.peek_kind(), TokenKind::Int | TokenKind::Minus) {
            self.parse_type()?;
            return Ok(());
        }
        let m = self.start(NodeKind::ConstArg)?;
        self.eat(TokenKind::Minus);
        let tok = self.expect(TokenKind::Int)?;
        self.check_int(tok);
        self.complete(m, NodeKind::ConstArg);
        Ok(())
    }

    // ------------------------------------------------------------ blocks and statements

    /// `{ stmts }` as an expression (newlines significant inside).
    fn parse_block_expr(&mut self) -> PResult<Completed> {
        let m = self.start(NodeKind::Block)?;
        self.expect(TokenKind::LBrace)?;
        let saved = std::mem::replace(&mut self.no_struct_lit, false);
        let block = self.with_nl(true, |p| p.parse_block_body());
        self.no_struct_lit = saved;
        block?;
        Ok(self.complete(m, NodeKind::Block))
    }

    fn parse_block_body(&mut self) -> PResult<()> {
        loop {
            self.skip_newlines();
            if self.at(TokenKind::RBrace) {
                break;
            }
            if self.at(TokenKind::Eof) {
                return Err(self.unexpected("`}`"));
            }
            self.parse_stmt()?;
            match self.peek_kind() {
                TokenKind::Newline | TokenKind::RBrace => {}
                TokenKind::Semi => {
                    let t = self.bump();
                    self.foreign(
                        t.span,
                        "`;` is not used in Onsa; statements end at the newline",
                        "remove the `;`",
                        "",
                        "a statement or declaration ends at the end of its line; there is no `;` (§2.5)",
                    );
                }
                TokenKind::DotDot | TokenKind::DotDotEq => {
                    let t = self.peek();
                    return Err(self.error(
                        Code::E0002,
                        t.span,
                        "ranges are only allowed in `for` and `par` heads (§7)",
                    ));
                }
                _ => return Err(self.unexpected("newline or `}`")),
            }
        }
        self.expect(TokenKind::RBrace)?;
        Ok(())
    }

    fn parse_stmt(&mut self) -> PResult<Completed> {
        let t = self.peek();
        match t.kind {
            TokenKind::KwLet => {
                let m = self.start(NodeKind::LetStmt)?;
                self.bump();
                let mt = self.peek();
                if self.is_ident(mt, "mut") {
                    self.bump();
                    let span = t.span.to(mt.span);
                    self.foreign(
                        span,
                        "a mutable local is declared with `var`",
                        "write `var`",
                        "var",
                        "`let` binds a value that does not change; a local that changes is declared with `var` (§5.1)",
                    );
                    return self.parse_var_rest(m);
                }
                self.parse_pattern()?;
                if self.eat(TokenKind::Colon).is_some() {
                    self.parse_type()?;
                }
                self.expect(TokenKind::Eq)?;
                self.skip_newlines();
                self.parse_consumed()?;
                Ok(self.complete(m, NodeKind::LetStmt))
            }
            TokenKind::KwVar => {
                let m = self.start(NodeKind::VarStmt)?;
                self.bump();
                self.parse_var_rest(m)
            }
            TokenKind::KwFor => {
                let m = self.start(NodeKind::ForStmt)?;
                self.bump();
                self.parse_pattern()?;
                self.expect(TokenKind::KwIn)?;
                if self.at(TokenKind::KwMove) {
                    // `for s in move xs`: `move xs` is the form `move` (§5.2).
                    let mv = self.bump();
                    self.without_node(NodeKind::MoveExpr, mv.span, |p| p.parse_head_expr(true))?;
                } else {
                    self.parse_head_expr(true)?;
                }
                self.parse_block_expr()?;
                Ok(self.complete(m, NodeKind::ForStmt))
            }
            TokenKind::KwWhile => {
                let m = self.start(NodeKind::WhileStmt)?;
                self.bump();
                self.parse_head_expr(false)?;
                self.parse_block_expr()?;
                Ok(self.complete(m, NodeKind::WhileStmt))
            }
            TokenKind::Ident if self.token_text(t) == "loop" && self.peek2().kind == TokenKind::LBrace => {
                let m = self.start(NodeKind::LoopStmt)?;
                self.bump();
                self.foreign(
                    t.span,
                    "there is no `loop`; write `while true`",
                    "write `while true`",
                    "while true",
                    "the loops are `while` and `for`; an endless loop is `while true` (§7)",
                );
                self.parse_block_expr()?;
                Ok(self.complete(m, NodeKind::LoopStmt))
            }
            TokenKind::KwBreak => {
                let m = self.start(NodeKind::BreakStmt)?;
                self.bump();
                Ok(self.complete(m, NodeKind::BreakStmt))
            }
            TokenKind::KwContinue => {
                let m = self.start(NodeKind::ContinueStmt)?;
                self.bump();
                Ok(self.complete(m, NodeKind::ContinueStmt))
            }
            TokenKind::KwReturn => {
                let m = self.start(NodeKind::ReturnStmt)?;
                self.bump();
                if !matches!(
                    self.peek_kind(),
                    TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof | TokenKind::Semi
                ) {
                    self.parse_expr()?;
                }
                Ok(self.complete(m, NodeKind::ReturnStmt))
            }
            TokenKind::KwAssert => {
                let m = self.start(NodeKind::AssertStmt)?;
                self.bump();
                self.parse_expr()?;
                Ok(self.complete(m, NodeKind::AssertStmt))
            }
            _ => {
                let expr = self.parse_expr()?;
                if self.at(TokenKind::Eq) {
                    let m = self.precede(expr, NodeKind::AssignStmt)?;
                    self.bump();
                    self.skip_newlines();
                    self.parse_consumed()?;
                    return Ok(self.complete(m, NodeKind::AssignStmt));
                }
                let m = self.precede(expr, NodeKind::ExprStmt)?;
                Ok(self.complete(m, NodeKind::ExprStmt))
            }
        }
    }

    fn parse_var_rest(&mut self, m: Marker) -> PResult<Completed> {
        self.parse_name("variable name")?;
        if self.eat(TokenKind::Colon).is_some() {
            self.parse_type()?;
        }
        self.expect(TokenKind::Eq)?;
        self.skip_newlines();
        self.parse_consumed()?;
        Ok(self.complete(m, NodeKind::VarStmt))
    }

    /// An expression in a consuming position (§5.2, S-21): `move <place>` or a
    /// plain expression. The `move` operand is a postfix expression (a place).
    fn parse_consumed(&mut self) -> PResult<Completed> {
        if !self.at(TokenKind::KwMove) {
            return self.parse_expr();
        }
        let m = self.start(NodeKind::MoveExpr)?;
        self.bump();
        self.parse_postfix()?;
        Ok(self.complete(m, NodeKind::MoveExpr))
    }

    /// Head expression of `if` / `while` / `match` / `for` / `par`: no struct
    /// literal (S-08); ranges allowed only when `allow_range`.
    fn parse_head_expr(&mut self, allow_range: bool) -> PResult<Completed> {
        let saved = std::mem::replace(&mut self.no_struct_lit, true);
        let r = self.parse_expr_inner(allow_range);
        self.no_struct_lit = saved;
        r
    }

    // ------------------------------------------------------------ expressions

    fn parse_expr(&mut self) -> PResult<Completed> {
        self.parse_expr_inner(false)
    }

    /// Binary chain, kept flat (§3.1; groups are checked in `groups.rs`).
    /// Its height is the one of the tree of §3.1 ([`Chain`]).
    fn parse_expr_inner(&mut self, allow_range: bool) -> PResult<Completed> {
        let first = self.parse_cast()?;
        let mut expr = first;
        if binop(self.peek_kind()) {
            let m = self.precede(first, NodeKind::BinaryExpr)?;
            let base = self.level();
            let mut chain = Chain::new(first.height);
            while let Some(op) = crate::lower::binop(self.peek_kind()) {
                let (pending, left) = chain.operator(op.group());
                self.chain_operator(base, pending, left)?;
                self.bump();
                self.skip_newlines(); // operator at the end of the line continues it (§2.5)
                let right = self.parse_cast()?;
                chain.operand(right.height);
            }
            let top = self.open.len() - 1;
            self.open[top].children = chain.height();
            self.open[top].level = base;
            expr = self.complete(m, NodeKind::BinaryExpr);
        }
        if matches!(self.peek_kind(), TokenKind::DotDot | TokenKind::DotDotEq) {
            let t = self.peek();
            if !allow_range {
                return Err(self.error(Code::E0002, t.span, "ranges are only allowed in `for` and `par` heads (§7)"));
            }
            let m = self.precede(expr, NodeKind::RangeExpr)?;
            self.bump();
            if t.kind == TokenKind::DotDotEq {
                // No candidate keeps the value (`a..b + 1` panics at the top of
                // the type), so E0002 with the note (§18.1, S-48; it was an E0020
                // without a candidate). W3-15 moves it into the table (D10).
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0002,
                    t.span,
                    "there is no inclusive range; use `..` with an adjusted end",
                )
                .with_found("..=")
                .with_rule("a range `a..b` excludes `b`; there is no inclusive range (§7)");
                self.report(d);
            }
            self.parse_expr_inner(false)?;
            return Ok(self.complete(m, NodeKind::RangeExpr));
        }
        Ok(expr)
    }

    /// The next operator of a chain whose node is at the level `base`: in the
    /// tree of §3.1 it is under `pending - 1` operators that wait for their
    /// right operand, and its left operand is `left` high (one level per
    /// operator, [`Chain`]). E0006 at the operator when that is over the limit,
    /// before the chain is read on (spec §2.5); else its right operand is read
    /// at its level.
    fn chain_operator(&mut self, base: u32, pending: u32, left: u32) -> PResult<()> {
        let at = self.peek().span;
        self.limit(base + pending + left, at, NodeKind::BinaryExpr)?;
        let top = self.open.len() - 1;
        self.open[top].level = base + pending;
        Ok(())
    }

    /// `prefix [as Type]*` — prefix binds tighter than `as` (§3.1).
    fn parse_cast(&mut self) -> PResult<Completed> {
        let mut expr = self.parse_prefix()?;
        while self.at(TokenKind::KwAs) {
            let m = self.precede(expr, NodeKind::CastExpr)?;
            self.bump();
            self.parse_type()?;
            expr = self.complete(m, NodeKind::CastExpr);
        }
        Ok(expr)
    }

    fn parse_prefix(&mut self) -> PResult<Completed> {
        let t = self.peek();
        if matches!(t.kind, TokenKind::Minus | TokenKind::Bang) {
            let m = self.start(NodeKind::PrefixExpr)?;
            self.bump();
            self.parse_prefix()?;
            return Ok(self.complete(m, NodeKind::PrefixExpr));
        }
        if t.kind == TokenKind::Amp {
            // `&mut x` / `&x` in argument position → `inout x` / `x`. The AST
            // has no node for it: the `RefExpr` node gives the inner expression.
            let m = self.start(NodeKind::RefExpr)?;
            self.bump();
            let mt = self.peek();
            let is_mut = self.is_ident(mt, "mut");
            if is_mut {
                self.bump();
            }
            let inner = self.parse_prefix()?;
            let span = self.span_from(t.span.start);
            let inner_src = self.src(inner.span);
            let fix = if is_mut { format!("inout {inner_src}") } else { inner_src.to_string() };
            self.foreign(
                span,
                "there are no references; arguments are borrowed by default and changed with `inout`",
                "write the argument without `&`",
                &fix,
                "there are no references; an argument is borrowed by default and changed with `inout` (§5.2)",
            );
            let c = self.complete(m, NodeKind::RefExpr);
            return Ok(Completed { span: inner.span, ..c });
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> PResult<Completed> {
        let first = self.peek();
        let mut expr = self.parse_primary()?;
        // The last name of a chain `a.b.C` of names (a struct literal path, S-08).
        let mut chain: Option<Token> = (expr.kind == NodeKind::PathExpr).then_some(first);
        loop {
            // `.` on the next line continues the expression (§2.5).
            if self.at(TokenKind::Newline) && self.peek_past_newlines().kind == TokenKind::Dot {
                self.skip_newlines();
            }
            let t = self.peek();
            match t.kind {
                TokenKind::LParen => {
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
                }
                TokenKind::Tilde | TokenKind::Bang
                    if !self.peek_gap().is_some()
                        && self.peek2().kind == TokenKind::LParen
                        && !self.gap(self.peek2_index()).is_some()
                        && matches!(expr.kind, NodeKind::PathExpr | NodeKind::FieldExpr) =>
                {
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.bump();
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
                }
                TokenKind::Tilde => {
                    return Err(self.error(
                        Code::E0002,
                        t.span,
                        "`~` is only the flow-call mark `name~(args)`, written without spaces (§2.6)",
                    ));
                }
                TokenKind::ColonColon => {
                    let m = self.precede(expr, NodeKind::FieldExpr)?;
                    self.bump();
                    self.foreign(
                        t.span,
                        "paths are separated with `.`",
                        "write `.`",
                        ".",
                        "the separator of a path is `.` (`F32.PI`, `std.math`, §15.1)",
                    );
                    let name = self.parse_ident("a name after `::`")?;
                    expr = self.complete(m, NodeKind::FieldExpr);
                    chain = chain.map(|_| name);
                }
                TokenKind::Dot => {
                    let m = self.precede(expr, NodeKind::FieldExpr)?;
                    self.bump();
                    let n = self.peek();
                    match n.kind {
                        k if k == TokenKind::Ident || k.is_keyword() => {
                            let name = self.parse_name_after_dot("a field name")?;
                            expr = self.complete(m, NodeKind::FieldExpr);
                            chain = chain.map(|_| name);
                        }
                        TokenKind::Int => {
                            self.bump();
                            if crate::lower::tuple_index_value(self.token_text(n)).is_none() {
                                return Err(self.error(Code::E0408, n.span, "tuple index is too large"));
                            }
                            expr = self.complete(m, NodeKind::TupleIndexExpr);
                            chain = None;
                        }
                        _ => return Err(self.unexpected("a field name or tuple index after `.`")),
                    }
                }
                TokenKind::LBracket if !self.peek_gap().is_some() => {
                    let m = self.precede(expr, NodeKind::IndexExpr)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        p.parse_expr()?;
                        p.expect(TokenKind::RBracket)?;
                        Ok(())
                    })?;
                    expr = self.complete(m, NodeKind::IndexExpr);
                    chain = None;
                }
                TokenKind::Question => {
                    let m = self.precede(expr, NodeKind::TryExpr)?;
                    self.bump();
                    expr = self.complete(m, NodeKind::TryExpr);
                    chain = None;
                }
                TokenKind::LBrace
                    if !self.no_struct_lit
                        && chain.is_some_and(|c| self.token_text(c).starts_with(|c: char| c.is_ascii_uppercase())) =>
                {
                    let m = self.precede(expr, NodeKind::StructLit)?;
                    let l = self.start(NodeKind::StructLitFields)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RBrace) {
                            let f = p.start(NodeKind::StructLitField)?;
                            p.parse_ident("field name")?;
                            p.expect(TokenKind::Colon)?;
                            p.parse_consumed()?;
                            p.complete(f, NodeKind::StructLitField);
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.expect(TokenKind::RBrace)?;
                        Ok(())
                    })?;
                    self.complete(l, NodeKind::StructLitFields);
                    expr = self.complete(m, NodeKind::StructLit);
                    chain = None;
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    /// `( args )`.
    fn parse_arg_list(&mut self) -> PResult<()> {
        let m = self.start(NodeKind::ArgList)?;
        self.bump(); // `(`
        self.with_nl(false, |p| {
            let saved = std::mem::replace(&mut p.no_struct_lit, false);
            while !p.at(TokenKind::RParen) {
                let a = p.start(NodeKind::Arg)?;
                if p.at(TokenKind::KwMove) {
                    // `f(move x)`: `move x` is the form `move` (§5.2).
                    let mv = p.bump();
                    p.without_node(NodeKind::MoveExpr, mv.span, |p| p.parse_expr())?;
                } else {
                    p.parse_mode();
                    p.parse_expr()?;
                }
                p.complete(a, NodeKind::Arg);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.no_struct_lit = saved;
            p.expect(TokenKind::RParen)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::ArgList);
        Ok(())
    }

    fn parse_primary(&mut self) -> PResult<Completed> {
        let t = self.peek();
        let kind = match t.kind {
            TokenKind::KwMove => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "`move` is written only where a value is consumed: let/var initializers, assignment, literal elements, `match move x`, and call arguments (§5.2)",
                ));
            }
            TokenKind::KwRt => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "an anonymous function cannot be `rt`; its `rt` comes from the expected type",
                ));
            }
            TokenKind::Int => {
                let m = self.start(NodeKind::Literal)?;
                self.bump();
                self.check_int(t);
                return Ok(self.complete(m, NodeKind::Literal));
            }
            TokenKind::Float | TokenKind::Char | TokenKind::Str | TokenKind::KwTrue | TokenKind::KwFalse => {
                NodeKind::Literal
            }
            TokenKind::Underscore => NodeKind::HoleExpr,
            TokenKind::Ident | TokenKind::KwSelf | TokenKind::KwSelfType => NodeKind::PathExpr,
            TokenKind::LParen => {
                let m = self.start(NodeKind::TupleExpr)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    let saved = std::mem::replace(&mut p.no_struct_lit, false);
                    let r = p.parse_paren_rest();
                    p.no_struct_lit = saved;
                    r
                })?;
                return Ok(self.complete(m, kind));
            }
            TokenKind::LBracket => {
                let m = self.start(NodeKind::ArrayExpr)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    let saved = std::mem::replace(&mut p.no_struct_lit, false);
                    let r = p.parse_array_rest();
                    p.no_struct_lit = saved;
                    r
                })?;
                return Ok(self.complete(m, kind));
            }
            TokenKind::LBrace => return self.parse_block_expr(),
            TokenKind::KwIf => return self.parse_if(),
            TokenKind::KwMatch => {
                let m = self.start(NodeKind::MatchExpr)?;
                self.bump();
                if self.at(TokenKind::KwMove) {
                    // `match move x` consumes the value (§7, S-21).
                    let mv = self.start(NodeKind::MoveExpr)?;
                    self.bump();
                    let saved = std::mem::replace(&mut self.no_struct_lit, true);
                    let inner = self.parse_postfix();
                    self.no_struct_lit = saved;
                    inner?;
                    self.complete(mv, NodeKind::MoveExpr);
                } else {
                    self.parse_head_expr(false)?;
                }
                let arms = self.start(NodeKind::MatchArms)?;
                self.expect(TokenKind::LBrace)?;
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RBrace) {
                        let a = p.start(NodeKind::MatchArm)?;
                        p.parse_pattern()?;
                        if p.eat(TokenKind::KwIf).is_some() {
                            p.parse_expr()?;
                        }
                        p.expect(TokenKind::FatArrow)?;
                        p.parse_expr()?;
                        p.complete(a, NodeKind::MatchArm);
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RBrace)?;
                    Ok(())
                })?;
                self.complete(arms, NodeKind::MatchArms);
                return Ok(self.complete(m, NodeKind::MatchExpr));
            }
            TokenKind::KwFn => {
                let m = self.start(NodeKind::ClosureExpr)?;
                self.bump();
                self.parse_params(false)?;
                if self.eat(TokenKind::Arrow).is_some() {
                    self.parse_type()?;
                }
                self.parse_effect_row_opt()?;
                self.parse_block_expr()?;
                return Ok(self.complete(m, NodeKind::ClosureExpr));
            }
            TokenKind::KwHandle => {
                let m = self.start(NodeKind::HandleExpr)?;
                self.bump();
                self.parse_block_expr()?;
                self.expect(TokenKind::KwWith)?;
                self.parse_path("a handler")?;
                if self.at(TokenKind::LBrace) {
                    self.parse_item_body(ItemCtx::InlineHandler)?;
                } else if self.at(TokenKind::LParen) && !self.peek_gap().is_some() {
                    self.parse_arg_list()?;
                }
                return Ok(self.complete(m, NodeKind::HandleExpr));
            }
            TokenKind::KwUnsafe => {
                let m = self.start(NodeKind::UnsafeExpr)?;
                self.bump();
                self.parse_block_expr()?;
                return Ok(self.complete(m, NodeKind::UnsafeExpr));
            }
            TokenKind::KwPar => {
                let m = self.start(NodeKind::ParExpr)?;
                self.bump();
                self.parse_name("replication index")?;
                self.expect(TokenKind::KwIn)?;
                let range = self.parse_head_expr(true)?;
                if range.kind != NodeKind::RangeExpr {
                    return Err(self.error(Code::E0002, range.span, "`par` needs a range `a..b`"));
                }
                self.parse_block_expr()?;
                return Ok(self.complete(m, NodeKind::ParExpr));
            }
            TokenKind::Dot if self.peek2().kind == TokenKind::Int && !self.gap(self.peek2_index()).is_some() => {
                // `.5` → `0.5`
                let m = self.start(NodeKind::LeadingDotFloat)?;
                let start = t.span.start;
                self.bump();
                let n = self.bump();
                let span = self.span_from(start);
                let fix = format!("0.{}", self.token_text(n));
                self.foreign(
                    span,
                    "a float literal needs digits on both sides of the point",
                    "add the `0` before the point",
                    &fix,
                    "a float literal with a point has digits on both sides of it (`1.0`, `0.5`, §2.4)",
                );
                return Ok(self.complete(m, NodeKind::LeadingDotFloat));
            }
            _ => return Err(self.unexpected("an expression")),
        };
        let m = self.start(kind)?;
        let t = self.bump();
        if t.kind == TokenKind::Str {
            self.interpolation_levels(t)?;
        }
        Ok(self.complete(m, kind))
    }

    /// The holes of the string literal `t`, the innermost open node (spec
    /// §2.5): a hole `{a.b.c}` counts as the path `a.b.c` written as an
    /// expression, one level per `.`. E0006 at the `.` over the limit.
    fn interpolation_levels(&mut self, t: Token) -> PResult<()> {
        let lit = crate::lower::str_lit(self.token_text(t), t.span);
        let level = self.level();
        let mut height = 0;
        for seg in &lit.segments {
            let crate::ast::StrSeg::Interp(path) = seg else { continue };
            for (i, name) in path.segments.iter().enumerate().skip(1) {
                let dot = Span::new(self.file, name.span.start - 1, name.span.start);
                self.limit(level + Self::height(NodeKind::FieldExpr, i as u32 - 1), dot, NodeKind::FieldExpr)?;
            }
            height = height.max(path.segments.len().saturating_sub(1) as u32);
        }
        let top = self.open.len() - 1;
        self.open[top].children = self.open[top].children.max(height);
        Ok(())
    }

    /// After `(`: `()`, `(e)` or `(a, b, ...)`.
    fn parse_paren_rest(&mut self) -> PResult<NodeKind> {
        if self.eat(TokenKind::RParen).is_some() {
            return Ok(NodeKind::TupleExpr);
        }
        self.parse_consumed()?;
        if self.eat(TokenKind::Comma).is_none() {
            self.expect(TokenKind::RParen)?;
            return Ok(NodeKind::ParenExpr);
        }
        while !self.at(TokenKind::RParen) {
            self.parse_consumed()?;
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;
        Ok(NodeKind::TupleExpr)
    }

    /// After `[`: `[]`, `[a, b]` or `[e; N]`.
    fn parse_array_rest(&mut self) -> PResult<NodeKind> {
        if self.eat(TokenKind::RBracket).is_some() {
            return Ok(NodeKind::ArrayExpr);
        }
        self.parse_consumed()?;
        if self.eat(TokenKind::Semi).is_some() {
            self.parse_expr()?;
            self.expect(TokenKind::RBracket)?;
            return Ok(NodeKind::RepeatExpr);
        }
        while self.eat(TokenKind::Comma).is_some() {
            if self.at(TokenKind::RBracket) {
                break;
            }
            self.parse_consumed()?;
        }
        self.expect(TokenKind::RBracket)?;
        Ok(NodeKind::ArrayExpr)
    }

    /// The candidate of E0003 (§2.5): `next` (`else`, and later `with` and a
    /// block's `{`) goes up to the line that ends at `end`. With only spaces
    /// and newlines between, they become one space. Comments between are kept
    /// and keep their order: the code of `next`'s line (up to a comment or the
    /// end of the line) moves to `end`, and that line is removed when nothing
    /// else is left on it (W3-02/b 4).
    fn join_line_fix(&self, title: &str, end: u32, next: Token) -> Fix {
        let at = self.all.partition_point(|t| t.span.start < next.span.start);
        let between = self.all[..at].iter().rev().take_while(|t| t.span.start >= end);
        if !between.clone().any(|t| matches!(t.kind, TokenKind::Comment | TokenKind::DocComment)) {
            return Fix::replace(title, Span::new(self.file, end, next.span.start), " ");
        }
        // The code of `next`'s line: up to a comment, a newline or the end.
        let rest = &self.all[at..];
        let code_len = rest
            .iter()
            .position(|t| {
                matches!(t.kind, TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment | TokenKind::Eof)
            })
            .unwrap_or(rest.len());
        let code_end = rest[..code_len]
            .iter()
            .rev()
            .find(|t| t.kind != TokenKind::Whitespace)
            .map_or(next.span.end, |t| t.span.end);
        let moved = &self.text[next.span.start as usize..code_end as usize];
        let after = rest[code_len..].first().copied();
        let removed = match after.map(|t| t.kind) {
            // Nothing else on the line: remove the line, its indentation and its newline.
            Some(TokenKind::Newline) | Some(TokenKind::Eof) | None => {
                let line_start = match self.all[at.saturating_sub(1)] {
                    t if at > 0 && t.kind == TokenKind::Whitespace => t.span.start,
                    _ => next.span.start,
                };
                let line_end = after.map_or(code_end, |t| t.span.end);
                Span::new(self.file, line_start, line_end)
            }
            // A comment stays on the line, after the indentation.
            Some(_) => Span::new(self.file, next.span.start, after.map_or(code_end, |t| t.span.start)),
        };
        Fix::new(title, vec![Edit::insert(self.file, end, format!(" {moved}")), Edit::delete(removed)])
    }

    fn parse_if(&mut self) -> PResult<Completed> {
        let m = self.start(NodeKind::IfExpr)?;
        self.expect(TokenKind::KwIf)?;
        self.parse_head_expr(false)?;
        self.parse_block_expr()?;
        let close_brace_end = self.last_end;
        // `else` must be on the same line as `}` (E0003).
        if self.at(TokenKind::Newline) && self.peek_past_newlines().kind == TokenKind::KwElse {
            let else_tok = self.peek_past_newlines();
            let span = Span::new(self.file, close_brace_end, else_tok.span.start);
            let fix = self.join_line_fix("move `else` to the line of the `}`", close_brace_end, else_tok);
            let d =
                Diagnostic::new(Stage::Syntax, Code::E0003, span, "`else` must be on the same line as the closing `}`")
                    .with_found("else")
                    .with_fix(fix);
            self.report(d);
            self.skip_newlines();
        }
        if self.eat(TokenKind::KwElse).is_some() {
            if self.at(TokenKind::KwIf) {
                self.parse_if()?;
            } else {
                self.parse_block_expr()?;
            }
        }
        Ok(self.complete(m, NodeKind::IfExpr))
    }

    // ------------------------------------------------------------ patterns

    fn parse_pattern(&mut self) -> PResult<Completed> {
        let first = self.parse_pattern_alt()?;
        if !self.at(TokenKind::Pipe) {
            return Ok(first);
        }
        let m = self.precede(first, NodeKind::OrPat)?;
        while self.eat(TokenKind::Pipe).is_some() {
            self.parse_pattern_alt()?;
        }
        Ok(self.complete(m, NodeKind::OrPat))
    }

    /// After a `-` in a pattern: `(`s, an integer and as many `)`s (the negative
    /// literal `-(128)`, S-185). Comments and newlines inside are skipped.
    fn parenthesised_int_after_minus(&self) -> bool {
        let mut i = self.peek2_index();
        let next = |i: &mut usize| loop {
            let t = self.tokens[*i];
            if t.kind != TokenKind::Eof {
                *i += 1;
            }
            match t.kind {
                TokenKind::Comment | TokenKind::DocComment | TokenKind::Newline => {}
                k => return k,
            }
        };
        let mut opens = 0;
        let mut k = next(&mut i);
        while k == TokenKind::LParen {
            opens += 1;
            k = next(&mut i);
        }
        if opens == 0 || k != TokenKind::Int {
            return false;
        }
        (0..opens).all(|_| next(&mut i) == TokenKind::RParen)
    }

    fn parse_pattern_alt(&mut self) -> PResult<Completed> {
        let t = self.peek();
        let kind = match t.kind {
            TokenKind::Underscore => NodeKind::WildPat,
            // `-1`, and `-(1)` / `-((1))`: the parentheses between `-` and the integer are not
            // seen (§7, §4.7; S-184, S-185). `-(-1)` is no literal (S-227) and stays E0002.
            TokenKind::Minus if self.peek2().kind == TokenKind::Int || self.parenthesised_int_after_minus() => {
                let m = self.start(NodeKind::NegLitPat)?;
                self.bump();
                self.with_nl(false, |p| {
                    let mut opens = 0;
                    while p.eat(TokenKind::LParen).is_some() {
                        opens += 1;
                    }
                    let n = p.bump();
                    p.check_int(n);
                    for _ in 0..opens {
                        p.bump();
                    }
                });
                return Ok(self.complete(m, NodeKind::NegLitPat));
            }
            TokenKind::Int => {
                let m = self.start(NodeKind::LitPat)?;
                self.bump();
                self.check_int(t);
                return Ok(self.complete(m, NodeKind::LitPat));
            }
            TokenKind::Float | TokenKind::Minus => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "float literals cannot be patterns; compare in a guard (§7)",
                ));
            }
            TokenKind::Char | TokenKind::Str | TokenKind::KwTrue | TokenKind::KwFalse => NodeKind::LitPat,
            TokenKind::LParen => {
                let m = self.start(NodeKind::TuplePat)?;
                self.bump();
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RParen) {
                        p.parse_pattern()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                    Ok(())
                })?;
                return Ok(self.complete(m, NodeKind::TuplePat));
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let m = self.start(NodeKind::PathPat)?;
                let path = self.parse_path("a pattern")?;
                if self.at(TokenKind::LParen) && !self.peek_gap().is_some() {
                    self.reshape(NodeKind::TupleStructPat)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RParen) {
                            p.parse_pattern()?;
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.expect(TokenKind::RParen)?;
                        Ok(())
                    })?;
                    return Ok(self.complete(m, NodeKind::TupleStructPat));
                }
                if self.at(TokenKind::LBrace)
                    && self.token_text(path.last).starts_with(|c: char| c.is_ascii_uppercase())
                {
                    self.reshape(NodeKind::StructPat)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RBrace) {
                            if p.at(TokenKind::DotDot) {
                                let t = p.peek();
                                return Err(p.error(
                                    Code::E0002,
                                    t.span,
                                    "struct patterns name every field; use `_` for the unused ones (§7)",
                                ));
                            }
                            let f = p.start(NodeKind::StructPatField)?;
                            p.parse_ident("field name")?;
                            p.expect(TokenKind::Colon)?;
                            p.parse_pattern()?;
                            p.complete(f, NodeKind::StructPatField);
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.expect(TokenKind::RBrace)?;
                        Ok(())
                    })?;
                    return Ok(self.complete(m, NodeKind::StructPat));
                }
                let bind =
                    path.segments == 1 && self.token_text(path.first).starts_with(|c: char| c.is_ascii_lowercase());
                return Ok(self.complete(m, if bind { NodeKind::BindPat } else { NodeKind::PathPat }));
            }
            _ => return Err(self.unexpected("a pattern")),
        };
        let m = self.start(kind)?;
        self.bump();
        Ok(self.complete(m, kind))
    }
}

fn binop(kind: TokenKind) -> bool {
    crate::lower::binop(kind).is_some()
}

/// The height of a binary chain read as the tree of §3.1 (spec §2.5): the
/// strengths of the groups ([`crate::ast::OpGroup::stronger`]) and left
/// associativity, one level per operator. The chain is read from the left,
/// as the shunting-yard algorithm reads it: the operators on the stack wait
/// for their right operand, each in the right operand of the one below it.
/// Groups without a strength between them (E0010) are read left to right.
pub(crate) struct Chain {
    /// The waiting operators: the height of their left operand and their group.
    stack: Vec<(u32, crate::ast::OpGroup)>,
    /// The height of the last operand, or of the operators it closed.
    current: u32,
}

impl Chain {
    pub(crate) fn new(first: u32) -> Chain {
        Chain { stack: Vec::new(), current: first }
    }

    /// An operator of `group` after the last operand: the waiting operators
    /// it does not bind tighter than take the operand as their right one and
    /// close. Returns how many operators wait then, this one included, and
    /// the height of its left operand.
    pub(crate) fn operator(&mut self, group: crate::ast::OpGroup) -> (u32, u32) {
        while let Some(&(left, waiting)) = self.stack.last() {
            if group.stronger(waiting) {
                break;
            }
            self.current = left.max(self.current) + 1;
            self.stack.pop();
        }
        self.stack.push((self.current, group));
        (self.stack.len() as u32, self.current)
    }

    pub(crate) fn operand(&mut self, height: u32) {
        self.current = height;
    }

    /// The height of the whole chain.
    pub(crate) fn height(mut self) -> u32 {
        while let Some((left, _)) = self.stack.pop() {
            self.current = left.max(self.current) + 1;
        }
        self.current
    }
}

/// How a declaration is parsed after its attributes and visibility.
type DeclParser = fn(&mut Parser<'_>, ItemCtx) -> PResult<()>;

/// Where a declaration may be written: the top level of a module, and the
/// lists of declarations it is a member of (§18.1, [`Parser::not_a_member`]).
const TOP: &[ItemCtx] = &[ItemCtx::Top];
const FUNCTION_PLACES: &[ItemCtx] = &[
    ItemCtx::Top,
    ItemCtx::Trait,
    ItemCtx::Impl,
    ItemCtx::Effect,
    ItemCtx::Handler,
    ItemCtx::Extern,
    ItemCtx::InlineHandler,
];
const CONST_PLACES: &[ItemCtx] = &[ItemCtx::Top, ItemCtx::Trait, ItemCtx::Impl];
const TYPE_PLACES: &[ItemCtx] = &[ItemCtx::Top, ItemCtx::Extern];

/// The keywords that start a declaration, with how to parse it and where it
/// may be written: the one list. `parse_item` dispatches on it and refuses a
/// declaration out of its places, and the recovery's item starts
/// ([`is_item_start`]) are these keywords and what may come before them.
const DECLARATIONS: &[(TokenKind, DeclParser, &[ItemCtx])] = &[
    (TokenKind::KwFn, |p, c| p.parse_fn(c), FUNCTION_PLACES),
    (TokenKind::KwRt, |p, c| p.parse_fn(c), FUNCTION_PLACES),
    (TokenKind::KwFlow, |p, c| p.parse_flow(c), TOP),
    (TokenKind::KwStruct, |p, c| p.parse_struct(c), TOP),
    (TokenKind::KwEnum, |p, c| p.parse_enum(c), TOP),
    (TokenKind::KwType, |p, c| p.parse_type_item(c), TYPE_PLACES),
    (TokenKind::KwTrait, |p, c| p.parse_trait(c), TOP),
    (TokenKind::KwImpl, |p, c| p.parse_impl(c), TOP),
    (TokenKind::KwEffect, |p, c| p.parse_effect(c), TOP),
    (TokenKind::KwBlocking, |p, c| p.parse_effect(c), TOP),
    (TokenKind::KwHandler, |p, c| p.parse_handler(c), TOP),
    (TokenKind::KwConst, |p, c| p.parse_const(c), CONST_PLACES),
    (TokenKind::KwUse, |p, c| p.parse_use(c), TOP),
    (TokenKind::KwExtern, |p, c| p.parse_extern(c), TOP),
    (TokenKind::KwTarget, |p, c| p.parse_target(c), TOP),
    (TokenKind::KwTest, |p, c| p.parse_test(c), TOP),
];

/// A token that starts an item: a declaration keyword, `pub`, an attribute, a doc comment.
fn is_item_start(kind: TokenKind) -> bool {
    DECLARATIONS.iter().any(|(k, _, _)| *k == kind)
        || matches!(kind, TokenKind::KwPub | TokenKind::At | TokenKind::DocComment)
}

/// Keep only the earliest diagnostic of each top-level item (P-01). Diagnostics
/// outside every item are grouped together as one "item".
pub(crate) fn first_per_item(items: &[Span], mut diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    diagnostics.sort_by_key(|d| (d.span.start, d.span.end));
    let mut seen: Vec<bool> = vec![false; items.len() + 1];
    let mut out = Vec::new();
    for d in diagnostics {
        let slot = items
            .iter()
            .position(|s| s.start <= d.span.start && d.span.start < s.end.max(s.start + 1))
            .unwrap_or(items.len());
        if !seen[slot] {
            seen[slot] = true;
            out.push(d);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId};

    #[test]
    fn const_type_arguments() {
        // S-24: integer literals (optionally negated) are const arguments; names stay types.
        let p = crate::parse(FileId(0), "fn f(r: Ring[F32, 4], s: Ring[F32, N], t: Ring[F32, -1]) {}\n");
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let d = crate::dump(&p.ast);
        assert!(d.contains("Ring[F32, 4]"), "{d}");
        assert!(d.contains("Ring[F32, N]"), "{d}");
        assert!(d.contains("Ring[F32, (neg 1)]"), "{d}");
    }

    use crate::dump;

    fn parse(src: &str) -> crate::Parsed {
        crate::parse(FileId(0), src)
    }

    fn codes(src: &str) -> Vec<Code> {
        parse(src).diagnostics.iter().map(|d| d.code).collect()
    }

    /// `src` after the first candidate of its first diagnostic.
    fn fixed(src: &str) -> String {
        let p = parse(src);
        let fix = &p.diagnostics[0].fixes[0];
        onsa_diag::apply_text(src, &fix.edits().iter().collect::<Vec<_>>()).unwrap()
    }

    #[test]
    fn the_e0003_candidate_keeps_the_comments_in_their_order() {
        let plain = "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  }\n  else {\n    2\n  }\n}\n";
        assert_eq!(fixed(plain), "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n    2\n  }\n}\n");
        let own_line = "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  }\n  // other\n  else {\n    2\n  }\n}\n";
        assert_eq!(fixed(own_line), "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n  // other\n    2\n  }\n}\n");
        let after_brace = "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } // a\n  else { // b\n    2\n  }\n}\n";
        assert_eq!(
            fixed(after_brace),
            "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else { // a\n  // b\n    2\n  }\n}\n"
        );
        let after = fixed(after_brace);
        assert!(parse(&after).diagnostics.is_empty(), "{:?}", parse(&after).diagnostics);
        assert!(parse(&fixed(own_line)).diagnostics.is_empty());
    }

    fn fixes(src: &str) -> Vec<String> {
        parse(src)
            .diagnostics
            .iter()
            .flat_map(|d| d.fixes.iter())
            .map(|f| f.edits().iter().map(|e| e.replace.as_str()).collect::<Vec<_>>().join("|"))
            .collect()
    }

    /// Dump of the body of `fn f() { <src> }`.
    fn body(src: &str) -> String {
        let p = parse(&format!("fn f() {{\n{src}\n}}"));
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let d = dump(&p.ast);
        let d = d.trim_start_matches("(fn f()\n  ").trim_end_matches(")\n");
        let mut out = String::new();
        for (i, line) in d.lines().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            out.push_str(line.trim_start());
        }
        out
    }

    #[test]
    fn newline_continuation() {
        assert_eq!(body("let a = x +\n  y"), "(block (let a = (chain x + y)))");
        assert_eq!(body("let a = xs\n  .len()"), "(block (let a = (call (. xs len) ())))");
        assert_eq!(body("let a =\n  1"), "(block (let a = 1))");
        // Newlines are whitespace inside parentheses and brackets.
        assert_eq!(body("let a = f(1,\n  2)\nlet b = [1,\n 2]"), "(block (let a = (call f (1, 2))) (let b = [1, 2]))");
        // A newline without a continuation ends the statement.
        assert_eq!(body("let a = x\n-y"), "(block (let a = x) tail (neg y))");
    }

    #[test]
    fn tail_vs_statement() {
        assert_eq!(body("let a = 1\na"), "(block (let a = 1) tail a)");
        assert_eq!(body("f(1)\n"), "(block tail (call f (1)))");
        assert_eq!(body("return"), "(block (return))");
        assert_eq!(body("x = 2"), "(block (assign x 2))");
    }

    #[test]
    fn else_position() {
        assert!(codes("fn f() {\n  if c { a } else { b }\n}").is_empty());
        assert_eq!(codes("fn f() {\n  if c { a }\n  else { b }\n}"), vec![Code::E0003]);
        assert_eq!(
            body("if a { 1 } else if b { 2 } else { 3 }"),
            "(block tail (if a (block tail 1) else (if b (block tail 2) else (block tail 3))))"
        );
    }

    #[test]
    fn call_marks() {
        assert_eq!(body("saw~(f0)"), "(block tail (call~ saw (f0)))");
        assert_eq!(body("out.fill!(0.0)"), "(block tail (call! (. out fill) (0.0)))");
        assert_eq!(body("a.f!=b"), "(block tail (chain (. a f) != b))");
        assert_eq!(body("!(a && b)"), "(block tail (not ((chain a && b))))");
        assert_eq!(codes("fn f() {\n  saw ~(f0)\n}"), vec![Code::E0002]);
        assert_eq!(codes("fn f() {\n  saw~ (f0)\n}"), vec![Code::E0002]);
    }

    #[test]
    fn tuple_index_and_fields() {
        assert_eq!(body("t.0.1"), "(block tail (. (. t 0) 1))");
        assert_eq!(body("self.params[i].f0 = v"), "(block (assign (. (index (. self params) i) f0) v))");
    }

    #[test]
    fn struct_literals_and_heads() {
        assert_eq!(body("let p = Point { x: 1.0, y: 2.0 }"), "(block (let p = (struct Point x: 1.0 y: 2.0)))");
        assert_eq!(body("voice.Config {}"), "(block tail (struct voice.Config))");
        // S-08: no struct literal in a head expression.
        assert_eq!(
            body("if s == Shape.Circle { 1 } else { 2 }"),
            "(block tail (if (chain s == (. Shape Circle)) (block tail 1) else (block tail 2)))"
        );
        assert_eq!(
            body("if f(Point { x: 1.0 }) { 1 } else { 2 }"),
            "(block tail (if (call f ((struct Point x: 1.0))) (block tail 1) else (block tail 2)))"
        );
        assert_eq!(body("while x { }"), "(block (while x (block)))");
    }

    #[test]
    fn ranges_only_in_heads() {
        assert_eq!(body("for i in 0..n { }"), "(block (for i in (range 0 n) (block)))");
        assert_eq!(
            body("let s = par i in 0..N { f~(i) }"),
            "(block (let s = (par i in 0..N (block tail (call~ f (i))))))"
        );
        assert_eq!(codes("fn f() {\n  let r = 0..n\n}"), vec![Code::E0002]);
        assert_eq!(codes("fn f() {\n  for i in 0..=n { }\n}"), vec![Code::E0002]);
    }

    #[test]
    fn precedence() {
        assert_eq!(body("-x.abs()"), "(block tail (neg (call (. x abs) ())))");
        assert_eq!(body("-x as F64"), "(block tail (as (neg x) F64))");
        assert_eq!(body("a + (x as F64)"), "(block tail (chain a + ((as x F64))))");
        assert_eq!(body("x?.y"), "(block tail (. (try x) y))");
    }

    #[test]
    fn patterns() {
        assert_eq!(body("let (a, b) = p"), "(block (let (tuple a b) = p))");
        assert_eq!(
            body("match v { Some(x) if x > 0 => x, None => 0, }"),
            "(block tail (match v Some(x) if (chain x > 0) => x None => 0))"
        );
        assert_eq!(
            body("match v { Point { x: px, y: _ } => px, _ => 0 }"),
            "(block tail (match v Point { x: px, y: _ } => px _ => 0))"
        );
        assert_eq!(
            body("match n { 1 | 2 => a, -1 => b, 'c' => d, _ => e }"),
            "(block tail (match n (1 | 2) => a -1 => b 'c' => d _ => e))"
        );
        assert_eq!(
            body("match s { Shape.Circle(r) => r, Shape.Rect(w, h) => w }"),
            "(block tail (match s Shape.Circle(r) => r Shape.Rect(w, h) => w))"
        );
    }

    #[test]
    fn items() {
        let src = "/// doc\n@derive(PartialEq, Eq)\npub struct Key[T: PartialOrd + Eq, const N: U32, e] {\n  id: U32,\n  xs: [T; N],\n}\n";
        assert_eq!(
            dump(&parse(src).ast),
            "(doc:1 @derive(PartialEq, Eq) pub struct Key[T: PartialOrd + Eq, const N: U32, effect e]\n  id: U32\n  xs: [T; N])\n"
        );
        let src = "pub fn map[T, U, e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {Alloc, e} { xs }";
        assert_eq!(
            dump(&parse(src).ast),
            "(pub fn map[T, U, effect e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {Alloc, e}\n  (block\n    tail xs))\n"
        );
        let src =
            "pub(pkg) type S = Buf[F32]\nconst X: (U32, F32) = (1, 2.0)\nuse a.b.{c, d}\ntest \"t\" { assert true }";
        let d = dump(&parse(src).ast);
        assert!(
            d.starts_with(
                "(pub(pkg) type S = Buf[F32])\n(const X: (U32, F32) = (tuple 1 2.0))\n(use a.b.{c, d})\n(test \"t\""
            ),
            "{d}"
        );
        let src = "pub trait Show {\n  fn show(self) -> Str uses {Alloc}\n  const ZERO: Self\n}\nimpl Show for Point {\n  fn show(self) -> Str uses {Alloc} { \"({self.x}, {self.y})\" }\n}";
        let p = parse(src);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        assert!(dump(&p.ast).contains("(block\n      tail \"({self.x}, {self.y})\"))"));
        let src = "handler arena(inout mem: Span[U8]): Alloc {\n  fn alloc(n: U32) -> U32 { n }\n}\nfn g() { handle { f() } with arena(inout scratch) }\nfn h() { handle { f() } with Fs { fn read(_: Path) -> Str { \"\" } } }";
        let p = parse(src);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    }

    /// The members of a list of declarations are a closed list (§18.1,
    /// S-263): any other declaration there is E0002, so declarations do not
    /// nest without bound (they count no level, spec §2.5): the 10 000
    /// nested `impl`s stop at the second one.
    #[test]
    fn members_are_a_closed_list() {
        for kw in [
            "impl B",
            "trait T",
            "effect E",
            "blocking effect E",
            "handler h: E",
            "extern \"C\" lib \"x\"",
            "struct S",
            "enum E",
            "flow g(x: Sig[F32]) -> Sig[F32]",
            "proc g(x: Sig[F32]) -> Sig[F32]",
            "test \"t\"",
        ] {
            assert_eq!(codes(&format!("impl A {{\n  {kw} {{\n  }}\n}}\n")), vec![Code::E0002], "{kw}");
        }
        for member in ["use a.{b}", "type T = I32", "target fn f()"] {
            assert_eq!(codes(&format!("impl A {{\n  {member}\n}}\n")), vec![Code::E0002], "{member}");
        }
        assert_eq!(codes("effect E {\n  const C: I32 = 1\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("handler h: E {\n  const C: I32 = 1\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("extern \"C\" lib \"x\" {\n  const C: I32 = 1\n}\n"), vec![Code::E0002]);
        assert!(codes("impl A {\n  const C: I32 = 1\n  fn f() { }\n  rt fn g() { }\n}\n").is_empty());
        assert!(codes("trait T {\n  const C: Self\n  fn f(self)\n}\n").is_empty());
        assert!(codes("extern \"C\" lib \"x\" {\n  type Raw\n  rt fn f(h: Ptr[Raw])\n}\n").is_empty());
        let p = parse("impl A {\n  struct S { x: I32 }\n}\n");
        assert_eq!(p.diagnostics[0].notes.len(), 1, "the note with the members");
        let deep = format!("{}{}", "impl A { ".repeat(10_000), "}".repeat(10_000));
        assert_eq!(codes(&deep), vec![Code::E0002]);
    }

    /// The height of a binary chain is the one of the tree of §3.1 (spec §2.5).
    #[test]
    fn chain_heights_follow_the_strengths() {
        use crate::ast::OpGroup::*;
        let height = |first: u32, rest: &[(crate::ast::OpGroup, u32)]| {
            let mut c = super::Chain::new(first);
            for &(g, h) in rest {
                c.operator(g);
                c.operand(h);
            }
            c.height()
        };
        // a + b + c: ((a + b) + c)
        assert_eq!(height(0, &[(Additive, 0), (Additive, 0)]), 2);
        // a + b * c * d: a + ((b * c) * d)
        assert_eq!(height(0, &[(Additive, 0), (Multiplicative, 0), (Multiplicative, 0)]), 3);
        // a * b + c * d: (a * b) + (c * d)
        assert_eq!(height(0, &[(Multiplicative, 0), (Additive, 0), (Multiplicative, 0)]), 2);
        // lo <= x && x < hi: (lo <= x) && (x < hi)
        assert_eq!(height(0, &[(Comparison, 0), (And, 0), (Comparison, 0)]), 2);
        // a deep operand on the right of the last operator
        assert_eq!(height(0, &[(Additive, 0), (Additive, 5)]), 6);
        // the strengths of §3.1
        assert!(Multiplicative.stronger(Additive) && Additive.stronger(Comparison) && Comparison.stronger(Or));
        assert!(!And.stronger(Or) && !Or.stronger(And) && !Bitwise.stronger(Or) && !Additive.stronger(Bitwise));
        assert!(!Additive.stronger(Multiplicative) && !Additive.stronger(Additive));
    }

    #[test]
    fn signatures_without_bodies() {
        assert!(codes("extern \"C\" lib \"x\" {\n  type Raw\n  rt fn f(h: Ptr[Raw]) uses {Alloc}\n}").is_empty());
        assert_eq!(codes("extern \"C\" lib \"x\" {\n  fn f() { }\n}"), vec![Code::E0002]);
        assert!(codes("target type Device\ntarget rt fn read(inout d: Device)").is_empty());
        assert_eq!(codes("fn f()\nfn g() { }"), vec![Code::E0002]);
        assert_eq!(codes("effect Log {\n  rt fn info(msg: Str)\n}"), vec![]);
    }

    #[test]
    fn foreign_forms() {
        assert_eq!(
            (codes("fn f() {\n  let x = 1;\n}"), fixes("fn f() {\n  let x = 1;\n}")),
            (vec![Code::E0020], vec!["".to_string()])
        );
        assert_eq!(fixes("fn f() {\n  std::math::exp(x)\n}"), vec![".".to_string()]);
        assert_eq!(fixes("fn f(x: Vec<T>) { }"), vec!["[T]".to_string()]);
        assert_eq!(fixes("fn f() {\n  g(&mut x)\n}"), vec!["inout x".to_string()]);
        assert_eq!(fixes("fn f() {\n  g(&x)\n}"), vec!["x".to_string()]);
        assert_eq!(fixes("fn f() {\n  let mut x = 1\n}"), vec!["var".to_string()]);
        assert!(dump(&parse("fn f() {\n  let mut x = 1\n}").ast).contains("(var x = 1)"));
        assert_eq!(fixes("fn f() {\n  loop { }\n}"), vec!["while true".to_string()]);
        assert_eq!(fixes("fn f(x: i32) -> usize { x }"), vec!["I32".to_string()]);
        assert_eq!(fixes("#[derive(PartialEq)]\nstruct A { }"), vec!["@derive(PartialEq)".to_string()]);
        assert_eq!(fixes("proc f(x: Sig[F32]) -> Sig[F32] { x }"), vec!["flow".to_string()]);
        assert_eq!(fixes("impl A {\n  fn f(mut self) { }\n}"), vec!["inout self".to_string()]);
        assert_eq!(fixes("fn f<T>(x: T) { }"), vec!["[T]".to_string()]);
        assert_eq!(fixes("fn f() {\n  let y = .5\n}"), vec!["0.5".to_string()]);
        assert_eq!(codes("fn f() {\n  for i in 0..=n { }\n}"), vec![Code::E0002]);
    }

    #[test]
    fn first_error_per_item_and_recovery() {
        let src = "fn a() {\n  let = 1\n  let = 2\n}\nfn b() { 1 }\nfn c() {\n  )\n}\n";
        let p = parse(src);
        let lines: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
        assert_eq!(p.diagnostics.len(), 2, "{lines:?}");
        assert_eq!(p.ast.root.len(), 1); // only `b` survived
        assert!(dump(&p.ast).starts_with("(fn b()"));
        // An item with a lexer error and a parse error reports the earliest only.
        let p = parse("fn a() {\n  let s = \"abc\n  let = 1\n}");
        assert_eq!(p.diagnostics.len(), 1);
        assert_eq!(p.diagnostics[0].code, Code::E0001);
    }

    #[test]
    fn literals() {
        assert_eq!(body("let s = \"a\\nb {{x}} {p.q}\""), "(block (let s = \"a\\nb {{x}} {p.q}\"))");
        assert_eq!(body("let c = '\\u{1F600}'"), "(block (let c = '\\u{1f600}'))");
        assert_eq!(body("let n = 0xFF + 1_000"), "(block (let n = (chain 255 + 1000)))");
        assert_eq!(codes("fn f() {\n  let n = 99999999999999999999\n}"), vec![Code::E0408]);
        assert_eq!(body("Ok(())"), "(block tail (call Ok ((tuple))))");
    }

    #[test]
    fn closures_and_args() {
        assert_eq!(
            body("xs.map(fn(x) { x * 2.0 })"),
            "(block tail (call (. xs map) ((fn(x) (block tail (chain x * 2.0))))))"
        );
        assert_eq!(body("f(inout a, move b, inout [c, d])"), "(block tail (call f (inout a, move b, inout [c, d])))");
        assert_eq!(
            body("fn(move v: S) -> U64 uses {Sync} { v }"),
            "(block tail (fn(move v: S) -> U64 uses {Sync} (block tail v)))"
        );
    }

    #[test]
    fn move_in_consuming_positions() {
        // S-21 (§5.2): `move x` as an expression form.
        let src = "fn f(move b: Buf[F32]) {\n  let y = move b\n  var v = move y\n  v = move b\n  let t = (move v, 1)\n  let a = [move b, move v]\n  let s = Box { b: move b }\n  match move b {\n    _ => 1,\n  }\n  take(move b)\n}\n";
        assert!(codes(src).is_empty(), "{:?}", crate::parse(FileId(0), src).diagnostics);
        let d = crate::dump(&crate::parse(FileId(0), src).ast);
        assert!(d.contains("(let y = (move b))"), "{d}");
        assert!(d.contains("(match (move b)"), "{d}");
        // Elsewhere it is E0002.
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  return move b\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  move b\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  let y = 1 + move b\n  y\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: Bool) -> U32 {\n  if move b { 1 } else { 2 }\n}\n"), vec![Code::E0002]);
    }
}
