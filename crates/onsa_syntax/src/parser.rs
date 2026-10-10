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
//! Errors: the parser reports every diagnostic; the choice of one per unit is
//! the driver's (`onsa_driver::reduce`, spec §18.1). The parser has no branch
//! for the forms of other languages (`;`, `::`, `<T>`, `&mut`, ...): it fails
//! at them as at any token it does not accept, and every failure goes through
//! [`Parser::fail`], which asks the table of those forms ([`crate::foreign`])
//! what the failure is (an E0020 with the Onsa form, or the general E0002).
//! A parse error is fatal for
//! its unit (a top-level item, or a member of an `impl`, `trait`, `effect`,
//! `handler` or `extern`, S-59): the parser closes the nodes it was in as
//! incomplete, puts the tokens up to the end of the unit in an `Error` node
//! ([`Parser::skip_unit`]), and continues with the next unit.

use onsa_diag::{Code, Diagnostic, FileId, Span, Stage};

use crate::ast::Ast;
use crate::cst::{Cst, Event, NodeKind};
use crate::foreign::{self, Want};
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
    /// Every diagnostic of the lexer, the parser and the checks on its tree
    /// (operator groups, naming), not reduced: the choice of one per unit is
    /// `onsa_driver::reduce`'s (spec §18.1, S-59).
    pub diagnostics: Vec<Diagnostic>,
    /// The units of the diagnostics of the file (spec §18.1, [`crate::units`]).
    pub units: crate::units::Units,
    /// The levels (spec §2.5) of each top-level item the parser finished, in
    /// the order of the file (`onsa dump --levels`; the fmt properties check
    /// that `fmt` makes no item deeper, `tools/fmt_props.py`).
    pub levels: Vec<u32>,
}

impl Parsed {
    /// The file has a diagnostic of the syntax stage, whatever its code
    /// (spec §18.2, S-214: E00xx, the reserved word's E0200, E0408, E0006):
    /// `onsa fmt` does not rewrite it and `onsa diff --ast` does not compare
    /// it. The one place of that decision (`fmt`, `diff --ast`, the test
    /// tools); what they report is `onsa_driver::reduce::syntax_report`.
    pub fn syntax_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.stage == Stage::Syntax)
    }
}

/// What the parser gives the later stages of [`crate::parse`].
pub(crate) struct ParseOutput {
    pub tokens: Vec<Token>,
    pub events: Vec<Event>,
    pub diagnostics: Vec<Diagnostic>,
    /// The levels of each top-level item that parsed ([`Parsed::levels`]).
    pub levels: Vec<u32>,
    /// The height of the tree in levels (spec §2.5), as the parser counted
    /// it (`Parser::height`): the deepest declaration unit. The tests compare
    /// it with the tree; the candidates of E0010 that add levels read it.
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
    /// The span of the AST node it gives.
    span: Span,
    /// The height of its subtree ([`Parser::height`]).
    height: u32,
}

/// An open node: its `Start` event, the greatest height of its children so
/// far, and its level.
#[derive(Debug, Clone, Copy)]
struct Open {
    event: u32,
    /// Where it starts (the table of the forms of other languages reads it).
    start: u32,
    children: u32,
    /// The levels (spec §2.5) from the root of the declaration unit down to
    /// this node, this node included: a child of `height(kind, 0)` levels is
    /// at `level + height(kind, 0)`. Items, lists and statements count no
    /// level, so every unit starts from 0. In a binary chain it is the level
    /// of the operator whose right operand is read ([`Parser::chain_operator`]).
    level: u32,
}

/// The rule of a `^` with no name right after it (§2.6, S-358).
const CARET_RULE: &str = "a prefix `^` is the mark of a name, written right before the name of a `let` of the flow (`prev~(^y)`), and no operator; the binary `^` is the exclusive or (§2.6)";

/// The rule of an `if~` with no `else` (§11.5, S-355).
const IF_TILDE_ELSE_RULE: &str =
    "`if~` evaluates every branch and takes one, so its chain ends with an `else` block (§11.5)";

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
    /// The `(`, `[` and `{` the cursor is inside, innermost last: their
    /// indices in `tokens` (the recovery, [`Parser::skip_unit`]).
    braces: Vec<usize>,
    /// For each `{` of `tokens`, whether a `}` closes it when the brackets of
    /// the file are paired in order (the recovery of a list of members whose
    /// `{` is never closed, [`Parser::parse_item_body`]).
    brace_closed: Vec<bool>,
    /// The token where the recovery reported an unclosed bracket: the units
    /// around that end there too and do not report it again.
    reported_stop: Option<usize>,
    events: Vec<Event>,
    /// The open nodes, innermost last.
    open: Vec<Open>,
    /// The nodes closed since the last token was consumed, innermost first,
    /// and where each starts: what ended right before the next token (the
    /// table of the forms of other languages reads it at a failure).
    closed: Vec<(NodeKind, u32)>,
    /// The height of the tree, once the root closed.
    height: u32,
    diagnostics: Vec<Diagnostic>,
    /// How many of `diagnostics` are the lexer's (the parser's follow).
    lexed: usize,
    /// The holes of the string literals ([`crate::Lexed::holes`]), in the
    /// order of the file.
    holes: Vec<Span>,
    /// The spans of the lexer's diagnostics, ordered by their start: the
    /// check of a `test` name finds those in its literal by a binary search.
    lexed_spans: Vec<Span>,
    /// The levels of each top-level item that parsed.
    levels: Vec<u32>,
    /// How many trial readings ([`Parser::snapshot`]) are open: a reading
    /// that is tried inside another one does not try the brackets of a
    /// call's type arguments again, so trials nest at most once per level.
    trials: u32,
    /// The last postfix opener not read on because of a gap before it
    /// ([`Parser::touches`], S-89): the table reads it at the failure there.
    detached: Option<crate::layout::Detached>,
}

/// What a trial reading restores ([`Parser::snapshot`]).
struct Snapshot {
    pos: usize,
    last_end: u32,
    events: usize,
    diagnostics: usize,
    open: Vec<Open>,
    closed: Vec<(NodeKind, u32)>,
    braces: Vec<usize>,
    nl: Vec<bool>,
    no_struct_lit: bool,
    detached: Option<crate::layout::Detached>,
}

/// Whether a token starts an operand (§3.1): a prefix operator, a literal,
/// a name or the reference `^name` (§2.6), `_`, a bracket, a block, or an expression keyword. `move` and
/// `rt` before an operand are errors of their own and start none.
pub(crate) fn starts_operand(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        Minus
            | Bang
            | Caret
            | Int
            | Float
            | Char
            | Str
            | KwTrue
            | KwFalse
            | Underscore
            | Ident
            | KwSelf
            | KwSelfType
            | LParen
            | LBracket
            | LBrace
            | KwIf
            | KwMatch
            | KwFn
            | KwHandle
            | KwUnsafe
            | KwPar
    )
}

/// Whether the tokens `first` and `second` declare a function (`fn name`),
/// which no expression is (§6.1): the one test, for the parser and the
/// missing `,` of a list ([`crate::layout::list_fixes`]).
pub(crate) fn declares_a_function(first: TokenKind, second: TokenKind) -> bool {
    first == TokenKind::KwFn && second == TokenKind::Ident
}

impl<'a> Parser<'a> {
    pub(crate) fn new(file: FileId, text: &'a str, lexed: crate::Lexed) -> Parser<'a> {
        let crate::Lexed { tokens: all, diagnostics, holes } = lexed;
        let full: Vec<u32> = (0..all.len() as u32).filter(|&i| all[i as usize].kind != TokenKind::Whitespace).collect();
        let tokens: Vec<Token> = full.iter().map(|&i| all[i as usize]).collect();
        let mut brace_closed = vec![false; tokens.len()];
        let mut open = Vec::new();
        for (k, t) in tokens.iter().enumerate() {
            match t.kind {
                TokenKind::LBrace => open.push(k),
                TokenKind::RBrace => {
                    if let Some(o) = open.pop() {
                        brace_closed[o] = true;
                    }
                }
                _ => {}
            }
        }
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
            braces: Vec::new(),
            brace_closed,
            reported_stop: None,
            events: Vec::new(),
            open: Vec::new(),
            closed: Vec::new(),
            height: 0,
            lexed: diagnostics.len(),
            lexed_spans: {
                let mut v: Vec<Span> = diagnostics.iter().map(|d| d.span).collect();
                v.sort_by_key(|s| s.start);
                v
            },
            diagnostics,
            holes,
            levels: Vec::new(),
            trials: 0,
            detached: None,
        }
    }

    /// The state before a trial reading: a reading that fails is undone with
    /// [`Parser::restore`] (its events and diagnostics are dropped). A trial
    /// opens and closes only nodes of its own (no `precede` of a node read
    /// before it).
    fn snapshot(&mut self) -> Snapshot {
        self.trials += 1;
        Snapshot {
            pos: self.pos,
            last_end: self.last_end,
            events: self.events.len(),
            diagnostics: self.diagnostics.len(),
            open: self.open.clone(),
            closed: self.closed.clone(),
            braces: self.braces.clone(),
            nl: self.nl.clone(),
            no_struct_lit: self.no_struct_lit,
            detached: self.detached,
        }
    }

    /// Undo the reading since `s`.
    fn restore(&mut self, s: Snapshot) {
        self.end_trial();
        self.pos = s.pos;
        self.last_end = s.last_end;
        self.events.truncate(s.events);
        self.diagnostics.truncate(s.diagnostics);
        self.open = s.open;
        self.closed = s.closed;
        self.braces = s.braces;
        self.nl = s.nl;
        self.no_struct_lit = s.no_struct_lit;
        self.detached = s.detached;
    }

    /// Keep the reading since the snapshot.
    fn end_trial(&mut self) {
        self.trials -= 1;
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
        self.open.push(Open { event, start, children, level: base + Self::height(kind, 0) });
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

    /// Whether the parser reads inside a type (a const argument or the
    /// length of an array type): an expression there has no `::[…]` (R-196).
    fn in_type(&self) -> bool {
        self.open.iter().any(|o| {
            matches!(self.events[o.event as usize], Event::Start { kind: Some(k), .. }
                if crate::lower::class(k) == crate::lower::Class::Type)
        })
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
            SourceFile | Error | Name | Item | Docs | Attr | AttrArgs | AttrNamedArg | Vis | Fn | Flow | Struct
            | FieldList | Field | TupleStructBody | Enum | VariantList | Variant | VariantFields | TypeAlias
            | OpaqueType | Trait | Impl | Effect | Handler | Const | Use | UseTree | UseNames | Extern | Target
            | Test | ItemList | GenericParams | TypeParam | ConstParam | EffectParam | Bound | ParamList | Param
            | EffectRow | Path => 0,
            // Types: a type with arguments counts at its `[` (the `TypeArgs`), a name none.
            PathType | ConstArg | FnTypeParams => 0,
            TypeArgs | UnitType | TupleType | ParenType | ArrayType | FnType => 1,
            // Statements are none, the loops one (and their blocks one more).
            LetStmt | VarStmt | BreakStmt | ContinueStmt | ReturnStmt | AssertStmt | AssignStmt | ExprStmt => 0,
            ForStmt | WhileStmt | Block => 1,
            // Expressions. A binary chain is flat in the tree: its height is
            // the one of the tree of §3.1, one level per operator ([`Chain`]).
            // A `::[…]` counts at its `[` (the `TypeArgs`), as a type with arguments.
            Literal | HoleExpr | PathExpr | BinaryExpr | MatchArms | MatchArm | ArgList | Arg | StructLitFields
            | StructLitField | TypeArgsExpr | FeedbackExpr => 0,
            // SPEC-GAP(S-361): the clock of an input or output counts no level
            // (the heading counts none); in an expression it is in an `AtExpr`.
            Clock => 0,
            ParenExpr | TupleExpr | ArrayExpr | RepeatExpr | IfExpr | MatchExpr | ClosureExpr | HandleExpr
            | UnsafeExpr | ParExpr | MoveExpr | RangeExpr | CastExpr | AtExpr | PrefixExpr | CallExpr | FieldExpr
            | TupleIndexExpr | IndexExpr | TryExpr | StructLit => 1,
            // Patterns: `|` is one level for all its alternatives.
            WildPat | LitPat | NegLitPat | BindPat | PathPat | StructPatField | StructPatRest => 0,
            TuplePat | ParenPat | TupleStructPat | StructPat | OrPat => 1,
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
            (Block | ForStmt | WhileStmt, _) => {
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
        self.closed.push((kind, m.start));
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
            self.closed.clear();
            self.events.push(Event::Token(self.full[i]));
            if is_opening(t.kind) {
                self.braces.push(i);
            } else if is_closing(t.kind) {
                close_bracket(&mut self.braces, &self.tokens, t.kind, 0);
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

    /// Whether the next token is the postfix opener `open` (`(`, `[`, or the
    /// mark `!` / `~` of a call) written right after the token before it
    /// (§2.5, S-89: the arguments of a call, an index, type arguments, the
    /// parameters of a declaration and of an anonymous function, a function
    /// type, a pattern, an attribute, the fields of a variant, the arguments
    /// of a handler, S-412). An opener after a blank or a line break is not
    /// read on: it is recorded with whether the token before ends a path of
    /// names (`by_name`, S-399) and whether an expression is before it
    /// (`expr`), and the grammar fails at it where it fails; the table names
    /// the form there ([`crate::layout::Detached`]). Two openers are read
    /// otherwise: the `(` of `pub(pkg)` and `pub(crate)` across a blank
    /// (one form each, [`Parser::parse_vis`], S-248), and the `(` of the
    /// tuple struct `struct P (I32)` (a form of another language whatever the
    /// blank, the table's `tuple_struct`, W3-08).
    fn touches(&mut self, open: TokenKind, by_name: bool, expr: bool) -> bool {
        let at = self.peek_index();
        if self.tokens[at].kind != open {
            return false;
        }
        if !self.gap(at).is_some() {
            return true;
        }
        // The site that read the opener first judges it: after `with h`,
        // the `handle` expression is no callee, but `h` takes the list.
        if self.detached.is_none_or(|d| d.at != at) {
            self.detached = Some(crate::layout::Detached { at, by_name, expr, required: false });
        }
        false
    }

    /// The opener `open` of a list that is required here (the parameters of
    /// a declaration or an anonymous function, a function type): one that a
    /// blank or a line break keeps apart from the token before it is the
    /// E0020 of [`Parser::touches`], with the gap taken out (S-89, S-412).
    fn opens(&mut self, open: TokenKind) -> PResult<Token> {
        if self.touches(open, true, false) {
            return Ok(self.bump());
        }
        let at = self.peek_index();
        if let Some(d) = self.detached.as_mut().filter(|d| d.at == at) {
            d.required = true;
        }
        Err(self.unexpected(open.describe()))
    }

    /// The closing bracket `close` of a list of `list` after its elements:
    /// any other token is the E0002 of the missing `,` or of what does not go
    /// there ([`Want::Separator`], S-384).
    fn close_list(&mut self, list: NodeKind, close: TokenKind) -> PResult<Token> {
        if self.at(close) {
            return Ok(self.bump());
        }
        Err(self.fail(Want::Separator(list), &format!("`,` or {}", close.describe())))
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
        self.fail(Want::Other, expected)
    }

    /// The one entry of the failures of the parser at the next token, where
    /// it wanted `want` (`expected`, for the message). The table of the forms
    /// of other languages says first whether the token starts such a form
    /// ([`foreign::at_failure`]); else, and also when the form is in a place
    /// where nothing of its kind goes (a literal `1.` among the items), the
    /// failure is the general E0002 (both are reported; the driver chooses
    /// one per unit, S-281).
    fn fail(&mut self, want: Want, expected: &str) -> ParseError {
        self.fail_with(want, expected, None)
    }

    /// [`Parser::fail`], where the general E0002 says what came instead
    /// (`found`, a token after the failure: what follows a `^`) and gives the
    /// correct rule as its note (§18.1: a form of no row whose rule is known,
    /// S-358).
    fn fail_noting(&mut self, want: Want, expected: &str, found: Token, rule: &str) -> ParseError {
        self.fail_with(want, expected, Some((found, rule)))
    }

    fn fail_with(&mut self, want: Want, expected: &str, noted: Option<(Token, &str)>) -> ParseError {
        let at = self.peek_index();
        let t = self.tokens[at];
        // The number of a literal written with a suffix is checked as any
        // integer literal (E0408): two errors of one token, of which the
        // driver reports one.
        if t.kind == TokenKind::ForeignLit {
            let number = foreign::number_part(self.token_text(t));
            if foreign::is_integer(number) && !number.is_empty() && crate::lower::int_value(number).is_none() {
                self.report(Diagnostic::new(
                    Stage::Syntax,
                    Code::E0408,
                    t.span,
                    "integer literal is larger than any integer type holds",
                ));
            }
        }
        let cursor = foreign::Cursor {
            file: self.file,
            text: self.text,
            tokens: &self.tokens,
            all: &self.all,
            full: &self.full,
            holes: &self.holes,
            lexed: &self.lexed_spans,
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
            found: std::cell::Cell::new(None),
        };
        let (row, general) = match foreign::at_failure(&cursor) {
            Some((d, misplaced)) => (Some(d), misplaced),
            None => (None, true),
        };
        // After an element of a list, the general error is the missing `,`;
        // an opener after a line break takes it out (S-89).
        let fixes = match want {
            Want::Separator(list) if general => crate::layout::list_fixes(&cursor, Some(list)),
            _ if general => crate::layout::list_fixes(&cursor, None),
            _ => Vec::new(),
        };
        if let Some(d) = row {
            self.report(d);
        }
        if general {
            let shown = noted.map_or(t, |(found, _)| found);
            let msg = format!("expected {expected}, found {}", shown.kind.describe());
            let mut d = Diagnostic::new(Stage::Syntax, Code::E0002, t.span, msg);
            let found = self.src(shown.span);
            if !found.is_empty() && !found.contains('\n') {
                d = d.with_found(found);
            } else if noted.is_some() {
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
            self.report(d);
        }
        ParseError
    }

    fn expect(&mut self, kind: TokenKind) -> PResult<Token> {
        if self.at(kind) { Ok(self.bump()) } else { Err(self.unexpected(kind.describe())) }
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
            let start = self.peek().span.start;
            let depth = self.open.len();
            let m = self.start_item(doc);
            match self.parse_item(ItemCtx::Top, m) {
                Ok(item) => {
                    self.levels.push(item.height);
                    // Terminator: newline or end of file.
                    match self.peek_kind() {
                        TokenKind::Newline | TokenKind::Eof => {}
                        _ => {
                            // The tokens after the item on its line are of its
                            // unit (`crate::units`, S-274).
                            let _ = self.unexpected("newline after the declaration");
                            self.skip_unit(start, 0, false, true);
                        }
                    }
                }
                Err(ParseError) => {
                    // The item node stays open: the skipped tokens go inside it.
                    self.close_open(depth + 1);
                    self.skip_unit(start, 0, false, false);
                    self.close_open(depth);
                }
            }
        }
        self.complete(root, NodeKind::SourceFile);
        ParseOutput {
            tokens: self.all,
            events: self.events,
            diagnostics: self.diagnostics,
            levels: self.levels,
            height: self.height,
        }
    }

    /// Skip to the end of the unit that starts at `unit_start` after a syntax
    /// error in it (spec §18.1, S-59): the skipped tokens form an `Error` node
    /// in the open node. `base` is the number of brackets open around the
    /// unit (0 for a top-level item, the list's for a `member`). The unit ends:
    ///
    /// - at a token that may start an item at the beginning of a line, once
    ///   the brackets of the unit are closed;
    /// - for a member, before the `}` that closes the list;
    /// - at a keyword that starts an item at the beginning of a line indented
    ///   as much as or less than every line that opened a bracket of the unit
    ///   still open: that bracket is never closed, and the innermost of them
    ///   gets the E0002 (§18.1 for `{`; `(` and `[` alike, S-280). The
    ///   indentation is read only here, in a file with an error. At the end
    ///   of the file, likewise when the reading stopped there (`expected `}`,
    ///   found end of file`); when another error stopped it earlier (E0006,
    ///   ...), the open brackets follow from that error and get no diagnostic
    ///   (2026-10-08, the parent's decision).
    ///
    /// With `line`, the unit is a finished item and the tokens after it on
    /// its line (S-274): the skip also ends at the end of that line, outside
    /// the brackets it opens.
    fn skip_unit(&mut self, unit_start: u32, base: usize, member: bool, line: bool) {
        let mut braces = self.braces.clone();
        let from = self.peek_index();
        let mut i = from;
        let mut unclosed = None;
        loop {
            let t = self.tokens[i];
            if t.kind == TokenKind::Eof {
                // A `{` of the unit still open at the end of the file: it is the
                // error when the reading stopped at the end (below).
                if braces.len() > base {
                    unclosed = braces.last().copied();
                }
                break;
            }
            if line && t.kind == TokenKind::Newline && braces.len() <= base {
                break;
            }
            let line_start = i == 0 || self.tokens[i - 1].kind == TokenKind::Newline;
            if t.span.start > unit_start && line_start && is_item_start(t.kind) {
                if braces.len() <= base {
                    break;
                }
                let indent = self.indent(t.span.start);
                if braces[base..].iter().all(|&b| self.indent(self.tokens[b].span.start) >= indent) {
                    unclosed = braces.last().copied();
                    break;
                }
            }
            if is_opening(t.kind) {
                braces.push(i);
            } else if is_closing(t.kind) && !close_bracket(&mut braces, &self.tokens, t.kind, base) {
                // A `}` that closes no `{` of the member closes the list.
                if t.kind == TokenKind::RBrace && member {
                    break;
                }
            }
            i += 1;
        }
        // An error found at the token where the unit ends (the next item, the
        // end of the file) is this unit's, though that token is not.
        let stop = self.tokens[i].span.start;
        let mut first_at_stop = self.diagnostics.len();
        while first_at_stop > self.lexed && self.diagnostics[first_at_stop - 1].span.start >= stop {
            first_at_stop -= 1;
        }
        let at_end = self.tokens[i].kind == TokenKind::Eof;
        if at_end && first_at_stop == self.diagnostics.len() {
            unclosed = None;
        }
        if let Some(b) = unclosed {
            // It is the unclosed bracket: reported at the bracket, not at that
            // token; once for all the units that end there.
            self.diagnostics.truncate(first_at_stop);
            if self.reported_stop != Some(i) {
                self.reported_stop = Some(i);
                self.unclosed_brace(b, unit_start);
            }
        } else if !at_end {
            // It is reported where the unit stops (`fn f(` before the next
            // `fn`), so that it is of the unit (`crate::units`).
            // SPEC-GAP(S-276): the position of an error found at the token that
            // starts the next item: the end of the unit, as an empty span.
            let end = Span::new(self.file, self.last_end, self.last_end);
            for d in &mut self.diagnostics[first_at_stop..] {
                d.span = end;
                d.found = None;
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

    /// The next token starts an item at the beginning of a line indented as
    /// much as or less than the line of the `{` of the list of members open
    /// around it (`base` brackets), and that `{` is never closed.
    fn list_ends_unclosed(&self, base: usize) -> bool {
        let i = self.peek_index();
        let t = self.tokens[i];
        let Some(&brace) = self.braces[..base].last() else { return false };
        let line_start = i == 0 || self.tokens[i - 1].kind == TokenKind::Newline;
        line_start
            && is_item_start(t.kind)
            && !self.brace_closed[brace]
            && self.indent(t.span.start) <= self.indent(self.tokens[brace].span.start)
    }

    /// The number of blanks before the first token of the line of `at`.
    fn indent(&self, at: u32) -> usize {
        let line = self.text[..at as usize].rfind('\n').map_or(0, |i| i + 1);
        self.text[line..].chars().take_while(|c| *c == ' ' || *c == '\t').count()
    }

    /// E0002 at the bracket (token `b`) that the unit starting at `unit_start`
    /// never closes, with a note on the declaration it is in (§18.1).
    fn unclosed_brace(&mut self, b: usize, unit_start: u32) {
        let brace = self.tokens[b];
        let first = self.tokens.partition_point(|t| t.span.start < unit_start);
        let keyword = (first..b).find(|&k| DECLARATIONS.iter().any(|(kind, _, _)| *kind == self.tokens[k].kind));
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
        self.report(d);
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
            self.skip_newlines_if_followed_by(|k| k == TokenKind::At);
            if self.at(TokenKind::At) {
                self.parse_attr()?;
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
        if self.touches(TokenKind::LParen, true, false) {
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
                p.close_list(NodeKind::AttrArgs, TokenKind::RParen)
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
        self.bump();
        // `pub(pkg)` (S-36: W3-08 makes it E0020 too) and `pub(crate)` (the
        // table's `pub_crate`) are each one form with the blanks in them
        // (S-248): a blank before the `(` is read across, so that the form's
        // row reports it once.
        let words = |p: &Self| ["pkg", "crate"].iter().any(|w| p.is_ident(p.peek2(), w));
        if self.at(TokenKind::LParen) && (!self.peek_gap().is_some() || words(self)) {
            self.bump();
            let t = self.peek();
            if !self.is_ident(t, "pkg") {
                return Err(self.unexpected("`pkg`"));
            }
            self.bump();
            self.expect(TokenKind::RParen)?;
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
        if let Some((_, _, places)) = DECLARATIONS.iter().find(|(k, _, _)| *k == t.kind)
            && !places.contains(&ctx)
        {
            return Err(self.not_a_member(t, ctx));
        }
        if let Some((_, parse, _)) = DECLARATIONS.iter().find(|(k, _, _)| *k == t.kind) {
            parse(self, ctx)?;
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
        let m = self.start(NodeKind::Flow)?;
        self.bump();
        self.parse_name("flow name")?;
        self.parse_params(true)?;
        self.expect(TokenKind::Arrow)?;
        self.parse_type()?;
        self.parse_block_expr()?;
        self.complete(m, NodeKind::Flow);
        Ok(())
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
                p.close_list(NodeKind::FieldList, TokenKind::RBrace)?;
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
                // S-412: the `(` of the fields of a variant follows the
                // rule of the postfix `(` (a blank before it is E0020).
                if p.touches(TokenKind::LParen, true, false) {
                    let f = p.start(NodeKind::VariantFields)?;
                    p.bump();
                    while !p.at(TokenKind::RParen) {
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::VariantFields, TokenKind::RParen)?;
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
            p.close_list(NodeKind::VariantList, TokenKind::RBrace)?;
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
        // The type parameters of `impl` after a blank (`impl [T] P[T]`, S-412)
        // are not read as an array type: a `[` with no `;` in it is the
        // list `touches` did not read.
        let at = self.peek_index();
        if self.detached.is_some_and(|d| d.at == at)
            && crate::layout::bracket_contents(&self.tokens, at).is_some_and(|(_, _, semi)| !semi)
        {
            return Err(self.unexpected("a type"));
        }
        let (first, args) = self.parse_type_ex()?;
        self.parse_clock_opt()?;
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
            if self.eat(TokenKind::Dot).is_none() {
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
                    p.close_list(NodeKind::UseNames, TokenKind::RBrace)?;
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
        let name = self.expect(TokenKind::Str)?;
        self.check_test_name(name);
        self.parse_block_expr()?;
        self.complete(m, NodeKind::Test);
        Ok(())
    }

    /// The name of a `test` (spec §11.8, S-244): a string literal with no
    /// interpolation, not empty, and with no control character, line
    /// separator or bidirectional control in its value
    /// ([`crate::test_name::problem`]). A name that breaks the rule is E0002
    /// of the syntax stage at the literal, with the rule as a note and no fix.
    /// The error does not stop the unit: the body is read, and the item is a
    /// failed one whose body is not checked (S-59).
    ///
    /// A hole is an interpolation whatever its form: the lexer's E0001 on the
    /// form of a hole (`{X}`, which is about the interpolation of an
    /// expression) gives way to the name's E0002. Any other error of the
    /// lexer in the literal (an escape, a hole without its `}`) makes the
    /// literal itself wrong, and the name is not checked further.
    fn check_test_name(&mut self, t: Token) {
        let inside = |s: Span| t.span.start <= s.start && s.end <= t.span.end;
        // The holes are in the order of the file: those of this literal are
        // found by a binary search, not by a walk over all of them.
        let first = self.holes.partition_point(|h| h.start < t.span.start);
        let holes: Vec<Span> = self.holes[first..].iter().copied().take_while(|&h| inside(h)).collect();
        let problem = if holes.is_empty() {
            let from = self.lexed_spans.partition_point(|s| s.start < t.span.start);
            if self.lexed_spans[from..].iter().take_while(|s| s.start < t.span.end).any(|&s| inside(s)) {
                return;
            }
            let lit = crate::lower::str_lit(self.token_text(t), t.span);
            let Some(value) = crate::test_name::value(&lit) else {
                onsa_diag::internal::bug(Some(t.span), "a literal without holes read as one with an interpolation")
            };
            match crate::test_name::problem(&value) {
                Some(p) => p,
                None => return,
            }
        } else {
            let before = self.diagnostics.len();
            let mut i = 0;
            self.diagnostics.retain(|d| {
                let lexer = i < self.lexed;
                i += 1;
                !(lexer && d.code == Code::E0001 && holes.contains(&d.span))
            });
            self.lexed -= before - self.diagnostics.len();
            // `lexed_spans` keeps their spans: they lie in this literal, which
            // no other name shares.
            "the name of a test cannot hold an interpolation".to_string()
        };
        let d = Diagnostic::new(Stage::Syntax, Code::E0002, t.span, problem)
            .with_found(self.src(t.span).to_string())
            .with_rule(crate::test_name::RULE);
        self.report(d);
    }

    /// `{ item NL item NL ... }` for trait / impl / effect / handler / extern bodies.
    fn parse_item_body(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::ItemList)?;
        self.expect(TokenKind::LBrace)?;
        let base = self.braces.len();
        self.with_nl(true, |p| {
            loop {
                let doc = p.collect_docs();
                if p.at(TokenKind::RBrace) {
                    break;
                }
                if p.at(TokenKind::Eof) {
                    return Err(p.unexpected("`}`"));
                }
                // The `{` of the list is never closed, and an item starts on a
                // line indented as much as or less than the line of the `{`:
                // the list ends there, and the item is the next of the file
                // (§18.1). The top-level recovery reports the `{`. A correct
                // program closes every `{`, so its reading does not change.
                if ctx != ItemCtx::InlineHandler && p.list_ends_unclosed(base) {
                    return Err(ParseError);
                }
                let start = p.peek().span.start;
                let depth = p.open.len();
                let item = p.start_item(doc);
                if let Err(e) = p.parse_item(ctx, item) {
                    // A member is a unit of its own (spec §18.1, S-59): the
                    // list goes on after it. The handler written inside an
                    // expression is part of the unit around it.
                    if ctx == ItemCtx::InlineHandler {
                        return Err(e);
                    }
                    p.close_open(depth + 1);
                    p.skip_unit(start, base, true, false);
                    p.close_open(depth);
                    continue;
                }
                match p.peek_kind() {
                    TokenKind::Newline | TokenKind::RBrace => {}
                    _ if ctx == ItemCtx::InlineHandler => return Err(p.unexpected("newline or `}`")),
                    _ => {
                        // The tokens after the member on its line are of its
                        // unit (`crate::units`, S-274).
                        let _ = p.unexpected("newline or `}`");
                        p.skip_unit(start, base, true, true);
                    }
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

    /// `a.b.c` (also accepts `Self` as a segment).
    fn parse_path(&mut self, what: &str) -> PResult<PathInfo> {
        let m = self.start(NodeKind::Path)?;
        let first = self.parse_path_segment(what)?;
        let mut last = first;
        let mut segments = 1;
        loop {
            if self.at(TokenKind::Dot) && (self.peek2().kind == TokenKind::Ident || self.peek2().kind.is_keyword()) {
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
        if !self.touches(TokenKind::LBracket, true, false) {
            return Ok(());
        }
        let m = self.start(NodeKind::GenericParams)?;
        self.bump();
        self.with_nl(false, |p| p.parse_generic_list())?;
        self.complete(m, NodeKind::GenericParams);
        Ok(())
    }

    fn parse_generic_list(&mut self) -> PResult<()> {
        let close = TokenKind::RBracket;
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
        self.close_list(NodeKind::GenericParams, close)?;
        Ok(())
    }

    /// `(params)`; `require_types` is false for anonymous functions (§6.1).
    fn parse_params(&mut self, require_types: bool) -> PResult<()> {
        let m = self.start(NodeKind::ParamList)?;
        // S-412: the `(` after `fn` of an anonymous function follows
        // the rule of the parameters of a declaration (a blank before it is E0020).
        self.opens(TokenKind::LParen)?;
        self.with_nl(false, |p| {
            while !p.at(TokenKind::RParen) {
                let param = p.start(NodeKind::Param)?;
                p.parse_attrs()?;
                p.parse_mode();
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
            p.close_list(NodeKind::ParamList, TokenKind::RParen)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::ParamList);
        Ok(())
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
            p.close_list(NodeKind::EffectRow, TokenKind::RBrace)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::EffectRow);
        Ok(())
    }

    // ------------------------------------------------------------ types

    /// A type and the clock written after it (`F32 at sample`, §11.3): the
    /// clock is read at every type position but the type of `as`
    /// ([`Parser::parse_bare_type`]); after the result of a function type it
    /// is the result's (S-367). Where it goes (the input or output of a
    /// flow or a function) and where it does not (a binding, a type: E0020)
    /// is decided on the tree after parsing (`crate::foreign`, S-356).
    fn parse_type(&mut self) -> PResult<Completed> {
        let c = self.parse_type_ex()?.0;
        self.parse_clock_opt()?;
        Ok(c)
    }

    /// A type with no clock after it: the type of `as`, whose `at` is the
    /// clock of the cast (E0011, §3.1).
    fn parse_bare_type(&mut self) -> PResult<Completed> {
        Ok(self.parse_type_ex()?.0)
    }

    fn parse_clock_opt(&mut self) -> PResult<()> {
        if self.at(TokenKind::KwAt) {
            self.parse_clock()?;
        }
        Ok(())
    }

    /// `at name`: a clock (§11.3). The name is read as it is; which names
    /// are clocks W3-10 looks up (S-359: an unknown one is the names stage's
    /// E0302).
    fn parse_clock(&mut self) -> PResult<()> {
        let m = self.start(NodeKind::Clock)?;
        self.bump();
        self.parse_ident("the name of a clock")?;
        self.complete(m, NodeKind::Clock);
        Ok(())
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
                    p.parse_type()?;
                    let Some(comma) = p.eat(TokenKind::Comma) else {
                        p.close_list(NodeKind::TupleType, TokenKind::RParen)?;
                        return Ok(NodeKind::ParenType);
                    };
                    if p.at(TokenKind::RParen) {
                        return Err(p.one_element(comma));
                    }
                    while !p.at(TokenKind::RParen) {
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::TupleType, TokenKind::RParen)?;
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
                // S-412: the `(` after `fn` in a function type follows the
                // rule of the postfix `(` (a blank before it is E0020).
                self.opens(TokenKind::LParen)?;
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RParen) {
                        p.parse_mode();
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::FnTypeParams, TokenKind::RParen)?;
                    Ok(())
                })?;
                self.complete(l, NodeKind::FnTypeParams);
                if self.eat(TokenKind::Arrow).is_some() {
                    // A clock after the result belongs to the result, as
                    // `uses` does (S-367): a clock in a type, E0020.
                    self.parse_type()?;
                }
                self.parse_effect_row_opt()?;
                self.complete(m, NodeKind::FnType)
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let m = self.start(NodeKind::PathType)?;
                let path = self.parse_path("a type")?;
                // A type name of another language that reads as a name (`i32`):
                // the one form the parser does not fail at by itself.
                if path.segments == 1
                    && let Some(d) = foreign::type_name(self.text, path.first)
                {
                    self.report(d);
                    return Err(ParseError);
                }
                if self.touches(TokenKind::LBracket, true, false) {
                    let a = self.start(NodeKind::TypeArgs)?;
                    self.bump();
                    nargs = self.with_nl(false, |p| p.parse_type_args())?;
                    self.complete(a, NodeKind::TypeArgs);
                }
                self.complete(m, NodeKind::PathType)
            }
            _ => return Err(self.fail(Want::Type, "a type")),
        };
        Ok((c, nargs))
    }

    /// The elements of a list of type arguments after its `[`, and its `]`:
    /// the one reading of the lists of a type position and of `::[…]` in an
    /// expression (§4.5). An empty list is E0002.
    fn parse_type_args(&mut self) -> PResult<usize> {
        let close = TokenKind::RBracket;
        if self.at(close) {
            return Err(self.fail(Want::Type, "a type argument"));
        }
        let mut n = 0;
        while !self.at(close) {
            self.parse_type_arg()?;
            n += 1;
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.close_list(NodeKind::TypeArgs, close)?;
        Ok(n)
    }

    /// A type argument: a type, or a const argument written as a constant
    /// expression (`Ring[F32, 4]`, `Ring[F32, N * 2]`, spec §4.5, S-24,
    /// R-192). The element is a type when it reads as a type and no operator
    /// or postfix goes on after it ([`continues_an_expression`]); else it is
    /// read as an expression, whose constant rules are the later stages'
    /// (E0417, E0401). A constant's name (`TABLE_SIZE`, `cfg.N`) reads as a
    /// type; the later stages take it by the kind of the parameter. What
    /// follows a type is the list's error (`Option[I32 Bool]`: the missing
    /// `,` of a list of type arguments, S-384), and so is the error inside a
    /// list of type arguments the type opened (`Option[Option[I32 Bool]]`;
    /// the expression would read the brackets as an index and lose the list). A type that fails
    /// with a diagnostic of its own (a form of the table, E0020; E0006) keeps
    /// it too.
    fn parse_type_arg(&mut self) -> PResult<()> {
        let s = self.snapshot();
        let as_type = self.parse_type();
        // A type followed by `::` keeps its reading: `Option::[I32]` in a
        // list is the mark in a type position (E0020), and a constant
        // expression with `::[…]` waits for S-329.
        let next = self.peek_index();
        let ends = self.tokens[next].kind == TokenKind::ColonColon
            || !continues_an_expression(self.tokens[next].kind, self.gap(next));
        // A list of type arguments the type opened (`Option[…]`): an
        // expression reads its brackets as an index, so its error stays the
        // type's. Parentheses are not: `(1 + 2) * 3` is a constant.
        let opened_a_list =
            || self.events[s.events..].iter().any(|e| matches!(e, Event::Start { kind: Some(NodeKind::TypeArgs), .. }));
        match as_type {
            Ok(_) if ends => {
                self.end_trial();
                return Ok(());
            }
            // `_` is no type (§2.2) and no constant: `pair::[U8, _]` is E0002 (§4.5).
            Err(ParseError)
                if self.diagnostics[s.diagnostics..].iter().any(|d| d.code != Code::E0002)
                    || opened_a_list()
                    || self.tokens[s.pos..]
                        .iter()
                        .find(|t| !t.kind.is_trivia())
                        .is_some_and(|t| t.kind == TokenKind::Underscore) =>
            {
                self.end_trial();
                return Err(ParseError);
            }
            _ => self.restore(s),
        }
        let m = self.start(NodeKind::ConstArg)?;
        self.parse_expr()?;
        self.complete(m, NodeKind::ConstArg);
        Ok(())
    }

    /// Whether the tokens from the `[` at `open` read as a list of type
    /// arguments with two or more elements (a `[…]` that is no index, §4.5):
    /// a trial reading, undone whatever its result. Not inside another trial.
    fn reads_as_type_list(&mut self) -> bool {
        if self.trials > 0 {
            return false;
        }
        let s = self.snapshot();
        self.bump();
        let n = self.with_nl(false, |p| p.parse_type_args());
        self.restore(s);
        matches!(n, Ok(n) if n >= 2)
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
                    // A range after its start (`for i in move 0..<n`) is read
                    // on, the `move` over the whole range (§7: E0703, of
                    // the modes stage, W4-09); the start is a postfix
                    // expression as any operand of `move` (§5.2).
                    // SPEC-GAP(S-362): `move lo + 1..<hi` is the E0002 of
                    // §5.2, which §7's E0703 for a range does not settle.
                    let mv = self.bump();
                    self.without_node(NodeKind::MoveExpr, mv.span, |p| {
                        let saved = std::mem::replace(&mut p.no_struct_lit, true);
                        let r = p.parse_marked(mv).and_then(|start| p.parse_range_rest(start));
                        p.no_struct_lit = saved;
                        r
                    })?;
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
                if !matches!(self.peek_kind(), TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof) {
                    self.parse_consumed()?;
                }
                Ok(self.complete(m, NodeKind::ReturnStmt))
            }
            // `move a` on the last expression of a block (§5.2, S-100): where
            // the block stands decides the rest (the modes stage).
            TokenKind::KwMove => {
                let expr = self.parse_consumed()?;
                if self.peek_past_newlines().kind != TokenKind::RBrace {
                    return Err(self.error(
                        Code::E0002,
                        t.span,
                        "a `move` statement is written only as the last expression of a block (§5.2)",
                    ));
                }
                let m = self.precede(expr, NodeKind::ExprStmt)?;
                Ok(self.complete(m, NodeKind::ExprStmt))
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

    /// An expression in a consuming position (§5.2, S-21) or where the
    /// function returns (S-100): `move <place>` or a plain expression.
    fn parse_consumed(&mut self) -> PResult<Completed> {
        if !self.at(TokenKind::KwMove) {
            return self.parse_expr();
        }
        let m = self.start(NodeKind::MoveExpr)?;
        let mv = self.bump();
        self.parse_marked(mv)?;
        Ok(self.complete(m, NodeKind::MoveExpr))
    }

    /// The operand of the mark `move` or `inout` (§5.2, R-42): a postfix
    /// expression, never the operand of a binary operator, `as` or `at`
    /// (`move y + 1` is E0002 at the `+`, not `move (y + 1)`).
    fn parse_marked(&mut self, mark: Token) -> PResult<Completed> {
        let prefix = matches!(self.peek_kind(), TokenKind::Minus | TokenKind::Bang);
        let operand = if prefix { None } else { Some(self.parse_postfix()?) };
        let t = self.peek();
        match operand {
            Some(e) if !binop(t.kind) && !matches!(t.kind, TokenKind::KwAs | TokenKind::KwAt) => Ok(e),
            _ => {
                let (mark, op) = (self.token_text(mark), self.token_text(t));
                let what = if prefix { "a prefix" } else { "the operand of" };
                Err(self.error(
                    Code::E0002,
                    t.span,
                    format!("the operand of `{mark}` is a postfix expression (a name and its fields, indexes and calls), not {what} `{op}` (§5.2)"),
                ))
            }
        }
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

    /// Binary chain, flat in the CST (§3.1: the AST reads it as a tree,
    /// `lower.rs`; the groups are checked in `groups.rs`).
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
        if allow_range {
            return self.parse_range_rest(expr);
        }
        Ok(expr)
    }

    /// The rest of a head whose start `expr` is read: a range when a range
    /// symbol follows, else `expr`. A range is the whole expression of a head
    /// and is weaker than the binary operators (§3.1, S-257). Its other
    /// symbols (`..`, `...`) fail at the symbol: the table of the forms of
    /// other languages says what they are (`range_dots`; a range anywhere
    /// else, `range_outside_header`).
    fn parse_range_rest(&mut self, expr: Completed) -> PResult<Completed> {
        if self.peek_kind().range_end().is_some() {
            let m = self.precede(expr, NodeKind::RangeExpr)?;
            self.bump();
            // A `{` after the symbol starts the body (S-338): `parse_primary` says so.
            self.parse_expr_inner(false)?;
            return Ok(self.complete(m, NodeKind::RangeExpr));
        }
        if self.peek_kind().is_foreign_range() {
            return Err(self.unexpected("`..<` or `..=`"));
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

    /// `prefix [as Type | at Clock]*`: a prefix binds tighter than `as` and
    /// `at` (§3.1). A chain of them is read whole and is E0011 (`groups.rs`).
    fn parse_cast(&mut self) -> PResult<Completed> {
        let mut expr = self.parse_prefix()?;
        loop {
            match self.peek_kind() {
                TokenKind::KwAs => {
                    let m = self.precede(expr, NodeKind::CastExpr)?;
                    self.bump();
                    self.parse_bare_type()?;
                    expr = self.complete(m, NodeKind::CastExpr);
                }
                TokenKind::KwAt => {
                    let m = self.precede(expr, NodeKind::AtExpr)?;
                    self.parse_clock()?;
                    expr = self.complete(m, NodeKind::AtExpr);
                }
                _ => return Ok(expr),
            }
        }
    }

    // The tokens `parse_prefix` reads as the start of an operand are those of
    // `starts_operand` (a `debug_assert` in `parse_primary` and the test
    // `operand_starts` hold the two together).
    fn parse_prefix(&mut self) -> PResult<Completed> {
        let t = self.peek();
        if matches!(t.kind, TokenKind::Minus | TokenKind::Bang) {
            let m = self.start(NodeKind::PrefixExpr)?;
            self.bump();
            self.parse_prefix()?;
            return Ok(self.complete(m, NodeKind::PrefixExpr));
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> PResult<Completed> {
        let first = self.peek();
        let mut expr = self.parse_primary()?;
        // The last name of a chain `a.b.C` of names (a struct literal path, S-08).
        let mut chain: Option<Token> = (expr.kind == NodeKind::PathExpr).then_some(first);
        // What the chain is so far, for the callee of a `(` (§6.1).
        let mut links = foreign::CalleeChain::start(expr.kind);
        loop {
            // `.` on the next line continues the expression (§2.5).
            if self.at(TokenKind::Newline) && self.peek_past_newlines().kind == TokenKind::Dot {
                self.skip_newlines();
            }
            let t = self.peek();
            match t.kind {
                TokenKind::LParen => {
                    // A callee not written by name is no item: E0020 here,
                    // `.(` (§6.1, S-191).
                    let by_name = foreign::callee_by_name(expr.kind, links);
                    if !self.touches(TokenKind::LParen, by_name, true) {
                        break;
                    }
                    if !by_name {
                        return Err(self.fail(Want::Callee, "an operator or the end of the expression"));
                    }
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
                }
                TokenKind::Tilde | TokenKind::Bang
                    if self.peek2().kind == TokenKind::LParen
                        && !self.gap(self.peek2_index()).is_some()
                        && (foreign::names_a_path(expr.kind) || expr.kind == NodeKind::TypeArgsExpr) =>
                {
                    if !self.touches(t.kind, true, true) {
                        break;
                    }
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.bump();
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
                }
                TokenKind::Tilde => {
                    return Err(self.fail(Want::Other, "the flow-call mark `name~(args)`, written without spaces"));
                }
                // Type arguments after a path of names (§4.5, S-239): `::[`
                // with no space on either side of `::`. Elsewhere `::` is not
                // read (the forms of other languages, `crate::foreign`).
                TokenKind::ColonColon
                    if crate::token::is_type_args_mark(&self.all, &self.full, &self.tokens, self.peek_index())
                        && foreign::names_a_path(expr.kind) =>
                {
                    let m = self.precede(expr, NodeKind::TypeArgsExpr)?;
                    self.bump();
                    let a = self.start(NodeKind::TypeArgs)?;
                    self.bump();
                    self.with_nl(false, |p| p.parse_type_args())?;
                    self.complete(a, NodeKind::TypeArgs);
                    // The name before the list stays the last name of a chain
                    // (`Pr::[U8] { a: 1 }`).
                    expr = self.complete(m, NodeKind::TypeArgsExpr);
                }
                // The member `.` takes no space on either side inside a line (§2.5, S-203).
                TokenKind::Dot if self.peek_gap() == Gap::Space || self.gap(self.peek2_index()) == Gap::Space => {
                    return Err(self.fail(Want::Postfix, "a member `.` without spaces around it"));
                }
                // `v.(x)`: a call through a function value (§6.1, S-191).
                TokenKind::Dot if self.peek2().kind == TokenKind::LParen => {
                    let m = self.precede(expr, NodeKind::CallExpr)?;
                    self.bump();
                    self.parse_arg_list()?;
                    expr = self.complete(m, NodeKind::CallExpr);
                    chain = None;
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
                // Type arguments of other languages before a call, `f<T>(x)`
                // and `f[A, B](x)` (§4.5): the table says from the tokens
                // whether the brackets are such a list ([`foreign::type_list_ahead`]);
                // the parser fails at them, so `<` is not read as a comparison
                // nor `[A, B]` as an index.
                // In a type (a const argument, an array's length) no `::[` is
                // written, so a `[…]` with `,` is read as an index (R-196).
                TokenKind::Lt | TokenKind::LBracket
                    if foreign::type_list_ahead(&self.tokens, &self.all, &self.full, self.peek_index(), expr.kind)
                        && (self.peek_kind() == TokenKind::Lt || (!self.in_type() && self.reads_as_type_list())) =>
                {
                    return Err(self.fail(Want::Other, "an operator or the end of the expression"));
                }
                TokenKind::LBracket
                    if self.touches(TokenKind::LBracket, foreign::callee_by_name(expr.kind, links), true) =>
                {
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
                        p.close_list(NodeKind::StructLitFields, TokenKind::RBrace)?;
                        Ok(())
                    })?;
                    self.complete(l, NodeKind::StructLitFields);
                    expr = self.complete(m, NodeKind::StructLit);
                    chain = None;
                }
                _ => break,
            }
            links = links.then(expr.kind);
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
                    p.without_node(NodeKind::MoveExpr, mv.span, |p| p.parse_marked(mv))?;
                } else if p.at(TokenKind::KwInout) {
                    let mark = p.bump();
                    p.parse_marked(mark)?;
                } else {
                    p.parse_expr()?;
                }
                p.complete(a, NodeKind::Arg);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.no_struct_lit = saved;
            p.close_list(NodeKind::ArgList, TokenKind::RParen)?;
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
                    "`move` is written only where a value is consumed: let/var initializers, assignment, literal elements, `match move x`, call arguments, and the last expression of a block (§5.2)",
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
            // `^name` (§2.6): a mark of the name, no operator; the `^` after
            // an operand is the binary one. A `^` with no name right after it
            // is E0002 with the rule (S-358).
            TokenKind::Caret => {
                if self.peek2().kind != TokenKind::Ident || self.gap(self.peek2_index()).is_some() {
                    let next = self.peek2();
                    return Err(self.fail_noting(Want::Expr, "a name right after `^`", next, CARET_RULE));
                }
                let m = self.start(NodeKind::FeedbackExpr)?;
                self.bump();
                self.bump();
                return Ok(self.complete(m, NodeKind::FeedbackExpr));
            }
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
            // In a header, a `{` at the start of an expression outside
            // parentheses starts the body (§4.4, S-338), as the `{` of a
            // struct literal does (S-08): a block is written in parentheses.
            TokenKind::LBrace if self.no_struct_lit => {
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0002,
                    t.span,
                    "a `{` at the start of an expression in a header starts the body",
                )
                .with_found("{")
                .with_rule("in the header of `if`, `while`, `match`, `for` and `par`, a `{` at the start of an expression outside parentheses starts the body: a block expression there is written in parentheses, `({ … })`, and a range has both ends, `0..<n` (§3.1, §4.4, §7)");
                self.report(d);
                return Err(ParseError);
            }
            TokenKind::LBrace => return self.parse_block_expr(),
            TokenKind::KwIf => return self.parse_if(None),
            TokenKind::KwMatch => {
                let m = self.start(NodeKind::MatchExpr)?;
                self.bump();
                self.branch_tilde()?;
                if self.at(TokenKind::KwMove) {
                    // `match move x` consumes the value (§7, S-21).
                    let mv = self.start(NodeKind::MoveExpr)?;
                    let mark = self.bump();
                    let saved = std::mem::replace(&mut self.no_struct_lit, true);
                    let inner = self.parse_marked(mark);
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
                        p.parse_consumed()?;
                        p.complete(a, NodeKind::MatchArm);
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::MatchArms, TokenKind::RBrace)?;
                    Ok(())
                })?;
                self.complete(arms, NodeKind::MatchArms);
                return Ok(self.complete(m, NodeKind::MatchExpr));
            }
            // `fn name` declares a function, which is written at the top level
            // or in a list of members: the error is at the `fn`, so that the
            // recovery may start the next unit there (an unclosed `{`, §18.1).
            TokenKind::KwFn if declares_a_function(t.kind, self.peek2().kind) => {
                return Err(self.unexpected("an expression (a function is declared at the top level)"));
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
                // S-412: the `(` after the handler of `with` follows the rule of
                // the postfix `(` (a blank before it is E0020).
                } else if self.touches(TokenKind::LParen, true, false) {
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
                    return Err(self.error(Code::E0002, range.span, "`par` needs a range `a..<b` or `a..=b`"));
                }
                self.parse_block_expr()?;
                return Ok(self.complete(m, NodeKind::ParExpr));
            }
            _ => {
                debug_assert!(!starts_operand(t.kind), "{:?} starts an operand", t.kind);
                return Err(self.fail(Want::Expr, "an expression"));
            }
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
        let first = self.parse_consumed()?;
        let Some(comma) = self.eat(TokenKind::Comma) else {
            if first.kind == NodeKind::MoveExpr {
                let mv = Span::new(self.file, first.span.start, first.span.start + "move".len() as u32);
                return Err(self.error(
                    Code::E0002,
                    mv,
                    "a marked expression stands where it is consumed; it is parenthesized only as an element of a tuple of two or more (§5.2)",
                ));
            }
            self.close_list(NodeKind::TupleExpr, TokenKind::RParen)?;
            return Ok(NodeKind::ParenExpr);
        };
        if self.at(TokenKind::RParen) {
            return Err(self.one_element(comma));
        }
        while !self.at(TokenKind::RParen) {
            self.parse_consumed()?;
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.close_list(NodeKind::TupleExpr, TokenKind::RParen)?;
        Ok(NodeKind::TupleExpr)
    }

    /// E0002 at the `,` after the only element of a parenthesis (`(e,)`,
    /// `(I32,)`, `(p,)`, §2.4, R-43): a tuple has two or more elements.
    fn one_element(&mut self, comma: Token) -> ParseError {
        self.error(
            Code::E0002,
            comma.span,
            "a tuple has two or more elements; `(e)` is a group, and a `,` after the only element is not written (§2.4)",
        )
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
        self.close_list(NodeKind::ArrayExpr, TokenKind::RBracket)?;
        Ok(NodeKind::ArrayExpr)
    }

    /// `if [~] cond { } [else (if … | { })]` (§11.5). `chain` is `None` for
    /// the first `if` of a chain and, for an `if` after `else`, whether the
    /// first one has the `~`: the `~` is written on the first `if` only (a
    /// later one is `else_if_tilde` of the table, S-355), and the chain of an
    /// `if~` ends with an `else` block (E0002 with the rule, S-355).
    fn parse_if(&mut self, chain: Option<bool>) -> PResult<Completed> {
        let m = self.start(NodeKind::IfExpr)?;
        self.expect(TokenKind::KwIf)?;
        let tilde = match chain {
            None => self.branch_tilde()?,
            Some(_) if self.at(TokenKind::Tilde) => {
                return Err(self.fail(Want::Expr, "the condition of `else if`"));
            }
            Some(tilde) => tilde,
        };
        self.parse_head_expr(false)?;
        self.parse_block_expr()?;
        let close_brace_end = self.last_end;
        // `else` must be on the same line as `}` (E0003).
        if self.at(TokenKind::Newline) && self.peek_past_newlines().kind == TokenKind::KwElse {
            let else_tok = self.peek_past_newlines();
            let span = Span::new(self.file, close_brace_end, else_tok.span.start);
            let fix = crate::layout::move_up(
                self.file,
                self.text,
                &self.all,
                "move `else` to the line of the `}`",
                close_brace_end,
                else_tok,
                " ",
            );
            let d =
                Diagnostic::new(Stage::Syntax, Code::E0003, span, "`else` must be on the same line as the closing `}`")
                    .with_found("else")
                    .with_fix(fix);
            self.report(d);
            self.skip_newlines();
        }
        if self.eat(TokenKind::KwElse).is_some() {
            if self.at(TokenKind::KwIf) {
                self.parse_if(Some(tilde))?;
            } else {
                self.parse_block_expr()?;
            }
        } else if tilde {
            // The chain of an `if~` ends without `else` (S-355): E0002 at the
            // `}` of its last block, after which the `else` goes.
            let close = Span::new(self.file, close_brace_end - 1, close_brace_end);
            let d =
                Diagnostic::new(Stage::Syntax, Code::E0002, close, "expected `else` after the last block of an `if~`")
                    .with_found("}")
                    .with_rule(IF_TILDE_ELSE_RULE);
            self.report(d);
            return Err(ParseError);
        }
        Ok(self.complete(m, NodeKind::IfExpr))
    }

    /// The `~` of `if~` and `match~` (§2.6), read when it touches the
    /// keyword. With a blank between them the parser fails at it, and the
    /// table names the form (`space_after_branch_keyword`, S-354).
    fn branch_tilde(&mut self) -> PResult<bool> {
        if !self.at(TokenKind::Tilde) {
            return Ok(false);
        }
        if self.peek_gap().is_some() {
            return Err(self.fail(Want::Expr, "the condition, after a `~` written without a blank"));
        }
        self.bump();
        Ok(true)
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

    /// After a `-` in a pattern: `(`s and a `-` (`-(-1)`, S-227).
    fn negated_negative(&self) -> bool {
        let mut kinds = self.tokens[self.peek_index() + 1..].iter().map(|t| t.kind).filter(|k| !k.is_trivia());
        let mut opens = 0;
        loop {
            match kinds.next() {
                Some(TokenKind::LParen) => opens += 1,
                Some(TokenKind::Minus) => return opens > 0,
                _ => return false,
            }
        }
    }

    /// What follows the pattern being read: `=>` in an arm of `match`, `=`
    /// in a `let`, `in` in a `for` (the words of a failure in it).
    fn pattern_end(&self) -> &'static str {
        let owner = self.open.iter().rev().find_map(|o| match self.events[o.event as usize] {
            Event::Start { kind: Some(k @ (NodeKind::MatchArm | NodeKind::LetStmt | NodeKind::ForStmt)), .. } => {
                Some(k)
            }
            _ => None,
        });
        match owner {
            Some(NodeKind::LetStmt) => "`=`",
            Some(NodeKind::ForStmt) => "`in`",
            _ => "`=>`",
        }
    }

    /// Whether the string literal `t` interpolates (`{x}`, §2.4).
    fn has_holes(&self, t: Token) -> bool {
        foreign::guard::interpolated(self.file, self.text, &self.holes, t)
    }

    fn parse_pattern_alt(&mut self) -> PResult<Completed> {
        let t = self.peek();
        // A range (`1..<3`, `..=5`, `lo..<n + 1`; spec §7): no pattern. The
        // table of the forms reads it from its first token (the guard form).
        let rest =
            self.tokens[self.pos..].iter().map(|t| t.kind).filter(|k| !k.is_trivia() || *k == TokenKind::Newline);
        if pattern_alternative(rest).1.is_some() {
            return Err(self.fail(Want::Pattern, "a pattern"));
        }
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
            // `-(-1)` is no literal (S-227, R-156).
            TokenKind::Minus if self.negated_negative() => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "a pattern's `-` is on an integer literal or a constant; `-(-1)` is neither (§7)",
                ));
            }
            TokenKind::Int => {
                let m = self.start(NodeKind::LitPat)?;
                self.bump();
                self.check_int(t);
                return Ok(self.complete(m, NodeKind::LitPat));
            }
            // A string with an interpolation makes a value: no pattern (§7, S-225).
            TokenKind::Str if self.has_holes(t) => return Err(self.fail(Want::Pattern, "a pattern")),
            TokenKind::Char | TokenKind::Str | TokenKind::KwTrue | TokenKind::KwFalse => NodeKind::LitPat,
            // `()`, `(p)` (a group, §2.4, R-43) or `(p, q, ...)`.
            TokenKind::LParen => {
                let m = self.start(NodeKind::TuplePat)?;
                self.bump();
                let kind = self.with_nl(false, |p| {
                    if p.eat(TokenKind::RParen).is_some() {
                        return Ok(NodeKind::TuplePat);
                    }
                    p.parse_pattern()?;
                    let Some(comma) = p.eat(TokenKind::Comma) else {
                        p.close_list(NodeKind::TuplePat, TokenKind::RParen)?;
                        return Ok(NodeKind::ParenPat);
                    };
                    if p.at(TokenKind::RParen) {
                        return Err(p.one_element(comma));
                    }
                    while !p.at(TokenKind::RParen) {
                        p.parse_pattern()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::TuplePat, TokenKind::RParen)?;
                    Ok(NodeKind::TuplePat)
                })?;
                return Ok(self.complete(m, kind));
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let m = self.start(NodeKind::PathPat)?;
                let path = self.parse_path("a pattern")?;
                if self.touches(TokenKind::LParen, true, false) {
                    self.reshape(NodeKind::TupleStructPat)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RParen) {
                            p.parse_pattern()?;
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.close_list(NodeKind::TupleStructPat, TokenKind::RParen)?;
                        Ok(())
                    })?;
                    return Ok(self.complete(m, NodeKind::TupleStructPat));
                }
                if self.at(TokenKind::LBrace) && crate::naming::is_type_name(self.token_text(path.last)) {
                    self.reshape(NodeKind::StructPat)?;
                    self.bump();
                    self.with_nl(false, |p| {
                        while !p.at(TokenKind::RBrace) {
                            // The rest `..`, last (§7: the stage that counts the
                            // fields reports it, S-109, S-366).
                            if p.at(TokenKind::DotDot) {
                                let r = p.start(NodeKind::StructPatRest)?;
                                p.bump();
                                p.complete(r, NodeKind::StructPatRest);
                                break;
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
                        p.close_list(NodeKind::StructPat, TokenKind::RBrace)?;
                        Ok(())
                    })?;
                    return Ok(self.complete(m, NodeKind::StructPat));
                }
                // `n @ p` (§7, S-186): no pattern; the table reads it at `@`.
                if self.at(TokenKind::At) {
                    let after = self.pattern_end();
                    return Err(self.fail(Want::Pattern, after));
                }
                let bind = path.segments == 1 && crate::naming::is_binding_name(self.token_text(path.first));
                return Ok(self.complete(m, if bind { NodeKind::BindPat } else { NodeKind::PathPat }));
            }
            _ => return Err(self.fail(Want::Pattern, "a pattern")),
        };
        let m = self.start(kind)?;
        self.bump();
        Ok(self.complete(m, kind))
    }
}

/// Whether a token of `kind` after `gap` goes on with an expression before
/// it: a binary operator, a range symbol (whose place the table judges,
/// `range_outside_header`), `as`, a member `.`, `?`, or a postfix opener
/// written right after it (a type argument, [`Parser::parse_type_arg`]).
fn continues_an_expression(kind: TokenKind, gap: Gap) -> bool {
    use TokenKind::*;
    binop(kind)
        || !kind.range_readings().is_empty()
        || matches!(kind, KwAs | Dot | Question)
        || (matches!(kind, LParen | LBracket | Bang | Tilde) && gap == Gap::None)
}

fn binop(kind: TokenKind) -> bool {
    crate::lower::binop(kind).is_some()
}

/// The alternative of a pattern whose tokens (no comment; newlines kept)
/// are `kinds`: where it ends (the first `|`, `if`, `=>`, `,`, `@`, `:`,
/// `=`, `in` or newline outside brackets, a closing bracket of none of its
/// own, or the end of the file) and the first range symbol outside brackets
/// before that, as positions among the tokens that are no newline (spec §7,
/// S-341: the ends of a range pattern are read as the ends of a range in a
/// header, and end there). The newlines before the alternative do not end
/// it, nor one after a binary operator (§2.5, as in an expression). The one
/// reading of a range in a pattern: the parser fails at it, and the table
/// of the forms reads its ends ([`crate::foreign`]).
pub(crate) fn pattern_alternative(kinds: impl Iterator<Item = TokenKind>) -> (usize, Option<usize>) {
    use TokenKind::*;
    let mut depth = 0u32;
    let mut range = None;
    let mut n = 0;
    let mut last = Eof;
    for k in kinds {
        match k {
            Newline if n == 0 || depth > 0 || binop(last) => continue,
            Eof | Newline => break,
            LParen | LBracket | LBrace => depth += 1,
            RParen | RBracket | RBrace if depth == 0 => break,
            RParen | RBracket | RBrace => depth -= 1,
            Pipe | KwIf | FatArrow | Comma | At | Colon | Eq | KwIn if depth == 0 => break,
            _ if depth == 0 && range.is_none() && !k.range_readings().is_empty() => range = Some(n),
            _ => {}
        }
        last = k;
        n += 1;
    }
    (n, range)
}

/// Whether the tokens `all[first..=last]` of a file are one expression,
/// read as an end of a range in a header (no struct literal and no block
/// at its start, §4.4, S-338; newlines not significant): the ends of a
/// range pattern (§7, S-341), read by the parser's own grammar (one
/// reading). Its diagnostics are not kept.
pub(crate) fn reads_as_expr(
    file: FileId,
    text: &str,
    all: &[Token],
    holes: &[Span],
    first: usize,
    last: usize,
) -> bool {
    let mut tokens = all[first..=last].to_vec();
    let end = all[last].span.end;
    tokens.push(Token { kind: TokenKind::Eof, span: Span::new(file, end, end) });
    let (from, to) = (all[first].span.start, end);
    let holes = holes.iter().copied().filter(|h| from <= h.start && h.end <= to).collect();
    let mut p = Parser::new(file, text, crate::Lexed { tokens, diagnostics: Vec::new(), holes });
    p.nl = vec![false];
    p.no_struct_lit = true;
    p.parse_expr_inner(false).is_ok() && p.at(TokenKind::Eof) && p.diagnostics.is_empty()
}

/// The height of a binary chain read as the tree of §3.1 (spec §2.5), one
/// level per operator: the one reading of a chain ([`crate::ast::Chain`]),
/// with heights for its nodes.
pub(crate) struct Chain(crate::ast::Chain<u32, crate::ast::OpGroup>);

fn tighter(op: crate::ast::OpGroup, waiting: crate::ast::OpGroup) -> bool {
    op.stronger(waiting)
}

fn join(left: u32, _: crate::ast::OpGroup, right: u32) -> u32 {
    left.max(right) + 1
}

impl Chain {
    pub(crate) fn new(first: u32) -> Chain {
        Chain(crate::ast::Chain::new(first))
    }

    /// An operator of `group` after the last operand. Returns how many
    /// operators wait then, this one included, and the height of its left
    /// operand.
    pub(crate) fn operator(&mut self, group: crate::ast::OpGroup) -> (u32, u32) {
        let (waiting, left) = self.0.operator(group, tighter, join);
        (waiting as u32, left)
    }

    pub(crate) fn operand(&mut self, height: u32) {
        self.0.operand(height);
    }

    /// The height of the whole chain.
    pub(crate) fn height(self) -> u32 {
        self.0.finish(join)
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

/// A bracket that opens: `(`, `[`, `{`.
fn is_opening(kind: TokenKind) -> bool {
    matches!(kind, TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace)
}

/// A bracket that closes: `)`, `]`, `}`.
fn is_closing(kind: TokenKind) -> bool {
    matches!(kind, TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
}

/// Close the innermost bracket of `open` (above `base`) that a closing
/// bracket of `kind` matches, with the brackets opened inside it and left
/// open (`f(a }` closes the `{` and the `(`). `false` when none matches.
fn close_bracket(open: &mut Vec<usize>, tokens: &[Token], kind: TokenKind, base: usize) -> bool {
    let opening = match kind {
        TokenKind::RParen => TokenKind::LParen,
        TokenKind::RBracket => TokenKind::LBracket,
        _ => TokenKind::LBrace,
    };
    match open[base.min(open.len())..].iter().rposition(|&b| tokens[b].kind == opening) {
        Some(k) => {
            open.truncate(base + k);
            true
        }
        None => false,
    }
}

/// A token that starts an item: a declaration keyword, `pub`, an attribute, a doc comment.
fn is_item_start(kind: TokenKind) -> bool {
    DECLARATIONS.iter().any(|(k, _, _)| *k == kind)
        || matches!(kind, TokenKind::KwPub | TokenKind::At | TokenKind::DocComment)
        // An attribute of another language, `#[x]` (the table of those
        // forms), starts an item as `@` does (§18.1, S-321).
        || kind == TokenKind::Hash
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
        assert_eq!(body("let a = x +\n  y"), "(block (let a = (+ x y)))");
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
        assert_eq!(body("a.f!=b"), "(block tail (!= (. a f) b))");
        assert_eq!(body("!(a && b)"), "(block tail (not ((&& a b))))");
        // A blank between the name and its mark (S-123, `space_before_tilde`).
        assert_eq!(codes("fn f() {\n  saw ~(f0)\n}"), vec![Code::E0020]);
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
            "(block tail (if (== s (. Shape Circle)) (block tail 1) else (block tail 2)))"
        );
        assert_eq!(
            body("if f(Point { x: 1.0 }) { 1 } else { 2 }"),
            "(block tail (if (call f ((struct Point x: 1.0))) (block tail 1) else (block tail 2)))"
        );
        assert_eq!(body("while x { }"), "(block (while x (block)))");
    }

    #[test]
    fn ranges_only_in_heads() {
        assert_eq!(body("for i in 0..<n { }"), "(block (for i in (range 0 ..< n) (block)))");
        assert_eq!(body("for i in 0..=n { }"), "(block (for i in (range 0 ..= n) (block)))");
        // Weaker than the binary operators (§3.1).
        assert_eq!(body("for i in a + 1..<n * 2 { }"), "(block (for i in (range (+ a 1) ..< (* n 2)) (block)))");
        assert_eq!(
            body("let s = par i in 0..<N { f~(i) }"),
            "(block (let s = (par i in 0..<N (block tail (call~ f (i))))))"
        );
        assert_eq!(
            body("let s = par i in 0..=N { f~(i) }"),
            "(block (let s = (par i in 0..=N (block tail (call~ f (i))))))"
        );
        // A range is the whole head (§3.1): in parentheses or an argument it
        // is outside the head (`range_outside_header`, E0002 with the note).
        let outside = |src: &str| {
            let p = parse(&format!("fn f() {{\n  {src}\n}}"));
            assert_eq!(codes_of(&p), [Code::E0002], "{src}");
            let d = &p.diagnostics[0];
            assert!(d.fixes.is_empty() && d.message.contains("`for` and `par` heads"), "{src}: {d:?}");
            assert!(d.notes.iter().any(|n| n.message.contains("xs.slice(from, to)")), "{src}: {d:?}");
            d.found.clone().unwrap_or_default()
        };
        assert_eq!(outside("let r = 0..<n"), "..<");
        assert_eq!(outside("let r = 0..=n"), "..=");
        assert_eq!(outside("let r = 0..n"), "..");
        assert_eq!(outside("let r = xs[1...3]"), "...");
        assert_eq!(outside("for i in (0..<4) { }"), "..<");
        assert_eq!(outside("for i in f(0..<3) { }"), "..<");
        assert_eq!(outside("while 0..<4 { }"), "..<");
        // A symbol after a range in a head: the general E0002, no candidate.
        let p = parse("fn f() {\n  for i in 0..<4..5 { }\n}");
        assert_eq!(codes_of(&p), [Code::E0002]);
        assert!(
            p.diagnostics[0].fixes.is_empty() && !p.diagnostics[0].message.contains("heads"),
            "{:?}",
            p.diagnostics
        );
        // The candidates of `..` for every end that starts an operand; none
        // for a range of one side (S-278).
        for end in
            ["n", "-n", "!n", "(n)", "[n][0]", "if c { 1 } else { 2 }", "match c { _ => 1 }", "'a'", "\"a\"", "_"]
        {
            let p = parse(&format!("fn f() {{\n  for i in 0..{end} {{ }}\n}}"));
            assert_eq!(p.diagnostics[0].code, Code::E0020, "{end}");
            assert_eq!(p.diagnostics[0].fixes.len(), 2, "{end}");
        }
        let p = parse("fn f() {\n  for i in 0.. { }\n}");
        assert!(p.diagnostics[0].fixes.is_empty(), "{:?}", p.diagnostics);
    }

    /// `starts_operand` is the set of tokens `parse_primary` and
    /// `parse_prefix` read as the start of an operand.
    #[test]
    fn operand_starts() {
        let operands = [
            "-x",
            "!x",
            "1",
            "1.0",
            "'a'",
            "\"s\"",
            "true",
            "false",
            "_",
            "x",
            "self",
            "Self",
            "(x)",
            "[x]",
            "{ x }",
            "if c { 1 } else { 2 }",
            "match x { _ => 1 }",
            "fn(x: U32) -> U32 { x }",
            "unsafe { x }",
            "handle { x } with h",
            "par i in 0..<2 { x }",
        ];
        for src in operands {
            let p = parse(&format!("fn f() {{\n  let a = {src}\n}}"));
            let first = crate::lex(FileId(0), src).tokens.into_iter().find(|t| !t.kind.is_trivia()).unwrap();
            assert!(super::starts_operand(first.kind), "{src}");
            assert!(
                p.diagnostics.iter().all(|d| d.span.start as usize > "fn f() {\n  let a = ".len()),
                "{src}: {:?}",
                p.diagnostics
            );
        }
        for src in ["..<", "..", ".", ",", ")", "}", "=>", "+", "*", "move", "rt", "@", "<"] {
            let first = crate::lex(FileId(0), src).tokens.into_iter().find(|t| !t.kind.is_trivia()).unwrap();
            assert!(!super::starts_operand(first.kind), "{src}");
        }
    }

    #[test]
    fn struct_pattern_rest_dots() {
        // `..` last is read (S-366: the stage that counts the fields reports it);
        // `...`, and `..` before another field, are no struct pattern.
        let p = parse("struct P { x: U32, y: U32 }\nfn f(p: P) -> U32 {\n  match p {\n    P { x: a, .. } => a\n  }\n}");
        assert_eq!(codes_of(&p), [], "{:?}", p.diagnostics);
        for rest in ["x: a, ...", ".., x: a", "x: a, ..,"] {
            let p = parse(&format!(
                "struct P {{ x: U32, y: U32 }}\nfn f(p: P) -> U32 {{\n  match p {{\n    P {{ {rest} }} => a\n  }}\n}}"
            ));
            assert_eq!(codes_of(&p), [Code::E0002], "{rest}");
        }
    }

    #[test]
    fn precedence() {
        assert_eq!(body("-x.abs()"), "(block tail (neg (call (. x abs) ())))");
        assert_eq!(body("-x as F64"), "(block tail (as (neg x) F64))");
        assert_eq!(body("a + (x as F64)"), "(block tail (+ a ((as x F64))))");
        assert_eq!(body("x?.y"), "(block tail (. (try x) y))");
    }

    #[test]
    fn patterns() {
        assert_eq!(body("let (a, b) = p"), "(block (let (tuple a b) = p))");
        assert_eq!(
            body("match v { Some(x) if x > 0 => x, None => 0, }"),
            "(block tail (match v Some(x) if (> x 0) => x None => 0))"
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
    fn a_form_of_another_language_fails_its_unit() {
        // R-87 (4): the first form stops the unit (the table of the forms,
        // `crate::foreign`, makes the diagnostic); the next unit is read.
        let p = parse("fn f() {\n  let x = 1;\n  let y = 2;\n}\nfn g(x: i32, y: i32) { }\nfn h() { }\n");
        assert_eq!(codes_of(&p), [Code::E0020, Code::E0020]);
        let d = dump(&p.ast);
        assert!(d.contains("(failed:body fn f()") && d.contains("(fn h()"), "{d}");
        assert_eq!(codes("fn f() {\n  for i in 0..n { }\n}"), vec![Code::E0020]);
    }

    #[test]
    fn first_error_per_item_and_recovery() {
        let src = "fn a() {\n  let = 1\n  let = 2\n}\nfn b() { 1 }\nfn c() {\n  )\n}\n";
        let p = parse(src);
        let lines: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
        // One parse error per unit: the parser stops at the first one of `a` (S-59).
        assert_eq!(p.diagnostics.len(), 2, "{lines:?}");
        // The failed items stay, by their name, with their body unread (R-71).
        assert_eq!(
            dump(&p.ast),
            "(failed:body fn a()\n  <error>)\n(fn b()\n  (block\n    tail 1))\n(failed:body fn c()\n  <error>)\n"
        );
        // The diagnostics are not reduced here (the driver chooses one per unit).
        let p = parse("fn a() {\n  let s = \"abc\n  let = 1\n}");
        assert_eq!(p.diagnostics[0].code, Code::E0001);
    }

    #[test]
    fn an_unclosed_brace_ends_at_an_item_keyword_indented_as_its_line() {
        // §18.1: the E0002 is at the `{` that is never closed, with a note on the declaration;
        // the error at the next item is that brace, and `g` is read.
        let src = "fn f() -> I32 {\n  if c {\n    1\n  }\nfn g() {}\n";
        let p = parse(src);
        let ds: Vec<(Code, &str)> =
            p.diagnostics.iter().map(|d| (d.code, &src[d.span.start as usize..d.span.end as usize])).collect();
        assert_eq!(ds, [(Code::E0002, "{")]);
        assert_eq!(p.diagnostics[0].span.start, 14);
        let note = p.diagnostics[0].notes.iter().find(|n| n.span.is_some()).unwrap();
        assert_eq!(note.message, "it is in the body of `f`");
        assert!(dump(&p.ast).contains("(fn g()"));
        // A line indented deeper than the `{` is not a place to end it.
        let p = parse("fn f() -> I32 {\n  1 +\n    fn g() {}\n");
        assert!(p.diagnostics.iter().all(|d| d.message != "this `{` is never closed"));
        // In an `impl`, by the member.
        let src = "impl P {\n  fn a(self) {\n    1\n\n  fn b(self) {}\n}\nfn c() {}\n";
        let p = parse(src);
        assert_eq!(p.diagnostics.len(), 1);
        assert_eq!(&src[p.diagnostics[0].span.start as usize..][..1], "{");
        assert_eq!(p.diagnostics[0].span.start, 22);
        let d = dump(&p.ast);
        assert!(d.contains("fn b(self)") && d.contains("(fn c()"), "{d}");
    }

    #[test]
    fn an_unclosed_list_of_members_ends_at_an_item_keyword_indented_as_its_line() {
        // The `{` of the `impl` is never closed: `after` is an item of the file (§18.1).
        let src = "impl S {\n  fn m(self) -> I32 {\n    1\n  }\n\nfn after() -> I32 { 5 }\n";
        let p = parse(src);
        let ds: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
        assert_eq!(ds, [(Code::E0002, 7)]);
        assert!(dump(&p.ast).contains("\n(fn after()"), "{}", dump(&p.ast));
        // The member's `{` is not closed either: the innermost is reported, once.
        let src = "impl S {\n  fn m(self) -> I32 {\n    1\n\nfn after() -> I32 { 5 }\n";
        let p = parse(src);
        let ds: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
        assert_eq!(ds, [(Code::E0002, 29)]);
        assert!(dump(&p.ast).contains("\n(fn after()"), "{}", dump(&p.ast));
        // A correct program whose members are not indented reads as before.
        assert!(codes("impl S {\nfn m(self) -> I32 { 1 }\n}\n").is_empty());
    }

    #[test]
    fn an_unclosed_parenthesis_ends_at_an_item_keyword_indented_as_its_line() {
        // S-280: an item keyword indented deeper than the line of an open `(` is not the end.
        let src = "pub flow v(\n  g: Sig[F32] oops,\n  @param(min: 1.0)\n  f0: Ctl[F32],\n) -> Sig[F32] {\n  g\n}\nfn after() -> I32 { 1 }\n";
        let p = parse(src);
        assert_eq!(codes_of(&p), [Code::E0002]);
        assert!(dump(&p.ast).contains("(fn after()"));
        // One at the indentation of its line ends it, and the `(` is reported.
        let src = "fn f(a: I32,\nfn g() {}\n";
        let p = parse(src);
        assert_eq!(p.diagnostics.iter().map(|d| d.message.as_str()).collect::<Vec<_>>(), ["this `(` is never closed"]);
        assert!(dump(&p.ast).contains("(fn g()"));
    }

    #[test]
    fn an_unclosed_brace_at_the_end_of_the_file() {
        // The reading stopped at the end of the file: the `{` of `f` is the error.
        let src = "fn f() -> I32 {\n  if c {\n    1\n  }\n";
        let p = parse(src);
        assert_eq!(codes_of(&p), [Code::E0002]);
        assert_eq!(p.diagnostics[0].span.start, 14);
        // Another error stopped it earlier: the open `{` follow from it, no diagnostic.
        let p = parse("fn f() -> I32 {\n  let = 1\n");
        assert_eq!(
            p.diagnostics.iter().map(|d| d.message.as_str()).collect::<Vec<_>>(),
            ["expected a pattern, found `=`"]
        );
    }

    #[test]
    fn a_member_is_a_unit_of_the_recovery() {
        // S-59: an error in a member does not stop the list.
        let p = parse("impl P {\n  fn a(self) {\n    let = 1\n  }\n  fn b(self) {\n    let = 2\n  }\n}\n");
        assert_eq!(codes_of(&p), [Code::E0002, Code::E0002]);
        // `fn name` is not a closure: the error is at the `fn`, where the next unit starts.
        let p = parse("fn f() {\n  let x = 1\nfn g() {}\n");
        assert!(dump(&p.ast).contains("(fn g()"), "{}", dump(&p.ast));
        // The tokens after an item on its line are its unit's (S-274); the next line is not.
        let p = parse("fn a() {} ) ]\nfn b() {}\n");
        assert!(dump(&p.ast).contains("(fn b()"));
        assert_eq!(codes_of(&p), [Code::E0002]);
    }

    fn codes_of(p: &crate::Parsed) -> Vec<Code> {
        p.diagnostics.iter().map(|d| d.code).collect()
    }

    #[test]
    fn literals() {
        assert_eq!(body("let s = \"a\\nb {{x}} {p.q}\""), "(block (let s = \"a\\nb {{x}} {p.q}\"))");
        assert_eq!(body("let c = '\\u{1F600}'"), "(block (let c = '\\u{1f600}'))");
        assert_eq!(body("let n = 0xFF + 1_000"), "(block (let n = (+ 255 1000)))");
        assert_eq!(codes("fn f() {\n  let n = 99999999999999999999\n}"), vec![Code::E0408]);
        assert_eq!(body("Ok(())"), "(block tail (call Ok ((tuple))))");
    }

    #[test]
    fn closures_and_args() {
        assert_eq!(
            body("xs.map(fn(x) { x * 2.0 })"),
            "(block tail (call (. xs map) ((fn(x) (block tail (* x 2.0))))))"
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
        // Where the function returns and on the last expression of a block (S-100).
        assert!(codes("fn f(move b: U32) -> U32 {\n  return move b\n}\n").is_empty());
        assert!(codes("fn f(move b: U32) -> U32 {\n  move b\n}\n").is_empty());
        assert!(
            codes("fn f(c: Bool, move b: U32) -> U32 {\n  let y = if c { move b } else { 1 }\n  y\n}\n").is_empty()
        );
        // Elsewhere it is E0002: an operand, a head, a group, a statement that is no block's last.
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  let y = 1 + move b\n  y\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: Bool) -> U32 {\n  if move b { 1 } else { 2 }\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  let y = (move b)\n  y\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  move b\n  1\n}\n"), vec![Code::E0002]);
    }
}
