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
//! two tokens is read from the line facts, [`crate::layout::Lines`]). A token it consumes is an
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
//! ([`Parser::skip_unit`]), and continues with the next unit. The head of a
//! declaration, up to its keyword, is read on after a form there that ends
//! on its line (§18.1, S-435: `heading`), so that the declaration is a name
//! of its module.
//!
//! Where the code is: this module holds the types (`Parser`, [`Parsed`], the
//! markers of the nodes), the construction of the parser, the nodes, the
//! cursor and the diagnostics, and the helpers that several parts read
//! (`DECLARATIONS`, the brackets, `binop`). The grammar is in a module per
//! part, each an `impl` of `Parser`: `file` (the file, the units and the
//! recovery), `heading` (the head of a declaration before its keyword),
//! `items` (the declarations), `signatures`, `types`,
//! `statements` (the blocks and the statements), `expressions` (with
//! `reads_as_expr`) and `patterns`; `chain` is `Chain`, the height of a
//! binary chain. The tests are `parser_tests.rs`.

use onsa_diag::{Code, Diagnostic, FileId, Fix, Span, Stage};

use crate::ast::Ast;
use crate::attrs::Place;
use crate::callee::Callee;
use crate::cst::{Class, Cst, Event, NodeKind};
use crate::foreign::{self, Detached, End, Want};
use crate::layout::Lines;
use crate::literal::Literals;
use crate::lower::AstMap;
use crate::scan::pattern_alternative;
use crate::starts::{declares_a_function, starts_operand};
use crate::token::{Gap, Token, TokenKind};

mod chain;
mod expressions;
mod file;
mod heading;
mod items;
mod patterns;
mod signatures;
mod statements;
mod types;

pub(crate) use chain::Chain;
pub(crate) use expressions::reads_as_expr;
pub(crate) use types::{reads_as_type, reads_as_type_list};

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
    /// The facts of the literals, from the lexer: the AST takes the paths of
    /// the holes from them.
    pub literals: Literals,
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
    /// The holes of the string literals and the lexer's errors in them
    /// ([`Literals`]).
    literals: Literals,
    /// The levels of each top-level item that parsed.
    levels: Vec<u32>,
    /// How many trial readings ([`Parser::snapshot`]) are open: a reading
    /// that is tried inside another one does not try the brackets of a
    /// call's type arguments again, so trials nest at most once per level.
    trials: u32,
    /// The line facts of `tokens` (§2.5): the gaps around each token and the
    /// line breaks that go on with their line ([`Lines`]).
    lines: Lines,
    /// The last postfix opener not read on because of a gap before it
    /// ([`Parser::touches`], S-89): the table reads it at the failure there.
    detached: Option<Detached>,
    /// The last tokens of the statements and declarations that end no operand
    /// (`for`, `while`, a declaration but `const` and `type`) or a bound value
    /// (`let`, `var`, an assignment), in order: a symbol at the head of the
    /// next line does not go on with the first, and a `=` not with the second
    /// (S-124, S-374, S-236; the table reads them, [`foreign::Cursor::ends`]).
    ends: Vec<(usize, End)>,
    /// The ranges of the literals right against a name whose form the row
    /// `string_prefix` reported ([`foreign::Failure::prefixed`]), kept and
    /// dropped with the diagnostics: the held errors of the others are
    /// reported after the file is read ([`Parser::release_held`]).
    prefixed: Vec<Span>,
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
    detached: Option<Detached>,
    ends: usize,
    prefixed: usize,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(file: FileId, text: &'a str, lexed: crate::Lexed) -> Parser<'a> {
        let crate::Lexed { tokens: all, diagnostics, literals } = lexed;
        let (tokens, full, lines) = crate::layout::code_tokens(&all);
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
            lines,
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
            diagnostics,
            literals,
            levels: Vec::new(),
            trials: 0,
            detached: None,
            ends: Vec::new(),
            prefixed: Vec::new(),
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
            ends: self.ends.len(),
            prefixed: self.prefixed.len(),
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
        self.ends.truncate(s.ends);
        self.prefixed.truncate(s.prefixed);
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
                if k.class() == Class::Type)
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
            SourceFile | Error | Name | Item | Docs | ModuleDocs | Attr | AttrArgs | AttrNamedArg | Vis | Fn | Flow
            | Struct | FieldList | Field | Derives | Enum | VariantList | Variant | VariantFields | TypeAlias
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
        use NodeKind::*;
        let split = match (kind, kind.class()) {
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

    /// Index of the next token that is not trivia under the current context:
    /// where a newline is significant, a newline that goes on with the line
    /// is trivia too ([`Lines::goes_on`], §2.5).
    fn peek_index(&self) -> usize {
        self.skip_trivia(self.pos)
    }

    /// The first token from `i` that is not trivia under the current context.
    fn skip_trivia(&self, mut i: usize) -> usize {
        loop {
            match self.tokens[i].kind {
                k if k.is_line_comment() => i += 1,
                TokenKind::Newline if !self.significant() || self.lines.goes_on(i) => i += 1,
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

    /// The next token is a member `.` with a blank before it, or a blank or a
    /// line break after it (§2.5, S-203, S-353): the one test, for the chain
    /// of an expression and for a path (a type, a pattern, a `use`, an
    /// `impl`). The parser fails at it ([`Want::Postfix`]), and the table names
    /// the form (`space_around_dot`, `newline_after_dot`).
    fn dot_apart(&self) -> bool {
        let i = self.peek_index();
        self.tokens[i].kind == TokenKind::Dot && (self.gap(i) == Gap::Space || self.gap_after(i).is_some())
    }

    /// The token after `tokens[i]`, newlines and comments skipped.
    fn next_code(&self, i: usize) -> usize {
        let mut j = i + 1;
        while j + 1 < self.tokens.len()
            && (self.tokens[j].kind == TokenKind::Newline || self.tokens[j].kind.is_line_comment())
        {
            j += 1;
        }
        j.min(self.tokens.len() - 1)
    }

    /// What separates `tokens[i]` from the token after it ([`Lines::after`]).
    fn gap_after(&self, i: usize) -> Gap {
        self.lines.after(i)
    }

    /// What separates `tokens[i]` from the token before it ([`Lines::before`]).
    fn gap(&self, i: usize) -> Gap {
        self.lines.before(i)
    }

    /// Index of the token after `peek()` (same skipping rules).
    fn peek2_index(&self) -> usize {
        let i = self.peek_index();
        if self.tokens[i].kind == TokenKind::Eof { i } else { self.skip_trivia(i + 1) }
    }

    /// The token after `peek()` (same skipping rules).
    fn peek2(&self) -> Token {
        self.tokens[self.peek2_index()]
    }

    /// The next token ignoring newlines regardless of context.
    fn peek_past_newlines(&self) -> Token {
        self.tokens[self.past_newlines()]
    }

    /// Index of [`Parser::peek_past_newlines`].
    fn past_newlines(&self) -> usize {
        let mut i = self.pos;
        loop {
            match self.tokens[i].kind {
                k if k == TokenKind::Newline || k.is_line_comment() => i += 1,
                _ => return i,
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
    /// the form there ([`Detached`]). Two openers are not asked here: the
    /// `(` after `pub` (a visibility of another language whatever the blank,
    /// [`Parser::parse_vis`], S-248, S-417), and the `(` of the tuple struct
    /// `struct P (I32)` (the table's `tuple_struct`, S-39).
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
            self.detached = Some(Detached { at, by_name, expr, required: false });
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
        self.fail_at(want, expected, noted, None);
        ParseError
    }

    /// [`Parser::fail_with`], in the head of a declaration: the general
    /// E0002 is `own` when the parser knows the form (a run of words before
    /// the head, a keyword before a keyword, the modifiers out of order;
    /// §18.1, S-459, S-464). The token to read on from, if the head may be
    /// read on: after the form a row found when it ends on its line
    /// ([`foreign::Hit::resume`]), else `own`'s.
    fn fail_at(&mut self, want: Want, expected: &str, noted: Option<(Token, &str)>, own: Option<Own>) -> Option<usize> {
        let at = self.peek_index();
        let t = self.tokens[at];
        // The number of a literal written as in other languages (`1u8`,
        // `0o17`, `017`) is checked as any integer literal (E0408): two
        // errors of one token, of which the driver reports one.
        if t.kind == TokenKind::ForeignLit
            && let Some(n) = self.literals.number(t.span)
            && let Some(number) = n.int_body(self.token_text(t))
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
        // A reserved word, where nothing of this version takes it: its E0200
        // where it is read, instead of the general E0002 (§2.2, S-169, S-371).
        let shown = noted.map_or(t, |(found, _)| found);
        if let Some(feature) = shown.kind.reserved() {
            let word = self.token_text(shown);
            let d = feature.diagnostic(Stage::Syntax, shown.span, &[]).with_found(word.to_string());
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
            self.report(d);
        }
        resume
    }

    /// Read on to token `to` after a failure in the head of a declaration
    /// (§18.1, S-435): the tokens from the cursor up to it go into the node
    /// open, the part of the head that was not read.
    fn read_on(&mut self, to: usize) {
        for k in self.pos..to {
            let t = self.tokens[k];
            if t.kind.is_trivia() {
                continue;
            }
            self.events.push(Event::Token(self.full[k]));
            self.last_end = t.span.end;
            if is_opening(t.kind) {
                self.braces.push(k);
            } else if is_closing(t.kind) {
                close_bracket(&mut self.braces, &self.tokens, t.kind, 0);
            }
        }
        self.pos = to;
        self.closed.clear();
    }

    /// The token after `tokens[k]` on its line, comments passed over; `None`
    /// at the end of the line or of the file.
    fn on_line_after(&self, k: usize) -> Option<usize> {
        let j = (k + 1..self.tokens.len()).find(|&j| !self.tokens[j].kind.is_comment())?;
        (!matches!(self.tokens[j].kind, TokenKind::Newline | TokenKind::Eof)).then_some(j)
    }

    /// What the table of the forms of other languages reads of the parser
    /// at token `at` (a failure, or a form read whole), wanting `want`; the
    /// place of an attribute read there is set by the caller that knows it.
    fn cursor(&self, at: usize, want: Want) -> foreign::Cursor<'_> {
        foreign::Cursor {
            file: self.file,
            text: self.text,
            tokens: &self.tokens,
            all: &self.all,
            full: &self.full,
            lines: &self.lines,
            literals: &self.literals,
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
        }
    }

    /// A form of another language or a redundant mark that the parser reads
    /// whole, starting at token `at` (an old attribute, a redundant
    /// visibility; [`foreign::Detect::Read`]), at `place` (an attribute's,
    /// and the keyword of the declaration whose head holds it, if any): the
    /// table's diagnostics are reported, and whether there was one. The
    /// reading goes on (the unit has the syntax error, so its body is not
    /// checked).
    fn read_form(&mut self, at: usize, place: Option<Place>, declaration: Option<usize>) -> bool {
        let mut cursor = self.cursor(at, Want::Other);
        (cursor.place, cursor.declaration) = (place, declaration);
        let found = foreign::at_read(&cursor);
        let any = !found.is_empty();
        for d in found {
            self.report(d);
        }
        any
    }

    fn expect(&mut self, kind: TokenKind) -> PResult<Token> {
        if self.at(kind) { Ok(self.bump()) } else { Err(self.unexpected(kind.describe())) }
    }

    /// E0408 when an integer literal does not fit any integer type (the
    /// value is read by the same function when the AST is made). A number
    /// with the lexer's E0001 (`123abc`, `0x_`) has that error alone.
    fn check_int(&mut self, t: Token) {
        if crate::literal::int_value(self.token_text(t)).is_none() && self.literals.ok(t.span) {
            self.report(Diagnostic::new(
                Stage::Syntax,
                Code::E0408,
                t.span,
                "integer literal is larger than any integer type holds",
            ));
        }
    }

    /// The held errors of the content of each literal right against a name
    /// that no `string_prefix` reported ([`foreign::held_errors`]), after the
    /// whole file is read (S-400, [`crate::literal::Touch`]).
    fn release_held(&mut self) {
        if self.literals.touches().is_empty() {
            return;
        }
        let held: Vec<Diagnostic> = foreign::held_errors(&self.literals, &self.prefixed).cloned().collect();
        self.diagnostics.extend(held);
    }
}

fn binop(kind: TokenKind) -> bool {
    kind.binop().is_some()
}

/// The general E0002 of a failure in the head of a declaration whose form
/// the parser knows ([`Parser::fail_at`]): its range, message, rule and
/// candidates, and the token the head is read on from.
struct Own {
    span: Span,
    message: String,
    rule: &'static str,
    fixes: Vec<Fix>,
    resume: usize,
}

/// A token that starts the head of a declaration (§18.1): a visibility, an
/// attribute (`@`, and `#[` of other languages, S-321) or a keyword of a
/// declaration ([`DECLARATIONS`]). The one list (the recovery's item starts
/// add the doc comments, `file::is_item_start`).
fn starts_heading(kind: TokenKind) -> bool {
    is_declaration_keyword(kind)
        || matches!(kind, TokenKind::KwPub | TokenKind::KwPriv | TokenKind::At | TokenKind::Hash)
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

/// A declaration: its keyword, its node, how it is parsed after its
/// attributes and visibility, and where it may be written.
struct Declaration {
    keyword: TokenKind,
    node: NodeKind,
    parse: DeclParser,
    places: &'static [ItemCtx],
}

/// The keywords that start a declaration, with the node of the declaration,
/// how to parse it and where it may be written: the one list. `parse_item`
/// dispatches on it and refuses a declaration out of its places, and the
/// recovery's item starts (`file::is_item_start`) are these keywords and
/// what may come before them.
const DECLARATIONS: &[Declaration] = &[
    Declaration { keyword: TokenKind::KwFn, node: NodeKind::Fn, parse: |p, c| p.parse_fn(c), places: FUNCTION_PLACES },
    Declaration { keyword: TokenKind::KwRt, node: NodeKind::Fn, parse: |p, c| p.parse_fn(c), places: FUNCTION_PLACES },
    Declaration { keyword: TokenKind::KwFlow, node: NodeKind::Flow, parse: |p, c| p.parse_flow(c), places: TOP },
    Declaration { keyword: TokenKind::KwStruct, node: NodeKind::Struct, parse: |p, c| p.parse_struct(c), places: TOP },
    Declaration { keyword: TokenKind::KwEnum, node: NodeKind::Enum, parse: |p, c| p.parse_enum(c), places: TOP },
    Declaration {
        keyword: TokenKind::KwType,
        node: NodeKind::TypeAlias,
        parse: |p, c| p.parse_type_item(c),
        places: TYPE_PLACES,
    },
    Declaration { keyword: TokenKind::KwTrait, node: NodeKind::Trait, parse: |p, c| p.parse_trait(c), places: TOP },
    Declaration { keyword: TokenKind::KwImpl, node: NodeKind::Impl, parse: |p, c| p.parse_impl(c), places: TOP },
    Declaration { keyword: TokenKind::KwEffect, node: NodeKind::Effect, parse: |p, c| p.parse_effect(c), places: TOP },
    Declaration {
        keyword: TokenKind::KwBlocking,
        node: NodeKind::Effect,
        parse: |p, c| p.parse_effect(c),
        places: TOP,
    },
    Declaration {
        keyword: TokenKind::KwHandler,
        node: NodeKind::Handler,
        parse: |p, c| p.parse_handler(c),
        places: TOP,
    },
    Declaration {
        keyword: TokenKind::KwConst,
        node: NodeKind::Const,
        parse: |p, c| p.parse_const(c),
        places: CONST_PLACES,
    },
    Declaration { keyword: TokenKind::KwUse, node: NodeKind::Use, parse: |p, c| p.parse_use(c), places: TOP },
    Declaration { keyword: TokenKind::KwExtern, node: NodeKind::Extern, parse: |p, c| p.parse_extern(c), places: TOP },
    Declaration { keyword: TokenKind::KwTarget, node: NodeKind::Target, parse: |p, c| p.parse_target(c), places: TOP },
    Declaration { keyword: TokenKind::KwTest, node: NodeKind::Test, parse: |p, c| p.parse_test(c), places: TOP },
];

/// The declaration whose keyword is `kind`, if one is ([`DECLARATIONS`]).
fn declaration(kind: TokenKind) -> Option<&'static Declaration> {
    DECLARATIONS.iter().find(|d| d.keyword == kind)
}

/// The node of the declaration whose keyword is `kind` ([`DECLARATIONS`]).
pub(crate) fn declaration_node(kind: TokenKind) -> Option<NodeKind> {
    declaration(kind).map(|d| d.node)
}

/// Whether `kind` is the keyword of a declaration ([`DECLARATIONS`]).
fn is_declaration_keyword(kind: TokenKind) -> bool {
    declaration(kind).is_some()
}

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
