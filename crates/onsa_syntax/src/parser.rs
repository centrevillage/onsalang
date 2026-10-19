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
//! Where the code is: this module holds the types (`Parser`, the markers
//! of the nodes), the construction of the parser, and the helpers that
//! several parts read (the brackets). The parser is in a module
//! per part, each an `impl` of `Parser`: `nodes` (the trial readings, the
//! nodes and their levels), `cursor` (the reading of the tokens),
//! `failure` (the diagnostics and the questions to the table of the forms
//! of other languages), `declarations` (`DECLARATIONS`, the declarations
//! and where they are written), and the grammar: `file` (the file, the
//! units and the recovery), `heading` (the head of a declaration before its
//! keyword), `items` (the declarations), `signatures`, `types`,
//! `statements` (the blocks and the statements), `expressions` (with
//! `reads_as_expr`) and `patterns`; `chain` is `ChainHeight`, the height
//! of a binary chain. The tests are `parser_tests.rs`.

use onsa_diag::{Code, Diagnostic, FileId, Fix, Span, Stage};

use crate::attrs::Place;
use crate::callee::Callee;
use crate::cst::{Class, Event, NodeKind};
use crate::foreign::{self, Detached, End, Want};
use crate::layout::Lines;
use crate::literal::Literals;
use crate::scan::pattern_alternative;
use crate::starts::{declares_a_function, starts_operand};
use crate::token::{Gap, Token, TokenKind};

mod chain;
mod cursor;
mod declarations;
mod expressions;
mod failure;
mod file;
mod heading;
mod items;
mod nodes;
mod patterns;
mod signatures;
mod statements;
mod types;

pub(crate) use chain::ChainHeight;
pub(crate) use declarations::declaration_node;
use declarations::{Declaration, declaration, is_declaration_keyword, starts_heading};
pub(crate) use expressions::reads_as_expr;
use failure::Own;
use statements::MoveAs;
use types::ClockAfter;
pub(crate) use types::{reads_as_type, reads_as_type_list};

/// What the parser gives the later stages of [`crate::parse`].
pub(crate) struct ParseOutput {
    pub tokens: Vec<Token>,
    pub events: Vec<Event>,
    pub diagnostics: Vec<Diagnostic>,
    /// The levels of each top-level item that parsed ([`crate::Parsed::levels`]).
    pub levels: Vec<u32>,
    /// The facts of the literals, from the lexer: the AST takes the paths of
    /// the holes from them.
    pub literals: Literals,
    /// The height of the tree in levels (spec §2.5), as the parser counted
    /// it (`Parser::height`): the deepest declaration unit. The tests compare
    /// it with the tree.
    #[cfg(test)]
    pub height: u32,
    /// The height in levels of each item node the parser closed (a member
    /// too, also one that failed: what it read of it), by the start of the
    /// node: the units take theirs from it (`crate::units`), and a check
    /// that a candidate stays in the nesting limit reads again only a unit
    /// near it (`nesting::nests_too_deep`).
    pub items: Vec<(u32, u32)>,
}

/// Marker for "a diagnostic was reported; abandon this item".
#[derive(Debug, Clone, Copy)]
pub(crate) struct ParseError;

pub(crate) type PResult<T> = Result<T, ParseError>;

/// What kind of declaration list we are inside; decides whether `fn` bodies
/// are required / allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ItemCtx {
    Top,
    Trait,
    Impl,
    Effect,
    Handler,
    Extern,
    InlineHandler,
}

impl ItemCtx {
    /// The list the members of a declaration of `kind` are read in, `None`
    /// for a declaration without members: the one table of it. The parser
    /// reads the member lists with it ([`Parser::parse_members`]), and the
    /// units of the members are made from it and read again in it
    /// (`crate::units`, §18.1). No wildcard: a new kind decides it here.
    pub(crate) fn of_members(kind: NodeKind) -> Option<ItemCtx> {
        use NodeKind::*;
        match kind {
            Trait => Some(ItemCtx::Trait),
            Impl => Some(ItemCtx::Impl),
            Effect => Some(ItemCtx::Effect),
            Handler => Some(ItemCtx::Handler),
            Extern => Some(ItemCtx::Extern),
            Fn | Flow | Struct | Enum | TypeAlias | OpaqueType | Const | Use | Target | Test => None,
            SourceFile | Error | Name | Item | Docs | ModuleDocs | Attr | AttrArgs | AttrNamedArg | Vis | FieldList
            | Field | Derives | VariantList | Variant | VariantFields | UseTree | UseNames | ItemList
            | GenericParams | TypeParam | ConstParam | EffectParam | Bound | ParamList | Param | EffectRow | Path
            | TypeArgs | FnTypeParams | LetStmt | VarStmt | ForStmt | WhileStmt | BreakStmt | ContinueStmt
            | ReturnStmt | AssertStmt | AssignStmt | ExprStmt | MatchArms | MatchArm | ArgList | Arg
            | StructLitFields | StructLitField | StructPatField | StructPatRest | Clock => None,
            Literal | HoleExpr | PathExpr | ParenExpr | TupleExpr | ArrayExpr | RepeatExpr | Block | IfExpr
            | MatchExpr | ClosureExpr | HandleExpr | UnsafeExpr | ParExpr | MoveExpr | BinaryExpr | RangeExpr
            | CastExpr | AtExpr | FeedbackExpr | PrefixExpr | CallExpr | FieldExpr | TupleIndexExpr | TypeArgsExpr
            | IndexExpr | TryExpr | StructLit | PathType | ConstArg | UnitType | TupleType | ParenType | ArrayType
            | FnType | WildPat | LitPat | NegLitPat | TuplePat | ParenPat | BindPat | PathPat | TupleStructPat
            | StructPat | OrPat => None,
        }
    }
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

/// The deepest nesting of the syntax (spec §2.5, S-183, S-221): a form at a
/// level above it is E0006 ([`Parser::too_deep`]).
pub const NESTING_LIMIT: u32 = 256;

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
    /// The height of each item node closed ([`ParseOutput::items`]).
    items: Vec<(u32, u32)>,
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
    /// [`Parser::complete`] records them from the kinds of the nodes
    /// ([`End::of`]).
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
            items: Vec::new(),
            trials: 0,
            detached: None,
            ends: Vec::new(),
            prefixed: Vec::new(),
        }
    }
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
