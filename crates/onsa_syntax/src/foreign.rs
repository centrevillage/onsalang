//! The table of the forms of other languages and of the redundant marks that
//! show a misreading (spec §18.1, P2; S-114, S-250): the one place that knows
//! them. Each row has the stage that finds the form, the code (E0020 when a
//! candidate can be made, else E0002 with the Onsa way in a note, S-48), the
//! message, the correct rule (the note, S-114) and how the form is found.
//!
//! The rows are one to one with the data file `docs/foreign-forms.toml` (the
//! closed list of S-250, written from the spec by the tests' side): the same
//! `id`, stage and code; the file's examples are the cases each row passes
//! (`onsa_tests::foreign_forms` checks both, D-15). A row whose form no work
//! has made yet is in [`WAITING`] (its `id`, stage and code), and its
//! examples wait in `tests/pending.toml` (kind `foreign-form`, the `id` as
//! target): they fail, and the row is never let through silently (R-81).
//!
//! How a form is found ([`Detect`]):
//!
//! - The syntax stage: the parser has no branch for any form. A form of
//!   another language is a token or a sequence of tokens the parser does not
//!   accept where it is written (the lexer makes `/* */`, `1.`, `1u8`, `++`
//!   tokens of their own), so the parser fails at it; at every failure it asks
//!   [`at_failure`] with what it was reading ([`Cursor`]: the token, the open
//!   nodes, the nodes that closed before it, what it wanted). A row that
//!   recognises the failure gives the diagnostic; else the failure is the
//!   general E0002. A form of the syntax stage fails its unit (R-87 (4)): the
//!   parser reads it as nothing else and goes on with the next unit.
//! - The type arguments of another language before a call, `f<T>(x)` and
//!   `f[A, B](x)`, which the parser could read as a comparison or an index:
//!   the parser asks [`type_list_ahead`] from the tokens (and reads a `[…]`
//!   on as a list of type arguments to be sure) before it reads the `<` or
//!   the `[`, and fails at it when the answer is yes; the row is then found
//!   at that failure (`paths::type_args_call`, with `f::<T>(x)`, where the parser
//!   fails by itself).
//! - A type name that the parser reads as a name (`i32`): [`type_name`], the
//!   one entry where the parser does not fail, called where it reads a type.
//! - The names, types and flow stages build their diagnostic with
//!   [`report`]: they find the form and give the span and the candidates; the
//!   code, the stage, the message and the note come from the row.
//!
//! The general E0002 of a failure that no row names is the parser's, but
//! its candidates are this module's too ([`Failure`], `lists`): the missing
//! `,` between the elements of a list (S-384, S-387, S-386, S-398, S-405),
//! two string literals made one (S-388) and the gap before a postfix opener
//! taken out (S-89, S-373, S-399).
//!
//! What it reads: the line facts of the tokens ([`crate::layout::Lines`]),
//! what a token starts ([`crate::starts`]), the scans of the tokens
//! ([`crate::scan`]), the facts of the literals ([`crate::literal::Literals`])
//! and what the parser recorded ([`Cursor`], [`Detached`], [`End`]). It asks
//! the parser nothing of its judgements; it reads the parser only to read a
//! candidate's code again (`parser::reads_as_expr`, and
//! `groups::nests_too_deep` with `parser::NESTING_LIMIT`), which a candidate
//! must keep readable (S-236).
//!
//! Where the code is: this module holds the types ([`Row`], [`RowId`],
//! [`Cursor`], [`Want`], [`Hit`], [`Detect`], [`Detached`], [`End`]), the
//! entries ([`at_failure`], [`report`]) and the helpers of the cursor that
//! many rows read; `lists` the candidates of the general E0002 and `edits`
//! the edits that move a symbol to its partner's line. The table
//! of the rows ([`ROWS`], [`WAITING`]) is `foreign/rows.rs`; the matchers are
//! in a module per family of forms: `semicolons` (`;`), `paths` (the `::` of
//! a path, `<T>`, the type arguments of other languages, the type names of
//! other languages), `calls` (the callee of a call), `modes` (`&mut`,
//! `mut self`), `decls` (`let mut`, `loop`, `proc`, `#[…]`, `pub(crate)`),
//! `literals` (the number literals), `faust` (the prefix `~` of C),
//! `comments` (the block comments), `assign` (`+=`, `++`), `ranges` (the
//! range symbols out of place), `guard` (the patterns written as guards),
//! `flow` (`if~`, the clocks) and `spaces` (the blanks inside a line).
//!
//! To add a row (the later works, W3-05 to W5-09):
//!
//! 1. move the row from [`WAITING`] to [`ROWS`] in `foreign/rows.rs` (a
//!    `RowId` here, the `id`, stage and code of its row in
//!    `docs/foreign-forms.toml`, the message and the rule); a new form is
//!    added to the data file from its decision (an S row of the plan), not
//!    to the text of the spec (§18.1 only names where the list is, S-250);
//! 2. write its matcher ([`Detect::Syntax`]) in the module of its family (or
//!    a new one), or call [`report`] from its stage; a candidate edits only
//!    the tokens it changes (S-251), one form is one diagnostic with one
//!    candidate that fixes all of it (S-248), and a form for which no
//!    candidate keeps the contract of §18.1 (S-236) has none (the
//!    diagnostic is then E0002 with the note);
//! 3. remove the `foreign-form` entry of the row from `tests/pending.toml`
//!    (and the `test-case` or `fix-contract` entries of its cases): the
//!    examples of the data file run through the same entry as the cases, and
//!    every candidate is checked against the contract (W3-17).

use onsa_diag::{Code, Diagnostic, Edit, FileId, Fix, Span, Stage};

use crate::ast::{BinOp, Operand};
use crate::cst::{Class, NodeKind};
use crate::starts::ends_operand;
use crate::token::{Gap, Token, TokenKind};

mod flow;
mod spaces;

pub(crate) use flow::clocks;

/// The stage that finds a form, as the data file names it: the lexical and
/// the syntax stages are both [`Stage::Syntax`] (§18.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Lexical,
    Syntax,
    Names,
    Types,
    Flow,
}

impl Phase {
    pub fn stage(self) -> Stage {
        match self {
            Phase::Lexical | Phase::Syntax => Stage::Syntax,
            Phase::Names => Stage::Names,
            Phase::Types => Stage::Types,
            Phase::Flow => Stage::Flow,
        }
    }

    /// The name of the data file (`stage = "..."`).
    pub fn name(self) -> &'static str {
        match self {
            Phase::Lexical => "lexical",
            Phase::Syntax => "syntax",
            Phase::Names => "names",
            Phase::Types => "types",
            Phase::Flow => "flow",
        }
    }
}

/// What the parser was reading when it failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Want {
    /// An expression (an operand).
    Expr,
    /// A pattern.
    Pattern,
    /// A type.
    Type,
    /// Anything else (a token of a declaration, a statement's end, ...).
    Other,
    /// The next link of a postfix chain, at a member `.` with a space (§2.5).
    Postfix,
    /// The `(` of a call whose callee [`callee_by_name`] says is no callee
    /// written by name (§6.1): the table does not judge the callee again.
    Callee,
    /// A blank or a line break after a prefix `-` / `!` of an expression, or
    /// after the `-` of a negative integer literal of a pattern (§2.5, S-123,
    /// S-369, S-411): the parser judged the gap (`Parser::parse_prefix`,
    /// `Parser::parse_pattern_alt`), at the symbol.
    Prefix,
    /// The `,` or the closing bracket after an element of a list of the
    /// node's kind (`Parser::close_list`, §2.5): the general E0002 of the
    /// failure is the missing `,` ([`super::lists::list_fixes`], S-384).
    Separator(NodeKind),
}

/// What the parser gives the table at a failure.
pub struct Cursor<'a> {
    pub file: FileId,
    pub text: &'a str,
    /// The tokens the parser reads (the full list without whitespace).
    pub tokens: &'a [Token],
    /// The full token list of the lexer.
    pub all: &'a [Token],
    /// Index in `all` of each of `tokens`.
    pub full: &'a [u32],
    /// The line facts of `tokens` (the gaps around each, the line breaks
    /// that go on, [`crate::layout::Lines`]).
    pub(crate) lines: &'a crate::layout::Lines,
    /// The holes of the string literals and the lexer's errors in them
    /// ([`crate::literal::Literals`]).
    pub(crate) literals: &'a crate::literal::Literals,
    /// The token the parser failed at (an index of `tokens`).
    pub at: usize,
    /// The open nodes, outermost first, and where each starts.
    pub open: Vec<(NodeKind, u32)>,
    /// The nodes that closed at the token before `at`, innermost first, and
    /// where each starts.
    pub closed: &'a [(NodeKind, u32)],
    pub want: Want,
    /// The postfix opener at `at` that the parser did not read on because a
    /// blank or a line break is before it ([`Detached`], S-89).
    pub detached: Option<Detached>,
    /// The last tokens of the statements and declarations that end no operand
    /// (`for`, `while`, a declaration but `const` and `type`) or with a bound
    /// value (`let`, `var`, an assignment), in order (`Parser::ends`).
    pub ends: &'a [(usize, End)],
    /// The row a matcher of several rows found ([`Cursor::say`]).
    pub found: std::cell::Cell<Option<RowId>>,
}

/// A postfix opener (`(`, `[`, or the mark `!` / `~` before a `(`) that the
/// parser did not read on, because a blank or a line break is before it
/// (§2.5, S-89): the grammar fails where it fails, and the table reads this
/// at that failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Detached {
    /// The opener, an index of the parser's tokens.
    pub at: usize,
    /// The token before it ends a path of names (§6.1: what a callee is,
    /// [`callee_by_name`]; a name of a declaration, a type,
    /// a pattern or an attribute is one), S-399.
    pub by_name: bool,
    /// The opener follows an expression (else a declaration, a type, a
    /// pattern or an attribute).
    pub expr: bool,
    /// The list is required there (`Parser::opens`): a line break before
    /// the opener is no next element either.
    pub required: bool,
}

impl Detached {
    /// Whether the code with the gap taken out reads as the postfix it would
    /// be (S-373, S-399, read from the tokens): a `(` or a mark after a path
    /// of names; a `[` whose list closes, is not empty and holds no `;` (an
    /// array, `[T; N]`), and, after an expression, holds no `,` either
    /// (`xs[0, 1]` is no index).
    pub(crate) fn joins(self, tokens: &[Token]) -> bool {
        match tokens[self.at].kind {
            TokenKind::LParen | TokenKind::Bang | TokenKind::Tilde => self.by_name,
            TokenKind::LBracket => {
                let Some((close, comma, semi)) = crate::scan::bracket_contents(tokens, self.at) else { return false };
                close > self.at + 1 && !semi && !(self.expr && comma)
            }
            _ => false,
        }
    }
}

/// What a statement or a declaration that the parser read to its end ends
/// with, for a symbol at the head of the next line (`Parser::ends`, S-236).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum End {
    /// No operand: a `for`, a `while`, a declaration but `const` and `type`.
    /// No symbol goes on with it.
    NoOperand,
    /// The value of a `let`, a `var`, an assignment, a `return` or an
    /// `assert`: an operator goes on with it, a `=` does not.
    Bound,
}

/// A form a row found: its span (the main position), its candidates (none:
/// the diagnostic is E0002 with the note), and whether the place is wrong
/// too (a literal where no expression goes: the parser reports its general
/// E0002 as well, and the driver chooses, S-281).
pub struct Hit {
    pub span: Span,
    pub fixes: Vec<Fix>,
    pub misplaced: bool,
}

/// How a row's form is found.
#[derive(Clone, Copy)]
pub enum Detect {
    /// Where the parser fails ([`at_failure`]).
    Syntax(fn(&Cursor) -> Option<Hit>),
    /// A type name the parser reads ([`type_name`]).
    TypeName,
    /// A form the parser reads whole, found on the tree after parsing (the
    /// clocks of S-356, [`clocks`]).
    Tree,
}

/// The rows the compiler finds. `name` is the row's `id` in
/// `docs/foreign-forms.toml`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowId {
    Semicolon,
    SemicolonInList,
    PathSeparator,
    AngleBrackets,
    RefMutParam,
    RefMutSelf,
    MutSelf,
    RefSelf,
    RefType,
    RefExpr,
    RefMutArg,
    RefMutOther,
    LowercaseType,
    CompoundAssign,
    CompoundAssignUnfixable,
    BinaryMinusPrefixMinus,
    Increment,
    IncrementUnfixable,
    LetMut,
    Loop,
    Proc,
    FloatTrailingDot,
    FloatLeadingDot,
    LiteralSuffix,
    BlockComment,
    BlockCommentUnclosed,
    BlockCommentNested,
    BlockCommentMultilineCodeAfter,
    FloatPattern,
    FloatPatternChoice,
    InterpolatedStringPattern,
    NegatedConstantPattern,
    AtBinding,
    AtBindingComplex,
    RangePattern,
    RangePatternChoice,
    RangeHeaderOneSided,
    StructPatternRest,
    HashAttribute,
    FaustBitNot,
    PubCrate,
    TypeArgsTurbofish,
    TypeArgsAngle,
    TypeArgsSquareComma,
    TypeArgsOnExpression,
    TypePositionPath,
    SpaceInTypeArgsMark,
    RangeDots,
    RangeOutsideHeader,
    SpaceAroundDot,
    SpaceBeforeParen,
    SpaceBeforeBracket,
    SpaceBeforeBang,
    SpaceBeforeTilde,
    StringPrefix,
    ArmReturn,
    SpaceBeforeQuestion,
    SpaceAfterPrefix,
    SpaceAfterCaret,
    AsymmetricBinarySpace,
    NewlineAfterDot,
    NewlineAfterPrefix,
    NewlineBeforeQuestion,
    LeadingOperator,
    LeadingMinus,
    LeadingRange,
    LeadingVert,
    PatternDoubleVert,
    PrefixPlus,
    CalleeExpression,
    SpaceAfterBranchKeyword,
    ElseIfTilde,
    ClockOnBinding,
    ClockInType,
}

pub struct Row {
    pub id: RowId,
    /// The row's `id` in the data file.
    pub name: &'static str,
    pub phase: Phase,
    pub code: Code,
    pub message: &'static str,
    /// The correct rule, the note without a position (S-114).
    pub rule: &'static str,
    pub detect: Detect,
}

/// A row of the data file whose form a later work finds: its examples wait
/// in `tests/pending.toml` (kind `foreign-form`, R-81). The work moves it
/// into [`ROWS`] with its message, rule and matcher (the module's
/// documentation).
pub struct Waiting {
    pub name: &'static str,
    pub phase: Phase,
    pub code: Code,
}

/// The row of `id`.
pub fn row(id: RowId) -> &'static Row {
    ROWS.iter().find(|r| r.id == id).unwrap_or_else(|| onsa_diag::internal::bug(None, format!("no row {id:?}")))
}

/// The diagnostic of a form of `id` found at `span` with `fixes`, from a
/// stage after the syntax (names, types, flow): the code, the stage, the
/// message and the note are the row's. No candidate makes it E0002 (S-48).
pub fn report(id: RowId, text: &str, span: Span, fixes: Vec<Fix>) -> Diagnostic {
    diagnostic(text, id, Hit { span, fixes, misplaced: false })
}

fn diagnostic(text: &str, id: RowId, hit: Hit) -> Diagnostic {
    let row = row(id);
    let code = if hit.fixes.is_empty() { Code::E0002 } else { row.code };
    let mut d = Diagnostic::new(row.phase.stage(), code, hit.span, row.message);
    let found = &text[hit.span.start as usize..hit.span.end as usize];
    if !found.trim().is_empty() {
        d = d.with_found(found);
    }
    for f in hit.fixes {
        d = d.with_fix(f);
    }
    d.with_rule(row.rule)
}

/// What the table says of a failure of the parser: the diagnostic of the row
/// that recognises it, if one does, and the candidates of the parser's
/// general E0002 when that is reported too (no row, or a form in a place
/// where nothing of its kind goes, [`Hit`]): the missing `,` of a list and
/// the gap before an opener taken out ([`lists::list_fixes`]).
pub(crate) struct Failure {
    pub row: Option<Diagnostic>,
    pub general: Option<Vec<Fix>>,
}

/// The table's reading of a failure of the parser ([`Failure`]).
pub(crate) fn at_failure(c: &Cursor) -> Failure {
    let (row, general) = match row_at_failure(c) {
        Some((d, misplaced)) => (Some(d), misplaced),
        None => (None, true),
    };
    // After an element of a list, the general error is the missing `,`;
    // an opener after a line break takes it out (S-89).
    let general = general.then(|| match c.want {
        Want::Separator(list) => lists::list_fixes(c, Some(list)),
        _ => lists::list_fixes(c, None),
    });
    Failure { row, general }
}

/// The diagnostic of a failure of the parser, when a row recognises it, and
/// whether the parser's general E0002 is to be reported too ([`Hit`]).
fn row_at_failure(c: &Cursor) -> Option<(Diagnostic, bool)> {
    let mut found: Option<(RowId, Hit)> = None;
    for row in ROWS {
        let Detect::Syntax(matcher) = row.detect else { continue };
        c.found.set(None);
        let Some(hit) = matcher(c) else { continue };
        let id = c.found.get().unwrap_or(row.id);
        // The rows do not overlap: one failure is one form (checked in the
        // debug builds, where every matcher runs).
        debug_assert!(found.is_none(), "two rows match one failure: {:?} and {id:?}", found.as_ref().map(|f| f.0));
        if found.is_none() {
            found = Some((id, hit));
        }
        if !cfg!(debug_assertions) {
            break;
        }
    }
    let (id, hit) = found?;
    let misplaced = hit.misplaced;
    Some((diagnostic(c.text, id, hit), misplaced))
}

/// The matcher of a row whose form the matcher of another row finds and
/// names ([`Cursor::say`]).
fn no_match(_: &Cursor) -> Option<Hit> {
    None
}

// ------------------------------------------------------------ the cursor

impl Cursor<'_> {
    pub(crate) fn kind(&self, i: usize) -> TokenKind {
        self.tokens[i].kind
    }

    pub(crate) fn span(&self, i: usize) -> Span {
        self.tokens[i].span
    }

    fn src(&self, i: usize) -> &str {
        let s = self.span(i);
        &self.text[s.start as usize..s.end as usize]
    }

    fn is_ident(&self, i: usize, text: &str) -> bool {
        self.kind(i) == TokenKind::Ident && self.src(i) == text
    }

    /// A comment of any kind (a block comment is a token of its own, which
    /// its own row reports; elsewhere it is passed over as a comment,
    /// [`TokenKind::is_comment`], as the line facts pass it over).
    pub(crate) fn comment(&self, i: usize) -> bool {
        self.kind(i).is_comment()
    }

    /// Whether the literal token `i` is one the lexer read with no error in
    /// it ([`crate::literal::Literals::ok`]).
    pub(crate) fn literal_ok(&self, i: usize) -> bool {
        self.literals.ok(self.span(i))
    }

    /// The token after `i`, comments skipped (a newline is a token).
    fn after(&self, i: usize) -> usize {
        let mut j = i;
        while j + 1 < self.tokens.len() {
            j += 1;
            if !self.comment(j) {
                return j;
            }
        }
        j
    }

    /// The token after `i`, newlines and comments skipped.
    pub(crate) fn sig_after(&self, i: usize) -> usize {
        let mut j = i;
        while j + 1 < self.tokens.len() {
            j += 1;
            if !self.comment(j) && self.kind(j) != TokenKind::Newline {
                return j;
            }
        }
        j
    }

    /// The token before `i`, newlines and comments skipped.
    pub(crate) fn sig_before(&self, i: usize) -> Option<usize> {
        (0..i).rev().find(|&j| !self.comment(j) && self.kind(j) != TokenKind::Newline)
    }

    /// The token right before `i` on its line (a comment or a newline before
    /// it gives none).
    pub(crate) fn before(&self, i: usize) -> Option<usize> {
        let j = i.checked_sub(1)?;
        (!self.comment(j) && self.kind(j) != TokenKind::Newline).then_some(j)
    }

    /// The innermost open node that has read a token before the failure: a
    /// node opened at the failing token (a `Block` before its `{`, a
    /// `FieldList` before its `{`, an item before its first token) is not yet
    /// what it will be, so the node around it is the context (the file is
    /// always one). The `;` rows read it (`pub struct Marker;` is no list).
    fn context(&self) -> Option<(usize, NodeKind)> {
        let at = self.span(self.at).start;
        self.open.iter().enumerate().rev().find(|(_, o)| o.0 == NodeKind::SourceFile || o.1 < at).map(|(k, o)| (k, o.0))
    }

    /// What separates `tokens[i]` from the token after it ([`crate::layout::Lines::after`]).
    pub(crate) fn gap_after(&self, i: usize) -> Gap {
        self.lines.after(i)
    }

    /// What separates `tokens[i]` from the token before it ([`crate::layout::Lines::before`]).
    pub(crate) fn gap(&self, i: usize) -> Gap {
        self.lines.before(i)
    }

    /// Whether `tokens[i]` is at the head of its line ([`crate::layout::Lines::at_line_head`]).
    pub(crate) fn at_line_head(&self, i: usize) -> bool {
        self.lines.at_line_head(i)
    }

    /// The whitespace token right after `tokens[i]`, if any.
    pub(crate) fn space_after(&self, i: usize) -> Option<Span> {
        let k = self.full[i] as usize + 1;
        self.all.get(k).filter(|t| t.kind == TokenKind::Whitespace).map(|t| t.span)
    }

    /// The whitespace token right before `tokens[i]`, if any.
    pub(crate) fn space_before(&self, i: usize) -> Option<Span> {
        let k = (self.full[i] as usize).checked_sub(1)?;
        self.all.get(k).filter(|t| t.kind == TokenKind::Whitespace).map(|t| t.span)
    }

    /// The innermost open node.
    fn top(&self) -> Option<NodeKind> {
        self.open.last().map(|o| o.0)
    }

    /// The open node `n` levels out from the innermost (0: the innermost).
    fn open_at(&self, n: usize) -> Option<(NodeKind, u32)> {
        self.open.len().checked_sub(n + 1).map(|k| self.open[k])
    }

    /// The index in `tokens` of the token that starts at `offset` (or the next one).
    pub(crate) fn index_at(&self, offset: u32) -> usize {
        self.tokens.partition_point(|t| t.span.start < offset)
    }

    /// The offset where the line of `offset` starts.
    fn line_start(&self, offset: u32) -> u32 {
        self.text[..offset as usize].rfind('\n').map_or(0, |i| i as u32 + 1)
    }

    /// The blanks that start the line of `offset`.
    fn indent(&self, offset: u32) -> &str {
        let start = self.line_start(offset) as usize;
        let rest = &self.text[start..];
        &rest[..rest.len() - rest.trim_start_matches([' ', '\t']).len()]
    }

    fn file_span(&self, start: u32, end: u32) -> Span {
        Span::new(self.file, start, end)
    }
}

impl Cursor<'_> {
    /// The symbol at the head of the line where the parser failed: the token of
    /// the failure, or, when the parser failed at a line break (a head waiting
    /// for its `{`, a `let` for its `=`), the first token of the next line; and
    /// the code before it, when that is an operand the symbol may go on with
    /// (S-124, S-374, S-380): no statement or declaration that ends no operand
    /// (`for`, `while`, a declaration, S-236, [`Cursor::ends`], [`End`]), but
    /// for a `->` or a `=`, which go on with the head of a declaration (the
    /// caller judges whose head).
    pub(crate) fn head_symbol_after_operand(&self) -> Option<(usize, usize)> {
        use TokenKind::*;
        let s = if self.kind(self.at) == Newline { self.sig_after(self.at) } else { self.at };
        if !self.lines.at_line_head(s) {
            return None;
        }
        let prev = self.sig_before(s)?;
        let kind = self.kind(s);
        let operand = ends_operand(self.kind(prev)) || (matches!(kind, Pipe | Eq) && self.kind(prev) == Underscore);
        let head = matches!(kind, Arrow | Eq);
        (operand && (head || self.end_at(prev) != Some(End::NoOperand))).then_some((s, prev))
    }

    /// What the statement or declaration whose last token is `i` ends with,
    /// when the parser read one to its end there ([`End`]).
    pub(crate) fn end_at(&self, i: usize) -> Option<End> {
        self.ends.binary_search_by_key(&i, |e| e.0).ok().map(|k| self.ends[k].1)
    }
}

impl Cursor<'_> {
    /// A matcher of several rows says which row it found (a matcher is a
    /// plain function of the cursor).
    fn say(&self, row: RowId) {
        self.found.set(Some(row));
    }
}

fn hit(span: Span, fixes: Vec<Fix>) -> Option<Hit> {
    Some(Hit { span, fixes, misplaced: false })
}

/// A name or a path of names and tuple indexes: `x`, `self.a.b`, `t.0.1`
/// (tokens `first..=last`, no newline between; S-322).
fn is_place(c: &Cursor, first: usize, last: usize) -> bool {
    if first > last {
        return false;
    }
    (first..=last).enumerate().all(|(k, i)| match k % 2 {
        0 if k == 0 => matches!(c.kind(i), TokenKind::Ident | TokenKind::KwSelf),
        0 => matches!(c.kind(i), TokenKind::Ident | TokenKind::KwSelf | TokenKind::Int),
        _ => c.kind(i) == TokenKind::Dot,
    }) && (last - first) % 2 == 0
}

/// Where the statement that goes on at token `from` ends: the last token of
/// it (a newline ends it unless the line goes on, as the parser reads it,
/// [`crate::layout::Lines::goes_on`]; a `}` or `)` that closes what it is in
/// ends it too).
fn statement_end(c: &Cursor, from: usize) -> Option<usize> {
    let mut depth = 0i32;
    let mut last: Option<usize> = None;
    let mut i = from;
    while i < c.tokens.len() {
        match c.kind(i) {
            TokenKind::Eof | TokenKind::Semi => break,
            _ if c.comment(i) => {}
            TokenKind::Newline if depth == 0 => {
                if !(last.is_some() && c.lines.goes_on(i)) {
                    break;
                }
            }
            TokenKind::Newline => {}
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => {
                depth += 1;
                last = Some(i);
            }
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                last = Some(i);
            }
            _ => last = Some(i),
        }
        i += 1;
    }
    last
}

/// The statement ends at token `i` (a newline, a `}`, a `;` (an error of its
/// own, reported next) or the end of the file follows, or a comment).
fn ends_statement(c: &Cursor, i: usize) -> bool {
    matches!(c.kind(c.after(i)), TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof | TokenKind::Semi)
        || c.comment(i + 1)
}

/// The bracket that closes the one at `open` (`(`, `[` or `{`).
pub(crate) fn closing(c: &Cursor, open: usize) -> Option<usize> {
    let mut depth = 0u32;
    for i in open..c.tokens.len() {
        match c.kind(i) {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            TokenKind::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The expression that ended right before the failure: the outermost
/// expression among the nodes closed there (an argument list closes before
/// its call; the `if` of `if c { f } else { g }`, not its last block, S-316).
fn closed_expr(c: &Cursor) -> Option<(NodeKind, u32)> {
    c.closed.iter().copied().rfind(|n| n.0.class() == Class::Expr)
}

// ------------------------------------------------------------ the rows by their families

mod assign;
mod calls;
mod comments;
mod decls;
mod edits;
mod faust;
pub mod guard;
mod lines;
mod lists;
mod literals;
mod modes;
mod paths;
mod ranges;
mod rows;
mod semicolons;

pub use guard::guard_name;
use guard::guard_pattern;

pub(crate) use calls::{CalleeChain, callee_by_name, names_a_path};
pub(crate) use edits::move_up;
pub use paths::TYPE_NAMES;
pub(crate) use paths::{type_list_ahead, type_name};
pub use rows::{ROWS, WAITING};
// The helpers that the rows of `guard` and `flow` share with a family.
use assign::operand;
use faust::bit_not;
use literals::float_spelling;
use paths::is_segment;
