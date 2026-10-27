//! The table of the forms of other languages and of the redundant marks that
//! show a misreading (spec §18.1, P2; S-114, S-250): the one place that knows
//! them. Each row has the stage that finds the form, the code (E0020 when a
//! candidate can be made, else E0002 with the Onsa way in a note, S-48), the
//! message, the correct rule (the note, S-114) and how the form is found.
//!
//! The rows are one to one with the data file `spec/foreign-forms.toml` (the
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
//!   nodes, the nodes that closed before it, what it wanted). Every matcher
//!   of [`MATCHERS`] runs, and every row that recognises the failure gives
//!   its diagnostic (one failure may be more than one form: `--..<3`); the
//!   driver reports the first of them in the order of the diagnostics
//!   (§18.1, S-281). When none does, the failure is the general E0002. A
//!   form of the syntax stage fails its unit (R-87 (4)): the parser reads it
//!   as nothing else and goes on with the next unit; before the name of a
//!   declaration, a form that ends on its line ([`Hit::resume`]) is reported
//!   and the head is read on after it (§18.1, S-435).
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
//! `nesting::nests_too_deep` from the level the parser read to, [`Cursor::reach`]), which a candidate
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
//! other languages), `calls` (a callee that is no path), `modes` (`&mut`,
//! `mut self`), `decls` (`let mut`, `loop`, `proc`, `#[…]`, `pub(crate)`),
//! `literals` (the number literals, the string delimiters), `faust` (the
//! forms of FAUST, the prefix `~` of C), `comments` (the block comments), `assign` (`+=`, `++`),
//! `ranges` (the range symbols out of place), `guard` (the patterns written
//! as guards), `flow` (`if~`, the clocks) and `spaces` (the blanks inside a
//! line, a literal against a name).
//!
//! To add a row (the later works, W3-05 to W5-09):
//!
//! 1. move the row from [`WAITING`] to [`ROWS`] in `foreign/rows.rs` (a
//!    `RowId` here, the `id`, stage and code of its row in
//!    `spec/foreign-forms.toml`, the message and the rule); a new form is
//!    added to the data file from its decision (an S row of the plan), not
//!    to the text of the spec (§18.1 only names where the list is, S-250);
//! 2. write its matcher in the module of its family (or a new one) and put
//!    it in [`MATCHERS`] with the rows it names ([`Matcher::one`],
//!    [`Matcher::many`], whose rows are a constant next to the matcher; the
//!    row's `detect` is [`Detect::Syntax`]), or call
//!    [`report`] from its stage ([`Detect::Reported`]); a candidate edits only
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
pub(crate) use spaces::held_errors;

/// The kind constraint `Copy` (§4.6): written in bounds, never derived.
pub const COPY: &str = "Copy";
/// The kind constraint `Dup` (§4.6).
pub const DUP: &str = "Dup";
/// The kind constraints (§4.6): the names a bound takes that are no trait, so
/// that the head of a declaration does not take them (`copy_bound`) and the
/// candidate of a derive leaves them out (S-463). The one list.
pub const KIND_CONSTRAINTS: [&str; 2] = [COPY, DUP];

/// The rates written as a type (`Sig[F32]`, the form of the 0.3 draft, the
/// row `rate_as_type`, S-120), in the order of the clocks, slowest first
/// (`init`, `block`, `sample`, §11.3): ordinary names, an E0020 only where
/// they are not found. The one list.
pub const RATE_TYPES: [&str; 3] = ["Init", "Ctl", "Sig"];

/// The rule of a derive (§6.4): the note of the old `@derive` (the row
/// `derive_attribute`) and of a trait that cannot be derived (E0416, whose
/// other note lists the traits, `onsa_sema`). The one text.
pub const DERIVE_RULE: &str = "the traits derived from a type are written at the head of its declaration, `pub struct Key: PartialEq + Eq {`; they are no attribute, their list is closed, and another trait is implemented with `impl Trait for Type` (§6.4)";

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
    /// The `(` of a call whose callee [`crate::callee::Callee::by_name`] says is no callee
    /// written by name (§6.1): the table does not judge the callee again.
    Callee,
    /// A blank or a line break after a prefix `-` / `!` of an expression, or
    /// after the `-` of a negative integer literal of a pattern (§2.5, S-123,
    /// S-369, S-411): the parser judged the gap (`Parser::parse_prefix`,
    /// `Parser::parse_pattern_alt`), at the symbol.
    Prefix,
    /// The `,` or the closing bracket after an element of a list of the
    /// node's kind (`Parser::close_list`, §2.5): the general E0002 of the
    /// failure is the missing `,` (`lists::list_fixes`, S-384).
    Separator(NodeKind),
    /// A tuple index after its `.` that starts with a `0` and is not `0`
    /// itself (`t.01`, §2.4, S-508): the parser judged its digits.
    TupleIndex,
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
    /// The deepest level (§2.5) that the unit of the failure reaches in what
    /// the parser read of it: a candidate that adds levels where it read is
    /// counted by [`crate::nesting::nests_too_deep`] only when it may go over
    /// the limit from there.
    pub reach: u32,
    /// The place of the attribute at `at`, when the parser asks about an
    /// attribute it read ([`at_read`], [`at_heading_hash`]): the parser knows
    /// it there.
    pub place: Option<crate::attrs::Place>,
    /// The keyword of the declaration whose head holds the attribute at
    /// `at`, when the parser asks about it: the parser read the head
    /// (`Parser::parse_heading`), its attributes, visibility and the forms
    /// it reads on after, and the rows read no head again.
    pub declaration: Option<usize>,
}

/// A postfix opener (`(`, `[`, or the mark `!` / `~` before a `(`) or a
/// postfix `?` that the parser did not read on, because a blank or a line
/// break is before it (§2.5, S-89; a `?` where the chain of an expression
/// would read it, R-214): the grammar fails where it fails, and the table
/// reads this at that failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Detached {
    /// The opener, an index of the parser's tokens.
    pub at: usize,
    /// The token before it ends a path of names (§6.1: what a callee is,
    /// [`crate::callee::Callee::by_name`]; a name of a declaration, a type,
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
                let Some((_, comma, semi)) = crate::scan::bracket_contents(tokens, self.at) else { return false };
                crate::scan::empty_brackets(tokens, self.at).is_none() && !semi && !(self.expr && comma)
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

impl End {
    /// What a node of `kind` that the parser closed ends with: the one table
    /// of it (`Parser::complete` records it at the node's last token). A
    /// constant ends with an expression and a type alias or an opaque type
    /// with a type, which a symbol on the next line may go on with. No
    /// wildcard: a new kind decides it here.
    pub(crate) fn of(kind: NodeKind) -> Option<End> {
        use NodeKind::*;
        match kind {
            LetStmt | VarStmt | AssignStmt | ReturnStmt | AssertStmt => Some(End::Bound),
            ForStmt | WhileStmt | Fn | Flow | Struct | Enum | Trait | Impl | Effect | Handler | Use | Extern
            | Target | Test => Some(End::NoOperand),
            Const | TypeAlias | OpaqueType => None,
            SourceFile | Error | Name | Item | Docs | ModuleDocs | Attr | AttrArgs | AttrNamedArg | Vis | FieldList
            | Field | Derives | VariantList | Variant | VariantFields | UseTree | UseNames | ItemList
            | GenericParams | TypeParam | ConstParam | EffectParam | Bound | ParamList | Param | EffectRow | Path
            | TypeArgs | FnTypeParams | BreakStmt | ContinueStmt | ExprStmt | MatchArms | MatchArm | ArgList | Arg
            | StructLitFields | StructLitField | StructPatField | StructPatRest | Clock | Literal | HoleExpr
            | PathExpr | ParenExpr | TupleExpr | ArrayExpr | RepeatExpr | Block | IfExpr | MatchExpr | ClosureExpr
            | HandleExpr | UnsafeExpr | ParExpr | MoveExpr | BinaryExpr | RangeExpr | CastExpr | AtExpr
            | FeedbackExpr | PrefixExpr | CallExpr | FieldExpr | TupleIndexExpr | TypeArgsExpr | IndexExpr
            | TryExpr | StructLit | PathType | ConstArg | UnitType | TupleType | ParenType | ArrayType | FnType
            | WildPat | LitPat | NegLitPat | TuplePat | ParenPat | BindPat | PathPat | TupleStructPat | StructPat
            | OrPat => None,
        }
    }
}

/// A form a row found: its span (the main position), its candidates (none:
/// the diagnostic is E0002 with the note), and whether the place is wrong
/// too (a literal where no expression goes: the parser reports its general
/// E0002 as well, and the driver chooses, S-281).
pub struct Hit {
    pub span: Span,
    pub fixes: Vec<Fix>,
    pub misplaced: bool,
    /// The token right after the form, when the form ends on the line where
    /// it starts: in the head of a declaration, the parser reads on from
    /// there (§18.1, S-435; `Parser::fail_at`).
    pub resume: Option<usize>,
    /// A note after the row's rule, on what the candidates leave out (the
    /// kinds `Copy` and `Dup` a derive does not take, S-463), or on another
    /// reading of the form (the delay `x'` of FAUST, `faust::prime_note`).
    pub note: Option<&'static str>,
    /// The range of a literal right against a name whose form this hit
    /// reports, so that the lexer's errors held in it are not reported (the
    /// row `string_prefix`, S-466; `Failure::prefixed`).
    pub held: Option<Span>,
}

impl Hit {
    /// The form at `span` with `fixes`: in a place of its kind, the parser not
    /// reading on after it, with no note and no literal held. The methods
    /// below set the other fields, so that a field added is written only
    /// where it is set.
    pub(crate) fn new(span: Span, fixes: Vec<Fix>) -> Hit {
        Hit { span, fixes, misplaced: false, resume: None, note: None, held: None }
    }

    /// The hit with the field `misplaced`: whether the place is wrong too.
    pub(crate) fn misplaced_if(self, misplaced: bool) -> Hit {
        Hit { misplaced, ..self }
    }

    /// The hit with the field `resume`: the parser reads on at token `at`.
    pub(crate) fn reading_on(self, at: usize) -> Hit {
        Hit { resume: Some(at), ..self }
    }

    /// The hit with the field `note`.
    pub(crate) fn with_note(self, note: Option<&'static str>) -> Hit {
        Hit { note, ..self }
    }

    /// The hit with the field `held`: the literal at `range`.
    pub(crate) fn holding(self, range: Span) -> Hit {
        Hit { held: Some(range), ..self }
    }
}

/// How a row's form is found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Detect {
    /// Where the parser fails ([`at_failure`]): a matcher of [`MATCHERS`]
    /// names it.
    Syntax,
    /// A type name the parser reads ([`type_name`]).
    TypeName,
    /// A form the parser reads whole, found on the tree after parsing (the
    /// clocks of S-356, [`clocks`]).
    Tree,
    /// A form a later stage finds and reports with [`report`] (the rest `..`
    /// of a struct pattern, `onsa_sema`).
    Reported,
    /// A form the parser reads whole and asks about where it read it
    /// ([`at_read`]: an old attribute, a redundant visibility); a matcher of
    /// [`READS`] names it.
    Read,
}

/// A matcher of the syntax stage: a plain function of the cursor that
/// recognises a form at the failure, and the rows it may name. A matcher of
/// one row gives the hit ([`Matcher::one`]); a matcher of several gives the
/// row with it ([`Matcher::many`]), and its module lists those rows next to
/// it (`<NAME>_ROWS`), so that a row it comes to name is listed where it is
/// found. The registry of [`MATCHERS`] says which rows each finds.
pub struct Matcher {
    /// The rows the matcher may name.
    pub rows: &'static [RowId],
    find: Find,
}

#[derive(Clone, Copy)]
enum Find {
    One(fn(&Cursor) -> Option<Hit>),
    Many(fn(&Cursor) -> Option<(RowId, Hit)>),
}

impl Matcher {
    /// A matcher of the one row `rows[0]`.
    pub(crate) const fn one(rows: &'static [RowId; 1], find: fn(&Cursor) -> Option<Hit>) -> Matcher {
        Matcher { rows, find: Find::One(find) }
    }

    /// A matcher that names one of `rows`.
    pub(crate) const fn many(rows: &'static [RowId], find: fn(&Cursor) -> Option<(RowId, Hit)>) -> Matcher {
        Matcher { rows, find: Find::Many(find) }
    }

    /// The row and the hit of the failure `c`, when the matcher recognises
    /// it. A row the matcher does not list is a bug of the table.
    fn find(&self, c: &Cursor) -> Option<(RowId, Hit)> {
        let (row, hit) = match self.find {
            Find::One(find) => (self.rows[0], find(c)?),
            Find::Many(find) => find(c)?,
        };
        if !self.rows.contains(&row) {
            onsa_diag::internal::bug(Some(hit.span), format!("a matcher of {:?} names {row:?}", self.rows));
        }
        Some((row, hit))
    }
}

/// The rows the compiler finds. `name` is the row's `id` in
/// `spec/foreign-forms.toml`.
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
    FloatDotExponent,
    OctalPrefix,
    LeadingZero,
    LiteralSuffix,
    BlockComment,
    BlockCommentUnclosed,
    BlockCommentNested,
    BlockCommentMultilineCodeAfter,
    StringDelimiter,
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
    HashAttributeNoCandidate,
    HashAttributeUnfixable,
    DeriveAttribute,
    RelaxedAttribute,
    BulkAttribute,
    MemFast,
    OldAttributeNoCandidate,
    TupleStruct,
    TupleStructMany,
    FaustBitNot,
    FaustFeedback,
    FaustFeedbackUnnamed,
    FaustDelay,
    FaustDelayVariable,
    FaustCompose,
    PubCrate,
    PubPkg,
    PubRestricted,
    FieldPubCrate,
    FieldPub,
    ImplMemberPub,
    PrivUse,
    ConstFn,
    ExternFn,
    ExportC,
    CopyBound,
    TypeArgsTurbofish,
    TypeArgsAngle,
    TypeArgsSquareComma,
    TypeArgsOnExpression,
    ValueCall,
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
    TupleIndexLeadingZero,
    CalleeExpression,
    SpaceAfterBranchKeyword,
    ElseIfTilde,
    ClockOnBinding,
    ClockInType,
    RateAsType,
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
    diagnostic(text, id, Hit::new(span, fixes))
}

fn diagnostic(text: &str, id: RowId, hit: Hit) -> Diagnostic {
    let row = row(id);
    let code = if hit.fixes.is_empty() { row.code.without_fixes() } else { row.code };
    let mut d = Diagnostic::new(row.phase.stage(), code, hit.span, row.message);
    let found = &text[hit.span.start as usize..hit.span.end as usize];
    if !found.trim().is_empty() {
        d = d.with_found(found);
    }
    for f in hit.fixes {
        d = d.with_fix(f);
    }
    d = d.with_rule(row.rule);
    match hit.note {
        Some(note) => d.with_rule(note),
        None => d,
    }
}

/// What the table says of a failure of the parser: the diagnostic of the row
/// that recognises it, if one does, and the candidates of the parser's
/// general E0002 when that is reported too (no row, or a form in a place
/// where nothing of its kind goes, [`Hit`]): the missing `,` of a list and
/// the gap before an opener taken out ([`lists::list_fixes`]).
pub(crate) struct Failure {
    pub rows: Vec<Diagnostic>,
    pub general: Option<Vec<Fix>>,
    /// The range of the literal right against a name whose form a row
    /// reported ([`Hit::held`]: the row `string_prefix`): the parser keeps it
    /// with its diagnostics, and its held errors are not reported
    /// ([`spaces::held_errors`]).
    pub prefixed: Option<Span>,
    /// Where the form a row found ends on its line ([`Hit::resume`]).
    pub resume: Option<usize>,
}

/// The table's reading of a failure of the parser ([`Failure`]): every
/// matcher runs, and the diagnostic of every row that recognises the failure
/// is reported. The table does not choose among them: one failure may be
/// read as more than one form (`--..<3`, a `--` and a range pattern), and the
/// driver reports, of the diagnostics of a unit, the first in the order of
/// the diagnostics (start, end, code, message; §18.1, S-281,
/// `onsa_driver::reduce`), the one place of that choice. Four readings of a
/// token that the decisions fixed are in the matchers instead, and are no
/// order of the rows: a `+` and a `&` at the head of a line after an operand
/// are the binary operator (S-405, W3-06; the order of the diagnostics gives
/// the same, by the order of their messages), and a `--` is one form or the
/// other (S-297, S-320) and a float in a pattern is the float pattern
/// (S-248), which the order of the diagnostics would not give. The general
/// E0002 is reported too when no row recognises the failure, or when a form
/// is where nothing of its kind goes ([`Hit::misplaced`]).
pub(crate) fn at_failure(c: &Cursor) -> Failure {
    let mut rows = Vec::new();
    let mut misplaced = false;
    let mut prefixed = None;
    let mut resume = None;
    for m in MATCHERS {
        if let Some((row, hit)) = m.find(c) {
            misplaced |= hit.misplaced;
            prefixed = prefixed.or(hit.held);
            resume = resume.or(hit.resume);
            rows.push(diagnostic(c.text, row, hit));
        }
    }
    // After an element of a list, the general error is the missing `,`;
    // an opener after a line break takes it out (S-89).
    let general = (rows.is_empty() || misplaced).then(|| match c.want {
        Want::Separator(list) => lists::list_fixes(c, Some(list)),
        _ => lists::list_fixes(c, None),
    });
    Failure { rows, general, prefixed, resume }
}

/// The table's reading of a form the parser read whole at `c.at`
/// ([`Detect::Read`]): the diagnostic of every matcher of [`READS`] that
/// names it. The parser reads on.
pub(crate) fn at_read(c: &Cursor) -> Vec<Diagnostic> {
    READS.iter().filter_map(|m| m.find(c)).map(|(row, hit)| diagnostic(c.text, row, hit)).collect()
}

/// The table's reading of a `#[…]` at `c.at` in the head of a declaration,
/// which the parser read on after (S-435) and asks about when it has read
/// the head (`c.place` and `c.declaration`; none when the head failed): the
/// row of [`decls::hash_attribute`], as at a failure, at the place the
/// parser knows (§6.5), as the attributes of Onsa are checked there.
/// `failed`: the head of a declaration began and failed, so the place is not
/// known ([`decls::hash_attribute_in`]).
pub(crate) fn at_heading_hash(c: &Cursor, failed: bool) -> Option<Diagnostic> {
    let (row, hit) = decls::hash_attribute_in(c, failed)?;
    Some(diagnostic(c.text, row, hit))
}

// ------------------------------------------------------------ the cursor

impl Cursor<'_> {
    /// The index `i` of a token, or of the `Eof` that ends the tokens when
    /// `i` is past it: the reads of a token by its index (its kind, span and
    /// gaps) read past the end as the `Eof`, so a row that looks a few tokens
    /// ahead (`c.at + 2`) does not fail at the end of a file.
    fn clamp(&self, i: usize) -> usize {
        i.min(self.tokens.len() - 1)
    }

    pub(crate) fn kind(&self, i: usize) -> TokenKind {
        self.tokens[self.clamp(i)].kind
    }

    pub(crate) fn span(&self, i: usize) -> Span {
        self.tokens[self.clamp(i)].span
    }

    fn src(&self, i: usize) -> &str {
        let s = self.span(i);
        &self.text[s.start as usize..s.end as usize]
    }

    fn is_ident(&self, i: usize, text: &str) -> bool {
        self.kind(i) == TokenKind::Ident && self.src(i) == text
    }

    /// Whether token `i` is the word `mut` of other languages, which Onsa
    /// has not (a name): the one test of it (`let mut`, `mut self`, `&mut`).
    pub(crate) fn mut_word(&self, i: usize) -> bool {
        self.is_ident(i, "mut")
    }

    /// Whether the `&` at `amp` is the `&mut` of other languages: the word
    /// `mut` is the next code after it (a line break or a comment between
    /// them is passed over, as the code of a line is read).
    pub(crate) fn ref_mut(&self, amp: usize) -> bool {
        self.mut_word(self.sig_after(amp))
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
        self.lines.after(self.clamp(i))
    }

    /// What separates `tokens[i]` from the token before it ([`crate::layout::Lines::before`]).
    pub(crate) fn gap(&self, i: usize) -> Gap {
        self.lines.before(self.clamp(i))
    }

    /// Whether `tokens[i]` is at the head of its line ([`crate::layout::Lines::at_line_head`]).
    pub(crate) fn at_line_head(&self, i: usize) -> bool {
        self.lines.at_line_head(self.clamp(i))
    }

    /// Whether the token at the failure is a postfix `?` after a gap that
    /// the chain of an expression stopped before (`Parser::parse_postfix`,
    /// [`Detached`]): only there does a candidate write it against the
    /// chain (§2.5, R-214).
    pub(crate) fn question_detached(&self) -> bool {
        self.kind(self.at) == TokenKind::Question && self.detached.is_some_and(|d| d.at == self.at)
    }

    /// The whitespace token right after `tokens[i]`, if any.
    pub(crate) fn space_after(&self, i: usize) -> Option<Span> {
        let k = self.full[self.clamp(i)] as usize + 1;
        self.all.get(k).filter(|t| t.kind == TokenKind::Whitespace).map(|t| t.span)
    }

    /// The whitespace token right before `tokens[i]`, if any.
    pub(crate) fn space_before(&self, i: usize) -> Option<Span> {
        let k = (self.full[self.clamp(i)] as usize).checked_sub(1)?;
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
        crate::lexer::line_start(self.text, offset)
    }

    /// The blanks that start the line of `offset`.
    fn indent(&self, offset: u32) -> &str {
        crate::lexer::indent(self.text, offset)
    }

    /// The line break that ends the line of `offset` (`\r\n` where the
    /// file writes one there), for a candidate that breaks a line.
    fn line_break(&self, offset: u32) -> &'static str {
        let rest = &self.text[offset as usize..];
        match rest.find('\n') {
            Some(i) if rest[..i].ends_with('\r') => "\r\n",
            _ => "\n",
        }
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
        let s = self.symbol_ahead();
        if !self.lines.at_line_head(s) {
            return None;
        }
        let prev = self.sig_before(s)?;
        let kind = self.kind(s);
        let operand = ends_operand(self.kind(prev)) || (matches!(kind, Pipe | Eq) && self.kind(prev) == Underscore);
        let head = matches!(kind, Arrow | Eq);
        (operand && (head || self.end_at(prev) != Some(End::NoOperand))).then_some((s, prev))
    }

    /// The symbol the failure is at: the token of the failure, or, when the
    /// parser failed at a line break, the first token of the next line
    /// ([`Cursor::head_symbol_after_operand`]; a row asks its kind first).
    pub(crate) fn symbol_ahead(&self) -> usize {
        if self.kind(self.at) == TokenKind::Newline { self.sig_after(self.at) } else { self.at }
    }

    /// What the statement or declaration whose last token is `i` ends with,
    /// when the parser read one to its end there ([`End`]).
    pub(crate) fn end_at(&self, i: usize) -> Option<End> {
        self.ends.binary_search_by_key(&i, |e| e.0).ok().map(|k| self.ends[k].1)
    }
}

/// The hit of a matcher of one row ([`Matcher::one`]).
fn hit(span: Span, fixes: Vec<Fix>) -> Option<Hit> {
    Some(Hit::new(span, fixes))
}

/// The row and the hit of a matcher of several rows ([`Matcher::many`]).
fn found(row: RowId, span: Span, fixes: Vec<Fix>) -> Option<(RowId, Hit)> {
    Some((row, Hit::new(span, fixes)))
}

/// [`found`] for a form that ends on its line, before token `resume`
/// ([`Hit::resume`]).
fn found_reading_on(row: RowId, span: Span, fixes: Vec<Fix>, resume: usize) -> Option<(RowId, Hit)> {
    Some((row, Hit::new(span, fixes).reading_on(resume)))
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

/// The bracket that closes the one at `open` (`(`, `[` or `{`; none at any
/// other token, [`crate::scan::closing`]).
pub(crate) fn closing(c: &Cursor, open: usize) -> Option<usize> {
    crate::scan::closing(c.tokens, open)
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

pub use paths::TYPE_NAMES;
pub(crate) use paths::{type_list_ahead, type_name};
pub use rows::{MATCHERS, READS, ROWS, WAITING};
// The helpers that the rows of `guard` and `flow` share with a family.
use assign::operand;
use faust::bit_not;
use literals::float_spelling_at;
use paths::is_segment;
