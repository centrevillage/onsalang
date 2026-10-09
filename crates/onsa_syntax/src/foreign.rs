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
//!   at that failure ([`type_args_call`], with `f::<T>(x)`, where the parser
//!   fails by itself).
//! - A type name that the parser reads as a name (`i32`): [`type_name`], the
//!   one entry where the parser does not fail, called where it reads a type.
//! - The names, types and flow stages build their diagnostic with
//!   [`report`]: they find the form and give the span and the candidates; the
//!   code, the stage, the message and the note come from the row.
//!
//! To add a row (the later works, W3-05 to W5-09):
//!
//! 1. move the row from [`WAITING`] to [`ROWS`] (a `RowId`, the `id`, stage
//!    and code of its row in `docs/foreign-forms.toml`, the message and the
//!    rule); a new form is added to the data file from its decision (an S
//!    row of the plan), not to the text of the spec (§18.1 only names where
//!    the list is, S-250);
//! 2. write its matcher ([`Detect::Syntax`]) or call [`report`] from its
//!    stage; a candidate edits only the tokens it changes (S-251), one form
//!    is one diagnostic with one candidate that fixes all of it (S-248), and
//!    a form for which no candidate keeps the contract of §18.1 (S-236) has
//!    none (the diagnostic is then E0002 with the note);
//! 3. remove the `foreign-form` entry of the row from `tests/pending.toml`
//!    (and the `test-case` or `fix-contract` entries of its cases): the
//!    examples of the data file run through the same entry as the cases, and
//!    every candidate is checked against the contract (W3-17).

use onsa_diag::{Code, Diagnostic, Edit, FileId, Fix, Span, Stage};

use crate::cst::NodeKind;
use crate::token::{Gap, Token, TokenKind};

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
    /// The holes of the string literals (`{name}`, [`crate::Lexed::holes`]).
    pub holes: &'a [Span],
    /// The token the parser failed at (an index of `tokens`).
    pub at: usize,
    /// The open nodes, outermost first, and where each starts.
    pub open: Vec<(NodeKind, u32)>,
    /// The nodes that closed at the token before `at`, innermost first, and
    /// where each starts.
    pub closed: &'a [(NodeKind, u32)],
    pub want: Want,
    /// The row a matcher of several rows found ([`Cursor::say`]).
    pub found: std::cell::Cell<Option<RowId>>,
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
    HashAttribute,
    FaustBitNot,
    PubCrate,
    TypeArgsTurbofish,
    TypeArgsAngle,
    TypeArgsSquareComma,
    TypeArgsOnExpression,
    TypePositionPath,
    SpaceInTypeArgsMark,
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

const NO_REFERENCES: &str =
    "there are no references: an argument is borrowed by default and changed with `inout` before it (§5.2)";
const SEMICOLON_RULE: &str = "a statement or declaration ends at the end of its line; there is no `;` (§2.5)";
const FLOAT_LITERAL_RULE: &str = "a float literal with a point has digits on both sides of it (`1.0`, `0.5`, §2.4)";
const BLOCK_COMMENT_RULE: &str =
    "comments are line comments `//`, to the end of the line; `///` documents the next declaration (§2.1)";

pub static ROWS: &[Row] = &[
    Row {
        id: RowId::Semicolon,
        name: "semicolon",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "`;` is not used in Onsa; a statement or declaration ends at the end of its line",
        rule: SEMICOLON_RULE,
        detect: Detect::Syntax(semicolon),
    },
    Row {
        id: RowId::SemicolonInList,
        name: "semicolon_in_list",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "the elements of a list are separated with `,`",
        rule: "the elements of a list (fields, arguments, parameters, ...) are separated with `,`; there is no `;` (§2.5)",
        detect: Detect::Syntax(semicolon_in_list),
    },
    Row {
        id: RowId::PathSeparator,
        name: "path_separator",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "paths are separated with `.`",
        rule: "the separator of a path is `.` (`F32.PI`, `std.math`, §15.1)",
        detect: Detect::Syntax(path_separator),
    },
    Row {
        id: RowId::AngleBrackets,
        name: "angle_brackets",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "type parameters and type arguments are written in `[ ]`",
        rule: "type parameters and type arguments are written in `[ ]` (§4.5)",
        detect: Detect::Syntax(angle_brackets),
    },
    Row {
        id: RowId::RefMutParam,
        name: "ref_mut_param",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "`&mut T` is written `inout name: T`; the mode comes before the name",
        rule: NO_REFERENCES,
        detect: Detect::Syntax(reference),
    },
    Row {
        id: RowId::RefMutSelf,
        name: "ref_mut_self",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "a receiver that changes is written `inout self`",
        rule: "the mode comes before the name; a receiver that changes is `inout self` (§5.2)",
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::MutSelf,
        name: "mut_self",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "a receiver the method takes is written `move self`",
        rule: "the mode comes before the name: `self` borrows, `inout self` changes the caller's value, `move self` takes it (§5.2)",
        detect: Detect::Syntax(mut_self),
    },
    Row {
        id: RowId::RefSelf,
        name: "ref_self",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "`&self` is the default borrow; write `self`",
        rule: "the mode comes before the name; `self` is borrowed by default (§5.2)",
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::RefType,
        name: "ref_type",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "`&T` is the default borrow; write the type without `&`",
        rule: NO_REFERENCES,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::RefExpr,
        name: "ref_expr",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "there are no references; a value is borrowed by default",
        rule: NO_REFERENCES,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::RefMutArg,
        name: "ref_mut_arg",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "an argument that changes is written `inout x`",
        rule: NO_REFERENCES,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::RefMutOther,
        name: "ref_mut_other",
        phase: Phase::Syntax,
        code: Code::E0002,
        message: "there are no mutable references; only a parameter or an argument changes a value it borrows, with `inout`",
        rule: NO_REFERENCES,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::LowercaseType,
        name: "lowercase_type",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "built-in types are written in UpperCamel (`I32`, `F32`, `Bool`)",
        rule: "type names are UpperCamel, the built-in ones too (`I32`, `F32`, `Bool`, `Char`, `Str`, §2.3)",
        detect: Detect::TypeName,
    },
    Row {
        id: RowId::CompoundAssign,
        name: "compound_assign",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "there is no compound assignment; write the operation out",
        rule: "an assignment is `place = value`; the operation is written out, `x = x + 1` (§5.1)",
        detect: Detect::Syntax(compound_assignment),
    },
    Row {
        id: RowId::CompoundAssignUnfixable,
        name: "compound_assign_unfixable",
        phase: Phase::Syntax,
        code: Code::E0002,
        message: "there is no compound assignment, and this one cannot be written out as it stands",
        rule: "an assignment is `place = value`; the operation is written out, `x = x + 1` (§5.1)",
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::Increment,
        name: "increment",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "there is no `++` or `--`; write the assignment out",
        rule: "there is no increment; a statement `x = x + 1` writes it out (§5.1)",
        detect: Detect::Syntax(increment),
    },
    Row {
        id: RowId::IncrementUnfixable,
        name: "increment_unfixable",
        phase: Phase::Syntax,
        code: Code::E0002,
        message: "there is no `++` or `--`, and an assignment is a statement, not an expression",
        rule: "there is no increment; a statement `x = x + 1` writes it out (§5.1)",
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::LetMut,
        name: "let_mut",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "a local that changes is declared with `var`",
        rule: "`let` binds a value that does not change; a local that changes is declared with `var` (§5.1)",
        detect: Detect::Syntax(let_mut),
    },
    Row {
        id: RowId::Loop,
        name: "loop",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "there is no `loop`; an endless loop is `while true`",
        rule: "the loops are `while` and `for`; an endless loop is `while true` (§7)",
        detect: Detect::Syntax(endless_loop),
    },
    Row {
        id: RowId::Proc,
        name: "proc",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "a signal-processing node is declared with `flow`",
        rule: "a stateful signal-processing node is declared with `flow` (§11)",
        detect: Detect::Syntax(proc),
    },
    Row {
        id: RowId::FloatTrailingDot,
        name: "float_trailing_dot",
        phase: Phase::Lexical,
        code: Code::E0020,
        message: "a float literal needs digits on both sides of the point",
        rule: FLOAT_LITERAL_RULE,
        detect: Detect::Syntax(foreign_literal),
    },
    Row {
        id: RowId::FloatLeadingDot,
        name: "float_leading_dot",
        phase: Phase::Lexical,
        code: Code::E0020,
        message: "a float literal needs digits on both sides of the point",
        rule: FLOAT_LITERAL_RULE,
        detect: Detect::Syntax(leading_point),
    },
    Row {
        id: RowId::LiteralSuffix,
        name: "literal_suffix",
        phase: Phase::Lexical,
        code: Code::E0020,
        message: "literals have no type suffix; the type comes from the context",
        rule: "a literal has no type suffix; its type comes from the context or an annotation (§2.4)",
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::BlockComment,
        name: "block_comment",
        phase: Phase::Lexical,
        code: Code::E0020,
        message: "Onsa has no block comments; comments are line comments `//`",
        rule: BLOCK_COMMENT_RULE,
        detect: Detect::Syntax(block_comment),
    },
    Row {
        id: RowId::BlockCommentUnclosed,
        name: "block_comment_unclosed",
        phase: Phase::Lexical,
        code: Code::E0002,
        message: "Onsa has no block comments, and this one is never closed",
        rule: BLOCK_COMMENT_RULE,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::BlockCommentNested,
        name: "block_comment_nested",
        phase: Phase::Lexical,
        code: Code::E0002,
        message: "Onsa has no block comments, and this one holds another",
        rule: BLOCK_COMMENT_RULE,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::BlockCommentMultilineCodeAfter,
        name: "block_comment_multiline_code_after",
        phase: Phase::Lexical,
        code: Code::E0002,
        message: "Onsa has no block comments, and code follows this one on the line it ends",
        rule: BLOCK_COMMENT_RULE,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::FloatPattern,
        name: "float_pattern",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "float literals cannot be patterns; compare in a guard",
        rule: "a pattern holds no float literal; IEEE equality is written in a guard, `x if x == 1.0` (§7)",
        detect: Detect::Syntax(float_pattern),
    },
    Row {
        id: RowId::FloatPatternChoice,
        name: "float_pattern_choice",
        phase: Phase::Syntax,
        code: Code::E0002,
        message: "float literals cannot be patterns, and these alternatives do not merge into one guard",
        rule: "a pattern holds no float literal; alternatives of other shapes are split into arms, or written in a guard (§7)",
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::HashAttribute,
        name: "hash_attribute",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "attributes are written `@name(...)`",
        rule: "an attribute is written `@name(...)` (§6.5)",
        detect: Detect::Syntax(hash_attribute),
    },
    Row {
        id: RowId::FaustBitNot,
        name: "faust_bit_not",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "bits are negated with the prefix `!`",
        rule: "the bitwise negation is the prefix `!` (§2.6); a prefix `~` reads as the feedback of FAUST",
        detect: Detect::Syntax(faust_bit_not),
    },
    Row {
        id: RowId::PubCrate,
        name: "pub_crate",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "`pub(crate)` is visibility within the package, which is the default; remove it",
        rule: "visibility is `pub` (outside the package), nothing (the package), or `priv` (§15.1)",
        detect: Detect::Syntax(pub_crate),
    },
    Row {
        id: RowId::TypeArgsTurbofish,
        name: "type_args_turbofish",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "type arguments in an expression are written `name::[…]`, in `[ ]`",
        rule: TYPE_ARGS_RULE,
        detect: Detect::Syntax(type_args_call),
    },
    Row {
        id: RowId::TypeArgsAngle,
        name: "type_args_angle",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "type arguments of a call are written `name::[…]`, not in `< >`",
        rule: TYPE_ARGS_RULE,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::TypeArgsSquareComma,
        name: "type_args_square_comma",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "type arguments in an expression are written `name::[…]`; a `[…]` with `,` is no index",
        rule: TYPE_ARGS_RULE,
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::TypeArgsOnExpression,
        name: "type_args_on_expression",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "a function value takes no type arguments; it is called with `.(`",
        rule: "a function value is called with `.(` (§6.1); type arguments go after the name of an item, `name::[T]` (§4.5)",
        detect: Detect::Syntax(no_match),
    },
    Row {
        id: RowId::TypePositionPath,
        name: "type_position_path",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "a type writes its arguments in `[ ]` without `::`",
        rule: "in a type the arguments follow the name, `Buf[F32]`; `name::[…]` is written only in an expression, where a `[` alone is an index (§4.5)",
        detect: Detect::Syntax(type_position_path),
    },
    Row {
        id: RowId::SpaceInTypeArgsMark,
        name: "space_in_type_args_mark",
        phase: Phase::Syntax,
        code: Code::E0020,
        message: "`::[` is written without spaces",
        rule: "type arguments in an expression are written `name::[T]`, with no space before or after the `::` (§2.5, §4.5)",
        detect: Detect::Syntax(space_in_type_args_mark),
    },
];

/// The rows of the data file that no work has made yet (the later works
/// of W3 to W7; [`Waiting`]).
pub static WAITING: &[Waiting] = &[
    Waiting { name: "arm_return", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "octal_prefix", phase: Phase::Lexical, code: Code::E0020 },
    Waiting { name: "leading_zero", phase: Phase::Lexical, code: Code::E0020 },
    Waiting { name: "float_dot_exponent", phase: Phase::Lexical, code: Code::E0020 },
    Waiting { name: "space_before_paren", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "space_before_bracket", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "space_around_dot", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "space_before_question", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "space_before_bang", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "space_before_tilde", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "space_after_prefix", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "space_after_caret", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "leading_operator", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "leading_minus", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "value_call", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "item_dot_call", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "callee_expression", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "indexed_value_call", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "field_call", phase: Phase::Types, code: Code::E0020 },
    Waiting { name: "interpolated_string_pattern", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "float_constant_pattern", phase: Phase::Types, code: Code::E0020 },
    Waiting { name: "negated_constant_pattern", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "at_binding", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "at_binding_complex", phase: Phase::Syntax, code: Code::E0002 },
    Waiting { name: "struct_pattern_rest", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "range_pattern", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "range_pattern_choice", phase: Phase::Syntax, code: Code::E0002 },
    Waiting { name: "range_dots", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "range_outside_header", phase: Phase::Syntax, code: Code::E0002 },
    Waiting { name: "type_args_square", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "type_args_method_square", phase: Phase::Types, code: Code::E0020 },
    Waiting { name: "rate_as_type", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "caret_visible", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "faust_feedback", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "faust_feedback_unnamed", phase: Phase::Syntax, code: Code::E0002 },
    Waiting { name: "faust_prime", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "faust_delay", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "faust_delay_variable", phase: Phase::Syntax, code: Code::E0002 },
    Waiting { name: "faust_compose", phase: Phase::Syntax, code: Code::E0002 },
    Waiting { name: "derive_attribute", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "relaxed_attribute", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "bulk_attribute", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "mem_fast", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "field_pub", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "field_priv_in_priv_struct", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "pub_pkg", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "priv_use", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "tuple_struct", phase: Phase::Syntax, code: Code::E0020 },
    Waiting { name: "copy_impl", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "copy_bound", phase: Phase::Names, code: Code::E0020 },
    Waiting { name: "clock_on_binding", phase: Phase::Syntax, code: Code::E0020 },
];

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

/// The diagnostics of a failure of the parser, when a row recognises it, and
/// whether the parser's general E0002 is to be reported too ([`Hit`]).
pub(crate) fn at_failure(c: &Cursor) -> Option<(Diagnostic, bool)> {
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

/// The type names of other languages (`i32`: `I32`, `usize`: `U32`, S-250).
/// `String`, `Vec`, `i128` and `u128` are not here: they are names that
/// are not declared (E0302).
pub const TYPE_NAMES: &[(&str, &str)] = &[
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
    ("char", "Char"),
    ("str", "Str"),
];

/// A type written as one name `t`: the E0020 of a built-in type name of
/// another language (`i32`). The parser fails the unit on it.
pub(crate) fn type_name(text: &str, t: Token) -> Option<Diagnostic> {
    let name = &text[t.span.start as usize..t.span.end as usize];
    let (_, fix) = TYPE_NAMES.iter().find(|(from, _)| *from == name)?;
    let fix = Fix::replace("write the built-in type name", t.span, *fix);
    Some(diagnostic(text, RowId::LowercaseType, Hit { span: t.span, fixes: vec![fix], misplaced: false }))
}

/// Whether a number may carry `suffix` as a type suffix of another
/// language (§2.4, §18.1): the lexer reads such a number as one token.
/// Every suffix until W3-05 closes the list (the others are E0001 then).
pub(crate) fn is_type_suffix(_suffix: &str) -> bool {
    true
}

// ------------------------------------------------------------ the cursor

impl Cursor<'_> {
    fn kind(&self, i: usize) -> TokenKind {
        self.tokens[i].kind
    }

    fn span(&self, i: usize) -> Span {
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
    /// its own row reports; elsewhere it is passed over as a comment).
    fn comment(&self, i: usize) -> bool {
        matches!(self.kind(i), TokenKind::Comment | TokenKind::DocComment | TokenKind::BlockComment)
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
    fn sig_after(&self, i: usize) -> usize {
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
    fn sig_before(&self, i: usize) -> Option<usize> {
        (0..i).rev().find(|&j| !self.comment(j) && self.kind(j) != TokenKind::Newline)
    }

    /// The token right before `i` on its line (a comment or a newline before
    /// it gives none).
    fn before(&self, i: usize) -> Option<usize> {
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

    /// What separates `tokens[i]` from the token before it.
    fn gap(&self, i: usize) -> Gap {
        crate::token::gap_before(self.all, self.full[i] as usize)
    }

    /// The whitespace token right after `tokens[i]`, if any.
    fn space_after(&self, i: usize) -> Option<Span> {
        let k = self.full[i] as usize + 1;
        self.all.get(k).filter(|t| t.kind == TokenKind::Whitespace).map(|t| t.span)
    }

    /// The whitespace token right before `tokens[i]`, if any.
    fn space_before(&self, i: usize) -> Option<Span> {
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
    fn index_at(&self, offset: u32) -> usize {
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
    /// A matcher of several rows says which row it found (a matcher is a
    /// plain function of the cursor).
    fn say(&self, row: RowId) {
        self.found.set(Some(row));
    }
}

fn hit(span: Span, fixes: Vec<Fix>) -> Option<Hit> {
    Some(Hit { span, fixes, misplaced: false })
}

/// A name or a path of names: `x`, `self.a.b` (tokens `first..=last`, no
/// newline between).
// SPEC-GAP(S-322): a tuple index (`t.0`) is no part of a path of fields here,
// until S-322.
fn is_place(c: &Cursor, first: usize, last: usize) -> bool {
    if first > last {
        return false;
    }
    (first..=last).enumerate().all(|(k, i)| {
        if k % 2 == 0 { matches!(c.kind(i), TokenKind::Ident | TokenKind::KwSelf) } else { c.kind(i) == TokenKind::Dot }
    }) && (last - first) % 2 == 0
}

/// Where the statement that goes on at token `from` ends: the last token of
/// it (a newline ends it unless the line ends with an operator or `=`, or the
/// next starts with `.`; a `}` or `)` that closes what it is in ends it too).
fn statement_end(c: &Cursor, from: usize) -> Option<usize> {
    let mut depth = 0i32;
    let mut last: Option<usize> = None;
    let mut i = from;
    while i < c.tokens.len() {
        match c.kind(i) {
            TokenKind::Eof | TokenKind::Semi => break,
            _ if c.comment(i) => {}
            TokenKind::Newline if depth == 0 => {
                let continued = last.is_some_and(|l| {
                    c.kind(l).is_binary_op()
                        || matches!(c.kind(l), TokenKind::Eq | TokenKind::Arrow | TokenKind::FatArrow)
                }) || c.kind(c.sig_after(i)) == TokenKind::Dot;
                if !continued {
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

// ------------------------------------------------------------ `;`

/// The nodes that hold statements or declarations, one per line.
fn holds_lines(kind: Option<NodeKind>) -> bool {
    matches!(kind, Some(NodeKind::Block | NodeKind::SourceFile | NodeKind::ItemList))
}

/// The lists whose elements are separated with `,`.
fn comma_list(kind: Option<NodeKind>) -> bool {
    matches!(
        kind,
        Some(
            NodeKind::ArgList
                | NodeKind::ParamList
                | NodeKind::FieldList
                | NodeKind::VariantList
                | NodeKind::VariantFields
                | NodeKind::TupleExpr
                | NodeKind::StructLitFields
                | NodeKind::GenericParams
                | NodeKind::TypeArgs
                | NodeKind::TupleType
                | NodeKind::FnTypeParams
                | NodeKind::TuplePat
                | NodeKind::TupleStructPat
                | NodeKind::StructPat
                | NodeKind::MatchArms
                | NodeKind::UseNames
                | NodeKind::EffectRow
                | NodeKind::AttrArgs
        )
    )
}

/// The run of `;` at `c.at` on one line (S-248: `;;` is one form).
fn semicolon_run(c: &Cursor) -> Option<usize> {
    if c.kind(c.at) != TokenKind::Semi {
        return None;
    }
    let mut last = c.at;
    while c.kind(last + 1) == TokenKind::Semi {
        last += 1;
    }
    Some(last)
}

/// The edits that remove the run `first..=last` of `;` (each token: the
/// spaces between stay).
fn remove_run(c: &Cursor, first: usize, last: usize) -> Vec<Edit> {
    (first..=last).map(|i| Edit::delete(c.span(i))).collect()
}

/// `;` at the end of a statement or a declaration (§2.5). The candidate
/// removes it; with code after it on its line (`let a = 1; let b = 2`), it
/// puts that code on a line of its own, at the indentation of the line.
fn semicolon(c: &Cursor) -> Option<Hit> {
    let last = semicolon_run(c)?;
    let context = c.context().map(|o| o.1);
    // `return;`: the statement `return` ends at the `;`.
    let after_return =
        context == Some(NodeKind::ReturnStmt) && c.sig_before(c.at).is_some_and(|p| c.kind(p) == TokenKind::KwReturn);
    if !holds_lines(context) && !after_return {
        return None;
    }
    // What comes before can end a statement (not `let x = ;`).
    if let Some(p) = c.sig_before(c.at)
        && (c.kind(p).is_binary_op()
            || matches!(
                c.kind(p),
                TokenKind::Eq
                    | TokenKind::Comma
                    | TokenKind::Colon
                    | TokenKind::Dot
                    | TokenKind::Arrow
                    | TokenKind::FatArrow
                    | TokenKind::LParen
                    | TokenKind::LBracket
                    | TokenKind::Bang
                    | TokenKind::Tilde
                    | TokenKind::At
                    | TokenKind::KwLet
                    | TokenKind::KwVar
                    | TokenKind::KwAs
            ))
    {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(last).end);
    let next = c.after(last);
    let fix = if matches!(c.kind(next), TokenKind::Newline | TokenKind::Eof | TokenKind::RBrace)
        || matches!(c.kind(last + 1), TokenKind::Comment | TokenKind::DocComment)
    {
        Fix::new(if last > c.at { "remove the `;`s" } else { "remove the `;`" }, remove_run(c, c.at, last))
    } else {
        // The next statement goes to a line of its own.
        let indent = c.indent(c.span(c.at).start).to_string();
        let gap = c.file_span(c.span(c.at).start, c.span(next).start);
        Fix::replace("end the line at the `;`", gap, format!("\n{indent}"))
    };
    hit(span, vec![fix])
}

/// `;` between the elements of a list (a struct's fields, the arguments):
/// the separator is `,` (S-250). Before the closing bracket, it is removed.
fn semicolon_in_list(c: &Cursor) -> Option<Hit> {
    let last = semicolon_run(c)?;
    if !comma_list(c.context().map(|o| o.1)) {
        return None;
    }
    // After an element (not `(;` or `,;`).
    if c.sig_before(c.at).is_none_or(|p| {
        matches!(c.kind(p), TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace | TokenKind::Comma)
    }) {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(last).end);
    let next = c.sig_after(last);
    let fix = if matches!(c.kind(next), TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
        Fix::new("remove the `;`", remove_run(c, c.at, last))
    } else {
        let mut edits = vec![Edit::replace(c.span(c.at), ",")];
        edits.extend(remove_run(c, c.at + 1, last).into_iter().filter(|_| last > c.at));
        Fix::new("separate with `,`", edits)
    };
    hit(span, vec![fix])
}

// ------------------------------------------------------------ `::`

fn is_segment(kind: TokenKind) -> bool {
    kind == TokenKind::Ident || kind.is_keyword()
}

/// `::` between the names of a path (`F32::PI`, `std::math::sqrt`, `use
/// a::{b}`): one path is one form, and the candidate writes every `::` of it
/// as `.` (S-248). The path goes on across a `::[…]` of type arguments
/// (`m::Buf::[F32]::zeroed`, S-239), whose `::` is no separator; it ends at a
/// `::<` (`Buf::<F32>::zeroed` is two forms, S-326).
fn path_separator(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ColonColon {
        return None;
    }
    let in_use = c.open.iter().chain(c.closed).any(|o| o.0 == NodeKind::Use);
    let follows = |i: usize| {
        let n = c.kind(i + 1);
        is_segment(n) || (in_use && n == TokenKind::LBrace)
    };
    let before = c.before(c.at)?;
    let after_list = c.kind(before) == TokenKind::RBracket && c.closed.iter().any(|o| o.0 == NodeKind::TypeArgsExpr);
    if !(is_segment(c.kind(before)) || c.kind(before) == TokenKind::KwSelfType || after_list) || !follows(c.at) {
        return None;
    }
    // The path: names separated with `.` or `::`, on and after the failure.
    let mut seps = vec![c.at];
    let mut i = c.at + 1;
    loop {
        if is_type_args_mark(c, i + 1) {
            match closing(c, i + 2) {
                Some(close) => i = close,
                None => break,
            }
        }
        match c.kind(i + 1) {
            TokenKind::Dot if is_segment(c.kind(i + 2)) => i += 2,
            TokenKind::ColonColon if follows(i + 1) => {
                seps.push(i + 1);
                i += 2;
            }
            _ => break,
        }
    }
    let edits = seps.iter().map(|&s| Edit::replace(c.span(s), ".")).collect();
    let title = if seps.len() > 1 { "write each `::` as `.`" } else { "write `.`" };
    // The range of the form (S-316): from its first `::` to its last.
    let last = *seps.last().unwrap_or(&c.at);
    hit(c.file_span(c.span(c.at).start, c.span(last).end), vec![Fix::new(title, edits)])
}

/// The mark `::[` of type arguments in an expression at token `i`.
fn is_type_args_mark(c: &Cursor, i: usize) -> bool {
    crate::token::is_type_args_mark(c.all, c.full, c.tokens, i)
}

/// The bracket that closes the one at `open` (`(`, `[` or `{`).
fn closing(c: &Cursor, open: usize) -> Option<usize> {
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

// ------------------------------------------------------------ `<T>`

/// `<` ... `>` of type parameters (`fn f<T>`) or type arguments
/// (`Vec<T>`): written in `[ ]` (§4.5). The candidate replaces each bracket
/// token (S-251; `>>` closing two is `]]`), the nested ones too (S-248).
fn angle_brackets(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Lt {
        return None;
    }
    let after_type = c.closed.iter().any(|n| n.0 == NodeKind::PathType);
    // The name of a declaration with type parameters (its list of
    // parameters, fields or members may be open already).
    let after_name = c.closed.first().is_some_and(|n| n.0 == NodeKind::Name)
        && c.open.iter().rev().take(2).any(|o| {
            matches!(o.0, NodeKind::Fn | NodeKind::Struct | NodeKind::Enum | NodeKind::Trait | NodeKind::TypeAlias)
        });
    let after_impl = c.before(c.at).is_some_and(|b| c.kind(b) == TokenKind::KwImpl);
    if !(after_type || after_name || after_impl) {
        return None;
    }
    // A `<` that no `>` closes is no list of type parameters (the general E0002).
    let (close_at, edits) = angle_list(c, c.at, "[")?;
    let span = c.file_span(c.span(c.at).start, c.span(close_at).end);
    // What follows the brackets is what follows a type or a list of type
    // parameters; else the brackets are not read so (no candidate).
    let follows = follows_type(c.kind(close_at + 1)) || c.kind(close_at + 1) == TokenKind::Dot;
    let fixes = if follows { vec![Fix::new("write the brackets `[ ]`", edits)] } else { Vec::new() };
    hit(span, fixes)
}

/// A token that may follow a type or a list of type parameters (`;` after
/// the element type of an array type).
fn follows_type(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        Comma
            | Semi
            | RParen
            | RBracket
            | RBrace
            | Eq
            | LBrace
            | LParen
            | Newline
            | Eof
            | Comment
            | DocComment
            | KwFor
            | KwUses
            | Ident
            | KwSelfType
    )
}

/// The list in angle brackets that opens at the `<` `open`: the token that
/// closes it, and the edits that write its brackets as `[ ]`, the first `<`
/// as `first` (S-251; `>>` closing two is `]]`, the nested lists too, S-248).
/// None when a token no list of types holds comes before its `>`.
fn angle_list(c: &Cursor, open: usize, first: &str) -> Option<(usize, Vec<Edit>)> {
    let (close, brackets) = angle_tokens(c.tokens, open)?;
    let edits =
        brackets.into_iter().map(|(i, to)| Edit::replace(c.span(i), if i == open { first } else { to })).collect();
    Some((close, edits))
}

/// The tokens of [`angle_list`]: the closing token, and each bracket with
/// what it becomes.
fn angle_tokens(tokens: &[Token], open: usize) -> Option<(usize, Vec<(usize, &'static str)>)> {
    let mut depth = 0i32;
    let mut brackets = Vec::new();
    // An element starts as a type, a type parameter or a constant does, and a
    // `>` closes what can end one (`<->`, `<A,>`, `<U->8>` are no lists).
    let starts = |k: TokenKind| {
        use TokenKind::*;
        matches!(k, Ident | KwSelfType | KwConst | KwFn | KwRt | LParen | LBracket | Int | Minus | Underscore)
    };
    let ends = |k: TokenKind| {
        use TokenKind::*;
        matches!(k, Ident | KwSelfType | RParen | RBracket | Int | Gt | Shr)
    };
    // The last token before `i` that is no comment or newline.
    let mut prev = TokenKind::Lt;
    for (i, t) in tokens.iter().enumerate().skip(open) {
        let blank =
            matches!(t.kind, TokenKind::Comment | TokenKind::DocComment | TokenKind::BlockComment | TokenKind::Newline);
        if i > open && !blank {
            if matches!(prev, TokenKind::Lt | TokenKind::Comma) && !starts(t.kind) {
                return None;
            }
            if matches!(t.kind, TokenKind::Gt | TokenKind::GtEq | TokenKind::Shr) && !ends(prev) {
                return None;
            }
            // `->` is the result of a function type, after its `)`.
            if t.kind == TokenKind::Arrow && prev != TokenKind::RParen {
                return None;
            }
            prev = t.kind;
        }
        match t.kind {
            TokenKind::Lt => {
                depth += 1;
                brackets.push((i, "["));
            }
            TokenKind::Gt => {
                depth -= 1;
                brackets.push((i, "]"));
            }
            TokenKind::GtEq => {
                depth -= 1;
                brackets.push((i, "]="));
            }
            TokenKind::Shr if depth >= 2 => {
                depth -= 2;
                brackets.push((i, "]]"));
            }
            TokenKind::Ident
            | TokenKind::KwSelfType
            | TokenKind::KwConst
            | TokenKind::KwFn
            | TokenKind::KwRt
            | TokenKind::Arrow
            | TokenKind::Underscore
            | TokenKind::LParen
            | TokenKind::RParen
            | TokenKind::Newline
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::Plus
            | TokenKind::Question
            | TokenKind::Dot
            | TokenKind::Int
            | TokenKind::Minus
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::Semi
            | TokenKind::Comment
            | TokenKind::DocComment
            | TokenKind::BlockComment => {}
            _ => return None,
        }
        if depth == 0 {
            return Some((i, brackets));
        }
    }
    None
}

// ------------------------------------------------------------ type arguments in an expression

/// The rule of the forms of type arguments in an expression (the note, §4.5).
const TYPE_ARGS_RULE: &str = "a type argument in an expression is written after the name, `name::[T]` (`id::[U8](250)`); a `[` alone is an index (§4.5)";

/// The nodes of an expression that name a path (a path of names, a method,
/// a tuple index): what a `::[…]`, a `!` or a `~` may follow, and the callees
/// whose type arguments of another language become `::[…]`. The one test,
/// for the parser and this table.
pub(crate) fn names_a_path(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::PathExpr | NodeKind::FieldExpr | NodeKind::TupleIndexExpr)
}

/// A callee that is a value and no path (`(e)`, `g(x)`, `xs[i]`, `x?`): no
/// `::[` can be written after it, and it is called with `.(` (§6.1).
fn is_value_callee(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::ParenExpr | NodeKind::CallExpr | NodeKind::IndexExpr | NodeKind::TryExpr)
}

/// Whether the `<` or `[` at `tokens[i]` opens type arguments of another
/// language before a call (`f<T>(x)`, `f[A, B](x)`, §4.5, S-256), after an
/// expression of `callee`'s kind: it touches the callee, its list closes,
/// and a `(` touches the list (for a `[` after a path, any token may follow:
/// `Rg[F32, 4].CAP`); a `[` holds a `,` (an index holds one expression). The
/// parser asks it before it reads `<` as a comparison or `[` as an index, and
/// reads a `[` on as a list of type arguments to be sure; the table builds
/// the diagnostic where the parser then fails ([`type_args_call`]).
pub(crate) fn type_list_ahead(tokens: &[Token], all: &[Token], full: &[u32], i: usize, callee: NodeKind) -> bool {
    let name = names_a_path(callee);
    if !(name || is_value_callee(callee)) || crate::token::gap_before(all, full[i] as usize) != Gap::None {
        return false;
    }
    let close = match tokens[i].kind {
        TokenKind::Lt => angle_tokens(tokens, i).map(|(close, _)| close),
        TokenKind::LBracket => bracket_with_comma(tokens, i),
        _ => None,
    };
    let Some(close) = close else { return false };
    let called = tokens.get(close + 1).is_some_and(|t| t.kind == TokenKind::LParen)
        && crate::token::gap_before(all, full[close + 1] as usize) == Gap::None;
    called || (name && tokens[i].kind == TokenKind::LBracket)
}

/// The `]` that closes the `[` at `open` when a `,` is directly in it.
fn bracket_with_comma(tokens: &[Token], open: usize) -> Option<usize> {
    let mut depth = 0u32;
    let mut comma = false;
    for (i, t) in tokens.iter().enumerate().skip(open) {
        match t.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return (comma && t.kind == TokenKind::RBracket).then_some(i);
                }
            }
            TokenKind::Comma if depth == 1 => comma = true,
            TokenKind::Eof => return None,
            _ => {}
        }
    }
    None
}

/// Type arguments of another language before a call (§4.5, S-239, S-256,
/// S-277): `f::<T>(x)` (Rust; the parser fails at the `::`), and `f<T>(x)`
/// and `f[A, B](x)`, at which the parser fails when [`type_list_ahead`] says
/// so. After a path of names or a method, the candidate is the Onsa form:
/// `::<` keeps the `::` and writes `[ ]`, `<` becomes `::[`, `[` gets `::`
/// before it (S-251; `>>` is `]]`, S-248); `f<T>(x)` with one name, literal
/// or path of names in the list has the reading of the languages that read
/// it as comparisons too (`f < T && T > (x)`, §18.1). After a value
/// (`g(x)`, `(e)`), no `::[` can be written: the one candidate drops the list
/// and calls the value with `.(` (§6.1). After anything else, and for an
/// empty list, the form is not this table's (the general E0002).
fn type_args_call(c: &Cursor) -> Option<Hit> {
    let callee = closed_expr(c)?;
    let (row, open) = match c.kind(c.at) {
        TokenKind::ColonColon if c.kind(c.at + 1) == TokenKind::Lt => (RowId::TypeArgsTurbofish, c.at + 1),
        TokenKind::Lt | TokenKind::LBracket if type_list_ahead(c.tokens, c.all, c.full, c.at, callee.0) => {
            let row = if c.kind(c.at) == TokenKind::Lt { RowId::TypeArgsAngle } else { RowId::TypeArgsSquareComma };
            (row, c.at)
        }
        _ => return None,
    };
    let (close, edits) = if row == RowId::TypeArgsSquareComma {
        let close = bracket_with_comma(c.tokens, open)?;
        (close, vec![Edit::insert(c.file, c.span(open).start, "::")])
    } else {
        let first = if row == RowId::TypeArgsAngle { "::[" } else { "[" };
        angle_list(c, open, first)?
    };
    if close == open + 1 {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(close).end);
    if is_value_callee(callee.0) {
        c.say(RowId::TypeArgsOnExpression);
        return hit(span, value_call(c, callee, c.at, close).into_iter().collect());
    }
    if !names_a_path(callee.0) {
        return None;
    }
    c.say(row);
    let mut fixes = vec![Fix::new("write the type arguments as `::[…]`", edits)];
    let single = is_place(c, open + 1, close - 1)
        || (open + 2 == close
            && matches!(
                c.kind(open + 1),
                TokenKind::Int
                    | TokenKind::Float
                    | TokenKind::Str
                    | TokenKind::Char
                    | TokenKind::KwTrue
                    | TokenKind::KwFalse
            ));
    if row == RowId::TypeArgsAngle && single && c.kind(close) == TokenKind::Gt {
        let m = &c.text[c.span(open + 1).start as usize..c.span(close - 1).end as usize];
        fixes.push(Fix::new(
            "compare: both comparisons, joined with `&&`",
            vec![Edit::replace(c.span(open), " < "), Edit::replace(c.span(close), format!(" && {m} > "))],
        ));
    }
    hit(span, fixes)
}

/// The candidate that calls the value `callee` with `.(` in place of the
/// type arguments in `first..=last` (the call's `(` follows `last`): the
/// list and the blanks before it become `.`, and the parentheses around a
/// path of names go (`(s.f)` is `s.f.(x)`, §4.5).
fn value_call(c: &Cursor, callee: (NodeKind, u32), first: usize, last: usize) -> Option<Fix> {
    if c.kind(last + 1) != TokenKind::LParen || c.gap(last + 1) != Gap::None {
        return None;
    }
    let before = first.checked_sub(1)?;
    let mut edits = vec![Edit::replace(c.file_span(c.span(before).end, c.span(last).end), ".")];
    if callee.0 == NodeKind::ParenExpr {
        let open = c.index_at(callee.1);
        if is_place(c, open + 1, before - 1) {
            edits.push(Edit::delete(c.span(open)));
            edits.push(Edit::delete(c.span(before)));
        }
    }
    Some(Fix::new("call the function value with `.(`", edits))
}

/// The expression that ended right before the failure: the innermost
/// expression among the nodes closed there (an argument list closes before
/// its call).
fn closed_expr(c: &Cursor) -> Option<(NodeKind, u32)> {
    c.closed.iter().copied().find(|n| crate::lower::class(n.0) == crate::lower::Class::Expr)
}

/// `::[` written in a type position (`b: Buf::[F32]`, §4.5): the mark is
/// needed only in an expression, where a `[` alone is an index; in a type
/// it misleads about that rule (P2). The candidate removes the `::` (and a
/// blank around it). A list that is empty or that something no type is
/// followed by follows (`Buf::[F32].Inner`) has none (the general E0002).
fn type_position_path(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ColonColon || c.kind(c.at + 1) != TokenKind::LBracket {
        return None;
    }
    if !c.closed.iter().any(|n| n.0 == NodeKind::PathType) || c.gap(c.at + 1) == Gap::Newline {
        return None;
    }
    let close = closing(c, c.at + 1)?;
    if close == c.at + 2 || !follows_type(c.kind(close + 1)) {
        return None;
    }
    let name = c.before(c.at)?;
    let gap = c.file_span(c.span(name).end, c.span(c.at + 1).start);
    hit(c.span(c.at), vec![Fix::delete("remove the `::`", gap)])
}

/// A space on either side of the `::` of `name::[…]` in an expression
/// (`id ::[U8]`, `id:: [U8]`, §2.5, §4.5): the candidate removes it.
fn space_in_type_args_mark(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ColonColon || c.kind(c.at + 1) != TokenKind::LBracket {
        return None;
    }
    if !closed_expr(c).is_some_and(|n| names_a_path(n.0)) {
        return None;
    }
    let (before, after) = (c.gap(c.at), c.gap(c.at + 1));
    if before == Gap::Newline || after == Gap::Newline {
        return None;
    }
    let edits: Vec<Edit> =
        [c.space_before(c.at), c.space_after(c.at)].into_iter().flatten().map(Edit::delete).collect();
    if edits.is_empty() {
        return None;
    }
    hit(c.span(c.at), vec![Fix::new("remove the space", edits)])
}

// ------------------------------------------------------------ `&` and `mut`

/// `&` and `&mut` of Rust (§5.2, S-250, R-173): before a parameter's name
/// (`&mut self`, `&self`), in a parameter's type (`v: &mut T` is `inout v:
/// T`, `v: &T` is `v: T`), in another type (`&T` is `T`; `&mut T` has no
/// form: E0002), before an argument (`&mut x` is `inout x`; `&x` is `x`, or
/// `inout x`) and in another expression (`&x` is `x`; `&mut x`: E0002).
fn reference(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Amp {
        return None;
    }
    let amp = c.at;
    let is_mut = c.is_ident(amp + 1, "mut");
    let mark_end = if is_mut { amp + 1 } else { amp };
    let operand = mark_end + 1;
    let mark = c.file_span(c.span(amp).start, c.span(mark_end).end);
    // The mark and the blanks after it.
    let mark_and_space = c.file_span(mark.start, c.span(operand).start);
    let mode = c.sig_before(amp).filter(|&m| matches!(c.kind(m), TokenKind::KwInout | TokenKind::KwMove));
    match c.want {
        // `&self` where the parameter starts (after its mode, if any; not `x&self`).
        Want::Other
            if c.top() == Some(NodeKind::Param)
                && c.kind(operand) == TokenKind::KwSelf
                && (mode.is_some() || c.open_at(0).is_some_and(|o| o.1 == c.span(amp).start)) =>
        {
            if is_mut {
                c.say(RowId::RefMutSelf);
                // A mode before it is not written twice (`inout &mut self`).
                hit(mark, mode_and_mark(c, mode, mark_and_space, Some("inout ")))
            } else {
                c.say(RowId::RefSelf);
                hit(mark, vec![Fix::delete("remove the `&`", mark_and_space)])
            }
        }
        Want::Type => {
            let in_param = c.top() == Some(NodeKind::Param);
            let in_fn_type = c.top() == Some(NodeKind::FnTypeParams);
            if !is_mut {
                c.say(RowId::RefType);
                return hit(mark, vec![Fix::delete("remove the `&`", mark_and_space)]);
            }
            if in_fn_type {
                c.say(RowId::RefMutParam);
                return hit(mark, mode_and_mark(c, mode, mark_and_space, Some("inout ")));
            }
            if !in_param {
                c.say(RowId::RefMutOther);
                return hit(mark, Vec::new());
            }
            c.say(RowId::RefMutParam);
            // `name: &mut T`: the name before the `:`, and a mode before it.
            let colon = c.sig_before(amp).filter(|&k| c.kind(k) == TokenKind::Colon)?;
            let name = c.sig_before(colon)?;
            let mode = c.sig_before(name).filter(|&m| matches!(c.kind(m), TokenKind::KwInout | TokenKind::KwMove));
            let fixes = match mode {
                None => vec![Fix::new(
                    "write `inout` before the name",
                    vec![Edit::insert(c.file, c.span(name).start, "inout "), Edit::delete(mark_and_space)],
                )],
                _ => mode_and_mark(c, mode, mark_and_space, None),
            };
            hit(mark, fixes)
        }
        Want::Expr => {
            let in_arg = c.top() == Some(NodeKind::Arg);
            // `f(inout &mut x)`, `f(inout &x)`: the mode is there; the mark goes.
            if in_arg && mode.is_some_and(|m| c.kind(m) == TokenKind::KwInout) {
                c.say(if is_mut { RowId::RefMutArg } else { RowId::RefExpr });
                return hit(mark, vec![Fix::delete("remove the reference mark", mark_and_space)]);
            }
            let in_arg = in_arg && mode.is_none();
            match (is_mut, in_arg) {
                (true, true) => {
                    c.say(RowId::RefMutArg);
                    hit(mark, vec![Fix::replace("write `inout`", mark_and_space, "inout ")])
                }
                (true, false) => {
                    c.say(RowId::RefMutOther);
                    hit(mark, Vec::new())
                }
                (false, true) => {
                    c.say(RowId::RefExpr);
                    hit(
                        mark,
                        vec![
                            Fix::delete("remove the `&`", mark_and_space),
                            Fix::replace("write `inout`", mark_and_space, "inout "),
                        ],
                    )
                }
                (false, false) => {
                    c.say(RowId::RefExpr);
                    hit(mark, vec![Fix::delete("remove the `&`", mark_and_space)])
                }
            }
        }
        _ => None,
    }
}

/// The candidates for a reference mark (`&mut `, `mut `, with its blanks:
/// `mark`) after the mode `mode` of a parameter: with `inout`, the mark goes;
/// with `move`, the reading is not one, the caller's value changing
/// (`inout`) or taken (`move`): both. Without a mode, `with` (the mode to
/// write in place of the mark), if any. A mode is never written twice.
fn mode_and_mark(c: &Cursor, mode: Option<usize>, mark: Span, with: Option<&str>) -> Vec<Fix> {
    match mode {
        Some(m) if c.kind(m) == TokenKind::KwInout => vec![Fix::delete("remove the mark", mark)],
        Some(m) => vec![
            Fix::new("write `inout` for `move`", vec![Edit::replace(c.span(m), "inout"), Edit::delete(mark)]),
            Fix::delete("remove the mark", mark),
        ],
        None => with.map(|w| Fix::replace(format!("write `{}`", w.trim()), mark, w)).into_iter().collect(),
    }
}

/// `mut self` of Rust: a receiver the method takes is `move self` (S-250).
/// After a mode (`inout mut self`), the `mut` goes.
fn mut_self(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::KwSelf || c.top() != Some(NodeKind::Param) {
        return None;
    }
    let m = c.before(c.at).filter(|&m| c.is_ident(m, "mut"))?;
    let span = c.file_span(c.span(m).start, c.span(c.at).end);
    let mode = c.sig_before(m).filter(|&k| matches!(c.kind(k), TokenKind::KwInout | TokenKind::KwMove));
    if mode.is_some() {
        return hit(span, vec![Fix::delete("remove the `mut`", c.file_span(c.span(m).start, c.span(c.at).start))]);
    }
    hit(span, vec![Fix::replace("write `move self`", c.span(m), "move")])
}

/// `let mut x` of Rust: `var x` (§5.1).
fn let_mut(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Ident || c.top() != Some(NodeKind::LetStmt) {
        return None;
    }
    let m = c.before(c.at).filter(|&m| c.is_ident(m, "mut"))?;
    let l = c.before(m).filter(|&l| c.kind(l) == TokenKind::KwLet)?;
    let span = c.file_span(c.span(l).start, c.span(m).end);
    let fix = Fix::new(
        "write `var`",
        vec![Edit::replace(c.span(l), "var"), Edit::delete(c.file_span(c.span(m).start, c.span(c.at).start))],
    );
    hit(span, vec![fix])
}

/// `loop { }` of Rust: `while true { }` (§7). `loop` alone is a statement,
/// and the parser fails at its `{`.
fn endless_loop(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::LBrace
        || c.top() != Some(NodeKind::Block)
        || !matches!(c.closed, [(NodeKind::PathExpr, _), (NodeKind::ExprStmt, _)])
    {
        return None;
    }
    let l = c.before(c.at).filter(|&l| c.is_ident(l, "loop"))?;
    hit(c.span(l), vec![Fix::replace("write `while true`", c.span(l), "while true")])
}

/// `proc name` (the older keyword) among the items of a module: `flow name`
/// (§11). In a list of members a flow is not a member (the general E0002).
fn proc(c: &Cursor) -> Option<Hit> {
    if !c.is_ident(c.at, "proc")
        || c.top() != Some(NodeKind::Item)
        || c.open_at(1).is_none_or(|o| o.0 != NodeKind::SourceFile)
        || c.kind(c.at + 1) != TokenKind::Ident
    {
        return None;
    }
    hit(c.span(c.at), vec![Fix::replace("write `flow`", c.span(c.at), "flow")])
}

/// `#[name(...)]` of Rust: `@name(...)` (§6.5).
fn hash_attribute(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Hash || c.kind(c.at + 1) != TokenKind::LBracket {
        return None;
    }
    let mut depth = 0;
    let mut close = None;
    for i in c.at + 1..c.tokens.len() {
        match c.kind(i) {
            TokenKind::LBracket | TokenKind::LParen => depth += 1,
            TokenKind::RBracket | TokenKind::RParen => {
                depth -= 1;
                if depth == 0 {
                    close = (c.kind(i) == TokenKind::RBracket).then_some(i);
                    break;
                }
            }
            TokenKind::Newline | TokenKind::Eof | TokenKind::LBrace | TokenKind::RBrace => break,
            _ => {}
        }
    }
    let end = close.map_or(c.span(c.at + 1).end, |e| c.span(e).end);
    let span = c.file_span(c.span(c.at).start, end);
    // Where an attribute goes (§6.5): the head of an item (opened at the
    // `#`), an input of a flow. A `let` takes `@mem` too, but the parser
    // reads no attribute there yet (W3-10): no candidate before it, which
    // would leave an E0002.
    let unread = c.open_at(0).is_some_and(|o| o.1 == c.span(c.at).start);
    let item = c.top() == Some(NodeKind::Item) && unread;
    let flow_input = c.top() == Some(NodeKind::Param)
        && unread
        && c.open_at(1).is_some_and(|o| o.0 == NodeKind::ParamList)
        && c.open_at(2).is_some_and(|o| o.0 == NodeKind::Flow);
    if !(item || flow_input) {
        return hit(span, Vec::new());
    }
    let fixes = match close {
        Some(e) if c.is_ident(c.at + 2, "derive") => derive(c, e).into_iter().collect(),
        Some(e) if c.kind(c.at + 2) == TokenKind::Ident => vec![Fix::new(
            "write the attribute with `@`",
            vec![Edit::replace(c.file_span(c.span(c.at).start, c.span(c.at + 1).end), "@"), Edit::delete(c.span(e))],
        )],
        _ => Vec::new(),
    };
    hit(span, fixes)
}

/// `#[derive(A, B)]` before a `struct` or an `enum` (its `]` is token
/// `close`): the traits are written at the head of the declaration, `struct
/// S: A + B` (§8.1, S-250). The attribute and the line break after it go.
fn derive(c: &Cursor, close: usize) -> Option<Fix> {
    // The traits: names separated with `,` in the parentheses.
    let mut traits = Vec::new();
    let mut i = c.at + 3;
    if c.kind(i) != TokenKind::LParen {
        return None;
    }
    loop {
        i += 1;
        if c.kind(i) != TokenKind::Ident {
            return None;
        }
        traits.push(c.src(i).to_string());
        i += 1;
        match c.kind(i) {
            TokenKind::Comma => {}
            TokenKind::RParen if i + 1 == close => break,
            _ => return None,
        }
    }
    let mut decl = c.sig_after(close);
    if c.kind(decl) == TokenKind::KwPub {
        decl = c.sig_after(decl);
    }
    if !matches!(c.kind(decl), TokenKind::KwStruct | TokenKind::KwEnum) || c.kind(decl + 1) != TokenKind::Ident {
        return None;
    }
    // After the name, or after its type parameters (`struct S[T]: A`, §6.4).
    let mut head = decl + 1;
    if c.kind(head + 1) == TokenKind::LBracket {
        let mut depth = 0;
        for i in head + 1..c.tokens.len() {
            match c.kind(i) {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    depth -= 1;
                    if depth == 0 {
                        head = i;
                        break;
                    }
                }
                TokenKind::LBrace | TokenKind::Eof => return None,
                _ => {}
            }
        }
        if c.kind(head) != TokenKind::RBracket {
            return None;
        }
    }
    if c.kind(head + 1) == TokenKind::Colon {
        return None;
    }
    let first = c.sig_after(close);
    Some(Fix::new(
        "write the traits at the head of the declaration",
        vec![
            Edit::delete(c.file_span(c.span(c.at).start, c.span(first).start)),
            Edit::insert(c.file, c.span(head).end, format!(": {}", traits.join(" + "))),
        ],
    ))
}

/// `pub(crate)` of Rust: visibility within the package is the default
/// (§15.1). The candidate removes it with the blanks after it.
fn pub_crate(c: &Cursor) -> Option<Hit> {
    if !c.is_ident(c.at, "crate") || c.top() != Some(NodeKind::Vis) {
        return None;
    }
    let open = c.before(c.at).filter(|&o| c.kind(o) == TokenKind::LParen)?;
    let public = c.before(open).filter(|&p| c.kind(p) == TokenKind::KwPub)?;
    let close = c.at + 1;
    if c.kind(close) != TokenKind::RParen {
        return hit(c.file_span(c.span(public).start, c.span(c.at).end), Vec::new());
    }
    let span = c.file_span(c.span(public).start, c.span(close).end);
    let end = c.space_after(close).map_or(span.end, |s| s.end);
    hit(span, vec![Fix::delete("remove the visibility", c.file_span(span.start, end))])
}

// ------------------------------------------------------------ literals

/// The number and the suffix of a `ForeignLit` written with a suffix
/// (`1u8`: `1` and `u8`), as the lexer reads them.
fn split_suffix(text: &str) -> (&str, &str) {
    let b = text.as_bytes();
    let mut i = 0;
    let digits = |i: &mut usize, ok: &dyn Fn(u8) -> bool| {
        while *i < b.len() && ok(b[*i]) {
            *i += 1;
        }
    };
    if b.len() > 1 && b[0] == b'0' && matches!(b[1], b'x' | b'b') {
        let hex = b[1] == b'x';
        i = 2;
        if hex {
            digits(&mut i, &|x: u8| x.is_ascii_hexdigit() || x == b'_');
        } else {
            digits(&mut i, &|x: u8| matches!(x, b'0' | b'1' | b'_'));
        }
    } else {
        digits(&mut i, &|x: u8| x.is_ascii_digit() || x == b'_');
        if i + 1 < b.len() && b[i] == b'.' && b[i + 1].is_ascii_digit() {
            i += 1;
            digits(&mut i, &|x: u8| x.is_ascii_digit() || x == b'_');
        }
        if i < b.len() && matches!(b[i], b'e' | b'E') {
            let mut j = i + 1;
            if j < b.len() && matches!(b[j], b'+' | b'-') {
                j += 1;
            }
            let start = j;
            digits(&mut j, &|x: u8| x.is_ascii_digit());
            if j > start {
                i = j;
            }
        }
    }
    text.split_at(i)
}

/// `1.` (a digit after the point is needed) and `1u8` (no type suffix, §2.4).
/// Where no literal goes (a declaration), the place is an error of its own
/// (S-281: the driver reports the E0002 there).
fn foreign_literal(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ForeignLit {
        return None;
    }
    let span = c.span(c.at);
    let text = c.src(c.at);
    // In a pattern a float is a float pattern, one form with it (S-248).
    if c.want == Want::Pattern && float_spelling(text).is_some() {
        return None;
    }
    // What the text after the token starts with: a number written in its
    // place must stay a token of its own (S-302).
    let next = c.text.as_bytes().get(span.end as usize).copied();
    let fixes = if let Some(number) = text.strip_suffix('.') {
        debug_assert!(number.bytes().all(|b| b.is_ascii_digit() || b == b'_'), "{number}");
        c.say(RowId::FloatTrailingDot);
        // The token is replaced whole: a `0` inserted after it would change
        // the reading of a token outside the edit (S-302).
        vec![Fix::replace("add the `0` after the point", span, format!("{text}0"))]
    } else {
        c.say(RowId::LiteralSuffix);
        let (number, _) = split_suffix(text);
        // An integer before a `.` reads with it when a digit follows the `.`
        // (`1d.5` would be `1.5`) or neither a name nor a `.` (`1d.` would be
        // `1.`); `0u32..n` and `1u8.abs()` read the same.
        let after_dot = c.text.as_bytes().get(span.end as usize + 1).copied();
        let joins = next == Some(b'.')
            && is_integer(number)
            && !after_dot.is_some_and(|b| b == b'.' || b.is_ascii_alphabetic() || b == b'_');
        if joins { Vec::new() } else { vec![Fix::replace("remove the type suffix", span, number)] }
    };
    Some(Hit { span, fixes, misplaced: !matches!(c.want, Want::Expr | Want::Pattern) })
}

/// Whether the number `number` (no suffix) is written as an integer.
pub(crate) fn is_integer(number: &str) -> bool {
    let hex = number.starts_with("0x") || number.starts_with("0b");
    hex || !number.contains(['.', 'e', 'E'])
}

/// The number part of a number written as in other languages (`1u8`: `1`).
pub(crate) fn number_part(text: &str) -> &str {
    split_suffix(text).0
}

/// The Onsa spelling of a float written as in other languages, in a
/// pattern (§2.4): `1.` is `1.0`, `0.5f32` is `0.5`, `1f32` is `1.0`; `None`
/// for an integer with an integer suffix (`1u8`).
fn float_spelling(text: &str) -> Option<String> {
    if let Some(n) = text.strip_suffix('.') {
        return Some(format!("{n}.0"));
    }
    let (number, suffix) = split_suffix(text);
    if !is_integer(number) {
        return Some(number.to_string());
    }
    suffix.trim_start_matches('_').starts_with(['f', 'F']).then(|| format!("{number}.0"))
}

/// A prefix `~` of the C languages (the bitwise negation): `!x` (§2.6,
/// §18.1). `~` after a name is the flow-call mark, and `~ _` is the feedback
/// of FAUST (another row).
fn faust_bit_not(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr
        || c.kind(c.at) != TokenKind::Tilde
        || c.gap(c.at + 1).is_some()
        || matches!(c.kind(c.at + 1), TokenKind::Underscore | TokenKind::LParen)
    {
        return None;
    }
    // `!` beside another prefix operator would be a stack of them (E0012):
    // no candidate then.
    let prefix =
        |k: TokenKind| matches!(k, TokenKind::Minus | TokenKind::Bang | TokenKind::Tilde | TokenKind::MinusMinus);
    if c.top() == Some(NodeKind::PrefixExpr) || matches!(c.kind(c.at + 1), TokenKind::Tilde | TokenKind::MinusMinus) {
        return hit(c.span(c.at), Vec::new());
    }
    if prefix(c.kind(c.at + 1)) {
        // `~-x`: `!(-x)`, the operand in parentheses (no stack of prefix
        // operators, §3.1); only when the operand is plain.
        let Some(end) = operand_end(c, c.at + 2) else { return hit(c.span(c.at), Vec::new()) };
        let fix =
            Fix::new("write `!`", vec![Edit::replace(c.span(c.at), "!("), Edit::insert(c.file, c.span(end).end, ")")]);
        return hit(c.span(c.at), vec![fix]);
    }
    hit(c.span(c.at), vec![Fix::replace("write `!`", c.span(c.at), "!")])
}

/// The last token of a plain operand that starts at token `i`: a name or a
/// literal, with fields, calls and indexes after it (touching it).
fn operand_end(c: &Cursor, i: usize) -> Option<usize> {
    use TokenKind::*;
    if !matches!(c.kind(i), Ident | KwSelf | Int | Float | KwTrue | KwFalse) || c.gap(i).is_some() {
        return None;
    }
    let mut end = i;
    loop {
        let n = end + 1;
        if c.gap(n).is_some() {
            return Some(end);
        }
        match c.kind(n) {
            Dot if matches!(c.kind(n + 1), Ident | Int) => end = n + 1,
            LParen | LBracket => {
                let mut depth = 0;
                let mut k = n;
                loop {
                    match c.kind(k) {
                        LParen | LBracket => depth += 1,
                        RParen | RBracket => depth -= 1,
                        Eof | Newline | LBrace | RBrace => return None,
                        _ => {}
                    }
                    if depth == 0 {
                        break;
                    }
                    k += 1;
                }
                end = k;
            }
            _ => return Some(end),
        }
    }
}

/// `.5`: `0.5` (§2.4).
fn leading_point(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr
        || c.kind(c.at) != TokenKind::Dot
        || c.kind(c.at + 1) != TokenKind::Int
        || c.gap(c.at + 1).is_some()
    {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(c.at + 1).end);
    let text = format!("0{}", &c.text[span.start as usize..span.end as usize]);
    hit(span, vec![Fix::replace("add the `0` before the point", span, text)])
}

// ------------------------------------------------------------ block comments

/// Whether the block comment `text` is closed, and whether it holds another.
fn block_shape(text: &str) -> (bool, bool) {
    let b = text.as_bytes();
    let (mut depth, mut nested, mut i) = (1, false, 2);
    while i < b.len() {
        if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return (i == b.len(), nested);
            }
        } else if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
            depth += 1;
            nested = true;
            i += 2;
        } else {
            i += 1;
        }
    }
    (false, nested)
}

/// A token that may start a declaration a `///` documents: an item but `use`
/// and `test`, or its attribute or visibility (§2.1).
fn documented(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        KwFn | KwRt
            | KwFlow
            | KwStruct
            | KwEnum
            | KwType
            | KwTrait
            | KwImpl
            | KwEffect
            | KwBlocking
            | KwHandler
            | KwConst
            | KwExtern
            | KwTarget
    )
}

/// What a `///` in place of the block comment at `c.at` would document
/// (§2.1): a declaration that takes one (past `pub` and attributes; not
/// `use` or `test`, whose `///` is E0004), a field, a variant, a flow input.
fn documents(c: &Cursor) -> bool {
    let mut i = c.sig_after(c.at);
    // Past `pub` (`pub(pkg)`) and the attributes (`@name(..)`).
    while matches!(c.kind(i), TokenKind::KwPub | TokenKind::At) {
        if c.kind(i) == TokenKind::At {
            i = c.sig_after(i);
        }
        i = c.sig_after(i);
        if c.kind(i) == TokenKind::LParen {
            let mut depth = 0;
            loop {
                match c.kind(i) {
                    TokenKind::LParen => depth += 1,
                    TokenKind::RParen => depth -= 1,
                    TokenKind::Eof => return false,
                    _ => {}
                }
                i = c.sig_after(i);
                if depth == 0 {
                    break;
                }
            }
        }
    }
    let ctx = c.context();
    let member = |k: usize, kind: NodeKind| c.open.get(k).is_some_and(|o| o.0 == kind);
    match ctx {
        Some((_, NodeKind::FieldList | NodeKind::VariantList)) => c.kind(i) == TokenKind::Ident,
        Some((k, NodeKind::ParamList)) => k > 0 && member(k - 1, NodeKind::Flow) && c.kind(i) == TokenKind::Ident,
        _ => documented(c.kind(i)),
    }
}

/// A block comment (§2.1, S-247, S-302, R-174). A closed one is E0020: the
/// candidate keeps its words in line comments and changes neither the
/// tokens outside it nor the line breaks between them. When nothing but
/// blanks follows it on its last line, the line comments take its place;
/// else (it is at the start or in the middle of a line) they go on lines of
/// their own above the line it starts on, at the indentation of that line,
/// and the comment is removed from the code (with a blank, so the tokens
/// around it stay apart). Several on one line are fixed one by one (one per
/// unit), each adding its lines above. `/** */` that starts its line, before
/// a declaration it may document, is `///` (else `//`, so that a `///` moved
/// above documents no other declaration), and `/*! */` at the head of the
/// file is `//!` (or `///`, a second candidate). One over lines with code
/// after its `*/` on that line has no candidate (the line break between the
/// code around it is only inside it, so no candidate keeps the line breaks
/// without another reading: E0002). One never closed and one that holds
/// another are E0002.
fn block_comment(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::BlockComment {
        return None;
    }
    let span = c.span(c.at);
    let text = c.src(c.at);
    let (closed, nested) = block_shape(text);
    if !closed {
        c.say(RowId::BlockCommentUnclosed);
        return hit(span, Vec::new());
    }
    if nested {
        c.say(RowId::BlockCommentNested);
        return hit(span, Vec::new());
    }
    let inner = &text[2..text.len() - 2];
    let (doc, inner) = match inner.as_bytes().first() {
        Some(b'*') if !inner.is_empty() => (Some('*'), &inner[1..]),
        Some(b'!') => (Some('!'), &inner[1..]),
        _ => (None, inner),
    };
    let mut lines: Vec<&str> = inner
        .split('\n')
        .enumerate()
        .map(|(k, l)| if k == 0 { l.trim() } else { l.trim_start_matches([' ', '\t']).trim_end() })
        .map(|l| l.trim_end_matches('\r'))
        .collect();
    if lines.len() > 1 && lines[0].is_empty() {
        lines.remove(0);
    }
    if lines.len() > 1 && lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    let line_start = c.line_start(span.start);
    let pre = c.text[line_start as usize..span.start as usize].trim().is_empty();
    let rest_start = span.end as usize;
    let rest_end = c.text[rest_start..].find('\n').map_or(c.text.len(), |n| rest_start + n);
    let post = !c.text[rest_start..rest_end].trim().is_empty();
    if post && text.contains('\n') {
        c.say(RowId::BlockCommentMultilineCodeAfter);
        return hit(span, Vec::new());
    }
    // What may come after the comment: a declaration a `///` documents.
    let documents = pre && documents(c);
    let head = pre && c.sig_before(c.at).is_none();
    let mut prefixes: Vec<(&str, &str)> = Vec::new();
    match doc {
        Some('!') if head => {
            prefixes.push(("//!", "write a module doc comment `//!`"));
            if documents {
                prefixes.push(("///", "write a doc comment `///`"));
            }
        }
        Some(_) if documents => prefixes.push(("///", "write a doc comment `///`")),
        _ => prefixes.push(("//", "write a line comment")),
    }
    let indent = c.indent(span.start).to_string();
    let fixes = prefixes
        .into_iter()
        .map(|(prefix, title)| {
            let rendered: Vec<String> =
                lines.iter().map(|l| if l.is_empty() { prefix.to_string() } else { format!("{prefix} {l}") }).collect();
            if !post {
                // In place: the comment ends its line.
                return Fix::replace(title, span, rendered.join(&format!("\n{indent}")));
            }
            let above: String = rendered.iter().map(|l| format!("{l}\n{indent}")).collect();
            let ws_before = c.space_before(c.at);
            let ws_after = c.space_after(c.at);
            if pre {
                // The comment starts its line: the words take its place, and
                // the code after it goes to the next line.
                let end = ws_after.map_or(span.end, |s| s.end);
                return Fix::replace(title, c.file_span(span.start, end), above);
            }
            let removal = match (ws_before, ws_after) {
                (Some(_), Some(after)) => Edit::delete(c.file_span(span.start, after.end)),
                (None, None) => Edit::replace(span, " "),
                _ => Edit::delete(span),
            };
            let above: String = rendered.iter().map(|l| format!("{indent}{l}\n")).collect();
            Fix::new(title, vec![Edit::insert(c.file, line_start, above), removal])
        })
        .collect();
    hit(span, fixes)
}

// ------------------------------------------------------------ float patterns

/// What a hole of a pattern tests, once it is a name of the guard (S-317).
/// The ranges of patterns (S-249, W3-07) are the next kind of hole.
#[derive(Clone)]
enum Test {
    /// `name == <literal>`: a float literal.
    Equal(String),
}

/// A pattern read from its tokens (`lo..=hi`, positions of the reader's
/// tokens), for the guard form: its holes, the forms the guard tests.
struct Pat {
    lo: usize,
    hi: usize,
    kind: PatKind,
}

enum PatKind {
    /// A form the guard tests (a float literal).
    Hole(Test),
    /// Tokens with nothing inside (a literal, a name, `_`).
    Leaf,
    /// Brackets around patterns (a tuple, `Some(..)`, `S { x: .. }`).
    Node(Vec<Pat>),
    /// Alternatives `p | q`.
    Or(Vec<Pat>),
}

/// A reader of the tokens `toks` (indexes of `tokens`, without newlines and
/// comments) of a pattern. It reads what `Parser::parse_pattern` reads, the
/// float literals too; anything else makes no candidate.
struct PatReader<'c, 'a> {
    c: &'c Cursor<'a>,
    toks: Vec<usize>,
    pos: usize,
}

impl PatReader<'_, '_> {
    fn peek(&self) -> Option<TokenKind> {
        self.toks.get(self.pos).map(|&i| self.c.kind(i))
    }

    fn bump(&mut self) -> usize {
        self.pos += 1;
        self.pos - 1
    }

    fn pat(&self, lo: usize, kind: PatKind) -> Pat {
        Pat { lo, hi: self.pos - 1, kind }
    }

    fn or(&mut self) -> Option<Pat> {
        let lo = self.pos;
        let one = self.one()?;
        if self.peek() != Some(TokenKind::Pipe) {
            return Some(one);
        }
        let mut alts = vec![one];
        while self.peek() == Some(TokenKind::Pipe) {
            self.bump();
            alts.push(self.one()?);
        }
        Some(self.pat(lo, PatKind::Or(alts)))
    }

    fn list(&mut self, close: TokenKind, fields: bool) -> Option<Vec<Pat>> {
        let mut out = Vec::new();
        while self.peek() != Some(close) {
            if fields {
                if self.peek() != Some(TokenKind::Ident) {
                    return None;
                }
                self.bump();
                if self.peek() != Some(TokenKind::Colon) {
                    return None;
                }
                self.bump();
            }
            out.push(self.or()?);
            if self.peek() != Some(TokenKind::Comma) {
                break;
            }
            self.bump();
        }
        (self.peek() == Some(close)).then(|| {
            self.bump();
            out
        })
    }

    /// The literal at the reader: `-`, `(`s, a number and as many `)`s.
    fn literal(&mut self, lo: usize) -> Option<Pat> {
        let minus = self.peek() == Some(TokenKind::Minus);
        if minus {
            self.bump();
        }
        let mut opens = 0;
        while minus && self.peek() == Some(TokenKind::LParen) {
            self.bump();
            opens += 1;
        }
        // The number: a float (`1.5`), one written as in other languages
        // (`1.`, `0.5f32`, `.5`: the guard writes it in the Onsa spelling).
        let at = self.pos;
        let float = match self.peek()? {
            TokenKind::Int => None,
            TokenKind::Float => Some(self.c.src(self.toks[at]).to_string()),
            TokenKind::ForeignLit => Some(float_spelling(self.c.src(self.toks[at]))?),
            TokenKind::Dot if self.toks.get(at + 1).is_some_and(|&n| self.c.kind(n) == TokenKind::Int) => {
                self.bump();
                Some(format!("0.{}", self.c.src(self.toks[at + 1])))
            }
            _ => return None,
        };
        self.bump();
        for _ in 0..opens {
            if self.peek() != Some(TokenKind::RParen) {
                return None;
            }
            self.bump();
        }
        let kind = match float {
            Some(value) => {
                let close = ")".repeat(opens);
                let open = "(".repeat(opens);
                PatKind::Hole(Test::Equal(format!("{}{open}{value}{close}", if minus { "-" } else { "" })))
            }
            None => PatKind::Leaf,
        };
        Some(self.pat(lo, kind))
    }

    fn one(&mut self) -> Option<Pat> {
        let lo = self.pos;
        match self.peek()? {
            TokenKind::Minus | TokenKind::Int | TokenKind::Float | TokenKind::ForeignLit | TokenKind::Dot => {
                self.literal(lo)
            }
            TokenKind::Char | TokenKind::Str | TokenKind::KwTrue | TokenKind::KwFalse | TokenKind::Underscore => {
                self.bump();
                Some(self.pat(lo, PatKind::Leaf))
            }
            TokenKind::LParen => {
                self.bump();
                let inner = self.list(TokenKind::RParen, false)?;
                Some(self.pat(lo, PatKind::Node(inner)))
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                self.bump();
                while self.peek() == Some(TokenKind::Dot) {
                    self.bump();
                    if !self.peek().is_some_and(is_segment) {
                        return None;
                    }
                    self.bump();
                }
                let last = self.c.src(self.toks[self.pos - 1]);
                match self.peek() {
                    // As the parser: `(` touching the path, `{` after an UpperCamel name.
                    Some(TokenKind::LParen) if !self.c.gap(self.toks[self.pos]).is_some() => {
                        self.bump();
                        let inner = self.list(TokenKind::RParen, false)?;
                        Some(self.pat(lo, PatKind::Node(inner)))
                    }
                    Some(TokenKind::LBrace) if last.starts_with(|ch: char| ch.is_ascii_uppercase()) => {
                        self.bump();
                        let inner = self.list(TokenKind::RBrace, true)?;
                        Some(self.pat(lo, PatKind::Node(inner)))
                    }
                    _ => Some(self.pat(lo, PatKind::Leaf)),
                }
            }
            _ => None,
        }
    }
}

/// The condition of a guard over the holes of a shape (by their index).
#[derive(Clone)]
enum Cond {
    True,
    Test(usize, Test),
    And(Vec<Cond>),
    Or(Vec<Cond>),
}

impl Cond {
    fn shifted(self, by: usize) -> Cond {
        match self {
            Cond::True => Cond::True,
            Cond::Test(i, t) => Cond::Test(i + by, t),
            Cond::And(v) => Cond::And(v.into_iter().map(|c| c.shifted(by)).collect()),
            Cond::Or(v) => Cond::Or(v.into_iter().map(|c| c.shifted(by)).collect()),
        }
    }

    /// The text, each comparison in parentheses (`&&` and `||` with a
    /// comparison are of different groups until W3-07, S-45: the
    /// parentheses keep it one reading either way, and `fmt` removes them
    /// after).
    fn render(&self, names: &[String]) -> String {
        match self {
            Cond::True => "true".into(),
            Cond::Test(i, Test::Equal(lit)) => format!("({} == {lit})", names[*i]),
            Cond::And(v) => v
                .iter()
                .map(|c| match c {
                    Cond::Or(_) => format!("({})", c.render(names)),
                    _ => c.render(names),
                })
                .collect::<Vec<_>>()
                .join(" && "),
            Cond::Or(v) => v
                .iter()
                .map(|c| match c {
                    Cond::And(items) if items.len() > 1 => format!("({})", c.render(names)),
                    _ => c.render(names),
                })
                .collect::<Vec<_>>()
                .join(" || "),
        }
    }
}

/// One token of a skeleton: a token, or a hole.
#[derive(PartialEq)]
enum Skel<'a> {
    Tok(TokenKind, &'a str),
    Hole,
}

/// A pattern as the guard form keeps it: its skeleton, its holes (the first
/// and last token of each, in the order of the text), the condition on them,
/// and the edits that merge alternatives.
struct Shape<'a> {
    skel: Vec<Skel<'a>>,
    holes: Vec<(usize, usize)>,
    cond: Cond,
    edits: Vec<Edit>,
}

/// The shape of `p` (S-317): the alternatives of a pattern with holes are
/// one when they have the same skeleton (the tokens but the holes); the
/// first stays, the others are removed, and the condition is the `||` of
/// theirs. `None` when they differ, or a comment lies in what is removed
/// (S-251).
fn shape<'a>(c: &'a Cursor<'_>, toks: &[usize], p: &Pat) -> Option<Shape<'a>> {
    let tok = |pos: usize| Skel::Tok(c.kind(toks[pos]), c.src(toks[pos]));
    match &p.kind {
        PatKind::Hole(t) => Some(Shape {
            skel: vec![Skel::Hole],
            holes: vec![(toks[p.lo], toks[p.hi])],
            cond: Cond::Test(0, t.clone()),
            edits: Vec::new(),
        }),
        PatKind::Leaf => Some(Shape {
            skel: (p.lo..=p.hi).map(tok).collect(),
            holes: Vec::new(),
            cond: Cond::True,
            edits: Vec::new(),
        }),
        PatKind::Node(inner) => {
            let mut out = Shape { skel: Vec::new(), holes: Vec::new(), cond: Cond::True, edits: Vec::new() };
            let mut conds = Vec::new();
            let mut pos = p.lo;
            for q in inner {
                out.skel.extend((pos..q.lo).map(tok));
                let s = shape(c, toks, q)?;
                out.skel.extend(s.skel);
                if !matches!(s.cond, Cond::True) {
                    conds.push(s.cond.shifted(out.holes.len()));
                }
                out.holes.extend(s.holes);
                out.edits.extend(s.edits);
                pos = q.hi + 1;
            }
            out.skel.extend((pos..=p.hi).map(tok));
            out.cond = match conds.len() {
                0 => Cond::True,
                1 => conds.remove(0),
                _ => Cond::And(conds),
            };
            Some(out)
        }
        PatKind::Or(alts) => {
            let shapes = alts.iter().map(|a| shape(c, toks, a)).collect::<Option<Vec<_>>>()?;
            if shapes.iter().all(|s| s.holes.is_empty()) {
                // No hole: the alternatives stay as written.
                let skel = (p.lo..=p.hi).map(tok).collect();
                return Some(Shape { skel, holes: Vec::new(), cond: Cond::True, edits: Vec::new() });
            }
            if shapes.iter().any(|s| s.skel != shapes[0].skel) {
                return None;
            }
            // Remove ` | A_2 | ...`, which must hold no comment.
            let (from, to) = (toks[alts[0].hi], toks[p.hi]);
            if (from..=to).any(|i| matches!(c.kind(i), TokenKind::Comment | TokenKind::DocComment)) {
                return None;
            }
            let mut shapes = shapes.into_iter();
            let mut out = shapes.next()?;
            let conds = std::iter::once(out.cond).chain(shapes.map(|s| s.cond)).collect();
            out.cond = Cond::Or(conds);
            out.edits.push(Edit::delete(c.file_span(c.span(from).end, c.span(to).end)));
            Some(out)
        }
    }
}

/// A float literal in a pattern (§7, S-109, S-252): E0020 in the syntax
/// stage. In an arm of `match`, the candidate is the guard form, for all the
/// float literals of the arm's pattern at once (one form, S-248, S-317):
/// each becomes a name no other name of the file has (S-253), and the guard
/// compares them; alternatives are merged when they have the same skeleton
/// ([`shape`]). Elsewhere (`let`, `for`), or when the alternatives differ,
/// E0002 with the note.
fn float_pattern(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Pattern {
        return None;
    }
    // A float (also written as in other languages: `1.`, `0.5f32`, `.5`),
    // after a `-` and `(`s.
    let float_at = |i: usize| match c.kind(i) {
        TokenKind::Float => Some(i),
        TokenKind::ForeignLit if float_spelling(c.src(i)).is_some() => Some(i),
        TokenKind::Dot if c.kind(i + 1) == TokenKind::Int && !c.gap(i + 1).is_some() => Some(i + 1),
        _ => None,
    };
    let lit = match c.kind(c.at) {
        TokenKind::Minus => {
            let mut i = c.sig_after(c.at);
            while c.kind(i) == TokenKind::LParen {
                i = c.sig_after(i);
            }
            float_at(i)?
        }
        _ => float_at(c.at)?,
    };
    let span = c.file_span(c.span(c.at).start, c.span(lit).end);
    // The pattern's owner: the innermost `match` arm, `let` or `for`.
    let owner = c.open.iter().rev().find(|o| matches!(o.0, NodeKind::MatchArm | NodeKind::LetStmt | NodeKind::ForStmt));
    let Some(&(NodeKind::MatchArm, arm_start)) = owner else { return hit(span, Vec::new()) };
    let fix = guard_fix(c, arm_start);
    // Alternatives that do not merge (S-317): their own row.
    let pattern = (c.index_at(arm_start)..c.tokens.len())
        .take_while(|&i| !matches!(c.kind(i), TokenKind::FatArrow | TokenKind::KwIf | TokenKind::Eof));
    if fix.is_none() && pattern.into_iter().any(|i| c.kind(i) == TokenKind::Pipe) {
        c.say(RowId::FloatPatternChoice);
    }
    hit(span, fix.into_iter().collect())
}

/// The `n`-th name (from 1) the guard-form candidates may bind: `v`, `v2`,
/// `v3`, ... (S-253). A candidate takes the first ones no identifier of the
/// file spells: a name visible at the arm is declared or imported in the
/// file, or is a name of the prelude, which has none of these
/// (`onsa_sema`'s test `the_prelude_has_no_name_of_the_guard_candidates`);
/// the names the merged pattern keeps are identifiers of the file too.
pub fn guard_name(n: usize) -> String {
    if n <= 1 { "v".to_string() } else { format!("v{n}") }
}

/// The guard-form candidate of the arm that starts at `arm_start`.
fn guard_fix(c: &Cursor, arm_start: u32) -> Option<Fix> {
    // The pattern runs to `if` or `=>` outside brackets; the guard to `=>`.
    let first = c.index_at(arm_start);
    let mut depth = 0i32;
    let mut toks = Vec::new();
    let mut i = first;
    let (if_tok, arrow) = loop {
        match c.kind(i) {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
            TokenKind::KwIf if depth == 0 => {
                let mut j = i + 1;
                while c.kind(j) != TokenKind::FatArrow {
                    if matches!(c.kind(j), TokenKind::Eof | TokenKind::RBrace) {
                        return None;
                    }
                    j += 1;
                }
                break (Some(i), j);
            }
            TokenKind::FatArrow if depth == 0 => break (None, i),
            TokenKind::Eof => return None,
            _ => {}
        }
        if depth < 0 {
            return None;
        }
        if !matches!(c.kind(i), TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment) {
            toks.push(i);
        }
        i += 1;
    };
    let last_pat = *toks.last()?;
    let mut reader = PatReader { c, toks, pos: 0 };
    let pat = reader.or()?;
    if reader.pos != reader.toks.len() {
        return None;
    }
    let shape = shape(c, &reader.toks, &pat)?;
    if shape.holes.is_empty() {
        return None;
    }
    // New names: none that the file has (S-253).
    // The names in the holes of the string literals count too (S-319): a new
    // name that a misspelt `{v}` names would hide its E0302.
    let in_holes = c.holes.iter().flat_map(|h| {
        let inner = &c.text[h.start as usize..h.end as usize];
        inner.trim_start_matches('{').trim_end_matches('}').split('.')
    });
    let used: std::collections::HashSet<&str> = c
        .all
        .iter()
        .filter(|t| t.kind == TokenKind::Ident)
        .map(|t| &c.text[t.span.start as usize..t.span.end as usize])
        .chain(in_holes)
        .collect();
    let mut n = 0;
    let mut names = Vec::new();
    while names.len() < shape.holes.len() {
        n += 1;
        let name = guard_name(n);
        if !used.contains(name.as_str()) {
            names.push(name);
        }
    }
    let mut edits = shape.edits;
    for (&(a, b), name) in shape.holes.iter().zip(&names) {
        edits.push(Edit::replace(c.file_span(c.span(a).start, c.span(b).end), name.clone()));
    }
    let cond = match &shape.cond {
        // One comparison alone needs no parentheses.
        Cond::Test(k, Test::Equal(lit)) if if_tok.is_none() => format!("{} == {lit}", names[*k]),
        Cond::Or(_) if if_tok.is_some() => format!("({})", shape.cond.render(&names)),
        other => other.render(&names),
    };
    match if_tok {
        None => edits.push(Edit::insert(c.file, c.span(last_pat).end, format!(" if {cond}"))),
        Some(t) => {
            let g_first = c.sig_after(t);
            let g_last = c.sig_before(arrow)?;
            edits.push(Edit::insert(c.file, c.span(g_first).start, format!("{cond} && (")));
            edits.push(Edit::insert(c.file, c.span(g_last).end, ")"));
        }
    }
    Some(Fix::new("compare in a guard", edits))
}

// ------------------------------------------------------------ `+=` and `++`

/// The operators of the compound assignments (S-250).
fn compound_operator(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(kind, Plus | Minus | Star | Slash | Percent | Amp | Pipe | Caret | Shl | Shr)
}

/// Whether the expression `first..=last` needs parentheses as the right
/// operand of a binary operator: it holds an operator outside brackets, or
/// starts with a prefix operator.
fn needs_parens(c: &Cursor, first: usize, last: usize) -> bool {
    if matches!(c.kind(first), TokenKind::Minus | TokenKind::Bang) {
        return true;
    }
    let mut depth = 0;
    for i in first..=last {
        match c.kind(i) {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
            k if depth == 0 && (k.is_binary_op() || k == TokenKind::KwAs) => return true,
            _ => {}
        }
    }
    false
}

/// `x += 1` (and the other operators): `x = x + 1` when it is a statement
/// whose left side is a name or a path of fields (S-250). A left side that
/// would be read twice (`a[i] += 1`) and an expression (`let y = x += 1`) are
/// E0002 with the note.
fn compound_assignment(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr || c.kind(c.at) != TokenKind::Eq || c.gap(c.at).is_some() {
        return None;
    }
    let op = c.at.checked_sub(1).filter(|&o| compound_operator(c.kind(o)))?;
    let span = c.file_span(c.span(op).start, c.span(c.at).end);
    let unfixable = || {
        c.say(RowId::CompoundAssignUnfixable);
        hit(span, Vec::new())
    };
    let statement = c.top() == Some(NodeKind::BinaryExpr) && c.open_at(1).is_some_and(|o| o.0 == NodeKind::Block);
    if !statement {
        return unfixable();
    }
    let lhs_first = c.index_at(c.open_at(0)?.1);
    let rhs_first = c.sig_after(c.at);
    let rhs_last = statement_end(c, rhs_first);
    let (Some(rhs_last), true) = (rhs_last, is_place(c, lhs_first, op - 1)) else { return unfixable() };
    if rhs_last < rhs_first {
        return unfixable();
    }
    let lhs = &c.text[c.span(lhs_first).start as usize..c.span(op - 1).end as usize];
    let parens = needs_parens(c, rhs_first, rhs_last);
    let mut edits = vec![
        Edit::delete(c.span(op)),
        Edit::replace(
            c.file_span(c.span(c.at).end, c.span(rhs_first).start),
            format!(" {lhs} {} {}", c.src(op), if parens { "(" } else { "" }),
        ),
    ];
    if parens {
        edits.push(Edit::insert(c.file, c.span(rhs_last).end, ")"));
    }
    hit(span, vec![Fix::new("write the assignment out", edits)])
}

/// `++x`, `x++`, `--x`, `x--` (S-250, S-297): `x = x + 1` as a statement
/// whose operand is a name or a path of fields; else E0002 with the note.
fn increment(c: &Cursor) -> Option<Hit> {
    let kind = c.kind(c.at);
    if !matches!(kind, TokenKind::PlusPlus | TokenKind::MinusMinus) {
        return None;
    }
    let op = if kind == TokenKind::PlusPlus { "+" } else { "-" };
    let span = c.span(c.at);
    let none = || {
        c.say(RowId::IncrementUnfixable);
        hit(span, Vec::new())
    };
    // `++x` as a statement: nothing of it was read yet.
    if c.want == Want::Expr && c.top() == Some(NodeKind::Block) {
        let first = c.at + 1;
        let Some(last) = statement_end(c, first) else { return none() };
        if !is_place(c, first, last) || !ends_statement(c, last) {
            return none();
        }
        let place = &c.text[c.span(first).start as usize..c.span(last).end as usize];
        let fix = Fix::new(
            "write the assignment out",
            vec![
                Edit::delete(c.file_span(span.start, c.span(first).start)),
                Edit::insert(c.file, c.span(last).end, format!(" = {place} {op} 1")),
            ],
        );
        return hit(span, vec![fix]);
    }
    // `x++` as a statement: the statement `x` closed before it.
    if let [(NodeKind::PathExpr | NodeKind::FieldExpr, start), .., (NodeKind::ExprStmt, _)] = c.closed
        && c.top() == Some(NodeKind::Block)
        && ends_statement(c, c.at)
    {
        let first = c.index_at(*start);
        if is_place(c, first, c.at - 1) && c.gap(c.at) == Gap::None {
            let place = &c.text[c.span(first).start as usize..c.span(c.at - 1).end as usize];
            return hit(span, vec![Fix::replace("write the assignment out", span, format!(" = {place} {op} 1"))]);
        }
    }
    none()
}
