//! Lexer, parser, CST, AST, and formatter for Onsa (M1, R-86).
//!
//! The stages: lexing → parsing into the CST → the AST from the CST → the
//! checks on the AST of this crate (operator groups, naming).

pub mod ast;
pub mod attrs;
mod callee;
mod chars;
pub mod cst;
#[cfg(test)]
mod cst_tests;
pub mod diff;
mod docs;
pub mod dump;
mod edits;
pub mod fmt;
pub mod foreign;
#[cfg(test)]
mod foreign_tests;
mod groups;
mod layout;
#[cfg(test)]
mod layout_tests;
pub mod lexer;
mod literal;
#[cfg(test)]
mod literal_tests;
mod lower;
mod naming;
mod nesting;
mod operands;
#[cfg(test)]
mod operands_tests;
pub mod parser;
#[cfg(test)]
mod parser_tests;
mod scan;
mod starts;
pub mod test_name;
pub mod token;
pub mod units;

use onsa_diag::{Diagnostic, FileId, Stage};

use crate::ast::Ast;

pub use cst::Cst;
pub use dump::dump;
pub use fmt::format;
pub use layout::continues;
pub use lexer::{Lexed, lex};
pub use literal::{FloatRange, FloatWidth, float_shown, float_value};
pub use lower::AstMap;
pub use naming::{PathPart, is_module_name, path_name_error};
pub use operands::CandidateReads;
pub use token::{Token, TokenKind};

/// The rules of the diagnostics ([`onsa_diag::contract`]) checked on
/// `diagnostics`, with the token boundaries of their files from the lexer: the
/// one place the driver (in debug builds) and the test runner check them
/// (plan D-04, W3-02). Each problem names the diagnostic's code and position.
pub fn diagnostic_contract(sources: &onsa_diag::SourceMap, diagnostics: &[onsa_diag::Diagnostic]) -> Vec<String> {
    let boundaries: std::cell::RefCell<std::collections::HashMap<FileId, Vec<u32>>> = Default::default();
    let is_boundary = |file: FileId, at: u32| {
        let mut cache = boundaries.borrow_mut();
        let b = cache.entry(file).or_insert_with(|| {
            let mut b: Vec<u32> =
                lex(file, sources.file(file).text()).tokens.iter().flat_map(|t| [t.span.start, t.span.end]).collect();
            b.sort_unstable();
            b.dedup();
            b
        });
        b.binary_search(&at).is_ok()
    };
    let mut out = Vec::new();
    for d in diagnostics {
        for p in onsa_diag::contract(d, sources, &is_boundary) {
            let f = sources.file(d.span.file);
            let lc = f.line_col(d.span.start);
            out.push(format!("{}:{}:{}: {p}", f.name(), lc.line, lc.col));
        }
    }
    out
}

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
    /// What the completion of the candidates read again (`crate::operands`).
    pub candidate_reads: crate::operands::CandidateReads,
}

impl Parsed {
    /// The file has a diagnostic of the syntax stage, whatever its code
    /// (spec §18.2, S-214: E00xx, the reserved word's E0200, E0408, E0006):
    /// `onsa fmt` does not rewrite it and `onsa diff --ast` does not compare
    /// it. The one place of that decision (`fmt`, `diff --ast`, the test
    /// tools); what they report is `onsa_driver::reduce::syntax_report`.
    pub fn syntax_errors(&self) -> bool {
        self.first_syntax_error().is_some()
    }

    /// The first diagnostic of the syntax stage ([`Parsed::syntax_errors`]):
    /// what the check of `onsa fmt` names when its output has one.
    pub fn first_syntax_error(&self) -> Option<&Diagnostic> {
        self.diagnostics.iter().find(|d| d.stage == Stage::Syntax)
    }
}

/// Lex and parse one file. Never fails: diagnostics are in `Parsed.diagnostics`
/// (every one; the choice of one per unit is the driver's, spec §18.1), and
/// the units they are of in `Parsed.units`. The CST holds the whole source;
/// the AST holds the items that parsed and the failed items whose name was
/// read (S-59). A broken CST (a bug) is an internal error
/// (`onsa_diag::internal::bug`), checked on every parse (R-82).
pub fn parse(file: FileId, text: &str) -> Parsed {
    // What the judgment of whether two tokens join lexes for the file
    // (`CandidateReads::lexed`): the rows' and the candidates' reported.
    let lexed = edits::lexed();
    let Read { mut ast, cst, map, mut diagnostics, levels, mut units, apart } = read(file, text, parser::ItemCtx::Top);
    naming::check(&ast, &mut diagnostics);
    units.mark_failed(&diagnostics, &mut ast);
    // The candidates that make a block-like expression an operand take its
    // parentheses (§3.1, S-537): the one place, after every check of the
    // syntax stage. It reads units again with `read` only.
    let mut candidate_reads = operands::complete(text, &cst, &units, &apart, &mut diagnostics);
    candidate_reads.lexed = edits::lexed() - lexed;
    Parsed { ast, cst, map, diagnostics, units, levels, candidate_reads }
}

/// What [`read`] makes of a text.
pub(crate) struct Read {
    pub ast: ast::Ast,
    pub cst: Cst,
    pub map: AstMap,
    pub diagnostics: Vec<onsa_diag::Diagnostic>,
    pub levels: Vec<u32>,
    /// The units of the text, not yet marked with the diagnostics
    /// ([`units::Units::mark_failed`]).
    pub units: units::Units,
    /// The insertions of the candidates that go apart from the tokens round
    /// them ([`edits::apart`]).
    pub apart: edits::Insertions,
}

/// The text lexed and parsed as the declarations of a list of `ctx` (a
/// file at the top level), its CST and AST, and the checks of the syntax
/// stage on its tree. [`parse`] reads a file with it, and
/// [`operands::complete`] the text of one unit with a candidate applied: it
/// never completes candidates itself, so that reading goes one level deep.
pub(crate) fn read(file: FileId, text: &str, ctx: parser::ItemCtx) -> Read {
    let lexed = lex(file, text);
    let out = parser::Parser::new(file, text, lexed).parse_units(ctx);
    let cst = cst::build(out.tokens, out.goes_on, out.events);
    if let Err(e) = cst.validate(text) {
        onsa_diag::internal::bug(Some(e.span), format!("the CST is broken: {}", e.message));
    }
    let (ast, map) = lower::lower(&cst, text, &out.literals);
    let mut diagnostics = out.diagnostics;
    // The doc comments are checked before the units are made: a run of
    // tokens of no item takes trivia with a diagnostic (S-259).
    docs::check(&cst, text, &mut diagnostics);
    let units = units::build(&cst, &map, text, &out.items, &diagnostics);
    let limit = nesting::Limit { text, units: &units };
    // The operator groups (E0010) are checked on the AST, so an E0010 in the
    // part of a failed body that has no AST is not found, and the parse error
    // after it is the unit's syntax error: §18.1 ("the first in the text")
    // may not hold there until the recovery by statement (M7, T7-1) lowers
    // the statements before the error (accepted, 2026-10-08).
    groups::check(&ast, &|e| map.expr_kind(&cst, e), limit, &mut diagnostics);
    let mut apart = edits::Insertions::default();
    foreign::clocks(&cst, limit, &mut diagnostics, &mut apart);
    Read { ast, cst, map, diagnostics, levels: out.levels, units, apart }
}
