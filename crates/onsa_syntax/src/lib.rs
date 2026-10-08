//! Lexer, parser, CST, AST, and formatter for Onsa (M1, R-86).
//!
//! The stages: lexing → parsing into the CST → the AST from the CST → the
//! checks on the AST of this crate (operator groups, naming).

pub mod ast;
pub mod cst;
#[cfg(test)]
mod cst_tests;
pub mod diff;
pub mod dump;
pub mod fmt;
mod groups;
pub mod lexer;
mod lower;
mod naming;
pub mod parser;
pub mod token;

use onsa_diag::{FileId, Stage};

pub use cst::Cst;
pub use dump::dump;
pub use fmt::format;
pub use lexer::{Lexed, lex};
pub use lower::AstMap;
pub use parser::Parsed;
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

/// Lex and parse one file. Never fails: diagnostics are in `Parsed.diagnostics`
/// (at most one per top-level item, P-01). The CST holds the whole source;
/// the AST holds the items that parsed. A broken CST (a bug) is an internal
/// error (`onsa_diag::internal::bug`), checked on every parse (R-82).
pub fn parse(file: FileId, text: &str) -> Parsed {
    let lexed = lex(file, text);
    let out = parser::Parser::new(file, text, lexed.tokens, lexed.diagnostics).parse_file();
    let cst = cst::build(out.tokens, out.events);
    if let Err(e) = cst.validate(text) {
        onsa_diag::internal::bug(Some(e.span), format!("the CST is broken: {}", e.message));
    }
    let (ast, map) = lower::lower(&cst, text);
    let mut diagnostics = out.diagnostics;
    groups::check(&ast, text, &mut diagnostics);
    naming::check(&ast, &mut diagnostics);
    // Read before the diagnostics are reduced to one per item (S-56): an
    // earlier diagnostic of a later stage must not hide a syntax one.
    let syntax: Vec<onsa_diag::Diagnostic> = diagnostics.iter().filter(|d| d.stage == Stage::Syntax).cloned().collect();
    let diagnostics = parser::first_per_item(&out.item_ranges, diagnostics);
    Parsed { ast, cst, map, diagnostics, syntax, levels: out.levels }
}
