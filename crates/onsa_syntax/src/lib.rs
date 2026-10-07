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

use onsa_diag::FileId;

pub use cst::Cst;
pub use dump::dump;
pub use fmt::format;
pub use lexer::{Lexed, lex};
pub use lower::AstMap;
pub use parser::Parsed;
pub use token::{Token, TokenKind};

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
    let diagnostics = parser::first_per_item(&out.item_ranges, diagnostics);
    Parsed { ast, cst, map, diagnostics }
}
