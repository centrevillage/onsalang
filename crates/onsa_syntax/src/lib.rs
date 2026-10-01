//! Lexer, parser, AST, and formatter for Onsa (M1).

pub mod ast;
pub mod diff;
pub mod dump;
pub mod fmt;
mod groups;
pub mod lexer;
mod naming;
pub mod parser;
pub mod token;

use onsa_diag::FileId;

pub use dump::dump;
pub use fmt::format;
pub use lexer::{Lexed, lex};
pub use parser::Parsed;
pub use token::{Token, TokenKind};

/// Lex and parse one file. Never fails: diagnostics are in `Parsed.diagnostics`
/// (at most one per top-level item, P-01) and the AST may be partial.
pub fn parse(file: FileId, text: &str) -> Parsed {
    let lexed = lex(file, text);
    parser::Parser::new(file, text, lexed.tokens, lexed.diagnostics).parse_file()
}
