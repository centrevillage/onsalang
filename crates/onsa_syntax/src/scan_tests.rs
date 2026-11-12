//! Tests of the table of where brackets close (`crate::scan::Brackets`,
//! R-401, R-403, R-408): it answers as the scans from each opener did, and
//! the failures of a file do not each scan on to its end.

use onsa_diag::FileId;

use crate::scan::{Brackets, MADE, OpenBrackets, WALKED, pair};
use crate::token::{Token, TokenKind};

/// The scan the table's contents replaced: from `open` on, brackets of any
/// kind closing one another, to the first closer back at the depth of
/// `open` (the reference).
fn scan_contents(tokens: &[Token], open: usize) -> Option<(usize, bool, bool)> {
    let (mut depth, mut comma, mut semi) = (0u32, false, false);
    for (i, t) in tokens.iter().enumerate().skip(open) {
        match t.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return (t.kind == TokenKind::RBracket).then_some((i, comma, semi));
                }
            }
            TokenKind::Comma if depth == 1 => comma = true,
            TokenKind::Semi if depth == 1 => semi = true,
            TokenKind::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The scan the table's closing replaced: from `open` on, paired by kind
/// ([`pair`]), none when a closer closes another than the innermost (the
/// reference).
fn scan_closing(tokens: &[Token], open: usize) -> Option<usize> {
    let mut brackets = OpenBrackets::default();
    for (i, t) in tokens.iter().enumerate().skip(open) {
        let innermost = brackets.last().copied();
        let closed = pair(&mut brackets, tokens, i, 0);
        match t.kind {
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if closed != innermost => return None,
            _ if closed == Some(open) => return Some(i),
            TokenKind::Eof => return None,
            _ => {}
        }
    }
    None
}

fn code_tokens(src: &str) -> Vec<Token> {
    crate::layout::code_tokens(&crate::lex(FileId(0), src).tokens).0
}

/// The table answers as the two scans at every opener of `src`, and none
/// at any other token.
fn assert_as_the_scans(name: &str, src: &str) {
    let tokens = code_tokens(src);
    let table = Brackets::new(&tokens);
    for i in 0..tokens.len() + 1 {
        let opens = tokens
            .get(i)
            .is_some_and(|t| matches!(t.kind, TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace));
        let (contents, closing) =
            if opens { (scan_contents(&tokens, i), scan_closing(&tokens, i)) } else { (None, None) };
        assert_eq!(table.contents(i), contents, "{name}: the contents at token {i}");
        assert_eq!(table.closing(i), closing, "{name}: the closing at token {i}");
        // The scan on a line reads as the table where no line break comes first.
        let on_line = closing.filter(|&c| tokens[i..c].iter().all(|t| t.kind != TokenKind::Newline));
        assert_eq!(crate::scan::closing_on_line(&tokens, i), on_line, "{name}: the closing on the line at token {i}");
    }
}

/// Every `.onsa` file of the repository (the cases, the inputs of the fuzz,
/// the library, the examples), and runs of brackets of every kind closing
/// one another out of order, from a fixed seed.
#[test]
fn the_table_answers_as_the_scans_from_each_opener() {
    let files = crate::cst_tests::repo_files();
    assert!(files.len() > 1000, "{} files", files.len());
    for (name, text) in &files {
        assert_as_the_scans(name, text);
    }
    let pieces = ["(", ")", "[", "]", "{", "}", ",", ";", "a", "\n"];
    let mut seed = 0x2545_f491_u32;
    for k in 0..2000 {
        let src: String = (0..24)
            .map(|_| {
                seed ^= seed << 13;
                seed ^= seed >> 17;
                seed ^= seed << 5;
                pieces[seed as usize % pieces.len()]
            })
            .collect::<Vec<_>>()
            .join(" ");
        assert_as_the_scans(&format!("run {k}: {src:?}"), &src);
    }
}

/// How many tables the reading of `src` made and how many tokens the
/// tables and the scans on a line went through, with the tokens of `src`.
fn walked(src: &str) -> (usize, usize, usize) {
    let (made, walked) = (MADE.get(), WALKED.get());
    crate::parse(FileId(0), src);
    (MADE.get() - made, WALKED.get() - walked, code_tokens(src).len())
}

/// A file of many failures in brackets left open (R-401: a `[` with a word
/// at the head of the next line; R-403: a `[` after a blank; R-408: a `[`
/// after a name, which the parser asks about before it reads on): the table
/// is made once for the file, and the tokens gone through are bounded by
/// the file, not by the failures times the file.
#[test]
fn the_failures_in_brackets_left_open_scan_the_file_once() {
    let forms = [
        "fn f{i}() -> I32 {\n  let y = [1,\nexport fn z{i}() -> I32 { 1 }\n",
        "fn f{i}() -> I32 {\n  let y = [1,\nexport 2\n",
        "fn f{i}() -> I32 {\n  let y = [1,\nx 2\n",
        "fn f{i}() -> I32 {\n  let y = g [1,\n",
        "fn f{i}() -> I32 {\n  let y = g[1,\n",
    ];
    for form in forms {
        let src: String = (0..200).map(|i| form.replace("{i}", &i.to_string())).collect();
        let (made, walked, tokens) = walked(&src);
        assert_eq!(made, 1, "{form:?}: made {made} tables");
        assert!(walked <= 2 * tokens, "{form:?}: went through {walked} tokens for a file of {tokens}");
    }
}

/// A file of no failure makes no table when no `[` touches a name or a
/// value before it (the parser asks about those, [`crate::foreign::type_list_ahead`]),
/// and one when one does.
#[test]
fn a_file_without_failures_makes_a_table_only_for_a_bracket_after_a_name() {
    let plain = "fn f(x: I32) -> I32 {\n  let y = (x + 1) * 2\n  y\n}\n";
    assert_eq!(walked(plain).0, 0);
    let indexed = "fn f(xs: [I32; 4]) -> I32 {\n  xs[0] + xs[1]\n}\n";
    assert_eq!(walked(indexed).0, 1);
}
