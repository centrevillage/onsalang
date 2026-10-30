//! Self-tests of the tables of the spaces and of the lists (`fmt/space.rs`,
//! `fmt/shape.rs`; W3-11 unit U2). The canonical files are the answers: the
//! files the harness of the cases asks to be canonical (no marker `//~`, a
//! case of a mode that runs and without `canonical = false`, [`canonical_by_case`])
//! under `tests/spec`, every file under `std`, and the sources of [`EXTRA`].
//! The choice reads the settings of the cases, not the printer, so it stays
//! when the printer reads the tables.
//!
//! - The spaces: on every line, the text between two code tokens is the
//!   space of the table. One rule of the canonical form puts more there and
//!   is left out: the column of the `=` of a run of `let` and `var`
//!   (`fmt/align.rs`), so the gap before such an `=` may be one space or more.
//!   The indentation and the comments at the end of the lines are not
//!   between two code tokens.
//! - The lists: in every list, the form agrees with the invariants of §3.2
//!   (block: a `,` after every element and the closing bracket on a line of
//!   its own; one line and continuation: no `,` after the last element;
//!   continuation: an element that starts a line starts at the column of the
//!   first). The `..` of a struct pattern
//!   is last and has no `,` after it (S-500).
//! - Every row of both tables is met, and no row that says one space meets a
//!   row that says none, except at `{}` and at a `{` right inside a round or
//!   square bracket (`f({ a })`), where none is meant to win.
//! - In every file of the repository that the syntax stage reads without a
//!   diagnostic, every node with a bracket among its tokens is in the table
//!   of the lists, with the brackets of its row (`Pairs`), and the parent of
//!   every block is a form whose body it is (`shape::BLOCK_HOLDERS`) or a
//!   kind that holds a block expression ([`EXPRESSION_BLOCK_HOLDERS`]): a new
//!   form with a body fails here instead of being read as a block expression.

use std::path::Path as FsPath;
use std::time::{Duration, Instant};

use onsa_diag::FileId;

use super::shape::{self, Form, Pairs, Shape};
use super::space::{self, Space};
use crate::cst::{Cst, NodeId, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// Canonical sources for what no file has: a struct pattern with `..` in the
/// block form (S-500; the syntax stage reads the `..`, a later stage reports
/// it, S-366).
pub(super) const EXTRA: &[(&str, &str)] = &[(
    "EXTRA[0]",
    "fn f(p: P) -> I32 {\n  match p {\n    P {\n      x: 1,\n      ..\n    } => 1,\n    P { x: 2, .. } => 2,\n    \
     P { .. } => 3,\n  }\n}\n",
)];

/// The kinds of the parents of the blocks that are block expressions (a form of their own,
/// `shape::Base::Body`), met in the files of the repository. A kind met anew goes here when the
/// block is an operand there, and in `shape::BLOCK_HOLDERS` when it is the body of the form. A
/// block in parentheses is the operand of an operator that E0013 asks for (`({ n }) - 10`, §3.1).
const EXPRESSION_BLOCK_HOLDERS: &[NodeKind] = &[
    NodeKind::Arg,
    NodeKind::ArrayExpr,
    NodeKind::Const,
    NodeKind::ExprStmt,
    NodeKind::LetStmt,
    NodeKind::MatchArm,
    NodeKind::ParenExpr,
];

/// The time the test may take in a debug build (it took about 4 s on 2026-10-13).
const BUDGET: Duration = Duration::from_secs(30);

const BRACKETS: &[TokenKind] = &[
    TokenKind::LParen,
    TokenKind::RParen,
    TokenKind::LBracket,
    TokenKind::RBracket,
    TokenKind::LBrace,
    TokenKind::RBrace,
];

#[derive(Default)]
struct Tally {
    files: usize,
    read: usize,
    lines: usize,
    pairs: usize,
    aligned: usize,
    lists: [usize; 3],
    space_rows: Vec<bool>,
    shape_rows: Vec<bool>,
    errors: Vec<String>,
}

fn line_col(text: &str, offset: u32) -> (usize, usize) {
    let before = &text[..offset as usize];
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    (before.matches('\n').count() + 1, before[line_start..].chars().count())
}

fn describe(cst: &Cst, t: TokenIdx) -> String {
    format!("{:?} in {}", cst.token(t).kind, cst.kind(cst.token_parent(t)).name())
}

/// The `[test]` settings that make a case's files without markers not
/// canonical, read from the fragment at the head of `text` (the lines of
/// `//` after `// onsa.toml`; the keys `mode` and `canonical` are only in
/// `[test]`): `mode = "none"` or `canonical = false`.
fn not_canonical(text: &str) -> bool {
    let mut lines = text.lines();
    if lines.next() != Some("// onsa.toml") {
        return false;
    }
    lines
        .take_while(|l| l.starts_with("//"))
        .map(|l| l.trim_start_matches('/').split_whitespace().collect::<String>())
        .any(|l| l == "mode=\"none\"" || l == "canonical=false")
}

/// Whether the harness of the cases asks the file `name` of `files` to be
/// canonical (`onsa_tests::run`): under `tests/spec`, no marker, and the
/// settings of its case (the fragment of the file, or of the package that
/// holds it, the nearest directory with `onsa.toml`) do not say otherwise.
pub(super) fn canonical_by_case(name: &str, text: &str, files: &[(String, String)], root: &FsPath) -> bool {
    if name.starts_with("std/") || name.starts_with("EXTRA") {
        return true;
    }
    if !name.starts_with("tests/spec/") || text.contains("//~") {
        return false;
    }
    let package = FsPath::new(name)
        .ancestors()
        .skip(1)
        .take_while(|d| d.starts_with("tests/spec"))
        .find(|d| root.join(d).join("onsa.toml").is_file());
    match package {
        Some(dir) => {
            let prefix = format!("{}/", dir.to_string_lossy());
            !files.iter().any(|(n, t)| n.starts_with(&prefix) && not_canonical(t))
        }
        None => !not_canonical(text),
    }
}

fn check_spaces(name: &str, text: &str, cst: &Cst, tally: &mut Tally) {
    let mut prev: Option<TokenIdx> = None;
    let mut code_lines = 0;
    for (i, tok) in cst.tokens().iter().enumerate() {
        let t = TokenIdx(i as u32);
        match tok.kind {
            TokenKind::Whitespace => continue,
            TokenKind::Newline | TokenKind::Eof => {
                code_lines += usize::from(prev.is_some());
                prev = None;
                continue;
            }
            k if k.is_comment() => {
                prev = None;
                continue;
            }
            _ => {}
        }
        if let Some(p) = prev {
            tally.pairs += 1;
            let actual = &text[cst.token(p).span.end as usize..tok.span.start as usize];
            let rows: Vec<(usize, Space)> = space::rows(cst, p, t).collect();
            for &(r, _) in &rows {
                tally.space_rows[r] = true;
            }
            let says = |s| rows.iter().any(|&(_, x)| x == s);
            let meant = matches!(
                (cst.token(p).kind, tok.kind),
                (TokenKind::LBrace, TokenKind::RBrace) | (TokenKind::LParen | TokenKind::LBracket, TokenKind::LBrace)
            );
            let expected = match space::space(cst, p, t) {
                Space::None => "",
                Space::One => " ",
            };
            let aligned = tok.kind == TokenKind::Eq
                && matches!(cst.kind(cst.token_parent(t)), NodeKind::LetStmt | NodeKind::VarStmt)
                && !actual.is_empty()
                && actual.bytes().all(|b| b == b' ');
            tally.aligned += usize::from(aligned && actual != " ");
            let (line, col) = line_col(text, tok.span.start);
            if actual != expected && !aligned {
                tally.errors.push(format!(
                    "{name}:{line}:{col}: {:?} between {} and {}, the table says {expected:?}",
                    actual,
                    describe(cst, p),
                    describe(cst, t)
                ));
            }
            if says(Space::One) && says(Space::None) && !meant {
                tally.errors.push(format!(
                    "{name}:{line}:{col}: rows {rows:?} disagree between {} and {}",
                    describe(cst, p),
                    describe(cst, t)
                ));
            }
        }
        prev = Some(t);
    }
    tally.lines += code_lines;
}

/// The first code token from `from` on (no trivia).
fn next_code(cst: &Cst, from: usize) -> Option<TokenKind> {
    cst.tokens()[from..].iter().map(|t| t.kind).find(|k| !k.is_trivia())
}

/// The last code token before `to` (no trivia).
fn last_code(cst: &Cst, to: usize) -> Option<TokenKind> {
    cst.tokens()[..to].iter().rev().map(|t| t.kind).find(|k| !k.is_trivia())
}

/// The last token before `to` that is no whitespace (and no comment, when `comments`).
fn last_before(cst: &Cst, to: usize, comments: bool) -> Option<TokenKind> {
    cst.tokens()[..to]
        .iter()
        .rev()
        .map(|t| t.kind)
        .find(|k| *k != TokenKind::Whitespace && !(comments && k.is_comment()))
}

fn check_list(name: &str, text: &str, cst: &Cst, n: NodeId, tally: &mut Tally) {
    let form = shape::form(cst, n).expect("a list has a form");
    let (_, close) = shape::brackets(cst, n).expect("a list has brackets");
    let elems = shape::elements(cst, n);
    let rest = shape::rest(cst, n);
    tally.lists[form as usize] += 1;
    let (line, col) = line_col(text, cst.span(n).start);
    let mut fail = |what: &str| {
        tally.errors.push(format!("{name}:{line}:{col}: {} in the {form:?} form: {what}", cst.kind(n).name()))
    };
    if let Some(r) = &rest
        && next_code(cst, r.end.index()) != Some(cst.token(close).kind)
    {
        fail("the `..` is not last, or has a `,` after it");
    }
    match form {
        Form::Block => {
            if elems.iter().any(|e| next_code(cst, e.end.index()) != Some(TokenKind::Comma)) {
                fail("an element without a `,` after it");
            }
            if last_before(cst, close.index(), false) != Some(TokenKind::Newline) {
                fail("the closing bracket is not on a line of its own");
            }
        }
        Form::OneLine | Form::Continuation => {
            if !elems.is_empty() && last_code(cst, close.index()) == Some(TokenKind::Comma) {
                fail("a `,` after the last element");
            }
        }
    }
    if form == Form::Continuation {
        let column = |e: &std::ops::Range<TokenIdx>| line_col(text, cst.token(e.start).span.start).1;
        let first = column(&elems[0]);
        let starts_line =
            |e: &std::ops::Range<TokenIdx>| last_before(cst, e.start.index(), true) == Some(TokenKind::Newline);
        if elems.iter().chain(&rest).any(|e| starts_line(e) && column(e) != first) {
            fail("an element that starts a line is not under the first");
        }
    }
}

/// Every node of `cst` with a bracket among its tokens is in the table of
/// the lists, with exactly the two brackets of its row.
fn check_coverage(name: &str, cst: &Cst, tally: &mut Tally) {
    let mut stack = vec![cst.root()];
    while let Some(n) = stack.pop() {
        stack.extend(cst.child_nodes(n));
        let kinds: Vec<TokenKind> =
            cst.child_tokens(n).map(|t| cst.token(t).kind).filter(|k| BRACKETS.contains(k)).collect();
        let fits = match shape::shape(cst.kind(n)) {
            Some(row) => match row.pairs {
                Pairs::One => kinds == [row.open, row.close],
                Pairs::Nested => {
                    let k = kinds.len() / 2;
                    kinds.iter().enumerate().all(|(i, &b)| b == if i < k { row.open } else { row.close })
                        && kinds.len() % 2 == 0
                }
            },
            None => kinds.is_empty(),
        };
        if cst.kind(n) == NodeKind::Block
            && let Some(p) = cst.parent(n)
            && !shape::BLOCK_HOLDERS.contains(&cst.kind(p))
            && !EXPRESSION_BLOCK_HOLDERS.contains(&cst.kind(p))
        {
            tally.errors.push(format!(
                "{name}: a block at {:?} in a {}, in neither shape::BLOCK_HOLDERS nor EXPRESSION_BLOCK_HOLDERS",
                cst.span(n),
                cst.kind(p).name()
            ));
        }
        if !fits {
            tally.errors.push(format!(
                "{name}: a {} at {:?} holds the brackets {kinds:?}, its row of the lists says otherwise",
                cst.kind(n).name(),
                cst.span(n)
            ));
        }
    }
}

fn check_shapes(name: &str, text: &str, cst: &Cst, tally: &mut Tally) {
    let mut stack = vec![cst.root()];
    while let Some(n) = stack.pop() {
        stack.extend(cst.child_nodes(n));
        let Some(row) = shape::shape(cst.kind(n)) else { continue };
        if shape::brackets(cst, n).is_none() {
            continue; // `-1`: check_coverage holds that only a row of `Pairs::Nested` may lack them
        }
        tally.shape_rows[shape::TABLE.iter().position(|b| b.node == row.node).unwrap()] = true;
        if row.shape == Shape::List {
            check_list(name, text, cst, n, tally);
        }
    }
}

#[test]
fn the_tables_of_the_spaces_and_of_the_lists_agree_with_every_canonical_file() {
    let started = Instant::now();
    let tally = onsa_diag::stack::run(|| {
        let mut tally = Tally {
            space_rows: vec![false; space::ROW_COUNT],
            shape_rows: vec![false; shape::TABLE.len()],
            ..Tally::default()
        };
        let root = crate::cst_tests::root_dir();
        let mut files = crate::cst_tests::repo_files();
        files.extend(EXTRA.iter().map(|(name, text)| (name.to_string(), text.to_string())));
        for (name, text) in &files {
            let canonical = canonical_by_case(name, text, &files, &root);
            let parsed = crate::parse(FileId(0), text);
            if parsed.syntax_errors() {
                assert!(!canonical, "{name}: a canonical file with a syntax error");
                continue;
            }
            tally.read += 1;
            check_coverage(name, &parsed.cst, &mut tally);
            if canonical {
                tally.files += 1;
                check_spaces(name, text, &parsed.cst, &mut tally);
                check_shapes(name, text, &parsed.cst, &mut tally);
            }
        }
        tally
    });
    let elapsed = started.elapsed();
    eprintln!(
        "{} canonical files of {} read, {} lines, {} pairs ({} aligned `=`), lists one line / block / continuation: \
         {:?}, {elapsed:?}",
        tally.files, tally.read, tally.lines, tally.pairs, tally.aligned, tally.lists
    );
    assert!(tally.files > 250, "only {} canonical files", tally.files);
    assert!(tally.read > 800, "only {} files read", tally.read);
    assert!(tally.lists.iter().all(|&n| n > 0), "a form of list never met: {:?}", tally.lists);
    let unmet: Vec<usize> = (0..space::ROW_COUNT).filter(|&i| !tally.space_rows[i]).collect();
    assert!(unmet.is_empty(), "rows of the spaces never met: {unmet:?}");
    let unmet: Vec<&str> =
        shape::TABLE.iter().zip(&tally.shape_rows).filter(|(_, met)| !**met).map(|(b, _)| b.node.name()).collect();
    assert!(unmet.is_empty(), "rows of the lists never met: {unmet:?}");
    assert!(tally.errors.is_empty(), "{} disagreements:\n{}", tally.errors.len(), tally.errors.join("\n"));
    assert!(elapsed < BUDGET, "the self-test took {elapsed:?}");
}

/// RF-14: `space::space`, which reads the rows through the index by the
/// left token, gives the answer of every row of the table (none when a
/// matching row says none) for every two code tokens one after the other
/// (trivia between them or not) in every file of the repository and of
/// [`EXTRA`], those with a syntax error too.
#[test]
fn the_index_of_the_spaces_gives_the_answer_of_every_row() {
    let (files, pairs, none) = onsa_diag::stack::run(|| {
        let mut files = crate::cst_tests::repo_files();
        files.extend(EXTRA.iter().map(|(name, text)| (name.to_string(), text.to_string())));
        let (mut pairs, mut none) = (0, 0);
        for (name, text) in &files {
            let cst = crate::parse(FileId(0), text).cst;
            let code = (0..cst.tokens().len()).map(|i| TokenIdx(i as u32)).filter(|&t| !cst.token(t).kind.is_trivia());
            let code: Vec<TokenIdx> = code.collect();
            for w in code.windows(2) {
                let every =
                    if space::rows(&cst, w[0], w[1]).any(|(_, s)| s == Space::None) { Space::None } else { Space::One };
                let got = space::space(&cst, w[0], w[1]);
                assert_eq!(got, every, "{name}: between {} and {}", describe(&cst, w[0]), describe(&cst, w[1]));
                (pairs, none) = (pairs + 1, none + usize::from(got == Space::None));
            }
        }
        (files.len(), pairs, none)
    });
    eprintln!("{files} files, {pairs} pairs of code tokens, {none} with no space");
    assert!(files > 1000 && pairs > 100_000 && none > 10_000, "{files} files, {pairs} pairs, {none} with none");
}

#[test]
fn the_kinds_of_the_brackets_in_the_table_of_the_spaces_are_those_of_the_table_of_the_lists() {
    for k in EXPRESSION_BLOCK_HOLDERS {
        assert!(!shape::BLOCK_HOLDERS.contains(k), "{} holds a body and a block expression", k.name());
    }
    let open_of = |kind: NodeKind| shape::shape(kind).map(|b| b.open);
    for &k in space::ATTACHED_PAREN {
        assert_eq!(open_of(k), Some(TokenKind::LParen), "{}", k.name());
    }
    for &k in space::ATTACHED_SQUARE {
        assert_eq!(open_of(k), Some(TokenKind::LBracket), "{}", k.name());
    }
    let braces: Vec<NodeKind> = space::SPACED_BRACES.iter().chain(space::TIGHT_BRACES).copied().collect();
    for &k in &braces {
        assert_eq!(open_of(k), Some(TokenKind::LBrace), "{}", k.name());
    }
    // Every kind with braces says whether it has a space inside.
    for b in shape::TABLE.iter().filter(|b| b.open == TokenKind::LBrace) {
        assert_eq!(braces.iter().filter(|&&k| k == b.node).count(), 1, "{}", b.node.name());
    }
}

/// The form of the first node of `kind` in `src`, and the number of its elements.
fn form_of(src: &str, kind: NodeKind) -> (Option<Form>, usize) {
    let parsed = crate::parse(FileId(0), src);
    assert!(!parsed.syntax_errors(), "{src}: {:?}", parsed.diagnostics);
    let cst = &parsed.cst;
    let mut stack = vec![cst.root()];
    while let Some(n) = stack.pop() {
        if cst.kind(n) == kind {
            return (shape::form(cst, n), shape::elements(cst, n).len());
        }
        stack.extend(cst.child_nodes(n).collect::<Vec<_>>().into_iter().rev());
    }
    panic!("{src}: no {}", kind.name())
}

#[test]
fn the_form_of_a_list_is_read_from_the_line_breaks_after_its_opening_bracket_and_between_its_elements() {
    let args = |body: &str| form_of(&format!("fn f() {{\n  {body}\n}}\n"), NodeKind::ArgList);
    // Line breaks only inside the elements: one line.
    assert_eq!(args("two(a +\n    1, b *\n    2)"), (Some(Form::OneLine), 2));
    // A comment at the end of the line of the opening bracket: still a block.
    assert_eq!(args("two( // c\n    a,\n    b,\n  )"), (Some(Form::Block), 2));
    assert_eq!(args("two(\n    a, b,\n  )"), (Some(Form::Block), 2));
    assert_eq!(args("two(a,\n      b)"), (Some(Form::Continuation), 2));
    // A comment between two elements does not change it.
    assert_eq!(args("two(a, // c\n      b)"), (Some(Form::Continuation), 2));
    // No element: one line.
    assert_eq!(args("two(\n  )"), (Some(Form::OneLine), 0));
    // The elements of a `use` list are tokens; those of a struct pattern come after its path, and its
    // `..` is none (S-500), but a line break before it makes the form.
    assert_eq!(form_of("use a.{x,\n  y}\n", NodeKind::UseNames), (Some(Form::Continuation), 2));
    let pat = |p: &str| {
        form_of(&format!("fn f(p: P) -> I32 {{\n  match p {{\n    {p} => 1,\n  }}\n}}\n"), NodeKind::StructPat)
    };
    assert_eq!(pat("P {\n      x: 1,\n      ..\n    }"), (Some(Form::Block), 1));
    assert_eq!(pat("P { x: 1,\n        .. }"), (Some(Form::Continuation), 1));
    assert_eq!(pat("P { .. }"), (Some(Form::OneLine), 0));
    // An enclosure has the form of a list of one element, with no element to which a `,` goes (S-522,
    // §3.2: `(I32)`); a container has none.
    assert_eq!(form_of("fn f() {\n  (1)\n}\n", NodeKind::ParenExpr), (Some(Form::OneLine), 0));
    assert_eq!(form_of("fn f() {\n  (1\n  )\n}\n", NodeKind::ParenExpr), (Some(Form::OneLine), 0));
    assert_eq!(form_of("type T = (\n  I32)\n", NodeKind::ParenType), (Some(Form::Block), 0));
    assert_eq!(form_of("fn f() {\n  (1)\n}\n", NodeKind::Block), (None, 0));
}
