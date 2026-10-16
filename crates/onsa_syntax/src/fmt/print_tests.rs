//! Self-tests of the printer (`fmt/print.rs`, W3-11 unit U3a). The answers
//! are the canonical files of the self-test of the tables
//! (`table_tests::canonical_by_case` and `table_tests::EXTRA`).
//!
//! - (i) The printer writes every canonical file as it is.
//! - (ii) In every file of the repository that the syntax stage reads without
//!   a diagnostic, the output reads without one, with the code tokens (kind
//!   and text) that the plan (`fmt/plan.rs`) keeps, respells and adds, and the
//!   same comments (their text without blanks at the end), in the same order.
//!   Without the `,` (which the plan moves, drops and adds) and the tokens
//!   the rewrites of §3.3 drop (`fmt/rewrites.rs`), the kinds of the code
//!   tokens are those of the file.
//! - (iii) Printing the output again gives the output.
//! - (iv) The printer gives every canonical file back from copies of it
//!   whose layout is changed with a fixed seed ([`jitter`]): the indentation,
//!   the spaces between tokens and before comments, blanks at the ends of
//!   lines, more blank lines where there are some and at the heads and tails
//!   of the file and of the brackets, and CR LF. The line breaks stay where
//!   they are, but a `,` at the end of a line may move to a line of its own
//!   (the plan moves it back, and the line breaks round it make no blank line).

use std::time::{Duration, Instant};

use onsa_diag::FileId;

use super::plan::Plan;
use super::print::print;
use super::rewrites;
use super::table_tests::{EXTRA, canonical_by_case};
use crate::cst::{Cst, TokenIdx};
use crate::lexer::BLANKS;
use crate::token::TokenKind;

/// The time the test may take in a debug build (it took about 3 s on 2026-10-14).
const BUDGET: Duration = Duration::from_secs(60);

/// The copies of each canonical file with a changed layout ((iv)).
const JITTERED_COPIES: usize = 3;

/// The code tokens of `cst` (kind and text) and its comments (text), in
/// order; with `plan`, those the printer writes by the plan.
fn tokens(cst: &Cst, text: &str, plan: Option<&Plan>) -> (Vec<(TokenKind, String)>, Vec<String>) {
    let (mut code, mut comments) = (Vec::new(), Vec::new());
    for (i, t) in cst.tokens().iter().enumerate() {
        let s = &text[t.span.start as usize..t.span.end as usize];
        let at = TokenIdx(i as u32);
        if t.kind.is_comment() {
            comments.push(s.trim_end_matches(BLANKS).to_string());
        } else if !t.kind.is_trivia() && plan.is_none_or(|p| p.kept(at)) {
            code.push((t.kind, plan.and_then(|p| p.text(at)).unwrap_or(s).to_string()));
            if plan.is_some_and(|p| p.comma_after(at)) {
                code.push((TokenKind::Comma, ",".to_string()));
            }
        }
    }
    (code, comments)
}

/// The kinds of the code tokens of `cst` without `,` and, with `dropped` (by the index of the token), without
/// the tokens the rewrites of §3.3 drop.
fn kinds(cst: &Cst, dropped: Option<&[bool]>) -> Vec<TokenKind> {
    let tokens = cst.tokens().iter().enumerate();
    let kept = tokens.filter(|&(i, t)| !t.kind.is_trivia() && dropped.is_none_or(|d| !d[i]));
    kept.map(|(_, t)| t.kind).filter(|&k| k != TokenKind::Comma).collect()
}

/// A generator with a fixed seed (xorshift64).
struct Rng(u64);

impl Rng {
    /// A number below `n`.
    fn below(&mut self, n: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % n
    }

    fn spaces(&mut self, most: u64) -> String {
        " ".repeat(self.below(most + 1) as usize)
    }

    /// An indentation: none, spaces, or a tab.
    fn indentation(&mut self) -> String {
        if self.below(5) == 0 { "\t".to_string() } else { self.spaces(12) }
    }
}

/// `text` (with the tree `cst`) with the layout changed where the printer
/// decides it alone (the module documentation, (iv)).
fn jitter(cst: &Cst, text: &str, rng: &mut Rng) -> String {
    use TokenKind as T;
    let toks = cst.tokens();
    let kind = |i: usize| toks.get(i).map(|t| t.kind);
    let not_blank = |i: usize, step: isize| {
        let mut j = i as isize + step;
        while j >= 0 && kind(j as usize) == Some(T::Whitespace) {
            j += step;
        }
        if j < 0 { None } else { kind(j as usize) }
    };
    let mut out = "\n".repeat(rng.below(3) as usize);
    if kind(0) != Some(T::Whitespace) {
        out.push_str(&rng.indentation());
    }
    for (i, t) in toks.iter().enumerate() {
        match t.kind {
            T::Whitespace if i == 0 || kind(i - 1) == Some(T::Newline) => out.push_str(&rng.indentation()),
            T::Whitespace if kind(i + 1).is_some_and(|k| k.is_comment()) => {
                out.push_str(&" ".repeat(1 + rng.below(6) as usize))
            }
            T::Whitespace if rng.below(5) == 0 => out.push('\t'),
            T::Whitespace => out.push_str(&" ".repeat(1 + rng.below(3) as usize)),
            T::Newline => {
                out.push_str(&rng.spaces(1));
                out.push_str(if rng.below(3) == 0 { "\r\n" } else { "\n" });
                let opened = not_blank(i, -1).is_some_and(|k| matches!(k, T::LParen | T::LBracket | T::LBrace));
                let closes =
                    not_blank(i, 1).is_some_and(|k| matches!(k, T::Newline | T::RParen | T::RBracket | T::RBrace));
                if opened || closes {
                    out.push_str(&"\n".repeat(rng.below(3) as usize));
                }
                if kind(i + 1) != Some(T::Whitespace) {
                    out.push_str(&rng.indentation());
                }
            }
            T::Eof => out.push_str(&"\n".repeat(rng.below(3) as usize)),
            T::Comma if not_blank(i, 1) == Some(T::Newline) && rng.below(2) == 0 => {
                out.push('\n');
                out.push_str(&rng.indentation());
                out.push(',');
            }
            k => {
                out.push_str(&text[t.span.start as usize..t.span.end as usize]);
                let next = kind(i + 1).filter(|n| n.is_code());
                let inside = matches!(k, T::LParen | T::LBracket) && !matches!(next, Some(T::RParen | T::RBracket));
                let before =
                    matches!(next, Some(T::RParen | T::RBracket | T::Comma)) && !matches!(k, T::LParen | T::LBracket);
                if next.is_some() && (inside || before) && rng.below(4) == 0 {
                    out.push(' ');
                }
            }
        }
    }
    out
}

/// The first line where `a` and `b` differ, for a message.
fn first_difference(a: &str, b: &str) -> String {
    let (mut la, mut lb) = (a.lines(), b.lines());
    for n in 1.. {
        match (la.next(), lb.next()) {
            (None, None) => return "the final line breaks differ".into(),
            (x, y) if x != y => return format!("line {n}: {x:?} became {y:?}"),
            _ => {}
        }
    }
    unreachable!()
}

#[derive(Default)]
struct Tally {
    canonical: usize,
    jittered: usize,
    /// The `,` the copies have on lines of their own.
    lone_commas: usize,
    read: usize,
    skipped: usize,
    errors: Vec<String>,
}

#[test]
fn the_printer_writes_the_canonical_files_as_they_are_and_keeps_the_tokens_of_every_file() {
    let started = Instant::now();
    let tally = onsa_diag::stack::run(|| {
        let root = crate::cst_tests::root_dir();
        let mut files = crate::cst_tests::repo_files();
        files.extend(EXTRA.iter().map(|(name, text)| (name.to_string(), text.to_string())));
        let mut tally = Tally::default();
        for (name, text) in &files {
            let parsed = crate::parse(FileId(0), text);
            if parsed.syntax_errors() {
                tally.skipped += 1;
                continue;
            }
            tally.read += 1;
            let out = print(&parsed.cst, text);
            if canonical_by_case(name, text, &files, &root) {
                tally.canonical += 1;
                if out != *text {
                    tally.errors.push(format!("(i) {name}: {}", first_difference(text, &out)));
                }
                let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ (tally.canonical as u64).wrapping_mul(0x2545_F491_4F6C_DD1D));
                for copy in 0..JITTERED_COPIES {
                    let jittered = jitter(&parsed.cst, text, &mut rng);
                    tally.jittered += 1;
                    tally.lone_commas += jittered.lines().filter(|l| l.trim_start().starts_with(',')).count();
                    let parsed = crate::parse(FileId(0), &jittered);
                    if parsed.syntax_errors() {
                        tally
                            .errors
                            .push(format!("(iv) {name}, copy {copy}: a syntax error: {:?}", parsed.diagnostics));
                    } else if print(&parsed.cst, &jittered) != *text {
                        let back = print(&parsed.cst, &jittered);
                        tally.errors.push(format!("(iv) {name}, copy {copy}: {}", first_difference(text, &back)));
                    }
                }
            }
            let again = crate::parse(FileId(0), &out);
            if again.syntax_errors() {
                tally.errors.push(format!("(ii) {name}: the output has a syntax error: {:?}", again.diagnostics));
                continue;
            }
            let (planned, comments) = tokens(&parsed.cst, text, Some(&Plan::new(&parsed.cst, text)));
            let (written, written_comments) = tokens(&again.cst, &out, None);
            if planned != written || comments != written_comments {
                tally.errors.push(format!("(ii) {name}: the tokens or the comments are not those of the plan"));
            }
            let dropped = rewrites::choose(&parsed.cst, &rewrites::all_nodes(&parsed.cst)).dropped;
            if kinds(&parsed.cst, Some(&dropped)) != kinds(&again.cst, None) {
                tally.errors.push(format!(
                    "(ii) {name}: a token other than `,` and those the rewrites of §3.3 drop was dropped or added"
                ));
            }
            let twice = print(&again.cst, &out);
            if twice != out {
                tally.errors.push(format!("(iii) {name}: {}", first_difference(&out, &twice)));
            }
        }
        tally
    });
    let elapsed = started.elapsed();
    eprintln!(
        "{} canonical files ({} copies with a changed layout, {} `,` on lines of their own) of {} read ({} with a \
         syntax error not read), {elapsed:?}",
        tally.canonical, tally.jittered, tally.lone_commas, tally.read, tally.skipped
    );
    assert!(tally.canonical > 250, "only {} canonical files", tally.canonical);
    assert!(tally.read > 800, "only {} files read", tally.read);
    assert!(tally.lone_commas > 1000, "only {} `,` moved to lines of their own", tally.lone_commas);
    assert!(tally.errors.is_empty(), "{} failures:\n{}", tally.errors.len(), tally.errors.join("\n"));
    assert!(elapsed < BUDGET, "the self-test took {elapsed:?}");
}

/// The output of the printer for `src` (which must read without a syntax error).
fn printed(src: &str) -> String {
    let parsed = crate::parse(FileId(0), src);
    assert!(!parsed.syntax_errors(), "{src}: {:?}", parsed.diagnostics);
    print(&parsed.cst, src)
}

/// The rows of the table of S-498 in the 28th set of the gaps of W3 (the column of the
/// decision (a1) and (b2)): the forms written with any indentation, and as the printer writes them.
#[test]
fn the_indentation_is_one_level_deeper_than_the_line_where_the_owner_starts() {
    let body = |lines: &[&str]| format!("fn f() {{\n{}\n}}\n", lines.join("\n"));
    let rows: &[(&[&str], &[&str])] = &[
        (&["let x = a +", "b +", "      c"], &["  let x = a +", "    b +", "    c"]),
        (&["let x =", "a +", "b"], &["  let x =", "    a +", "    b"]),
        (&["let x = a +", "b *", "c"], &["  let x = a +", "    b *", "    c"]),
        (&["let y =", "a", ".max(b)"], &["  let y =", "    a", "    .max(b)"]),
        (&["let x = foo() +", "bar(", "1,", ")"], &["  let x = foo() +", "    bar(", "      1,", "    )"]),
        (&["a", ".max(", "b,", ")"], &["  a", "    .max(", "      b,", "    )"]),
        // A block-like operand is in parentheses (E0013, S-537).
        (
            &["let x = foo() +", "(if t {", "1", "} else {", "2", "})"],
            &["  let x = foo() +", "    (if t {", "      1", "    } else {", "      2", "    })"],
        ),
        (
            &["for i in 0 ..<", "bar(", "1,", ") {", "g(i)", "}"],
            &["  for i in 0 ..<", "    bar(", "      1,", "    ) {", "    g(i)", "  }"],
        ),
        (&["if a &&", "b {", "g()", "}"], &["  if a &&", "    b {", "    g()", "  }"]),
        (&["two(", "a +", "b +", "c,", ")"], &["  two(", "    a +", "      b +", "      c,", "  )"]),
        (&["two(a +", "1, b *", "2)"], &["  two(a +", "    1, b *", "      2)"]),
        (&["two(a,", "b +", "c)"], &["  two(a,", "      b +", "        c)"]),
    ];
    for (input, output) in rows {
        assert_eq!(printed(&body(input)), body(output), "{input:?}");
    }
    assert_eq!(printed("type Op =\nfn(I32) ->\n    I32\n"), "type Op =\n  fn(I32) ->\n  I32\n");
}

/// The blank lines (S-122, S-499, S-502), the line after an attribute and the comments (§3.4).
#[test]
fn blank_lines_separate_parts_and_comments_stay_on_their_lines() {
    let src = "\n\n// head\n\n\n@fp(relaxed)\n  // between\nfn f(x: I32) -> I32 { // after the brace\n\n  // first\n\n\n  \
               let a = 1 // a\n\n\n  let bb = two(\n\n    a,\n\n\n    x, // x\n\n  )\n  match x {\n    0 => 1,\n\n    _ => \
               2,\n  }\n\n  // last\n\n}\n\n\n";
    let want = "// head\n\n@fp(relaxed)\n// between\nfn f(x: I32) -> I32 { // after the brace\n  // first\n\n  let a = 1 // a\n\n  \
                let bb = two(\n    a,\n\n    x, // x\n  )\n  match x {\n    0 => 1,\n\n    _ => 2,\n  }\n\n  // last\n}\n";
    assert_eq!(printed(src), want);
}

/// The base line of an effect row on a continued head is the line of its `uses` (S-518); the line
/// after a line that starts with an attribute has its indentation, also in the continuation form and
/// after an attribute over more than one line (S-519); a `let` whose `=` is not on its first line has
/// no column of `=`.
#[test]
fn effect_rows_attributes_and_lets_take_the_lines_where_they_start() {
    let rows: &[(&str, &str)] = &[
        (
            "pub fn f(n: U32) -> U32\nuses {\nAlloc,\n} {\nn\n}\n",
            "pub fn f(n: U32) -> U32\n  uses {\n    Alloc,\n  } {\n  n\n}\n",
        ),
        (
            "pub flow f(x: F32 at sample,\n@param(min: 0.0) @param(max: 1.0)\nlevel: F32 at block) -> F32 at sample {\n  \
             x * level\n}\n",
            "pub flow f(x: F32 at sample,\n           @param(min: 0.0) @param(max: 1.0)\n           level: F32 at block) \
             -> F32 at sample {\n  x * level\n}\n",
        ),
        (
            "@fp(\nrelaxed,\n)\npub fn g(x: F32) -> F32 {\n  x\n}\n",
            "@fp(\n  relaxed,\n)\npub fn g(x: F32) -> F32 {\n  x\n}\n",
        ),
        (
            "fn h(w: Wrap) -> I32 {\n  let a = 1\n  let Wrap {\n    inner: q,\n  } = w\n  let bb = q\n  a + bb\n}\n",
            "fn h(w: Wrap) -> I32 {\n  let a = 1\n  let Wrap {\n    inner: q,\n  } = w\n  let bb = q\n  a + bb\n}\n",
        ),
    ];
    for (input, output) in rows {
        assert_eq!(printed(input), *output, "{input:?}");
    }
}

/// The base lines that the canonical files do not show: the effect row of a closure on a continued
/// line (S-518; the body is one level deeper than the line where the closure starts), a `use` list on
/// a continued line (its `{` is the base, S-518), and the content of an enclosure as the owner of its
/// continuation lines (S-522): a group, an enclosure opened on a continuation line, an index, `[e; N]`
/// and an array type.
#[test]
fn closures_use_lists_and_enclosures_take_their_base_lines() {
    let rows: &[(&str, &str)] = &[
        (
            "fn f() {\nlet g = fn(x: I32) -> I32\nuses {Alloc} {\nx\n}\ng\n}\n",
            "fn f() {\n  let g = fn(x: I32) -> I32\n    uses {Alloc} {\n    x\n  }\n  g\n}\n",
        ),
        (
            "fn f() {\nh(1,\nfn(x: I32) -> I32\nuses {Alloc} {\nx\n})\n}\n",
            "fn f() {\n  h(1,\n    fn(x: I32) -> I32\n      uses {Alloc} {\n      x\n    })\n}\n",
        ),
        ("use std\n.math\n.{\nsqrt,\ncos,\n}\n", "use std\n  .math\n  .{\n    sqrt,\n    cos,\n  }\n"),
        (
            "fn f(a: I32, b: I32, xs: [I32; 4]) -> I32 {\nlet x = a +\n(\nb +\na\n)\nlet y = (\na +\nb\n)\n\
             let z = xs[\na +\nb\n]\nlet w = [\na +\nb; 4\n]\nx\n}\n",
            "fn f(a: I32, b: I32, xs: [I32; 4]) -> I32 {\n  let x = a +\n    (\n      b +\n        a\n    )\n  \
             let y = (\n    a +\n      b\n  )\n  let z = xs[\n    a +\n      b\n  ]\n  let w = [\n    a +\n      b; 4\n  \
             ]\n  x\n}\n",
        ),
        // The line break after the `;` is inside the element and goes (§3.2, S-374, S-497).
        ("type A = [\nI32;\n4\n]\n", "type A = [\n  I32; 4\n]\n"),
    ];
    for (input, output) in rows {
        assert_eq!(printed(input), *output, "{input:?}");
    }
}

/// The `=` of a `let` is in a column only when the `let` starts its line and the line ends after it
/// (S-122). The line breaks the plan adds after the `{` and before the `}` of a block over more than
/// one line (§3.2) put the `let` there alone on its line; a `let` in a block on one line is in no column.
#[test]
fn the_column_of_the_equals_holds_only_the_lets_alone_on_their_lines() {
    let aligned = "fn f() {\n  let a   = 1\n  let bbb = 2\n}\n";
    for src in ["fn f() { let a = 1\n  let bbb = 2\n}\n", "fn f() {\n  let a = 1\n  let bbb = 2 }\n", aligned] {
        assert_eq!(printed(src), aligned, "{src:?}");
    }
    let one_line = "fn f(c: Bool) {\n  let a = 1\n  if c { let bbb = 2 }\n}\n";
    assert_eq!(printed(one_line), one_line);
}

/// A `,` on a line of its own moves to the element before it (§3.2), and the line breaks before and
/// after it make no blank line: only the blank lines of the writer are kept (S-499), in every form and
/// before a comment (W3-11/b U3b, finding 1).
#[test]
fn a_comma_on_a_line_of_its_own_leaves_no_blank_line() {
    let body = |lines: &[&str]| format!("fn f() {{\n{}\n}}\n", lines.join("\n"));
    let rows: &[(&[&str], &[&str])] = &[
        (&["g(", "a", ",", "b", ")"], &["  g(", "    a,", "    b,", "  )"]),
        (&["g(a", ",", "b)"], &["  g(a,", "    b)"]),
        (&["g(a", ",", "// c", "b)"], &["  g(a,", "    // c", "    b)"]),
        (&["g(a // c", ",", "b)"], &["  g(a, // c", "    b)"]),
        (&["g(a", ", // c", "b)"], &["  g(a,", "    // c", "    b)"]),
        (&["g(", "a,", "b", ",", "// c", ")"], &["  g(", "    a,", "    b,", "    // c", "  )"]),
        (&["g(a, b", ",", "// d", ")"], &["  g(a, b", "    // d", "  )"]),
        // The blank lines of the writer, on either side of the `,`, stay (one).
        (&["g(a", "", ",", "b)"], &["  g(a,", "", "    b)"]),
        (&["g(a", ",", "", "b)"], &["  g(a,", "", "    b)"]),
        (&["g(a", "", ",", "", "b)"], &["  g(a,", "", "    b)"]),
    ];
    for (input, output) in rows {
        assert_eq!(printed(&body(input)), body(output), "{input:?}");
    }
}

/// Each pair of the nested brackets of a negative literal pattern has the form of an enclosure (S-522):
/// on one line its closing bracket follows its content (S-507), in the block form it is on its own
/// line at the base line of the pair (W3-11/b U3b, finding 2).
#[test]
fn the_nested_pairs_of_a_negative_literal_pattern_take_their_forms() {
    let arms =
        |lines: &[&str]| format!("fn f(x: I32) -> I32 {{\n  match x {{\n{}\n    _ => 0,\n  }}\n}}\n", lines.join("\n"));
    let rows: &[(&[&str], &[&str])] = &[
        (&["-(", "(2", ")) => 1,"], &["    -(", "      (2)", "    ) => 1,"]),
        (&["-((", "4)) => 3,"], &["    -((", "      4", "    )) => 3,"]),
        (&["-((5)", ") => 4,"], &["    -((5)) => 4,"]),
        (&["-(", "(", "6", ")", ") => 5,"], &["    -(", "      (", "        6", "      )", "    ) => 5,"]),
        (&["-(((", "7) // c", ")) => 6,"], &["    -(((", "      7", "    ) // c", "    )) => 6,"]),
    ];
    for (input, output) in rows {
        assert_eq!(printed(&arms(input)), arms(output), "{input:?}");
    }
}

/// The code tokens before which the plan removes a line break of the writer (a `JOIN` on a token with a
/// line break before it).
fn joined(src: &str) -> Vec<String> {
    let parsed = crate::parse(FileId(0), src);
    assert!(!parsed.syntax_errors(), "{src}: {:?}", parsed.diagnostics);
    let (cst, plan) = (&parsed.cst, Plan::new(&parsed.cst, src));
    let mut out = Vec::new();
    let mut breaks = false;
    for (i, tok) in cst.tokens().iter().enumerate() {
        let t = TokenIdx(i as u32);
        breaks |= tok.kind == TokenKind::Newline;
        if tok.kind.is_trivia() || !plan.kept(t) {
            continue;
        }
        if breaks && plan.joins(t) {
            out.push(src[tok.span.start as usize..tok.span.end as usize].to_string());
        }
        breaks = false;
    }
    out
}

/// The line breaks inside an element of a list or an enclosure go, but those at a place of a
/// continuation (§2.5: after a binary operator, `->`, the `|` of a pattern, before `.` and `uses`,
/// after an attribute; a range is not written in brackets), after the opening bracket, between the elements, in a block and
/// between statements (§3.2, S-497, S-505). The line breaks between the attribute of a `let` and the
/// `let` go too (§3.2). The `JOIN` goes on the code token after the line break (W3-11 U3c).
#[test]
fn the_plan_removes_the_line_breaks_inside_an_element_but_at_a_place_of_a_continuation() {
    let body = |lines: &[&str]| format!("fn f() {{\n{}\n}}\n", lines.join("\n"));
    let flow = |lines: &[&str]| format!("flow g(x: F32 at sample) -> F32 at sample {{\n{}\n}}\n", lines.join("\n"));
    let rows: &[(String, &[&str])] = &[
        // Removed: round `as`, after a keyword, after `=>` and `:`, before `:` (S-505), after `;`.
        (body(&["g(x", "as", "F64, b)"]), &["as", "F64"]),
        (body(&["two(if", "a { 1 } else { 2 }, 3)"]), &["a"]),
        (body(&["take(move", "b)"]), &["b"]),
        (body(&["match a {", "0 =>", "1,", "_ => 2,", "}"]), &["1"]),
        (body(&["let s = S { f", ": a }", "s"]), &[":"]),
        (body(&["g([b;", "4])"]), &["4"]),
        ("fn h(x\n: I32) -> I32 {\n  x\n}\n".to_string(), &[":"]),
        // Removed with a comment between: the printer keeps it (S-497 (β)), the plan marks it alike.
        (body(&["take(move // c", "b)"]), &["b"]),
        // The closing bracket of a list on one line (S-507, U3b), with a `,` the plan drops between.
        (body(&["g(x", "as F64", ",", ")"]), &["as", ")"]),
        // Kept: the places of a continuation.
        (body(&["two(a +", "b, c)"]), &[]),
        (body(&["two(1 -", "b, c)"]), &[]),
        (body(&["two(a ^", "b, c)"]), &[]),
        (body(&["g(a", ".abs())"]), &[]),
        (body(&["match a {", "0 |", "1 => 1,", "_ => 2,", "}"]), &[]),
        ("fn k(f: fn(I32) ->\nI32) -> I32 {\n  1\n}\n".to_string(), &[]),
        (body(&["h(1, fn(x: I32) -> I32", "uses {Alloc} {", "x", "})"]), &[]),
        // Kept: after the opening bracket, between the elements, in a block, between statements.
        (body(&["two(", "a,", "b", ")"]), &[]),
        (body(&["two(a,", "b)"]), &[]),
        (body(&["two(a", ", b)"]), &[]),
        (body(&["two(if a {", "1", "} else {", "2", "}, 3)"]), &[]),
        (body(&["let a = 1", "a"]), &[]),
        // After an attribute: kept but after that of a `let`.
        (
            "flow g(@param(min: 0.0, max: 1.0, default: 0.5)\nlevel: F32 at block, x: F32 at sample) -> F32 at \
             sample {\n  x\n}\n"
                .to_string(),
            &[],
        ),
        ("@repr(c)\nstruct P {\n  x: F32,\n}\n".to_string(), &[]),
        (flow(&["@mem(bulk)", "let d = delay~(x, 4800)", "d"]), &["let"]),
    ];
    for (src, want) in rows {
        assert_eq!(joined(src), *want, "{src}");
    }
}

/// Where a removed line break and a token the plan drops meet, the line breaks round the dropped
/// token are one (`Printer::gap`, U3b) and the removed one leaves no blank line; a line break of the
/// writer between two elements stays with its blank line (S-499).
#[test]
fn a_removed_line_break_and_a_dropped_comma_leave_no_line_and_no_blank_line() {
    let body = |lines: &[&str]| format!("fn f() {{\n{}\n}}\n", lines.join("\n"));
    let rows: &[(&[&str], &[&str])] = &[
        (&["g(x", "as F64", ",", "b)"], &["  g(x as F64,", "    b)"]),
        (&["g(x", "", "as F64", ",", "", "b)"], &["  g(x as F64,", "", "    b)"]),
        (&["g(x", "as F64", ",", "", ")"], &["  g(x as F64)"]),
        (&["g(", "x", "as F64", ",", "b", ")"], &["  g(", "    x as F64,", "    b,", "  )"]),
        (&["match a {", "0 =>", "", "1", ",", "_ => 2,", "}"], &["  match a {", "    0 => 1,", "    _ => 2,", "  }"]),
    ];
    for (input, output) in rows {
        assert_eq!(printed(&body(input)), body(output), "{input:?}");
    }
}
