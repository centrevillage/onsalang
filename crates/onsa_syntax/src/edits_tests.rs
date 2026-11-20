//! Tests of the edits of the candidates (`crate::edits`): which edits of a
//! candidate [`apart`] keeps apart from the tokens round them (§18.1).

use onsa_diag::{Edit, FileId, Fix, Span};

use crate::edits::{Insertions, apart};

const F: FileId = FileId(0);

/// The text of `src` after the candidate of `edits` kept apart, or `None`
/// when it has no such candidate.
fn kept_apart(src: &str, edits: Vec<Edit>) -> Option<String> {
    let tokens = crate::lex(F, src).tokens;
    let fix = apart(F, src, &tokens, Fix::new("t", edits), &Insertions::default())?;
    Some(onsa_diag::apply_text(src, &fix.edits().iter().collect::<Vec<_>>()).unwrap())
}

fn delete(start: u32, end: u32) -> Edit {
    Edit::delete(Span::new(F, start, end))
}

#[test]
fn an_edit_whose_tokens_join_only_through_another_edit_is_kept() {
    // R-413: the removal of `()` joins `export` and `pub`, not the removal
    // of the blank after `@`, which stays a removal.
    assert_eq!(kept_apart("@ export()pub", vec![delete(1, 2), delete(8, 10)]).as_deref(), Some("@export pub"));
    // An insertion that is not of `insert_apart` alike: `@` before `export`.
    let insert = Edit::insert(F, 2, "@");
    assert_eq!(kept_apart("\n\nexport()pub", vec![insert, delete(8, 10)]).as_deref(), Some("\n\n@export pub"));
}

#[test]
fn edits_that_join_of_their_own_are_each_kept_apart() {
    // Each removal of `()` joins its own tokens: both become a blank.
    assert_eq!(kept_apart("a()b()c", vec![delete(1, 3), delete(4, 6)]).as_deref(), Some("a b c"));
    // `b` joins `a` through the left edit and `c` through the right one:
    // both stay blanks.
    assert_eq!(kept_apart("a/**/b()c", vec![delete(1, 5), delete(6, 8)]).as_deref(), Some("a b c"));
    // An insertion that joins of its own has no way apart: no candidate.
    assert_eq!(kept_apart("a b()c", vec![Edit::insert(F, 1, "x"), delete(3, 5)]), None);
}

/// The span [`crate::edits::whole_line`] gives for the token that starts
/// at `at` in `src` alone (the blanks after it taken with it), or `None`.
fn line_of(src: &str, at: u32) -> Option<(u32, u32)> {
    let tokens = crate::lex(F, src).tokens;
    let k = tokens.iter().position(|t| t.span.start == at).unwrap();
    let stop = k + 1 + usize::from(tokens.get(k + 1).is_some_and(|t| t.kind == crate::token::TokenKind::Whitespace));
    crate::edits::whole_line(F, &tokens, (k, stop, tokens[k].span.end)).map(|s| (s.start, s.end))
}

#[test]
fn a_symbol_alone_on_its_line_takes_the_whole_line_at_the_end_of_the_file_too() {
    // The one judgment of the candidates that move a symbol up and down
    // (W6-04 U10c): the indentation, the symbol, the blanks after it and the
    // newline; on the last line with no newline, the blanks to the end.
    assert_eq!(line_of("const A: I32 = 1\n  +  \n", 19), Some((17, 23)));
    assert_eq!(line_of("const A: I32 = 1\n  +  ", 19), Some((17, 22)));
    assert_eq!(line_of("const A: I32 = 1\n+", 17), Some((17, 18)));
    // Code or a comment after it on its line: not the whole line.
    assert_eq!(line_of("const A: I32 = 1\n  + 2", 19), None);
    assert_eq!(line_of("const A: I32 = 1\n  + // c", 19), None);
    // The candidate that moves it up takes that line out (`2:1-2:6`).
    let tokens = crate::lex(F, "const A: I32 = 1\n  +  ").tokens;
    let at = tokens.iter().position(|t| t.span.start == 19).unwrap();
    let fix = crate::edits::move_token_up(F, "const A: I32 = 1\n  +  ", &tokens, "t", 16, at, " +");
    assert_eq!(fix.edits()[1].span, Span::new(F, 17, 22));
}

/// The candidate of [`crate::edits::move_token_up`] for the token that
/// starts at `at` in `src`, moved to `end` and written there as `written`.
fn token_moved_up(src: &str, end: u32, at: u32, written: &str) -> Fix {
    let tokens = crate::lex(F, src).tokens;
    let k = tokens.iter().position(|t| t.span.start == at).unwrap();
    crate::edits::move_token_up(F, src, &tokens, "t", end, k, written)
}

#[test]
fn a_symbol_moved_up_as_it_is_written_is_the_writers_text() {
    // S-1187: `par` and `~ i` on the next line: the `~` goes to the keyword,
    // the writer's text moved (`Fix::moves`), so the E0812 that takes it out
    // after it undoes no step of a walk (S-475).
    let fix = token_moved_up("two(par\n  ~ i", 7, 10, "~");
    assert_eq!((fix.edits()[0].replace.as_str(), fix.edits()[0].writers()), ("~", &[(0, 1)][..]));
    assert!(fix.moves());
    // After a blank, the symbol alone is the writer's (` +`).
    let fix = token_moved_up("const A: I32 = 1\n  + 2", 16, 19, " +");
    assert_eq!(fix.edits()[0].writers(), &[(1, 2)]);
    assert!(fix.moves());
    // A symbol written as another (`..` as ` ..<`, S-257) is the compiler's.
    let fix = token_moved_up("for i in 0\n  .. 4", 10, 13, " ..<");
    assert_eq!(fix.edits()[0].writers(), &[]);
    assert!(!fix.moves());
}

#[test]
fn code_moved_up_before_a_comment_is_the_writers_text() {
    // `move_up` with a comment on the way moves the code of the next line
    // (` b` inserted, `b` taken out): the writer's text, as a symbol moved up.
    let src = "a // c\nb";
    let tokens = crate::lex(F, src).tokens;
    let next = *tokens.iter().find(|t| t.span.start == 7).unwrap();
    let fix = crate::edits::move_up(F, src, &tokens, "t", 1, next, " ").unwrap();
    assert_eq!((fix.edits()[0].replace.as_str(), fix.edits()[0].writers()), (" b", &[(1, 2)][..]));
    assert!(fix.moves());
    // With nothing but blanks between, the blanks become the separator: nothing moves.
    let src = "a\nb";
    let tokens = crate::lex(F, src).tokens;
    let next = *tokens.iter().find(|t| t.span.start == 2).unwrap();
    let fix = crate::edits::move_up(F, src, &tokens, "t", 1, next, " ").unwrap();
    assert!(!fix.moves());
}
