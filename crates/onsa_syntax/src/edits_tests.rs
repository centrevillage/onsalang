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
