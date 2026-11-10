//! The repeats of a list read as a set (spec §4.5): the bounds of a type
//! parameter, the traits of a derive list, the attributes of one place and
//! an effect row. Each reader reports in the code of its own section; the
//! judgment of the first repeat and the form of its report are here alone
//! (D-15): at the first element that repeats one before it, that one as a
//! note, and no candidate.

use std::collections::HashMap;
use std::hash::Hash;

use crate::{Code, Diagnostic, Span, Stage};

/// The first element of `keys` equal to one before it, read from the front
/// in one pass: the index of that earlier one and of the repeat.
pub fn first_repeat<K: Eq + Hash>(keys: impl IntoIterator<Item = K>) -> Option<(usize, usize)> {
    let mut seen = HashMap::new();
    for (k, key) in keys.into_iter().enumerate() {
        if let Some(&before) = seen.get(&key) {
            return Some((before, k));
        }
        seen.insert(key, k);
    }
    None
}

/// The report of the repeat at `at` of the element at `before`, which the
/// caller names in words (`what`, "the attribute `@fp`"), with no candidate.
pub fn repeated(stage: Stage, code: Code, at: Span, before: Span, what: &str) -> Diagnostic {
    Diagnostic::new(stage, code, at, format!("{what} is written twice (§4.5)"))
        .with_note(before, format!("{what} is first written here"))
}

#[cfg(test)]
mod tests {
    use super::first_repeat;

    #[test]
    fn the_first_repeat_is_the_second_of_its_key_read_from_the_front() {
        assert_eq!(first_repeat(["a", "b", "c"]), None);
        assert_eq!(first_repeat(["a", "b", "a", "a"]), Some((0, 2)));
        assert_eq!(first_repeat(["a", "b", "b", "a"]), Some((1, 2)));
        assert_eq!(first_repeat(Vec::<u8>::new()), None);
    }
}
