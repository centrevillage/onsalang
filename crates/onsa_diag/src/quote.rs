//! The quoted line of the text of a diagnostic ([`crate::to_text`]): the
//! source line under the heading and the line of `^` under it (R-345,
//! R-346). The JSON is not shaped here. `spec/tools.md` §4 does not promise
//! the form of these lines.
//!
//! A long line shows only [`WIDTH`] characters around the range, with
//! [`CUT`] at an end that is cut, so the text grows with the number of
//! diagnostics and not with their product with the line's length. A character
//! that would act on the terminal is shown as one visible character, so that
//! the columns of the `^` (counted in characters, §18.1) still point at the
//! range.

/// The most characters of a source line one quoted line shows.
const WIDTH: usize = 120;
/// The mark at an end of a quoted line that is cut.
const CUT: &str = "...";

/// `c` as one character that prints as itself: a C0 control character (the
/// tab and the line end too) and DEL as its picture (U+2400..U+2421, ESC as
/// `␛`), any other control character (C1) and a character that overrides the
/// direction of the text as U+FFFD. One character for one keeps the columns.
pub(crate) fn visible_char(c: char) -> char {
    match c {
        '\0'..='\x1f' => char::from_u32(0x2400 + c as u32).expect("U+2400..U+241F are characters"),
        '\x7f' => '\u{2421}',
        '\u{80}'..='\u{9f}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}' => '\u{fffd}',
        _ => c,
    }
}

/// `s` with every character [`visible_char`] (the strings of a fix candidate).
pub(crate) fn visible(s: &str) -> String {
    s.chars().map(visible_char).collect()
}

/// The quoted `line` and its line of `^` for a range that starts at the
/// 0-based character `start` of the line, the byte `at` of it, and covers
/// `len` characters (`start` may be the end of the line; at least one `^` is
/// drawn).
///
/// A line of more than [`WIDTH`] characters shows the [`WIDTH`] around the
/// range: the range in the middle, or from its start when it is longer than
/// [`WIDTH`], moved inward at the ends of the line. The `^` stop at a cut end.
/// Only about [`WIDTH`] characters are walked from `at`, so a long line with
/// many ranges costs the ranges and not their product with the line.
pub(crate) fn line(line: &str, at: usize, start: usize, len: usize) -> (String, String) {
    // A range after the end of `line` starts after its trimmed `\r` (a byte each).
    let over = at.saturating_sub(line.len());
    let (at, before) = (at - over, start.saturating_sub(over));
    // The characters from `at` to the end, counted up to one more than `WIDTH`.
    let right = line[at..].chars().take(WIDTH + 1).count();
    let (from, text) = if before + right <= WIDTH {
        (0, line)
    } else {
        let left = ((WIDTH - len.min(WIDTH)) / 2).max(WIDTH.saturating_sub(right)).min(before);
        let back = line[..at].char_indices().rev().take(left).last().map_or(at, |(i, _)| i);
        (before - left, &line[back..])
    };
    let lead = if from > 0 { CUT } else { "" };
    let cut = right > WIDTH - (before - from);
    let mut shown = String::from(lead);
    shown.extend(text.chars().take(WIDTH).map(visible_char));
    if cut {
        shown.push_str(CUT);
    }
    let end = if cut { (start + len).min(from + WIDTH) } else { start + len };
    let carets = " ".repeat(start - from + lead.len()) + &"^".repeat(end.saturating_sub(start).max(1));
    (shown, carets)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Code, Diagnostic, Fix, SourceMap, Span, Stage};

    /// The characters of `text` above the `^` of `carets`.
    fn pointed(text: &str, carets: &str) -> String {
        let at: Vec<usize> = carets.char_indices().filter(|(_, c)| *c == '^').map(|(i, _)| i).collect();
        text.chars().enumerate().filter(|(i, _)| at.contains(i)).map(|(_, c)| c).collect()
    }

    /// A line of `n` characters `0123456789012...` with `word` at `at`.
    fn long(n: usize, at: usize, word: &str) -> String {
        let mut s: String = (0..n).map(|i| char::from(b'0' + (i % 10) as u8)).collect();
        s.replace_range(at..at + word.len(), word);
        s
    }

    #[test]
    fn a_short_line_is_shown_whole() {
        let (text, carets) = line("let x = 1", 4, 4, 1);
        assert_eq!((text.as_str(), carets.as_str()), ("let x = 1", "    ^"));
        // A range at the end of the line (an empty one too) still has one `^`.
        assert_eq!(line("ab", 2, 2, 0).1, "  ^");
        // The `\r` of a CRLF line is not in `line`; a range over it or after it keeps its columns.
        assert_eq!(line("ab", 0, 0, 3).1, "^^^");
        assert_eq!(line("ab", 3, 3, 1).1, "   ^");
    }

    #[test]
    fn a_long_line_is_cut_around_the_range_at_its_head_middle_and_end() {
        let n = 1000;
        for (at, head, tail) in [(0, false, true), (500, true, true), (n - 5, true, false)] {
            let src = long(n, at, "WORD!");
            let (text, carets) = line(&src, at, at, 5);
            assert_eq!(text.starts_with(CUT), head, "{at}: {text}");
            assert_eq!(text.ends_with(CUT), tail, "{at}: {text}");
            let cut = usize::from(head) + usize::from(tail);
            assert_eq!(text.chars().count(), WIDTH + cut * CUT.len(), "{at}");
            assert_eq!(pointed(&text, &carets), "WORD!", "{at}: {text}\n{carets}");
        }
        // In the middle the range is in the middle of what is shown.
        let (text, carets) = line(&long(n, 500, "WORD!"), 500, 500, 5);
        let before = carets.find('^').unwrap() - CUT.len();
        let after = text.chars().count() - CUT.len() - (before + CUT.len() + 5);
        assert!(before.abs_diff(after) <= 1, "{before} {after}");
        // The end of a long line is a place too.
        let (text, carets) = line(&long(n, 0, "x"), n, n, 0);
        assert_eq!(carets.chars().count(), text.chars().count() + 1, "{text}\n{carets}");
    }

    #[test]
    fn a_range_longer_than_what_is_shown_starts_it_and_its_carets_stop_at_the_cut() {
        let src = long(1000, 300, "S");
        let (text, carets) = line(&src, 300, 300, 400);
        assert!(text.starts_with("...S") && text.ends_with(CUT), "{text}");
        assert_eq!(carets, " ".repeat(CUT.len()) + &"^".repeat(WIDTH));
    }

    #[test]
    fn two_ranges_on_one_long_line_each_quote_their_own_part() {
        let mut sources = SourceMap::default();
        let src = long(2000, 1500, "BBB");
        let src = format!("{}AAA{}", &src[..100], &src[103..]);
        let f = sources.add("a.onsa", format!("{src}\n"));
        let d = |s: u32, m: &str| Diagnostic::new(Stage::Syntax, Code::E0001, Span::new(f, s, s + 3), m);
        let text = crate::to_text(&sources, &[d(1500, "b"), d(100, "a")]);
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines.len(), 6, "{text}");
        assert_eq!(pointed(lines[1], lines[2]), "AAA", "{text}");
        assert_eq!(pointed(lines[4], lines[5]), "BBB", "{text}");
        assert!(text.len() < 2 * 3 * (WIDTH + 40), "{}", text.len());
    }

    #[test]
    fn a_control_character_is_one_visible_character_and_the_carets_stay() {
        let src = "a\x1b[31m\t\x7f\u{9b}\u{202e}\u{2066}\r\0 xy";
        let (text, carets) = line(src, src.len() - 2, src.chars().count() - 2, 2);
        assert_eq!(text, "a␛[31m␉␡\u{fffd}\u{fffd}\u{fffd}␍␀ xy");
        assert_eq!(pointed(&text, &carets), "xy");
        assert!(!text.chars().any(char::is_control), "{text:?}");
        assert_eq!(visible_char('\n'), '␊');
        assert_eq!(visible_char('\x1f'), '␟');
        assert_eq!((visible_char('é'), visible_char('日')), ('é', '日'));
        // On a long line too.
        let src = long(1000, 600, "\x1bQ");
        let (text, carets) = line(&src, 601, 601, 1);
        assert!(text.contains("␛Q") && !text.contains('\x1b'), "{text}");
        assert_eq!(pointed(&text, &carets), "Q");
    }

    #[test]
    fn the_strings_of_a_candidate_are_visible() {
        let mut sources = SourceMap::default();
        let f = sources.add("a.onsa", "x\x1b\ny\n");
        let d = Diagnostic::new(Stage::Syntax, Code::E0001, Span::new(f, 0, 1), "m").with_fix(Fix::replace(
            "t",
            Span::new(f, 1, 3),
            "\x07\t",
        ));
        let text = crate::to_text(&sources, &[d]);
        assert!(text.contains("replace `␛␊` with `␇␉`"), "{text}");
        assert!(text.contains("  x␛\n  ^\n"), "{text}");
    }
}
