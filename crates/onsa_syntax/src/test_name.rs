//! The name of a `test` (spec §11.8, S-244): which values a name may have,
//! and how the full name text of a test writes it. The one place of both
//! rules: the parser checks a name with [`problem`], and the result lines,
//! `onsa test --filter` and the diagnostics write a name with [`quote`].

/// The rule a name follows, for the note of its E0002 (spec §11.8).
pub(crate) const RULE: &str = "the name of a test is a string literal that is not empty, has no interpolation, and \
     holds no control character (U+0000 to U+001F and U+007F to U+009F, the line feed and the tab included), no \
     U+2028 / U+2029 and no bidirectional control (U+202A to U+202E, U+2066 to U+2069), also when the character is \
     written with an escape (§11.8)";

/// A character the value of a name may not hold (spec §11.8): the control
/// characters (U+0000 to U+001F and U+007F to U+009F, the line feed and the
/// tab included), U+2028 / U+2029, and the bidirectional controls of §2.5
/// (U+202A to U+202E and U+2066 to U+2069).
pub(crate) fn forbidden(c: char) -> bool {
    matches!(c, '\u{0}'..='\u{1f}' | '\u{7f}'..='\u{9f}' | '\u{2028}' | '\u{2029}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}')
}

/// The value of the name written as `lit`: the text of the literal with its
/// escapes read (`"\u{61}"` is `a`, S-244). `None` when the literal holds an
/// interpolation: then it is no name (the parser's E0002). The one place a
/// name's value is made (the parser's check, the names of `onsa_sema`).
pub fn value(lit: &crate::ast::StrLit) -> Option<String> {
    let mut out = String::new();
    for s in &lit.segments {
        match s {
            crate::ast::StrSeg::Text(text) => out.push_str(text),
            crate::ast::StrSeg::Interp(_) => return None,
        }
    }
    Some(out)
}

/// What is wrong with the name whose value (the literal with its escapes
/// read, and no interpolation) is `value`, or `None` when it is a name.
pub(crate) fn problem(value: &str) -> Option<String> {
    if value.is_empty() {
        return Some("the name of a test is empty".into());
    }
    let c = value.chars().find(|&c| forbidden(c))?;
    Some(format!("the name of a test holds the character U+{:04X}", c as u32))
}

/// The name `value` written as an Onsa string literal, as the full name text
/// of a test has it (spec §11.8, S-244): in quotes, with `\` as `\\`, `"` as
/// `\"`, `{` as `{{` and `}` as `}}`, and every other character as it is (a
/// name holds no control character, so these four decide the text).
pub fn quote(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for c in value.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '{' => out.push_str("{{"),
            '}' => out.push_str("}}"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_four_escapes_and_nothing_else() {
        assert_eq!(quote("decays"), "\"decays\"");
        assert_eq!(quote("q\"u\\o{t}e"), r#""q\"u\\o{{t}}e""#);
        assert_eq!(quote("it's é ✓"), "\"it's é ✓\"");
        assert_eq!(quote(""), "\"\"");
    }

    #[test]
    fn the_forbidden_characters_are_the_ranges_of_the_spec() {
        let edges = [
            ('\u{0}', true),
            ('\u{1f}', true),
            ('\u{20}', false),
            ('\u{7e}', false),
            ('\u{7f}', true),
            ('\u{9f}', true),
            ('\u{a0}', false),
            ('\u{2027}', false),
            ('\u{2028}', true),
            ('\u{2029}', true),
            ('\u{202a}', true),
            ('\u{202e}', true),
            ('\u{202f}', false),
            ('\u{2065}', false),
            ('\u{2066}', true),
            ('\u{2069}', true),
            ('\u{206a}', false),
        ];
        for (c, want) in edges {
            assert_eq!(forbidden(c), want, "U+{:04X}", c as u32);
        }
        assert!(problem("").is_some());
        assert!(problem("a\tb").is_some());
        assert!(problem(" ").is_none());
    }
}
