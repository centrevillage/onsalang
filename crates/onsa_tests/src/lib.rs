//! The test cases of the repository (plan D-05, R-80 (5), R-89 (3)).
//!
//! A case is one `.onsa` file, or a package directory with `onsa.toml`, found
//! by scanning `tests/` ([`case::collect`]); Rust holds no table of cases.
//! The settings of a case are an `onsa.toml` fragment at the head of a file
//! ([`fragment`]); the expected diagnostics are inline markers at the end of a
//! line:
//!
//! ```text
//! let c = x + y * z   //~ E0010
//! let c = x + y * z   //~ E0010 @13            (column, 1-based)
//! @param(...) k: Ctl[F32],  //~ E0809 [trap]    (only for the build of target `trap`)
//! @param(...) k: Ctl[F32],  //~ E0809 @3 [trap, poison]
//! ```
//!
//! A file without markers expects zero diagnostics. A marker without targets
//! applies to the check and, when the check reports nothing, to the build of
//! every target ([`run`]). In `mode = "test"` every `test` block must pass
//! unless a marker names it as an expected failure the spec requires:
//!
//! ```text
//! test "overflow panics" {        //~ TESTFAIL "overflow panics"
//! ```
//!
//! Tests the implementation cannot pass yet are listed in `tests/pending.toml`
//! instead (kind `test-case`, [`run::reconcile`]); the two marks are not mixed.

pub mod c;
pub mod case;
pub mod conformance;
pub mod fragment;
pub mod golden;
pub mod pending;
pub mod run;

pub use fragment::{GoldenKind, Mode, TestSettings};

use onsa_diag::Code;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expected {
    pub code: Code,
    pub line: u32,
    pub col: Option<u32>,
    /// `[t, ...]`: the marker applies only to the builds of these targets.
    pub targets: Option<Vec<String>>,
}

/// Markers of one file (D-05).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Markers {
    pub expected: Vec<Expected>,
    /// Names of `test` blocks expected to fail (`//~ TESTFAIL "name"`).
    pub testfails: Vec<String>,
}

/// Parse the `//~` markers of one file.
pub fn parse_markers(text: &str) -> Result<Markers, String> {
    let mut expected = Vec::new();
    let mut testfails = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let lineno = i as u32 + 1;
        let Some(idx) = line.find("//~") else { continue };
        for marker in line[idx + 3..].split("//~") {
            let marker = marker.trim();
            let (code_str, rest) = marker.split_once(char::is_whitespace).unwrap_or((marker, ""));
            if code_str.is_empty() {
                return Err(format!("line {lineno}: empty `//~` marker"));
            }
            if code_str == "TESTFAIL" {
                let rest = rest.trim();
                let name = rest.strip_prefix('"').and_then(|r| r.strip_suffix('"'));
                let Some(name) = name else {
                    return Err(format!("line {lineno}: `TESTFAIL` needs a quoted test name"));
                };
                testfails.push(name.to_string());
                continue;
            }
            let Some(code) = Code::parse(code_str) else {
                return Err(format!("line {lineno}: unknown code `{code_str}` in marker"));
            };
            let (col, targets) = marker_options(rest).map_err(|e| format!("line {lineno}: {e}"))?;
            expected.push(Expected { code, line: lineno, col, targets });
        }
    }
    expected.sort();
    Ok(Markers { expected, testfails })
}

/// `[@<col>] [[t, ...]]` after the code of a marker.
fn marker_options(rest: &str) -> Result<(Option<u32>, Option<Vec<String>>), String> {
    let mut rest = rest.trim();
    let mut col = None;
    if let Some(r) = rest.strip_prefix('@') {
        let end = r.find(|c: char| c.is_whitespace() || c == '[').unwrap_or(r.len());
        let n = &r[..end];
        col = Some(n.parse().map_err(|_| format!("bad column `@{n}` (expected `@<n>`)"))?);
        rest = r[end..].trim();
    }
    let mut targets = None;
    if let Some(r) = rest.strip_prefix('[') {
        let Some(end) = r.find(']') else { return Err("`[` of the targets is not closed".into()) };
        let mut names: Vec<String> = Vec::new();
        for n in r[..end].split(',') {
            let n = n.trim();
            if n.is_empty() || !n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-') {
                return Err(format!("bad target name `{n}` in `[{}]`", &r[..end]));
            }
            if names.iter().any(|x| x == n) {
                return Err(format!("target `{n}` is named twice"));
            }
            names.push(n.to_string());
        }
        names.sort();
        targets = Some(names);
        rest = r[end + 1..].trim();
    }
    if !rest.is_empty() {
        return Err(format!("unexpected `{rest}` in marker (expected `@<col>` and `[<targets>]`)"));
    }
    Ok((col, targets))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(code: Code, line: u32, col: Option<u32>, targets: Option<&[&str]>) -> Expected {
        Expected { code, line, col, targets: targets.map(|t| t.iter().map(|s| s.to_string()).collect()) }
    }

    #[test]
    fn markers_parse() {
        let m = parse_markers(
            "x\nlet c = x + y * z //~ E0010 @13\nlet d = 1 //~ E0405 //~ E0420\nk //~ E0809 [trap]\nk //~ E0809 @3 [trap, poison]\n",
        )
        .unwrap();
        assert_eq!(
            m.expected,
            vec![
                e(Code::E0010, 2, Some(13), None),
                e(Code::E0405, 3, None, None),
                e(Code::E0420, 3, None, None),
                e(Code::E0809, 4, None, Some(&["trap"])),
                e(Code::E0809, 5, Some(3), Some(&["poison", "trap"])),
            ]
        );
    }

    #[test]
    fn bad_marker_is_error() {
        assert!(parse_markers("x //~ E9999\n").is_err());
        assert!(parse_markers("x //~ E0010 13\n").is_err());
        assert!(parse_markers("x //~ E0010 @13 trailing\n").is_err());
        assert!(parse_markers("x //~ E0010 [a\n").is_err());
        assert!(parse_markers("x //~ E0010 []\n").is_err());
        assert!(parse_markers("x //~ E0010 [a, a]\n").is_err());
        assert!(parse_markers("x //~ E0010 [a] @3\n").is_err());
        let m = parse_markers("test \"x\" { //~ TESTFAIL \"x\"\n").unwrap();
        assert_eq!(m.testfails, vec!["x".to_string()]);
        assert!(parse_markers("x //~ TESTFAIL x\n").is_err());
    }
}
