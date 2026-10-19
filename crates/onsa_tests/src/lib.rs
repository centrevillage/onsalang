//! The test cases of the repository (plan D-05, R-80 (5), R-89 (3)). How a
//! case is written (its fragment, the markers `//~ E…`, `TESTFAIL` and
//! `PANIC`, the directories) is in `tests/README.md`; this says where each
//! part is implemented.
//!
//! - The cases are found by scanning `tests/` ([`case::collect`]); Rust holds
//!   no table of cases. The fragment is read by [`fragment`], the markers by
//!   [`parse_markers`].
//! - The markers are matched by [`run`]: the diagnostics of the check and of
//!   the build of each target, the `test` blocks of `mode = "test"`, and a
//!   `PANIC` mark against the origin of the failure (a failed assertion of the
//!   body is `onsa_core::PanicOrigin::Assert` with no `calls`, X9-36).
//! - The pending list `tests/pending.toml` is matched by [`run::reconcile`]
//!   (kind `test-case` for a case).
//! - `[[test.host]]` runs in [`host`] (K-14), `[[test.fix]]` and the contract
//!   of the fix candidates (§18.1) in [`fix_contract`] (W3-17).

pub mod c;
pub mod capi;
pub mod case;
pub mod ccheck;
pub mod conformance;
pub mod copy_guard;
pub mod default_inits;
pub mod fix_contract;
pub mod fix_loop;
pub mod fixes;
pub mod foreign_forms;
pub mod fragment;
pub mod golden;
pub mod host;
pub mod inventory;
pub mod pending;
pub mod run;
pub mod scalar;
pub mod single_files;
pub mod vectors;

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
    pub panics: Vec<PanicMark>,
}

/// `//~ PANIC "name" [@<col>]`: the test `name` panics at this line (and column).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PanicMark {
    pub name: String,
    pub line: u32,
    pub col: Option<u32>,
}

/// Parse the `//~` markers of one file.
pub fn parse_markers(text: &str) -> Result<Markers, String> {
    let mut expected = Vec::new();
    let mut testfails = Vec::new();
    let mut panics = Vec::new();
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
            if code_str == "PANIC" {
                let rest = rest.trim();
                let quoted = rest.strip_prefix('"').and_then(|r| r.rfind('"').map(|end| (&r[..end], &r[end + 1..])));
                let Some((name, rest)) = quoted else {
                    return Err(format!("line {lineno}: `PANIC` needs a quoted test name"));
                };
                let (col, targets) = marker_options(rest).map_err(|e| format!("line {lineno}: {e}"))?;
                if targets.is_some() {
                    return Err(format!("line {lineno}: `PANIC` takes no targets"));
                }
                panics.push(PanicMark { name: name.to_string(), line: lineno, col });
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
    Ok(Markers { expected, testfails, panics })
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
            "x\nlet c = x + y % z //~ E0010 @13\nlet d = 1 //~ E0405 //~ E0420\nk //~ E0809 [trap]\nk //~ E0809 @3 [trap, poison]\n",
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
        let m = parse_markers("a //~ PANIC \"x\"\nb //~ PANIC \"say \"y\"\" @3\n").unwrap();
        let mark = |name: &str, line, col| PanicMark { name: name.into(), line, col };
        assert_eq!(m.panics, [mark("x", 1, None), mark("say \"y\"", 2, Some(3))]);
        for bad in ["x", "\"x", "\"x\" 3", "\"x\" @a", "\"x\" [a]", "\"x\" @3 [a]", "\"x\" more"] {
            assert!(parse_markers(&format!("t //~ PANIC {bad}\n")).is_err(), "{bad}");
        }
    }
}
