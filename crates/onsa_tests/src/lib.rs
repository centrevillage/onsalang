//! Runner for `tests/spec` (D-05).
//!
//! Each `.onsa` file is checked as a one-file package. Expected diagnostics
//! are inline markers at the end of a line:
//!
//! ```text
//! let c = x + y * z   //~ E0010
//! let c = x + y * z   //~ E0010 @13      (column, 1-based, optional)
//! ```
//!
//! The first line may set the depth of the check:
//!
//! ```text
//! //! mode: none      recorded only, never run (fragments with `...`, pseudo code)
//! //! mode: parse     only parsing (fn-world examples until phase 2)
//! //! mode: check     compare `check` diagnostics with the markers (default)
//! //! mode: test      check, then run `test` blocks in the interpreter
//! ```
//!
//! A file without markers expects zero diagnostics.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use onsa_diag::{Code, SourceMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    None,
    Parse,
    Check,
    Test,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expected {
    pub code: Code,
    pub line: u32,
    pub col: Option<u32>,
}

/// Parse the `//! mode:` header and `//~` markers of one file.
pub fn parse_markers(text: &str) -> Result<(Mode, Vec<Expected>), String> {
    let mut mode = Mode::Check;
    let mut expected = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let lineno = i as u32 + 1;
        if lineno == 1
            && let Some(rest) = line.strip_prefix("//! mode:")
        {
            mode = match rest.trim() {
                "none" => Mode::None,
                "parse" => Mode::Parse,
                "check" => Mode::Check,
                "test" => Mode::Test,
                other => return Err(format!("line 1: unknown mode `{other}`")),
            };
            continue;
        }
        let Some(idx) = line.find("//~") else { continue };
        for marker in line[idx + 3..].split("//~") {
            let mut parts = marker.split_whitespace();
            let Some(code_str) = parts.next() else {
                return Err(format!("line {lineno}: empty `//~` marker"));
            };
            let Some(code) = Code::parse(code_str) else {
                return Err(format!("line {lineno}: unknown code `{code_str}` in marker"));
            };
            let col = match parts.next() {
                Some(c) => Some(
                    c.strip_prefix('@')
                        .and_then(|n| n.parse().ok())
                        .ok_or_else(|| format!("line {lineno}: bad column `{c}` (expected `@<n>`)"))?,
                ),
                None => None,
            };
            expected.push(Expected { code, line: lineno, col });
        }
    }
    expected.sort();
    Ok((mode, expected))
}

/// Check one file and return a failure message if its diagnostics differ
/// from the markers. `None` means the file passed (or was skipped).
pub fn run_file(path: &Path) -> Option<String> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let (mode, expected) = match parse_markers(&text) {
        Ok(x) => x,
        Err(e) => return Some(format!("{}: bad markers: {e}", path.display())),
    };
    let mut sources = SourceMap::default();
    let file = sources.add(path.to_string_lossy(), text);
    let result = onsa_driver::check(&sources);
    let src = sources.file(file);

    if mode == Mode::None {
        return None;
    }
    // M0: the pipeline is empty, so `parse` and `test` behave like `check`.

    let mut actual: Vec<Expected> = result
        .diagnostics
        .iter()
        .map(|d| {
            let lc = src.line_col(d.span.start);
            Expected { code: d.code, line: lc.line, col: Some(lc.col) }
        })
        .collect();
    actual.sort();

    let matches = expected.len() == actual.len()
        && expected
            .iter()
            .zip(&actual)
            .all(|(e, a)| e.code == a.code && e.line == a.line && e.col.is_none_or(|c| Some(c) == a.col));
    if matches {
        return None;
    }
    let mut msg = format!("{}:\n", path.display());
    let _ = writeln!(msg, "  expected: {}", render(&expected));
    let _ = writeln!(msg, "  actual:   {}", render(&actual));
    let _ = write!(msg, "{}", onsa_diag::to_text(&sources, &result.diagnostics).replace('\n', "\n  "));
    Some(msg)
}

fn render(xs: &[Expected]) -> String {
    if xs.is_empty() {
        return "(none)".into();
    }
    xs.iter()
        .map(|e| match e.col {
            Some(c) => format!("{}@{}:{}", e.code.as_str(), e.line, c),
            None => format!("{}@{}", e.code.as_str(), e.line),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// All `.onsa` files under `dir`, sorted.
pub fn collect(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else { continue };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn markers_parse() {
        let (mode, exp) =
            parse_markers("//! mode: parse\nlet c = x + y * z //~ E0010 @13\nlet d = 1 //~ E0405 //~ E0420\n").unwrap();
        assert_eq!(mode, Mode::Parse);
        assert_eq!(
            exp,
            vec![
                Expected { code: Code::E0010, line: 2, col: Some(13) },
                Expected { code: Code::E0405, line: 3, col: None },
                Expected { code: Code::E0420, line: 3, col: None },
            ]
        );
    }

    #[test]
    fn bad_marker_is_error() {
        assert!(parse_markers("x //~ E9999\n").is_err());
        assert!(parse_markers("//! mode: run\n").is_err());
        assert_eq!(parse_markers("//! mode: none\n").unwrap().0, Mode::None);
    }
}
