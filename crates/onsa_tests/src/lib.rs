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
//! A file without markers expects zero diagnostics. In `mode: test` every
//! `test` block must pass unless a marker names it as an expected failure:
//!
//! ```text
//! test "overflow panics" {        //~ TESTFAIL "overflow panics"
//! ```

pub mod c;
pub mod pending;

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use onsa_diag::Code;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Mode {
    None,
    Parse,
    #[default]
    Check,
    Test,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expected {
    pub code: Code,
    pub line: u32,
    pub col: Option<u32>,
}

/// Markers of one file (D-05).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Markers {
    pub mode: Mode,
    pub expected: Vec<Expected>,
    /// Names of `test` blocks expected to fail (`//~ TESTFAIL "name"`).
    pub testfails: Vec<String>,
}

/// Parse the `//! mode:` header and `//~` markers of one file.
pub fn parse_markers(text: &str) -> Result<Markers, String> {
    let mut mode = Mode::Check;
    let mut expected = Vec::new();
    let mut testfails = Vec::new();
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
            if code_str == "TESTFAIL" {
                let rest = marker.trim().strip_prefix("TESTFAIL").unwrap_or("").trim();
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
    Ok(Markers { mode, expected, testfails })
}

/// A test unit: one `.onsa` file, or a package directory (with `onsa.toml`)
/// whose files share one set of expected markers.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Unit {
    File(PathBuf),
    Package(PathBuf),
}

impl Unit {
    pub fn path(&self) -> &Path {
        match self {
            Unit::File(p) | Unit::Package(p) => p,
        }
    }
}

/// Check one unit and return a failure message if its diagnostics differ
/// from the markers. `None` means the unit passed (or was skipped).
pub fn run_unit(unit: &Unit) -> Option<String> {
    let path = unit.path();
    let paths: Vec<PathBuf> = match unit {
        Unit::File(p) => vec![p.clone()],
        Unit::Package(p) => vec![p.clone()],
    };
    let mut loaded = match onsa_driver::load(&paths) {
        Ok(l) => l,
        Err(e) => return Some(format!("{}: {e}", path.display())),
    };
    // Markers and mode from every file of the unit (line numbers are per file).
    let mut mode = Mode::Check;
    let mut expected: Vec<(u32, Expected)> = Vec::new();
    let mut testfails: Vec<String> = Vec::new();
    for (file, _) in loaded.modules.clone() {
        let text = loaded.sources.file(file).text().to_string();
        match parse_markers(&text) {
            Ok(m) => {
                if m.mode != Mode::Check {
                    mode = m.mode;
                }
                expected.extend(m.expected.into_iter().map(|e| (file.0, e)));
                testfails.extend(m.testfails);
            }
            Err(e) => return Some(format!("{}: bad markers: {e}", loaded.sources.file(file).name())),
        }
    }
    expected.sort();
    if mode == Mode::None {
        return None;
    }
    let mut analyzed = None;
    let result = match mode {
        Mode::Parse => onsa_driver::parse_only(&loaded.sources),
        Mode::Check | Mode::None => onsa_driver::check_loaded(&mut loaded),
        Mode::Test => {
            let a = onsa_driver::analyze_loaded(&mut loaded);
            let r = onsa_driver::CheckResult { diagnostics: a.diagnostics.clone() };
            analyzed = Some(a);
            r
        }
    };
    let sources = &loaded.sources;

    let mut actual: Vec<(u32, Expected)> = result
        .diagnostics
        .iter()
        .map(|d| {
            let lc = sources.file(d.span.file).line_col(d.span.start);
            (d.span.file.0, Expected { code: d.code, line: lc.line, col: Some(lc.col) })
        })
        .collect();
    actual.sort();

    let matches = expected.len() == actual.len()
        && expected.iter().zip(&actual).all(|((ef, e), (af, a))| {
            ef == af && e.code == a.code && e.line == a.line && e.col.is_none_or(|c| Some(c) == a.col)
        });
    if matches {
        if let Some(a) = analyzed.filter(|a| a.diagnostics.is_empty()) {
            // `mode: test`: lower and run every `test` block (T3-8).
            let module = match onsa_driver::lower_core(&a) {
                Ok(m) => m,
                Err(diags) => {
                    return Some(format!(
                        "{}: lowering failed:\n{}",
                        path.display(),
                        onsa_diag::to_text(sources, &diags).replace('\n', "\n  ")
                    ));
                }
            };
            let report = onsa_driver::run_tests(&module, &onsa_driver::TestOptions::default());
            let mut problems = Vec::new();
            for t in &report.tests {
                let expected_fail = testfails.contains(&t.name);
                match (t.status == onsa_driver::TestStatus::Failed, expected_fail) {
                    (true, false) => {
                        problems.push(format!("test \"{}\" failed: {}", t.name, t.message.as_deref().unwrap_or("")))
                    }
                    (false, true) => problems.push(format!("test \"{}\" passed but is marked TESTFAIL", t.name)),
                    _ => {}
                }
            }
            for name in &testfails {
                if !report.tests.iter().any(|t| &t.name == name) {
                    problems.push(format!("TESTFAIL names an unknown test \"{name}\""));
                }
            }
            if !problems.is_empty() {
                return Some(format!("{}:\n  {}", path.display(), problems.join("\n  ")));
            }
        }
        // T2-12: every diagnostic of a negative example carries the offending
        // source (`found`), and codes with a unique repair carry a fix (§18.1).
        if path.to_string_lossy().contains("negative") {
            for d in &result.diagnostics {
                if d.found.as_deref().is_none_or(str::is_empty) {
                    return Some(format!(
                        "{}: {} at {} has no `found` text",
                        path.display(),
                        d.code.as_str(),
                        d.span.start
                    ));
                }
                if matches!(d.code.as_str(), "E0713" | "E0714" | "E0703" | "E0811" | "E0812" | "E0411" | "E0020")
                    && d.fixes.is_empty()
                {
                    return Some(format!("{}: {} at {} has no fix", path.display(), d.code.as_str(), d.span.start));
                }
            }
        }
        return None;
    }
    let mut msg = format!("{}:\n", path.display());
    let _ = writeln!(msg, "  expected: {}", render(&expected));
    let _ = writeln!(msg, "  actual:   {}", render(&actual));
    let _ = write!(msg, "{}", onsa_diag::to_text(sources, &result.diagnostics).replace('\n', "\n  "));
    Some(msg)
}

/// Compatibility wrapper for one file.
pub fn run_file(path: &Path) -> Option<String> {
    run_unit(&Unit::File(path.to_path_buf()))
}

fn render(xs: &[(u32, Expected)]) -> String {
    if xs.is_empty() {
        return "(none)".into();
    }
    xs.iter()
        .map(|(f, e)| match e.col {
            Some(c) => format!("{}@{}:{}:{}", e.code.as_str(), f, e.line, c),
            None => format!("{}@{}:{}", e.code.as_str(), f, e.line),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// All test units under `dir`, sorted: a directory holding `onsa.toml` is one
/// package unit; every other `.onsa` file is a unit of its own.
pub fn collect(dir: &Path) -> Vec<Unit> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        if d.join("onsa.toml").exists() && d != dir {
            out.push(Unit::Package(d));
            continue;
        }
        let Ok(entries) = std::fs::read_dir(&d) else { continue };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                out.push(Unit::File(p));
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
        let m =
            parse_markers("//! mode: parse\nlet c = x + y * z //~ E0010 @13\nlet d = 1 //~ E0405 //~ E0420\n").unwrap();
        assert_eq!(m.mode, Mode::Parse);
        assert_eq!(
            m.expected,
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
        assert_eq!(parse_markers("//! mode: none\n").unwrap().mode, Mode::None);
        let m = parse_markers("//! mode: test\ntest \"x\" { //~ TESTFAIL \"x\"\n").unwrap();
        assert_eq!(m.testfails, vec!["x".to_string()]);
        assert!(parse_markers("x //~ TESTFAIL x\n").is_err());
    }
}
