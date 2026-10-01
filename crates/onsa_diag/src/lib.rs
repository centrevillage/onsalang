//! Diagnostics for Onsa: codes, spans, JSON and human-readable output.
//!
//! The JSON form is the one in spec §18.1. Spans are byte offsets (D-02);
//! lines and columns are computed from a [`LineIndex`] when rendering.

mod codes;
mod source;

pub use codes::{Category, Code};
pub use source::{FileId, LineCol, LineIndex, SourceFile, SourceMap};

use serde::Serialize;

/// A byte range `[start, end)` in one file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(file: FileId, start: u32, end: u32) -> Span {
        debug_assert!(start <= end);
        Span { file, start, end }
    }

    pub fn len(self) -> u32 {
        self.end - self.start
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// The smallest span covering both (same file).
    pub fn to(self, other: Span) -> Span {
        debug_assert_eq!(self.file, other.file);
        Span::new(self.file, self.start.min(other.start), self.end.max(other.end))
    }

    pub fn contains(self, offset: u32) -> bool {
        self.start <= offset && offset < self.end
    }
}

/// A suggested edit. `replace` rewrites the diagnostic's span.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub enum Fix {
    Replace { replace: String },
    InsertBefore { insert_before: String },
    InsertAfter { insert_after: String },
}

/// One diagnostic. Errors only; Onsa has no warnings (lints are errors).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: Code,
    pub message: String,
    pub span: Span,
    /// The offending source text, when it helps the reader.
    pub found: Option<String>,
    pub fixes: Vec<Fix>,
    /// Related positions ("bound here", "defined here").
    pub notes: Vec<(Span, String)>,
}

impl Diagnostic {
    pub fn new(code: Code, span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic { code, message: message.into(), span, found: None, fixes: Vec::new(), notes: Vec::new() }
    }

    pub fn with_found(mut self, found: impl Into<String>) -> Diagnostic {
        self.found = Some(found.into());
        self
    }

    pub fn with_fix(mut self, fix: Fix) -> Diagnostic {
        self.fixes.push(fix);
        self
    }

    pub fn with_note(mut self, span: Span, note: impl Into<String>) -> Diagnostic {
        self.notes.push((span, note.into()));
        self
    }
}

/// JSON shape of spec §18.1 (`end_line` is added only when the span spans lines).
#[derive(Debug, Serialize)]
struct JsonSpan<'a> {
    file: &'a str,
    line: u32,
    col: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    end_line: Option<u32>,
    end_col: u32,
}

#[derive(Debug, Serialize)]
struct JsonDiagnostic<'a> {
    code: &'static str,
    message: &'a str,
    span: JsonSpan<'a>,
    #[serde(skip_serializing_if = "Option::is_none")]
    found: Option<&'a str>,
    fixes: &'a [Fix],
    #[serde(skip_serializing_if = "Vec::is_empty")]
    notes: Vec<JsonNote<'a>>,
}

#[derive(Debug, Serialize)]
struct JsonNote<'a> {
    span: JsonSpan<'a>,
    message: &'a str,
}

fn json_span<'a>(sources: &'a SourceMap, span: Span) -> JsonSpan<'a> {
    let file = sources.file(span.file);
    let start = file.line_col(span.start);
    let end = file.line_col(span.end);
    JsonSpan {
        file: file.name(),
        line: start.line,
        col: start.col,
        end_line: (end.line != start.line).then_some(end.line),
        end_col: end.col,
    }
}

/// Render diagnostics as a JSON array (spec §18.1). Sorted by file and position.
pub fn to_json(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    let mut sorted: Vec<&Diagnostic> = diagnostics.iter().collect();
    sorted.sort_by_key(|d| (d.span.file, d.span.start, d.code));
    let items: Vec<JsonDiagnostic> = sorted
        .iter()
        .map(|d| JsonDiagnostic {
            code: d.code.as_str(),
            message: &d.message,
            span: json_span(sources, d.span),
            found: d.found.as_deref(),
            fixes: &d.fixes,
            notes: d.notes.iter().map(|(s, m)| JsonNote { span: json_span(sources, *s), message: m }).collect(),
        })
        .collect();
    serde_json::to_string_pretty(&items).expect("diagnostics serialize")
}

/// Render diagnostics for a terminal: `file:line:col: error[E0010]: message`.
pub fn to_text(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    use std::fmt::Write;
    let mut sorted: Vec<&Diagnostic> = diagnostics.iter().collect();
    sorted.sort_by_key(|d| (d.span.file, d.span.start, d.code));
    let mut out = String::new();
    for d in sorted {
        let file = sources.file(d.span.file);
        let lc = file.line_col(d.span.start);
        let _ = writeln!(out, "{}:{}:{}: error[{}]: {}", file.name(), lc.line, lc.col, d.code.as_str(), d.message);
        if let Some(line) = file.line_text(lc.line) {
            let _ = writeln!(out, "  {line}");
            let width = file.line_col(d.span.end.min(file.line_end(lc.line))).col.saturating_sub(lc.col).max(1);
            let _ = writeln!(out, "  {}{}", " ".repeat((lc.col - 1) as usize), "^".repeat(width as usize));
        }
        for fix in &d.fixes {
            match fix {
                Fix::Replace { replace } => {
                    let _ = writeln!(out, "  fix: replace with `{replace}`");
                }
                Fix::InsertBefore { insert_before } => {
                    let _ = writeln!(out, "  fix: insert `{insert_before}` before");
                }
                Fix::InsertAfter { insert_after } => {
                    let _ = writeln!(out, "  fix: insert `{insert_after}` after");
                }
            }
        }
        for (span, note) in &d.notes {
            let nf = sources.file(span.file);
            let nlc = nf.line_col(span.start);
            let _ = writeln!(out, "  note: {}:{}:{}: {}", nf.name(), nlc.line, nlc.col, note);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_shape_matches_spec() {
        let mut sources = SourceMap::default();
        let f = sources.add("dsp/voice.onsa", "flow v() {\n  let f1 = resonator(src, vowel_f1, 80.0)\n}\n");
        let text = sources.file(f).text();
        let start = text.find("resonator(").unwrap() as u32;
        let end = text.find(", 80.0)").unwrap() as u32 + ", 80.0)".len() as u32;
        let d = Diagnostic::new(
            Code::E0811,
            Span::new(f, start, end),
            "`resonator` is a flow; calling it creates a stateful instance and needs `~`",
        )
        .with_found("resonator(src, vowel_f1, 80.0)")
        .with_fix(Fix::Replace { replace: "resonator~(src, vowel_f1, 80.0)".into() });
        let json = to_json(&sources, &[d]);
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v[0]["code"], "E0811");
        assert_eq!(v[0]["span"]["file"], "dsp/voice.onsa");
        assert_eq!(v[0]["span"]["line"], 2);
        assert_eq!(v[0]["span"]["col"], 12);
        assert_eq!(v[0]["span"]["end_col"], 42);
        assert_eq!(v[0]["fixes"][0]["replace"], "resonator~(src, vowel_f1, 80.0)");
        assert!(v[0].get("notes").is_none());
    }

    #[test]
    fn empty_is_empty_array() {
        let sources = SourceMap::default();
        assert_eq!(to_json(&sources, &[]), "[]");
    }
}
