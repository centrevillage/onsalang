//! Diagnostics for Onsa: codes, spans, fix candidates, JSON and human-readable output.
//!
//! The JSON form is the one in spec §18.1. Spans are byte offsets (D-02);
//! lines and columns are computed from a [`LineIndex`] when rendering, with
//! columns in characters (Unicode scalar values), by [`SourceFile::line_col`]
//! only.
//!
//! A fix candidate ([`Fix`]) is a title and edits; an edit replaces a range
//! with a string, and an insertion replaces an empty range (§18.1, S-81). The
//! edits of one candidate do not overlap ([`overlap`], the one rule that
//! [`Fix::new`] and [`apply`] share), may cross files, and are applied
//! together. Their ranges come from the tokens of the CST (R-86): both ends of
//! an edit lie on token boundaries, which [`contract`] checks.

mod codes;
pub mod internal;
mod source;

use std::collections::BTreeMap;

pub use codes::{Category, Code, FixRule, NoteRule, Stage};
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

    /// The empty range at `offset` (where an insertion goes).
    pub fn empty(file: FileId, offset: u32) -> Span {
        Span { file, start: offset, end: offset }
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

/// One edit of a fix candidate: the range `span` is replaced by `replace`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edit {
    pub span: Span,
    pub replace: String,
}

impl Edit {
    pub fn replace(span: Span, text: impl Into<String>) -> Edit {
        Edit { span, replace: text.into() }
    }

    /// An insertion: the replacement of the empty range at `offset`.
    pub fn insert(file: FileId, offset: u32, text: impl Into<String>) -> Edit {
        Edit { span: Span::empty(file, offset), replace: text.into() }
    }

    pub fn delete(span: Span) -> Edit {
        Edit { span, replace: String::new() }
    }
}

/// A fix candidate: a short title and the edits applied together (§18.1).
/// The edits are sorted by position and do not overlap (checked when made).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fix {
    title: String,
    edits: Vec<Edit>,
}

impl Fix {
    /// A candidate of several edits, kept in the order of [`sort_edits`]. No
    /// edit or overlapping edits break the rules of diagnostics: [`contract`]
    /// reports them (in debug builds the driver stops on them, W3-02 D11).
    pub fn new(title: impl Into<String>, mut edits: Vec<Edit>) -> Fix {
        sort_edits(&mut edits);
        Fix { title: title.into(), edits }
    }

    /// One edit that replaces `span` with `text`.
    pub fn replace(title: impl Into<String>, span: Span, text: impl Into<String>) -> Fix {
        Fix::new(title, vec![Edit::replace(span, text)])
    }

    /// One edit that inserts `text` at `offset` of `file`.
    pub fn insert(title: impl Into<String>, file: FileId, offset: u32, text: impl Into<String>) -> Fix {
        Fix::new(title, vec![Edit::insert(file, offset, text)])
    }

    /// One edit that removes `span`.
    pub fn delete(title: impl Into<String>, span: Span) -> Fix {
        Fix::new(title, vec![Edit::delete(span)])
    }

    pub fn title(&self) -> &str {
        &self.title
    }

    pub fn edits(&self) -> &[Edit] {
        &self.edits
    }
}

/// The order of edits: by file, start and end (the one place of it).
pub fn sort_edits<E: std::borrow::Borrow<Edit>>(edits: &mut [E]) {
    edits.sort_by_key(|e| {
        let s = e.borrow().span;
        (s.file, s.start, s.end)
    });
}

/// The first pair of edits that overlap, as indexes into `edits` (in any
/// order: it sorts a copy itself). Two edits overlap when the first ends
/// after the second starts, or when both insert at the same position (the
/// order of the two insertions would be undecided). Edits that only touch do
/// not overlap. The one rule of [`apply`], [`contract`] and the test runner
/// (§18.1).
pub fn overlap(edits: &[&Edit]) -> Option<(usize, usize)> {
    let mut order: Vec<usize> = (0..edits.len()).collect();
    order.sort_by_key(|&i| {
        let s = edits[i].span;
        (s.file, s.start, s.end)
    });
    for w in order.windows(2) {
        let (a, b) = (edits[w[0]].span, edits[w[1]].span);
        if a.file != b.file {
            continue;
        }
        if a.end > b.start || (a.is_empty() && b.is_empty() && a.start == b.start) {
            return Some((w[0], w[1]));
        }
    }
    None
}

/// A note of a diagnostic: a related position ("bound here") or, without a
/// position, the correct rule (S-114).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Note {
    pub span: Option<Span>,
    pub message: String,
}

impl Note {
    pub fn at(span: Span, message: impl Into<String>) -> Note {
        Note { span: Some(span), message: message.into() }
    }

    pub fn rule(message: impl Into<String>) -> Note {
        Note { span: None, message: message.into() }
    }
}

/// One diagnostic. Errors only; Onsa has no warnings (lints are errors).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: Code,
    /// The stage that reported it (not in the JSON).
    pub stage: Stage,
    pub message: String,
    pub span: Span,
    /// The offending source text, when it helps the reader.
    pub found: Option<String>,
    /// The fix candidates, in the order the rule of the code gives (§18.1).
    pub fixes: Vec<Fix>,
    pub notes: Vec<Note>,
}

impl Diagnostic {
    /// A diagnostic of `code` reported by `stage`. A stage the registry does
    /// not list for the code breaks the rules of diagnostics ([`contract`]):
    /// debug builds stop here at once, so that the trace names the stage;
    /// release builds report the diagnostic (W3-02 D11).
    pub fn new(stage: Stage, code: Code, span: Span, message: impl Into<String>) -> Diagnostic {
        if cfg!(debug_assertions) && !code.stages().contains(&stage) {
            internal::bug(
                Some(span),
                format!(
                    "{} is reported by the {} stage, which the registry does not list",
                    code.as_str(),
                    stage.name()
                ),
            );
        }
        Diagnostic { code, stage, message: message.into(), span, found: None, fixes: Vec::new(), notes: Vec::new() }
    }

    pub fn with_found(mut self, found: impl Into<String>) -> Diagnostic {
        self.found = Some(found.into());
        self
    }

    pub fn with_fix(mut self, fix: Fix) -> Diagnostic {
        self.fixes.push(fix);
        self
    }

    /// A note at a related position.
    pub fn with_note(mut self, span: Span, note: impl Into<String>) -> Diagnostic {
        self.notes.push(Note::at(span, note));
        self
    }

    /// A note with the correct rule, without a position (S-114).
    pub fn with_rule(mut self, rule: impl Into<String>) -> Diagnostic {
        self.notes.push(Note::rule(rule));
        self
    }
}

/// Apply edits to the files of `sources` at once. Returns the new text of
/// every file an edit touches. Fails on overlapping edits ([`overlap`]), a
/// range outside its file, or an end that is not at a character boundary.
pub fn apply<'a>(
    sources: &SourceMap,
    edits: impl IntoIterator<Item = &'a Edit>,
) -> Result<BTreeMap<FileId, String>, String> {
    let mut by_file: BTreeMap<FileId, Vec<&Edit>> = BTreeMap::new();
    for e in edits {
        if e.span.file.0 as usize >= sources.len() {
            return Err(format!("an edit in an unknown file: {:?}", e.span));
        }
        by_file.entry(e.span.file).or_default().push(e);
    }
    let mut out = BTreeMap::new();
    for (file, edits) in by_file {
        out.insert(file, apply_text(sources.file(file).text(), &edits)?);
    }
    Ok(out)
}

/// Apply edits of one file to its `text` at once (the rule of [`apply`]).
pub fn apply_text(text: &str, edits: &[&Edit]) -> Result<String, String> {
    let mut edits: Vec<&Edit> = edits.to_vec();
    sort_edits(&mut edits);
    if let Some((a, b)) = overlap(&edits) {
        return Err(format!("edits overlap: {:?} and {:?}", edits[a].span, edits[b].span));
    }
    let mut out = text.to_string();
    // Back to front, so that earlier offsets stay valid.
    for e in edits.iter().rev() {
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        if t > out.len() || !out.is_char_boundary(s) || !out.is_char_boundary(t) {
            return Err(format!("an edit outside its file or inside a character: {:?}", e.span));
        }
        out.replace_range(s..t, &e.replace);
    }
    Ok(out)
}

/// The longest title of a fix candidate, in characters ([`contract`]).
pub const TITLE_MAX: usize = 60;

/// The rules every diagnostic follows, as messages (empty when it follows
/// them; plan D-04, W3-02 D11). The tests run it on every diagnostic of every
/// case, and the driver on every diagnostic it returns in debug builds.
/// `is_boundary(file, offset)` says whether a token of the file starts or ends
/// at `offset` (the lexer is not in this crate).
///
/// - The stage is one the registry lists for the code.
/// - A code whose fix is required has a candidate; a code whose rule note is
///   required (E0020, S-114) has a note without a position.
/// - A candidate's title is one line of at most [`TITLE_MAX`] characters (it
///   names the kind of the change; the edits carry the text).
/// - A candidate has edits; they do not overlap, lie in their file on token
///   boundaries (R-86), and change the source.
pub fn contract(d: &Diagnostic, sources: &SourceMap, is_boundary: &dyn Fn(FileId, u32) -> bool) -> Vec<String> {
    let mut out = Vec::new();
    let code = d.code.as_str();
    if !d.code.stages().contains(&d.stage) {
        out.push(format!("{code} from the {} stage, which the registry does not list", d.stage.name()));
    }
    if d.code.fix_rule() == FixRule::Required && d.fixes.is_empty() {
        out.push(format!("{code} has no fix candidate (the registry requires one)"));
    }
    if d.code.note_rule() == NoteRule::Rule && !d.notes.iter().any(|n| n.span.is_none()) {
        out.push(format!("{code} has no note with the correct rule (a note without a position, S-114)"));
    }
    for f in &d.fixes {
        let title = f.title();
        if title.trim().is_empty() || title.contains(['\n', '\r']) || title.chars().count() > TITLE_MAX {
            out.push(format!("{code}: the title {title:?} is not one line of at most {TITLE_MAX} characters"));
        }
        if f.edits().is_empty() {
            out.push(format!("{code}: `{title}` has no edit"));
        }
        for e in f.edits() {
            if e.span.file.0 as usize >= sources.len() || e.span.end as usize > sources.file(e.span.file).text().len() {
                out.push(format!("{code}: the edit {:?} of `{title}` is outside its file", e.span));
                continue;
            }
            for at in [e.span.start, e.span.end] {
                if !is_boundary(e.span.file, at) {
                    out.push(format!("{code}: the edit {:?} of `{title}` does not end on a token boundary", e.span));
                    break;
                }
            }
        }
        match apply(sources, f.edits()) {
            Err(e) => out.push(format!("{code}: `{title}` cannot be applied: {e}")),
            Ok(texts) => {
                if texts.iter().all(|(file, t)| sources.file(*file).text() == t) {
                    out.push(format!("{code}: `{title}` does not change the source"));
                }
            }
        }
    }
    out
}

/// JSON shape of a span (spec §18.1): `end_line` is always there.
#[derive(Debug, Serialize)]
struct JsonSpan<'a> {
    file: &'a str,
    line: u32,
    col: u32,
    end_line: u32,
    end_col: u32,
}

#[derive(Debug, Serialize)]
struct JsonDiagnostic<'a> {
    code: &'static str,
    message: &'a str,
    span: JsonSpan<'a>,
    #[serde(skip_serializing_if = "Option::is_none")]
    found: Option<&'a str>,
    fixes: Vec<JsonFix<'a>>,
    // SPEC-GAP(S-213): §18.1 has no JSON form for notes. `notes` is always an
    // array; a note has `message` and, when it has a position, `span`.
    notes: Vec<JsonNote<'a>>,
}

#[derive(Debug, Serialize)]
struct JsonFix<'a> {
    title: &'a str,
    edits: Vec<JsonEdit<'a>>,
}

#[derive(Debug, Serialize)]
struct JsonEdit<'a> {
    span: JsonSpan<'a>,
    replace: &'a str,
}

#[derive(Debug, Serialize)]
struct JsonNote<'a> {
    message: &'a str,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<JsonSpan<'a>>,
}

fn json_span(sources: &SourceMap, span: Span) -> JsonSpan<'_> {
    let file = sources.file(span.file);
    let start = file.line_col(span.start);
    let end = file.line_col(span.end);
    JsonSpan { file: file.name(), line: start.line, col: start.col, end_line: end.line, end_col: end.col }
}

/// Diagnostics in the order they are rendered: by file, position and code.
fn sorted(diagnostics: &[Diagnostic]) -> Vec<&Diagnostic> {
    let mut sorted: Vec<&Diagnostic> = diagnostics.iter().collect();
    sorted.sort_by_key(|d| (d.span.file, d.span.start, d.code));
    sorted
}

/// Render diagnostics as a JSON array (spec §18.1). Sorted by file and position.
pub fn to_json(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    let items: Vec<JsonDiagnostic> = sorted(diagnostics)
        .into_iter()
        .map(|d| JsonDiagnostic {
            code: d.code.as_str(),
            message: &d.message,
            span: json_span(sources, d.span),
            found: d.found.as_deref(),
            fixes: d
                .fixes
                .iter()
                .map(|f| JsonFix {
                    title: f.title(),
                    edits: f
                        .edits()
                        .iter()
                        .map(|e| JsonEdit { span: json_span(sources, e.span), replace: &e.replace })
                        .collect(),
                })
                .collect(),
            notes: d
                .notes
                .iter()
                .map(|n| JsonNote { message: &n.message, span: n.span.map(|s| json_span(sources, s)) })
                .collect(),
        })
        .collect();
    serde_json::to_string_pretty(&items).expect("diagnostics serialize")
}

/// Render diagnostics for a terminal: `file:line:col: error[E0010]: message`.
pub fn to_text(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    for d in sorted(diagnostics) {
        let file = sources.file(d.span.file);
        let lc = file.line_col(d.span.start);
        let _ = writeln!(out, "{}:{}:{}: error[{}]: {}", file.name(), lc.line, lc.col, d.code.as_str(), d.message);
        if let Some(line) = file.line_text(lc.line) {
            let _ = writeln!(out, "  {line}");
            let width = file.line_col(d.span.end.min(file.line_end(lc.line))).col.saturating_sub(lc.col).max(1);
            let _ = writeln!(out, "  {}{}", " ".repeat((lc.col - 1) as usize), "^".repeat(width as usize));
        }
        for fix in &d.fixes {
            let _ = writeln!(out, "  fix: {}", fix.title());
            for e in fix.edits() {
                let ef = sources.file(e.span.file);
                let elc = ef.line_col(e.span.start);
                let old = &ef.text()[e.span.start as usize..e.span.end as usize];
                let what = match (old.is_empty(), e.replace.is_empty()) {
                    (true, _) => format!("insert `{}`", e.replace),
                    (false, true) => format!("remove `{old}`"),
                    (false, false) => format!("replace `{old}` with `{}`", e.replace),
                };
                let _ = writeln!(out, "    {}:{}:{}: {what}", ef.name(), elc.line, elc.col);
            }
        }
        for note in &d.notes {
            match note.span {
                Some(span) => {
                    let nf = sources.file(span.file);
                    let nlc = nf.line_col(span.start);
                    let _ = writeln!(out, "  note: {}:{}:{}: {}", nf.name(), nlc.line, nlc.col, note.message);
                }
                None => {
                    let _ = writeln!(out, "  note: {}", note.message);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn voice() -> (SourceMap, FileId) {
        let mut sources = SourceMap::default();
        let f = sources.add("dsp/voice.onsa", "flow v() {\n  let f1 = resonator(src, vowel_f1, 80.0)\n}\n");
        (sources, f)
    }

    #[test]
    fn json_shape_matches_spec() {
        let (sources, f) = voice();
        let text = sources.file(f).text();
        let start = text.find("resonator(").unwrap() as u32;
        let end = text.find(", 80.0)").unwrap() as u32 + ", 80.0)".len() as u32;
        let tilde = text.find("(src").unwrap() as u32;
        let d = Diagnostic::new(
            Stage::Flow,
            Code::E0811,
            Span::new(f, start, end),
            "`resonator` is a flow; calling it creates a stateful instance and needs `~`",
        )
        .with_found("resonator(src, vowel_f1, 80.0)")
        .with_fix(Fix::insert("add `~`", f, tilde, "~"));
        let json = to_json(&sources, &[d]);
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v[0]["code"], "E0811");
        assert_eq!(v[0]["span"]["file"], "dsp/voice.onsa");
        assert_eq!(v[0]["span"]["line"], 2);
        assert_eq!(v[0]["span"]["col"], 12);
        assert_eq!(v[0]["span"]["end_line"], 2);
        assert_eq!(v[0]["span"]["end_col"], 42);
        assert_eq!(v[0]["fixes"][0]["title"], "add `~`");
        let e = &v[0]["fixes"][0]["edits"][0];
        assert_eq!(e["replace"], "~");
        assert_eq!((&e["span"]["col"], &e["span"]["end_col"]), (&21.into(), &21.into()));
        assert_eq!(v[0]["notes"], serde_json::json!([]));
    }

    #[test]
    fn notes_have_a_message_and_a_span_only_when_placed() {
        let (sources, f) = voice();
        let d = Diagnostic::new(Stage::Syntax, Code::E0020, Span::new(f, 0, 4), "m")
            .with_fix(Fix::replace("t", Span::new(f, 0, 4), "fn"))
            .with_note(Span::new(f, 5, 6), "here")
            .with_rule("the rule");
        let v: serde_json::Value = serde_json::from_str(&to_json(&sources, &[d])).unwrap();
        assert_eq!(v[0]["notes"][0]["message"], "here");
        assert_eq!(v[0]["notes"][0]["span"]["line"], 1);
        assert_eq!(v[0]["notes"][1], serde_json::json!({"message": "the rule"}));
    }

    #[test]
    fn empty_is_empty_array() {
        let sources = SourceMap::default();
        assert_eq!(to_json(&sources, &[]), "[]");
    }

    #[test]
    fn overlap_rule() {
        let f = FileId(0);
        let e = |a, b| Edit::replace(Span::new(f, a, b), "x");
        let ov = |v: Vec<Edit>| overlap(&v.iter().collect::<Vec<_>>());
        assert_eq!(ov(vec![e(0, 2), e(2, 3)]), None, "touching");
        assert_eq!(ov(vec![e(0, 2), e(1, 3)]), Some((0, 1)));
        assert_eq!(ov(vec![e(1, 3), e(4, 5), e(0, 2)]), Some((2, 0)), "unsorted input: indexes into it");
        assert_eq!(ov(vec![e(1, 1), e(1, 3)]), None, "an insertion before a replacement");
        assert_eq!(ov(vec![e(1, 1), e(1, 1)]), Some((0, 1)), "two insertions at one place");
        assert_eq!(
            ov(vec![Edit::replace(Span::new(f, 0, 5), "x"), Edit::replace(Span::new(FileId(1), 1, 2), "y")]),
            None
        );
    }

    #[test]
    fn apply_edits_of_two_files() {
        let mut sources = SourceMap::default();
        let a = sources.add("a.onsa", "let mut x = 1");
        let b = sources.add("b.onsa", "BadName()");
        let edits = [Edit::replace(Span::new(a, 0, 7), "var"), Edit::replace(Span::new(b, 0, 7), "bad_name")];
        let out = apply(&sources, edits.iter()).unwrap();
        assert_eq!(out[&a], "var x = 1");
        assert_eq!(out[&b], "bad_name()");
        let bad = [Edit::replace(Span::new(a, 0, 7), "v"), Edit::replace(Span::new(a, 4, 5), "w")];
        assert!(apply(&sources, bad.iter()).is_err());
    }

    #[test]
    fn fix_new_sorts_its_edits() {
        let f = FileId(0);
        let fix = Fix::new("t", vec![Edit::insert(f, 5, "]"), Edit::replace(Span::new(f, 1, 2), "[")]);
        assert_eq!(fix.edits()[0].span.start, 1);
    }

    #[test]
    fn contract_reports_what_is_missing() {
        let mut sources = SourceMap::default();
        let f = sources.add("a.onsa", "let mut x = 1");
        let any = |_: FileId, _: u32| true;
        let d = Diagnostic::new(Stage::Syntax, Code::E0020, Span::new(f, 0, 7), "m");
        let problems = contract(&d, &sources, &any);
        assert_eq!(problems.len(), 2, "{problems:?}");
        let d = d.with_fix(Fix::replace("write `var`", Span::new(f, 0, 7), "var")).with_rule("rule");
        assert!(contract(&d, &sources, &any).is_empty());
        let same = Diagnostic::new(Stage::Syntax, Code::E0002, Span::new(f, 0, 3), "m").with_fix(Fix::replace(
            "t",
            Span::new(f, 0, 3),
            "let",
        ));
        assert_eq!(contract(&same, &sources, &any).len(), 1, "a candidate that changes nothing");
        let placed = Diagnostic::new(Stage::Syntax, Code::E0020, Span::new(f, 0, 7), "m")
            .with_fix(Fix::replace("write `var`", Span::new(f, 0, 7), "var"))
            .with_note(Span::new(f, 8, 9), "not a rule");
        assert_eq!(contract(&placed, &sources, &any).len(), 1, "a placed note is not the rule note");
        let long = Diagnostic::new(Stage::Syntax, Code::E0002, Span::new(f, 0, 3), "m").with_fix(Fix::replace(
            "write `[T,\n U]`",
            Span::new(f, 0, 3),
            "x",
        ));
        assert_eq!(contract(&long, &sources, &any).len(), 1, "a title of two lines");
        let empty =
            Diagnostic::new(Stage::Syntax, Code::E0002, Span::new(f, 0, 3), "m").with_fix(Fix::new("t", vec![]));
        assert!(!contract(&empty, &sources, &any).is_empty(), "a candidate without edits");
        let crossed = Diagnostic::new(Stage::Syntax, Code::E0002, Span::new(f, 0, 3), "m").with_fix(Fix::new(
            "t",
            vec![Edit::replace(Span::new(f, 0, 3), "a"), Edit::replace(Span::new(f, 2, 5), "b")],
        ));
        assert!(contract(&crossed, &sources, &any).iter().any(|p| p.contains("overlap")), "overlapping edits");
        let boundary = |_: FileId, o: u32| o != 1;
        let inside = Diagnostic::new(Stage::Syntax, Code::E0002, Span::new(f, 0, 3), "m").with_fix(Fix::replace(
            "t",
            Span::new(f, 1, 3),
            "x",
        ));
        assert_eq!(contract(&inside, &sources, &boundary).len(), 1, "an edit inside a token");
    }
}
