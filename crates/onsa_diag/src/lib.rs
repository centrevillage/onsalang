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
pub mod stack;
pub mod unsupported;

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

    /// The order of the diagnostics of one file (§18.1, S-281): start, end,
    /// code, message. Of the diagnostics of one unit, the driver reports the
    /// first in this order (`onsa_driver::reduce`), also when one failure of
    /// the parser is read as more than one form.
    pub fn order_in_file(&self) -> (u32, u32, &str, &str) {
        (self.span.start, self.span.end, self.code.as_str(), self.message.as_str())
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
/// The texts of [`apply_mapped`].
pub fn apply<'a>(
    sources: &SourceMap,
    edits: impl IntoIterator<Item = &'a Edit>,
) -> Result<BTreeMap<FileId, String>, String> {
    apply_mapped(sources, edits).map(|a| a.texts)
}

/// Edits applied ([`apply_mapped`]): the new texts, and where each edit and
/// each place of the original texts went.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Applied {
    /// The new text of every file an edit touches.
    pub texts: BTreeMap<FileId, String>,
    /// For each edit, in the order given: the range its replacement takes in
    /// the new text of its file (empty for a deletion).
    pub ranges: Vec<Span>,
    /// Per file, each edit as (old start, old end, new start, new end), in
    /// the order of the text ([`Applied::map_span`]).
    moves: BTreeMap<FileId, Vec<[u32; 4]>>,
}

impl Applied {
    /// Where the range `span` of an original text is after the edits: each
    /// end moves by the edits before it; an end inside an edited range goes
    /// to that end of its replacement, and an insertion at either end of
    /// `span` goes inside it (the start stays before the inserted text, the
    /// end goes after it). So an empty `span` at an insertion covers the
    /// inserted text.
    pub fn map_span(&self, span: Span) -> Span {
        let Some(moves) = self.moves.get(&span.file) else { return span };
        let shift = |at: u32, start: bool| -> u32 {
            let mut delta: i64 = 0;
            for &[os, oe, ns, ne] in moves {
                // Wholly before `at` (an insertion at `at` is before the end, not the start).
                if oe < at || (oe == at && (os < oe || !start)) {
                    delta = ne as i64 - oe as i64;
                } else if os < at || (start && os == at && os < oe) {
                    // `at` is inside the edited range.
                    return if start { ns } else { ne };
                } else {
                    break;
                }
            }
            (at as i64 + delta) as u32
        };
        Span { file: span.file, start: shift(span.start, true), end: shift(span.end, false) }
    }
}

/// Apply edits to the files of `sources` at once, as [`apply`] (the one place
/// of applying them, W3-17), keeping where each replacement lies in the new
/// texts and where the places of the original texts went.
pub fn apply_mapped<'a>(sources: &SourceMap, edits: impl IntoIterator<Item = &'a Edit>) -> Result<Applied, String> {
    let edits: Vec<&Edit> = edits.into_iter().collect();
    let mut by_file: BTreeMap<FileId, Vec<usize>> = BTreeMap::new();
    for (i, e) in edits.iter().enumerate() {
        if e.span.file.0 as usize >= sources.len() {
            return Err(format!("an edit in an unknown file: {:?}", e.span));
        }
        by_file.entry(e.span.file).or_default().push(i);
    }
    let mut out = Applied { ranges: edits.iter().map(|e| e.span).collect(), ..Applied::default() };
    for (file, idx) in by_file {
        let mine: Vec<&Edit> = idx.iter().map(|&i| edits[i]).collect();
        let (text, ranges) = apply_text_mapped(sources.file(file).text(), &mine)?;
        let mut moves = Vec::with_capacity(idx.len());
        for (k, &i) in idx.iter().enumerate() {
            out.ranges[i] = Span::new(file, ranges[k].0, ranges[k].1);
            moves.push([edits[i].span.start, edits[i].span.end, ranges[k].0, ranges[k].1]);
        }
        moves.sort();
        out.moves.insert(file, moves);
        out.texts.insert(file, text);
    }
    Ok(out)
}

/// Apply edits of one file to its `text` at once (the rule of [`apply`]).
pub fn apply_text(text: &str, edits: &[&Edit]) -> Result<String, String> {
    apply_text_mapped(text, edits).map(|(t, _)| t)
}

/// [`apply_text`], with the range each replacement takes in the new text (in
/// the order of `edits`).
fn apply_text_mapped(text: &str, edits: &[&Edit]) -> Result<(String, Vec<(u32, u32)>), String> {
    let mut order: Vec<usize> = (0..edits.len()).collect();
    order.sort_by_key(|&i| {
        let s = edits[i].span;
        (s.file, s.start, s.end)
    });
    if let Some((a, b)) = overlap(edits) {
        return Err(format!("edits overlap: {:?} and {:?}", edits[a].span, edits[b].span));
    }
    let mut out = String::with_capacity(text.len());
    let mut ranges = vec![(0, 0); edits.len()];
    let mut pos = 0;
    // Front to back: the text before each edit, then its replacement.
    for i in order {
        let e = edits[i];
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        if s > t || t > text.len() || !text.is_char_boundary(s) || !text.is_char_boundary(t) {
            return Err(format!("an edit outside its file or inside a character: {:?}", e.span));
        }
        out.push_str(&text[pos..s]);
        let start = out.len() as u32;
        out.push_str(&e.replace);
        ranges[i] = (start, out.len() as u32);
        pos = t;
    }
    out.push_str(&text[pos..]);
    Ok((out, ranges))
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

/// JSON shape of a span (spec §18.1): `end_line` is always there. The one
/// shape of a position in every `--json` document ([`json_span`]).
#[derive(Debug, Serialize)]
pub struct JsonSpan<'a> {
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
    /// Always there, also when empty; so is `notes` (§18.1, S-213).
    fixes: Vec<JsonFix<'a>>,
    notes: Vec<JsonNote<'a>>,
}

/// The one object `--json` prints, for every command (§18.1, S-215): the
/// diagnostics are its `diagnostics` array, an empty one when there is none;
/// the keys of `rest` (a command's own result, such as `onsa interface`'s)
/// are beside it in the same object.
#[derive(Debug, Serialize)]
struct JsonDocument<'a, T: Serialize> {
    diagnostics: Vec<JsonDiagnostic<'a>>,
    #[serde(flatten)]
    rest: &'a T,
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

/// A note (§18.1, S-213): `message`, and `span` only when it has a position.
#[derive(Debug, Serialize)]
struct JsonNote<'a> {
    message: &'a str,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<JsonSpan<'a>>,
}

/// The JSON of `span` (spec §18.1): the file's name as the source map has
/// it, lines and columns from 1, the end column not included.
pub fn json_span(sources: &SourceMap, span: Span) -> JsonSpan<'_> {
    let file = sources.file(span.file);
    let start = file.line_col(span.start);
    let end = file.line_col(span.end);
    JsonSpan { file: file.name(), line: start.line, col: start.col, end_line: end.line, end_col: end.col }
}

/// Diagnostics in the order they are rendered, in JSON and in text alike (the
/// one place of it; §18.1, S-234): by the file name as printed (code points,
/// so neither the order of reading nor the locale matters), then line,
/// column, end line, end column, code and message. Equal keys keep the order
/// they came in (the sort is stable).
fn sorted<'a>(sources: &SourceMap, diagnostics: &'a [Diagnostic]) -> Vec<&'a Diagnostic> {
    let mut keyed: Vec<_> = diagnostics
        .iter()
        .map(|d| {
            let file = sources.file(d.span.file);
            let (start, end) = (file.line_col(d.span.start), file.line_col(d.span.end));
            ((file.name(), start.line, start.col, end.line, end.col, d.code.as_str(), d.message.as_str()), d)
        })
        .collect();
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    keyed.into_iter().map(|(_, d)| d).collect()
}

/// Render diagnostics as the JSON document of `--json` (spec §18.1, S-215):
/// one object whose `diagnostics` array is in the order of [`sorted`].
pub fn to_json(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    #[derive(Serialize)]
    struct Nothing {}
    to_json_document(sources, diagnostics, &Nothing {})
}

/// The JSON document of `--json` with a command's own result: the keys of
/// `rest` (which serializes as an object without a `diagnostics` key) beside
/// the `diagnostics` array of [`to_json`]. The one place of the document's
/// shape for every command.
pub fn to_json_document<T: Serialize>(sources: &SourceMap, diagnostics: &[Diagnostic], rest: &T) -> String {
    let document = JsonDocument { diagnostics: json_diagnostics(sources, diagnostics), rest };
    serde_json::to_string_pretty(&document).expect("diagnostics serialize")
}

fn json_diagnostics<'a>(sources: &'a SourceMap, diagnostics: &'a [Diagnostic]) -> Vec<JsonDiagnostic<'a>> {
    sorted(sources, diagnostics)
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
        .collect()
}

/// Render diagnostics for a terminal: `file:line:col: error[E0010]: message`,
/// in the order of the JSON ([`sorted`]; `docs/onsa-tools.md` §4).
pub fn to_text(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    for d in sorted(sources, diagnostics) {
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
        let doc: serde_json::Value = serde_json::from_str(&json).unwrap();
        let v = &doc["diagnostics"];
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
        let doc: serde_json::Value = serde_json::from_str(&to_json(&sources, &[d])).unwrap();
        let v = &doc["diagnostics"];
        assert_eq!(v[0]["notes"][0]["message"], "here");
        assert_eq!(v[0]["notes"][0]["span"]["line"], 1);
        assert_eq!(v[0]["notes"][1], serde_json::json!({"message": "the rule"}));
    }

    #[test]
    fn no_diagnostic_is_an_object_with_an_empty_array() {
        let sources = SourceMap::default();
        let doc: serde_json::Value = serde_json::from_str(&to_json(&sources, &[])).unwrap();
        assert_eq!(doc, serde_json::json!({"diagnostics": []}));
    }

    #[test]
    fn a_command_result_is_beside_the_diagnostics_in_one_object() {
        #[derive(Serialize)]
        struct R {
            package: &'static str,
            modules: Vec<u32>,
        }
        let sources = SourceMap::default();
        let text = to_json_document(&sources, &[], &R { package: "p", modules: vec![1] });
        let doc: serde_json::Value = serde_json::from_str(&text).unwrap();
        assert_eq!(doc, serde_json::json!({"diagnostics": [], "package": "p", "modules": [1]}));
    }

    /// §18.1 (S-234): file string, line, column, end line, end column, code,
    /// message; not the order of the files' ids, the stage or the input.
    #[test]
    fn the_order_is_the_file_string_then_the_position_then_code_and_message() {
        let mut sources = SourceMap::default();
        let ab = sources.add("a/b.onsa", "xx\nyy\n");
        let a = sources.add("a.onsa", "xx\nyy\n");
        let d = |f, s, e, code, m: &str| Diagnostic::new(Stage::Syntax, code, Span::new(f, s, e), m);
        let ds = [
            d(ab, 0, 1, Code::E0002, "m"),
            d(a, 3, 4, Code::E0001, "m"),
            d(a, 0, 2, Code::E0002, "m"),
            d(a, 0, 1, Code::E0002, "n"),
            d(a, 0, 1, Code::E0002, "m"),
            d(a, 0, 1, Code::E0001, "z"),
        ];
        let got: Vec<(&str, u32, u32, &str, &str)> = sorted(&sources, &ds)
            .iter()
            .map(|d| (sources.file(d.span.file).name(), d.span.start, d.span.end, d.code.as_str(), d.message.as_str()))
            .collect();
        assert_eq!(
            got,
            [
                ("a.onsa", 0, 1, "E0001", "z"),
                ("a.onsa", 0, 1, "E0002", "m"),
                ("a.onsa", 0, 1, "E0002", "n"),
                ("a.onsa", 0, 2, "E0002", "m"),
                ("a.onsa", 3, 4, "E0001", "m"),
                ("a/b.onsa", 0, 1, "E0002", "m"),
            ]
        );
        let text = to_text(&sources, &ds);
        let heads: Vec<&str> = text.lines().filter(|l| !l.starts_with(' ')).collect();
        assert_eq!(heads[0], "a.onsa:1:1: error[E0001]: z");
        assert_eq!(heads[5], "a/b.onsa:1:1: error[E0002]: m");
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
    fn apply_mapped_keeps_where_the_edits_went() {
        let mut sources = SourceMap::default();
        let a = sources.add("a.onsa", "let mut x = 1 + y");
        let b = sources.add("b.onsa", "abc");
        // `mut ` removed, `1` replaced by `22`, `!` inserted at the end; `b` gets `[` at 1.
        let edits = [
            Edit::insert(a, 17, "!"),
            Edit::delete(Span::new(a, 4, 8)),
            Edit::replace(Span::new(a, 12, 13), "22"),
            Edit::insert(b, 1, "["),
        ];
        let out = apply_mapped(&sources, edits.iter()).unwrap();
        assert_eq!(out.texts[&a], "let x = 22 + y!");
        assert_eq!(out.texts[&b], "a[bc");
        // In the order given, each replacement's range in the new text.
        assert_eq!(out.ranges, [Span::new(a, 14, 15), Span::new(a, 4, 4), Span::new(a, 8, 10), Span::new(b, 1, 2)]);
        for (e, r) in edits.iter().zip(&out.ranges) {
            assert_eq!(&out.texts[&r.file][r.start as usize..r.end as usize], e.replace);
        }
        let m = |s: u32, e: u32| {
            let r = out.map_span(Span::new(a, s, e));
            (r.start, r.end)
        };
        assert_eq!(m(0, 3), (0, 3), "before every edit");
        assert_eq!(m(8, 9), (4, 5), "`x`, after the deletion");
        assert_eq!(m(5, 6), (4, 4), "inside the deleted range");
        assert_eq!(m(12, 13), (8, 10), "the replaced `1`");
        assert_eq!(m(10, 17), (6, 15), "an insertion at the end goes inside");
        let mut one = SourceMap::default();
        let t = one.add("t.onsa", "abc");
        let ins = [Edit::insert(t, 1, "X")];
        let at = apply_mapped(&one, ins.iter()).unwrap();
        assert_eq!(at.texts[&t], "aXbc");
        assert_eq!(at.map_span(Span::new(t, 1, 2)), Span::new(t, 1, 3), "an insertion at the start goes inside");
        assert_eq!(at.map_span(Span::new(t, 0, 1)), Span::new(t, 0, 2), "and at the end");
        assert_eq!(m(16, 17), (13, 15), "`y`, with the insertion at its end");
        assert_eq!(m(16, 16), (13, 13), "the start of `y`");
        assert_eq!(m(17, 17), (14, 15), "an empty range at an insertion covers it");
        assert_eq!(m(4, 8), (4, 4), "the deleted range");
        // A file no edit touches does not move.
        let c = sources.add("c.onsa", "x");
        assert_eq!(out.map_span(Span::new(c, 0, 1)), Span::new(c, 0, 1));
        // The same rule as `apply`.
        let bad = [Edit::replace(Span::new(a, 0, 7), "v"), Edit::replace(Span::new(a, 4, 5), "w")];
        assert!(apply_mapped(&sources, bad.iter()).is_err());
        let outside = [Edit::replace(Span::new(b, 2, 9), "v")];
        assert!(apply_mapped(&sources, outside.iter()).is_err());
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
