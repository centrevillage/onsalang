//! The contract of the fix candidates (spec §18.1; S-236, S-247, S-248,
//! S-266; W3-17).
//!
//! §18.1: "every candidate, applied alone and checked again, leaves no
//! diagnostic of the same or an earlier stage in any unit its edits touch,
//! when the original diagnostic was the only error of that stage or earlier
//! in its unit". The runner checks it on every candidate of every diagnostic
//! of every case of `mode = "check"` or `"test"` ([`check`]):
//!
//! 1. the candidate alone is applied to the case's files
//!    ([`onsa_diag::apply_mapped`]), and the case runs again through the same
//!    entry as the case (`Loaded::from_input`, `analyze_loaded`, plan D-05);
//! 2. the units its edits touch are those of the check after it (the
//!    driver's table, `Analyzed::units`; never computed here, D-15) whose
//!    range meets the range of a replacement (both ends included, so a
//!    deletion and the borders count). A unit with members is touched only
//!    outside them (its heading and braces): an edit inside one member
//!    touches that member. The unit of the original diagnostic is not added
//!    (S-266: the edits alone decide);
//! 3. the diagnostics the check after it reports in those units, of the
//!    stage of the original diagnostic or an earlier one (the order of
//!    [`onsa_diag::Stage::CHECK_ORDER`]), are the ones the case expects:
//!    none by default (the reported diagnostic is the only error of its unit,
//!    S-236; one syntactic form is one error, S-248), else the `leaves` of a
//!    `[[test.fix]]` entry ([`FixSpec`]). A diagnostic outside every unit
//!    counts when it meets a replacement. Later stages are not looked at.
//!
//! A `[[test.fix]]` entry may also promise more of one candidate: `clean`
//! (the check after it reports nothing at all, S-253) and `same_code` (the
//! tokens other than comments, and whether a line break lies between two of
//! them, are the same before and after it; a comment may move, S-247).
//!
//! A candidate that breaks the contract is [`Problem::FixContract`], named
//! `<file from the repository root>:<line>:<col> <code> fix<K>`: an entry of
//! kind `fix-contract` of `tests/pending.toml` silences that one candidate
//! (a whole-case entry does not). A candidate that cannot be checked (it
//! edits a file outside the case, it cannot be applied, the check after it
//! ends in an internal error, it belongs to a stage that has no way to be
//! checked again: lowering, the build, `onsa test`) is
//! [`Problem::FixUnchecked`], never silenced. A `[[test.fix]]` entry that
//! names no diagnostic or candidate is an error of the case.
//!
//! The fuzzing cannot know how many errors a mutant holds, so it uses the
//! near "same place" of S-236 ([`same_place`], `onsa_cases --fix-same-place`,
//! `tools/fuzz.py`).

use std::collections::BTreeSet;

use serde::{Deserialize, Deserializer};

use onsa_diag::{Applied, Code, Diagnostic, FileId, Fix, SourceMap, Span};
use onsa_driver::reduce::Unit;
use onsa_driver::{Analyzed, Loaded, PackageInput, SourceFile};
use onsa_syntax::TokenKind;

use crate::case::{Case, CaseKind, Setup};
use crate::fragment::Mode;
use crate::run::Problem;

/// A `[[test.fix]]` entry of a case's fragment: what one candidate leaves
/// after it, or what more it promises.
///
/// ```text
/// // [[test.fix]]
/// // at = "22:22"              # the original diagnostic ("src/a.onsa:22:22" in a package)
/// // code = "E0020"
/// // candidate = 1
/// // leaves = ["22:30 E0020"]  # after the candidate, in the touched units (default: none)
/// // clean = true              # the check after it reports nothing at all (S-253)
/// // same_code = true          # the tokens but comments and the line breaks between them stay (S-247)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixSpec {
    pub at: String,
    pub code: String,
    pub candidate: u32,
    pub leaves: Vec<String>,
    pub clean: bool,
    pub same_code: bool,
    /// The line of the entry in the file ([`locate`]).
    pub line: usize,
    at_offset: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSpec {
    at: String,
    code: String,
    candidate: u32,
    #[serde(default)]
    leaves: Vec<String>,
    #[serde(default)]
    clean: bool,
    #[serde(default)]
    same_code: bool,
}

/// Read `[[test.fix]]`, keeping where each entry starts.
pub fn de_specs<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<FixSpec>, D::Error> {
    let raw: Vec<toml::Spanned<RawSpec>> = Vec::deserialize(d)?;
    Ok(raw
        .into_iter()
        .map(|r| {
            let at_offset = r.span().start;
            let r = r.into_inner();
            FixSpec {
                at: r.at,
                code: r.code,
                candidate: r.candidate,
                leaves: r.leaves,
                clean: r.clean,
                same_code: r.same_code,
                line: 0,
                at_offset,
            }
        })
        .collect())
}

/// Turn the offsets of [`de_specs`] into lines of `toml_text` (which keeps the
/// lines of the file).
pub fn locate(specs: &mut [FixSpec], toml_text: &str) {
    for s in specs {
        s.line = toml_text[..s.at_offset.min(toml_text.len())].matches('\n').count() + 1;
    }
}

/// A place in a case: the file as the case's source map names it (`None`: the
/// one file of a single-file case), the line and the column (from 1).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Place {
    pub file: Option<String>,
    pub line: u32,
    pub col: u32,
}

impl Place {
    /// `<line>:<col>` or `<file>:<line>:<col>`.
    pub fn parse(s: &str) -> Result<Place, String> {
        let bad = || format!("`{s}` is not `<line>:<col>` or `<file>:<line>:<col>` (from 1)");
        let mut parts = s.rsplitn(3, ':');
        let col = parts.next().ok_or_else(bad)?;
        let line = parts.next().ok_or_else(bad)?;
        let file = parts.next();
        let num = |t: &str| -> Result<u32, String> {
            if t.is_empty() || !t.bytes().all(|b| b.is_ascii_digit()) || t.starts_with('0') {
                return Err(bad());
            }
            t.parse().map_err(|_| bad())
        };
        if file.is_some_and(|f| f.is_empty() || f.trim() != f) {
            return Err(bad());
        }
        Ok(Place { file: file.map(str::to_string), line: num(line)?, col: num(col)? })
    }

    fn show(&self) -> String {
        match &self.file {
            Some(f) => format!("{f}:{}:{}", self.line, self.col),
            None => format!("{}:{}", self.line, self.col),
        }
    }
}

/// A `leaves` item: `<place> <code>`.
fn parse_leaf(s: &str) -> Result<(Place, Code), String> {
    let (place, code) = s.split_once(' ').ok_or_else(|| format!("`{s}` is not `<line>:<col> <code>`"))?;
    let code = Code::parse(code).ok_or_else(|| format!("`{s}`: unknown code `{code}`"))?;
    Ok((Place::parse(place)?, code))
}

/// The checks of the entries that need no run (an error of the case).
pub fn check_specs(specs: &[FixSpec], mode: Mode) -> Result<(), String> {
    if let Some(s) = specs.first()
        && matches!(mode, Mode::None | Mode::Parse)
    {
        return Err(format!(
            "line {}: [[test.fix]] needs `mode = \"check\"` or `\"test\"` (not {mode:?}): the candidates are checked \
             again only there",
            s.line
        ));
    }
    for (i, s) in specs.iter().enumerate() {
        let at = |m: String| format!("line {}: [[test.fix]]: {m}", s.line);
        Place::parse(&s.at).map_err(|e| at(format!("at: {e}")))?;
        if Code::parse(&s.code).is_none() {
            return Err(at(format!("code: unknown code `{}`", s.code)));
        }
        if s.candidate == 0 {
            return Err(at("candidate: the candidates count from 1".into()));
        }
        let mut leaves = Vec::new();
        for l in &s.leaves {
            let leaf = parse_leaf(l).map_err(|e| at(format!("leaves: {e}")))?;
            if leaves.contains(&leaf) {
                return Err(at(format!("leaves: `{l}` is written twice")));
            }
            leaves.push(leaf);
        }
        if s.clean && !s.leaves.is_empty() {
            return Err(at("`clean` leaves nothing at all; it cannot have `leaves`".into()));
        }
        if s.leaves.is_empty() && !s.clean && !s.same_code {
            return Err(at(
                "the entry says only the default (nothing left in the touched units); write `leaves`, `clean` or \
                 `same_code`, or remove it"
                    .into(),
            ));
        }
        if let Some(o) = specs[..i].iter().find(|o| o.at == s.at && o.code == s.code && o.candidate == s.candidate) {
            return Err(at(format!("the same candidate as the entry on line {}", o.line)));
        }
    }
    Ok(())
}

/// What [`check`] found in a case.
#[derive(Debug, Clone, Default)]
pub struct Checked {
    /// Every candidate checked again, by its name in `tests/pending.toml`.
    pub targets: Vec<String>,
    pub problems: Vec<Problem>,
}

/// The files of a case: their id, their name in the source map, and their
/// path from the repository root (the name of a candidate).
struct Files {
    list: Vec<(FileId, String, String)>,
    package: bool,
}

impl Files {
    fn of(case: &Case, loaded: &Loaded) -> Files {
        let list = loaded
            .modules
            .iter()
            .map(|(id, _)| {
                let name = loaded.sources.file(*id).name().to_string();
                let rel = match case.kind {
                    CaseKind::File => case.path.clone(),
                    CaseKind::Package => format!("{}/{name}", case.path),
                };
                (*id, name, rel)
            })
            .collect();
        Files { list, package: case.kind == CaseKind::Package }
    }

    fn has(&self, f: FileId) -> bool {
        self.list.iter().any(|(id, _, _)| *id == f)
    }

    /// The place of `span`'s start as the entries write it.
    fn place(&self, sources: &SourceMap, span: Span) -> Place {
        let f = sources.file(span.file);
        let lc = f.line_col(span.start);
        Place { file: self.package.then(|| f.name().to_string()), line: lc.line, col: lc.col }
    }

    /// The name of candidate `k` of `d` in `tests/pending.toml`.
    fn target(&self, sources: &SourceMap, d: &Diagnostic, k: usize) -> String {
        let name = sources.file(d.span.file).name();
        let rel = self.list.iter().find(|(id, _, _)| *id == d.span.file).map_or(name, |(_, _, r)| r.as_str());
        target_name(rel, sources, d, k)
    }
}

/// The name of candidate `k` of `d` in `tests/pending.toml` (kind
/// `fix-contract`), with `file` the path of its file from the repository
/// root: `<file>:<line>:<col> <code> fix<K>`. The one place of the form.
fn target_name(file: &str, sources: &SourceMap, d: &Diagnostic, k: usize) -> String {
    let lc = sources.file(d.span.file).line_col(d.span.start);
    format!("{file}:{}:{} {} fix{k}", lc.line, lc.col, d.code.as_str())
}

/// Check every candidate of the check's diagnostics `analyzed` of a case (the
/// module's documentation). `loaded` is the case as it ran.
pub fn check(case: &Case, setup: &Setup, loaded: &Loaded, analyzed: &Analyzed) -> Checked {
    let files = Files::of(case, loaded);
    let mut out = Checked::default();
    let specs = &setup.test.fix;
    let mut used = vec![false; specs.len()];
    for s in specs {
        if Place::parse(&s.at).is_ok_and(|p| p.file.is_some() != files.package) {
            out.problems.push(Problem::Case(format!(
                "line {}: [[test.fix]]: at `{}`: {}",
                s.line,
                s.at,
                if files.package {
                    "a package names the file (`src/a.onsa:3:5`)"
                } else {
                    "a single-file case writes `<line>:<col>`"
                }
            )));
        }
    }
    for d in &analyzed.diagnostics {
        let place = files.place(&loaded.sources, d.span);
        for (k0, fix) in d.fixes.iter().enumerate() {
            let k = k0 + 1;
            let target = files.target(&loaded.sources, d, k);
            let spec = specs.iter().position(|s| {
                Place::parse(&s.at).is_ok_and(|p| p == place) && s.code == d.code.as_str() && s.candidate as usize == k
            });
            if let Some(i) = spec {
                used[i] = true;
            }
            let Some(rank) = d.stage.check_rank() else {
                out.problems.push(unchecked_stage(&target, d));
                continue;
            };
            let after = match recheck(setup, loaded, &files, fix) {
                Ok(a) => a,
                Err(why) => {
                    out.problems.push(Problem::FixUnchecked(format!("{target} `{}`: {why}", fix.title())));
                    continue;
                }
            };
            out.targets.push(target.clone());
            let spec = spec.map(|i| &specs[i]);
            for message in judge(&files, rank, &after, spec) {
                out.problems.push(Problem::FixContract {
                    target: target.clone(),
                    message: format!("fix candidate {target} `{}`: {message}", fix.title()),
                });
            }
            if spec.is_some_and(|s| s.same_code) {
                for (file, text) in &after.applied.texts {
                    if let Some(diff) = code_difference(loaded.sources.file(*file).text(), text) {
                        out.problems.push(Problem::FixContract {
                            target: target.clone(),
                            message: format!(
                                "fix candidate {target} `{}`: `same_code`: in {}, {diff}",
                                fix.title(),
                                loaded.sources.file(*file).name()
                            ),
                        });
                    }
                }
            }
        }
    }
    for (s, used) in specs.iter().zip(used) {
        if !used {
            out.problems.push(Problem::Case(format!(
                "line {}: [[test.fix]]: no diagnostic {} at {} with a candidate {} (the check reports {})",
                s.line,
                s.code,
                s.at,
                s.candidate,
                describe(&files, &loaded.sources, &analyzed.diagnostics)
            )));
        }
    }
    out
}

/// A candidate of a diagnostic whose stage the runner cannot check again
/// (lowering, the build, `onsa test`, the manifest): never pending, so the
/// work that makes the first such candidate widens the check (W3-17).
pub fn unchecked_stage(target: &str, d: &Diagnostic) -> Problem {
    Problem::FixUnchecked(format!(
        "{target}: a candidate of the {} stage, which the runner cannot check again (only the check stages \
         are; extend `onsa_tests::fix_contract` first)",
        d.stage.name()
    ))
}

/// The candidates of diagnostics outside the check (the build of a target,
/// `onsa test`): each is [`unchecked_stage`].
pub fn unchecked(sources: &SourceMap, diagnostics: &[Diagnostic]) -> Vec<Problem> {
    let mut out = Vec::new();
    for d in diagnostics {
        for k in 1..=d.fixes.len() {
            out.push(unchecked_stage(&target_name(sources.file(d.span.file).name(), sources, d, k), d));
        }
    }
    out
}

/// The candidates of the diagnostics of a `mode = "parse"` case, where the
/// runner does not check candidates again: each fails, never silenced, so
/// that no candidate passes unchecked (W3-17).
pub fn unchecked_in_parse(sources: &SourceMap, diagnostics: &[Diagnostic]) -> Vec<Problem> {
    let mut out = Vec::new();
    for d in diagnostics {
        for k in 1..=d.fixes.len() {
            out.push(Problem::FixUnchecked(format!(
                "{}: a candidate in a `mode = \"parse\"` case, which the runner does not check again (make the \
                 case `mode = \"check\"`)",
                target_name(sources.file(d.span.file).name(), sources, d, k)
            )));
        }
    }
    out
}

/// The case after one candidate, checked again.
struct After {
    loaded: Loaded,
    analyzed: Analyzed,
    applied: Applied,
}

/// Apply `fix` alone to the case's files and check the case again, through
/// the case's own entry. `Err`: why it cannot be checked.
fn recheck(setup: &Setup, loaded: &Loaded, files: &Files, fix: &Fix) -> Result<After, String> {
    if let Some(e) = fix.edits().iter().find(|e| !files.has(e.span.file)) {
        return Err(format!("it edits {}, a file outside the case", loaded.sources.file(e.span.file).name()));
    }
    let applied = onsa_diag::apply_mapped(&loaded.sources, fix.edits()).map_err(|e| format!("cannot apply it: {e}"))?;
    let mut input: PackageInput = setup.input.clone();
    for ((id, _), f) in loaded.modules.iter().zip(input.files.iter_mut()) {
        if let Some(t) = applied.texts.get(id) {
            f.text = t.clone();
        }
    }
    let mut again = Loaded::from_input(input);
    if again.modules.iter().map(|(f, _)| *f).ne(loaded.modules.iter().map(|(f, _)| *f)) {
        return Err("the files of the case have other ids when loaded again".into());
    }
    let analyzed = onsa_driver::analyze_loaded(&mut again).map_err(|e| {
        format!(
            "the check after it ends in an internal error: {}",
            e.render(&again.sources).trim_end().replace('\n', "\n  ")
        )
    })?;
    Ok(After { loaded: again, analyzed, applied })
}

/// Whether `[a, b]` and `[c, d]` meet, both ends included.
fn meet(a: Span, b: Span) -> bool {
    a.file == b.file && a.start <= b.end && b.start <= a.end
}

/// The units the replacements `ranges` touch (the module's documentation, 2).
// SPEC-GAP(S-302): "the units the edits touch" is read as the units of the text
// after the candidate whose range meets a replacement, both ends included (so a
// unit that only borders a replacement counts too). A candidate that takes code
// after it into its replacement and moves the border of the units (a block
// comment before `pub fn`, turned into `//`) is not seen, until S-302.
fn touched(units: &[Unit], ranges: &[Span]) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    for r in ranges {
        for (u, unit) in units.iter().enumerate() {
            if !meet(unit.span, *r) {
                continue;
            }
            let in_member = units.iter().any(|m| {
                m.parent == Some(u) && m.span.file == r.file && m.span.start <= r.start && r.end <= m.span.end
            });
            if !in_member {
                out.insert(u);
            }
        }
    }
    out
}

/// What breaks the contract after one candidate (the module's documentation, 3).
fn judge(files: &Files, rank: usize, after: &After, spec: Option<&FixSpec>) -> Vec<String> {
    let sources = &after.loaded.sources;
    let ranges = &after.applied.ranges;
    let units = touched(&after.analyzed.units, ranges);
    let mut left: Vec<(Place, Code)> = Vec::new();
    let mut shown = Vec::new();
    for (d, unit) in after.analyzed.diagnostics.iter().zip(&after.analyzed.diagnostic_units) {
        // SPEC-GAP(S-267): where the flow checks sit in the order decides whether a candidate
        // of a flow code may leave a modes or effects diagnostic (`Stage::CHECK_ORDER`).
        if d.stage.check_rank().is_none_or(|r| r > rank) {
            continue;
        }
        let hit = match unit {
            Some(u) => units.contains(u),
            None => files.has(d.span.file) && ranges.iter().any(|r| meet(*r, d.span)),
        };
        if hit {
            left.push((files.place(sources, d.span), d.code));
            shown.push(d.clone());
        }
    }
    left.sort();
    let mut out = Vec::new();
    let mut expected: Vec<(Place, Code)> = Vec::new();
    for l in spec.map_or(&[][..], |s| &s.leaves[..]) {
        // The fragment's reader checked the form already (`check_specs`).
        match parse_leaf(l) {
            Ok(leaf) => expected.push(leaf),
            Err(e) => out.push(format!("`leaves`: {e}")),
        }
    }
    expected.sort();
    let show = |v: &[(Place, Code)]| {
        if v.is_empty() {
            "none".to_string()
        } else {
            v.iter().map(|(p, c)| format!("{} {}", p.show(), c.as_str())).collect::<Vec<_>>().join(", ")
        }
    };
    if left != expected {
        out.push(format!(
            "after it, the units its edits touch hold {} of its stage or an earlier one; expected {}{}\n  {}",
            show(&left),
            show(&expected),
            if spec.is_some() { " (`leaves`)" } else { " (it is the only error of its unit)" },
            onsa_diag::to_text(sources, &shown).trim_end().replace('\n', "\n  ")
        ));
    }
    if spec.is_some_and(|s| s.clean) && !after.analyzed.diagnostics.is_empty() {
        out.push(format!(
            "`clean`: the check after it reports {}",
            describe(files, sources, &after.analyzed.diagnostics)
        ));
    }
    out
}

/// The diagnostics, briefly: `E0020 at 3:5, E0401 at 7:1`, or `nothing`.
fn describe(files: &Files, sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    if diagnostics.is_empty() {
        return "nothing".into();
    }
    diagnostics
        .iter()
        .map(|d| format!("{} at {}", d.code.as_str(), files.place(sources, d.span).show()))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The code of a text for `same_code`: every token but whitespace, newlines
/// and comments, with whether a line break lies between it and the token
/// before it (not before the first one: a comment may move above the first
/// line).
fn code_shape(text: &str) -> Vec<(TokenKind, &str, bool)> {
    let mut out = Vec::new();
    let mut line_break = false;
    for t in onsa_syntax::lex(FileId(0), text).tokens {
        match t.kind {
            TokenKind::Newline => line_break = true,
            TokenKind::Whitespace | TokenKind::Comment | TokenKind::DocComment | TokenKind::Eof => {}
            kind => {
                let first = out.is_empty();
                out.push((kind, &text[t.span.start as usize..t.span.end as usize], line_break && !first));
                line_break = false;
            }
        }
    }
    out
}

/// Where the code of `after` first differs from that of `before` (`same_code`, S-247).
fn code_difference(before: &str, after: &str) -> Option<String> {
    let (b, a) = (code_shape(before), code_shape(after));
    let i = (0..b.len().max(a.len())).find(|&i| b.get(i) != a.get(i))?;
    let token = |t: Option<&(TokenKind, &str, bool)>| t.map_or("the end".to_string(), |t| format!("`{}`", t.1));
    let (x, y) = (b.get(i), a.get(i));
    if x.map(|t| (t.0, t.1)) == y.map(|t| (t.0, t.1)) {
        let lb = |t: Option<&(TokenKind, &str, bool)>| if t.is_some_and(|t| t.2) { "a line break" } else { "none" };
        return Some(format!(
            "before {} (token {}): the line break changed: {} before, {} after",
            token(x),
            i + 1,
            lb(x),
            lb(y)
        ));
    }
    Some(format!("token {}: {} before, {} after (the code but comments changed)", i + 1, token(x), token(y)))
}

// ------------------------------------------------------------ the fuzzing

/// One violation of the near "same place" ([`same_place`]).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Violation {
    /// The original diagnostic.
    pub code: String,
    pub line: u32,
    pub col: u32,
    /// The title of its first candidate.
    pub title: String,
    /// The code of the diagnostic at the same place after it, or `internal`
    /// when the check after it ends in an internal error.
    pub left: String,
    pub left_line: Option<u32>,
    pub left_col: Option<u32>,
    pub message: String,
}

/// What [`same_place`] found in one file.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize)]
pub struct SamePlace {
    /// The candidates checked again.
    pub candidates: usize,
    pub violations: Vec<Violation>,
    /// The check of the file itself ended in an internal error (the fuzzing's
    /// own run of `onsa check` reports it).
    pub internal: Option<String>,
}

/// The near "same place" of S-236 for the fuzzing, which cannot know how many
/// errors an input holds: the file `text` checked as a single-file package
/// (as `onsa check` checks it); for each diagnostic, its first candidate
/// alone applied and the file checked again. A violation is a diagnostic of
/// the check after it, of the original's stage or an earlier one, whose
/// start lies in the same place: the original diagnostic's range or a
/// replacement, both moved to the text after it
/// ([`onsa_diag::Applied::map_span`]). An error the input held there before
/// is not one (the input has two errors there, as a stray `1.` at the top
/// level, an E0020 and an E0002): a diagnostic of the same code and message
/// among every diagnostic the stages found before the choice of one per
/// unit, but the original, whose start moves into the same place. One of the
/// original's own code inside the original's range is no other error, though:
/// it is a part of the same form, which the candidate must fix whole (S-248;
/// the inner `--x` of `---x`), and stays a violation. The diagnostics are
/// compared by code, range and message (`found` is filled in only after the
/// choice per unit). The units are not used: this is a net for new kinds,
/// not the contract.
pub fn same_place(text: &str) -> SamePlace {
    let input = |text: String| PackageInput {
        manifest: None,
        files: vec![SourceFile { path: "m.onsa".into(), text }],
        root: None,
    };
    let mut loaded = Loaded::from_input(input(text.to_string()));
    let analyzed = match onsa_driver::analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(e) => return SamePlace { internal: Some(e.render(&loaded.sources)), ..SamePlace::default() },
    };
    let mut out = SamePlace::default();
    for d in &analyzed.diagnostics {
        let Some(fix) = d.fixes.first() else { continue };
        let lc = loaded.sources.file(d.span.file).line_col(d.span.start);
        let violation = |left: String, at: Option<(u32, u32)>, message: String| Violation {
            code: d.code.as_str().to_string(),
            line: lc.line,
            col: lc.col,
            title: fix.title().to_string(),
            left,
            left_line: at.map(|a| a.0),
            left_col: at.map(|a| a.1),
            message,
        };
        out.candidates += 1;
        // What cannot be checked is a violation of its own kind, never skipped.
        let Some(rank) = d.stage.check_rank() else {
            out.violations.push(violation("unchecked-stage".into(), None, format!("the {} stage", d.stage.name())));
            continue;
        };
        let applied = match onsa_diag::apply_mapped(&loaded.sources, fix.edits()) {
            Ok(a) => a,
            Err(e) => {
                out.violations.push(violation("cannot-apply".into(), None, e));
                continue;
            }
        };
        let Some(new_text) = applied.texts.get(&FileId(0)).filter(|_| applied.texts.len() == 1) else {
            out.violations.push(violation("other-file".into(), None, "it edits a file other than the input".into()));
            continue;
        };
        let mut again = Loaded::from_input(input(new_text.clone()));
        let after = match onsa_driver::analyze_loaded(&mut again) {
            Ok(a) => a,
            Err(e) => {
                out.violations.push(violation("internal".into(), None, e.render(&again.sources)));
                continue;
            }
        };
        let mut places: Vec<Span> = applied.ranges.clone();
        places.push(applied.map_span(d.span));
        let in_place = |s: Span| places.iter().any(|p| p.file == s.file && p.start <= s.start && s.start <= p.end);
        for d2 in &after.diagnostics {
            if d2.stage.check_rank().is_none_or(|r| r > rank) || !in_place(d2.span) {
                continue;
            }
            let same = |a: &Diagnostic, b: &Diagnostic| a.code == b.code && a.span == b.span && a.message == b.message;
            let held_before = found_before(&analyzed).any(|o| {
                let part_of_the_form = o.code == d.code
                    && o.span.file == d.span.file
                    && d.span.start <= o.span.start
                    && o.span.end <= d.span.end;
                !same(o, d)
                    && !part_of_the_form
                    && o.code == d2.code
                    && o.message == d2.message
                    && in_place(applied.map_span(o.span))
            });
            if held_before {
                continue;
            }
            let lc2 = again.sources.file(d2.span.file).line_col(d2.span.start);
            out.violations.push(violation(d2.code.as_str().to_string(), Some((lc2.line, lc2.col)), d2.message.clone()));
        }
    }
    out
}

/// Every diagnostic the stages found, before the choice of one per unit.
fn found_before(a: &Analyzed) -> impl Iterator<Item = &Diagnostic> {
    a.pkg.modules.iter().flat_map(|m| m.parsed.diagnostics.iter()).chain(a.analysis.diagnostics.iter())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn places_and_leaves() {
        assert_eq!(Place::parse("3:5").unwrap(), Place { file: None, line: 3, col: 5 });
        assert_eq!(Place::parse("src/a.onsa:3:5").unwrap(), Place { file: Some("src/a.onsa".into()), line: 3, col: 5 });
        for bad in ["3", "3:", ":5", "0:1", "1:0", "03:1", "a:b", ":3:5", "x :3:5", "3:5 "] {
            assert!(Place::parse(bad).is_err(), "{bad}");
        }
        assert_eq!(parse_leaf("22:30 E0020").unwrap(), (Place { file: None, line: 22, col: 30 }, Code::E0020));
        assert!(parse_leaf("22:30").is_err());
        assert!(parse_leaf("22:30 E9999").is_err());
    }

    fn spec(at: &str, leaves: &[&str], clean: bool, same_code: bool) -> FixSpec {
        FixSpec {
            at: at.into(),
            code: "E0020".into(),
            candidate: 1,
            leaves: leaves.iter().map(|s| s.to_string()).collect(),
            clean,
            same_code,
            line: 5,
            at_offset: 0,
        }
    }

    #[test]
    fn entries_that_say_nothing_or_contradict_are_errors() {
        assert!(check_specs(&[spec("3:5", &["3:9 E0020"], false, false)], Mode::Check).is_ok());
        assert!(check_specs(&[spec("3:5", &[], true, false)], Mode::Test).is_ok());
        assert!(check_specs(&[spec("3:5", &[], false, true)], Mode::Check).is_ok());
        let e = |specs: &[FixSpec], mode: Mode| check_specs(specs, mode).unwrap_err();
        assert!(e(&[spec("3:5", &[], false, false)], Mode::Check).contains("only the default"));
        assert!(e(&[spec("3:5", &["3:9 E0020"], true, false)], Mode::Check).contains("cannot have `leaves`"));
        assert!(e(&[spec("3:5", &[], true, false)], Mode::Parse).contains("needs `mode"));
        assert!(e(&[spec("3:5", &["3:9 E0020", "3:9 E0020"], false, false)], Mode::Check).contains("twice"));
        assert!(e(&[spec("x", &[], true, false)], Mode::Check).contains("at:"));
        let mut zero = spec("3:5", &[], true, false);
        zero.candidate = 0;
        assert!(e(&[zero], Mode::Check).contains("from 1"));
        let two = [spec("3:5", &[], true, false), spec("3:5", &[], false, true)];
        assert!(e(&two, Mode::Check).contains("the same candidate"));
    }

    #[test]
    fn same_code_ignores_comments_and_their_lines_but_not_code_or_line_breaks() {
        let before = "let a = 1 /* one */ + 2\n";
        assert_eq!(code_difference(before, "let a = 1 + 2 // one\n"), None, "moved to the end of the line");
        assert_eq!(code_difference(before, "// one\nlet a = 1 + 2\n"), None, "moved above the line");
        assert!(code_difference(before, "let a = 1 // one + 2\n").is_some(), "the code went into the comment");
        assert!(code_difference(before, "let a = 1\n+ 2 // one\n").is_some(), "a line break added");
        assert!(code_difference("a\nb\n", "a b\n").is_some(), "a line break removed");
        assert_eq!(code_difference("a\n\nb\n", "a\nb\n"), None, "one line break or more");
        assert!(code_difference("a\n", "a b\n").unwrap().contains("`b`"));
    }

    fn units(spans: &[(u32, u32, Option<usize>)]) -> Vec<Unit> {
        spans.iter().map(|&(s, e, p)| Unit { span: Span::new(FileId(0), s, e), parent: p }).collect()
    }

    #[test]
    fn touched_units_meet_the_replacements_and_skip_the_parent_inside_a_member() {
        // 0: an item 0..10; 1: an impl 20..60 with members 2 (25..35) and 3 (40..50).
        let us = units(&[(0, 10, None), (20, 60, None), (25, 35, Some(1)), (40, 50, Some(1))]);
        let r = |s: u32, e: u32| Span::new(FileId(0), s, e);
        let t = |rs: &[Span]| touched(&us, rs).into_iter().collect::<Vec<_>>();
        assert_eq!(t(&[r(3, 4)]), [0]);
        assert_eq!(t(&[r(10, 10)]), [0], "a deletion at the end of a unit");
        assert_eq!(t(&[r(12, 15)]), Vec::<usize>::new(), "between the units");
        assert_eq!(t(&[r(27, 29)]), [2], "inside a member: not its impl");
        assert_eq!(t(&[r(21, 22)]), [1], "the heading of the impl");
        assert_eq!(t(&[r(30, 42)]), [1, 2, 3], "over two members and the impl between them");
        assert_eq!(t(&[r(3, 4), r(45, 45)]), [0, 3], "every replacement");
        let other = Span::new(FileId(1), 3, 4);
        assert_eq!(t(&[other]), Vec::<usize>::new(), "another file");
    }

    #[test]
    fn same_place_finds_a_diagnostic_left_where_the_candidate_was() {
        // `let mut` (E0020) gives `var`: nothing left.
        let ok = same_place("pub fn f() -> I32 {\n  let mut n = 0\n  n\n}\n");
        assert_eq!(ok.candidates, 1, "{ok:?}");
        assert!(ok.violations.is_empty(), "{ok:?}");
        assert!(ok.internal.is_none());
        // No diagnostic: nothing to check.
        assert_eq!(same_place("pub fn f() -> I32 {\n  1\n}\n"), SamePlace::default());
        // The candidate of the E0010 gives `x >= (0 && x) < 9`: an E0010 is left there (R-72).
        let left = same_place("pub fn f(x: I32) -> Bool {\n  x >= 0 && x < 9\n}\n");
        assert_eq!(left.candidates, 1);
        let v: Vec<(&str, &str, Option<u32>)> =
            left.violations.iter().map(|v| (v.code.as_str(), v.left.as_str(), v.left_line)).collect();
        assert_eq!(v, [("E0010", "E0010", Some(2))], "{left:?}");
        // The inner `--x` of `---x` is a part of the one form (S-248): left, it is a violation.
        let form = same_place("pub fn f(x: I32) -> I32 {\n  ---x\n}\n");
        let v: Vec<(&str, &str)> = form.violations.iter().map(|v| (v.code.as_str(), v.left.as_str())).collect();
        assert_eq!(v, [("E0012", "E0012")], "{form:?}");
        // A stray `1.` holds two errors (E0020 and E0002): the E0002 left after `1.0` was there before.
        let stray = same_place("1.\n");
        assert_eq!(stray.candidates, 1, "{stray:?}");
        assert!(stray.violations.is_empty(), "{stray:?}");
    }
}
