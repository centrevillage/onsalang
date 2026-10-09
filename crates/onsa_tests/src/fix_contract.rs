//! The contract of the fix candidates (spec §18.1; S-236, S-247, S-248,
//! S-266, S-302, S-314; W3-17, W3-15).
//!
//! §18.1: "every candidate, applied alone and checked again, leaves no
//! diagnostic of the same or an earlier stage in any unit it touches after
//! it, when the original diagnostic was the only error of that stage or
//! earlier in every unit it touches before it"; and "the lexical reading of
//! the text outside its edits does not change". The runner checks it on
//! every candidate of every diagnostic of every case of `mode = "check"` or
//! `"test"` ([`check`]):
//!
//! 1. the candidate alone is applied to the case's files
//!    ([`onsa_diag::apply_mapped`]), and the case runs again through the same
//!    entry as the case (`Loaded::from_input`, `analyze_loaded`, plan D-05);
//! 2. the units it touches (S-302) are the units of the check after it but
//!    the untouched ones: a unit of the check before it (the driver's table,
//!    `Analyzed::units`; never computed here, D-15) whose characters no edit
//!    replaces and no insertion falls inside (for a unit with members, its
//!    characters outside them), and whose range, moved by the edits before
//!    it, is a unit after it too. The unit of the original diagnostic is not
//!    added (S-266: the edits alone decide). One definition serves the
//!    premise and the promise (S-314): the runner does not compute the
//!    premise; a case whose touched units hold other errors before the
//!    candidate says what is left with `leaves`;
//! 3. the diagnostics the check after it reports in those units, of the
//!    stage of the original diagnostic or an earlier one (the order of
//!    [`onsa_diag::Stage::CHECK_ORDER`]), are the ones the case expects:
//!    none by default (the reported diagnostic is the only error of its unit,
//!    S-236; one syntactic form is one error, S-248), else the `leaves` of a
//!    `[[test.fix]]` entry ([`FixSpec`]). A diagnostic outside every unit
//!    counts when it meets a replacement. Later stages are not looked at;
//! 4. the tokens and comments outside the edits are read the same after it
//!    (kind and range, moved by the edits before them; blanks are not
//!    compared, and an insertion at an end of a token is not inside it,
//!    [`reading_difference`]).
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
use onsa_syntax::Token;
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
            let edits = moved(fix, &after.applied);
            for (file, text) in &after.applied.texts {
                if let Some(diff) = reading_difference(loaded.sources.file(*file).text(), text, *file, &edits) {
                    out.problems.push(Problem::FixContract {
                        target: target.clone(),
                        message: format!(
                            "fix candidate {target} `{}`: the reading outside its edits changed: in {}, {diff}",
                            fix.title(),
                            loaded.sources.file(*file).name()
                        ),
                    });
                }
            }
            for message in judge(&files, rank, &analyzed.units, &edits, &after, spec) {
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

/// One edit of a candidate: its range before it, and the length of its
/// replacement after it.
#[derive(Debug, Clone, Copy)]
struct Moved {
    before: Span,
    /// The range of its replacement after the candidate.
    after: Span,
}

/// The edits of `fix` as `applied` placed them.
fn moved(fix: &Fix, applied: &Applied) -> Vec<Moved> {
    fix.edits().iter().zip(&applied.ranges).map(|(e, r)| Moved { before: e.span, after: *r }).collect()
}

/// Where the offset `at` of `file` lies after the edits: moved by the length
/// differences of the edits before it. An insertion at `at` is before a
/// `start` and after an end (an insertion at an end of a range is not inside
/// it; [`Applied::map_span`] puts it inside, so it is not used here, S-302).
fn shift(edits: &[Moved], file: FileId, at: u32, start: bool) -> u32 {
    let mut delta: i64 = 0;
    for e in edits.iter().filter(|e| e.before.file == file) {
        let b = e.before;
        let before = if b.is_empty() { b.start < at || (start && b.start == at) } else { b.end <= at };
        if before {
            delta += e.after.len() as i64 - b.len() as i64;
        }
    }
    (at as i64 + delta) as u32
}

/// Whether the edit range `edit` falls in `range`: it replaces a character of
/// it, or it is an insertion strictly inside it.
fn falls_in(edit: Span, range: Span) -> bool {
    edit.file == range.file
        && if edit.is_empty() {
            range.start < edit.start && edit.start < range.end
        } else {
            edit.start < range.end && range.start < edit.end
        }
}

/// The units a candidate touches (the module's documentation, 2; S-302): the
/// indexes of `after` but those of the untouched units of `before`.
fn touched(before: &[Unit], after: &[Unit], edits: &[Moved]) -> BTreeSet<usize> {
    let mut untouched = BTreeSet::new();
    for (u, unit) in before.iter().enumerate() {
        let members: Vec<Span> = before.iter().filter(|m| m.parent == Some(u)).map(|m| m.span).collect();
        // An edit inside a member touches the member, not the item.
        let in_member = |e: Span| {
            members.iter().any(|m| {
                m.file == e.file
                    && if e.is_empty() {
                        m.start < e.start && e.start < m.end
                    } else {
                        m.start <= e.start && e.end <= m.end
                    }
            })
        };
        if edits.iter().any(|e| falls_in(e.before, unit.span) && !in_member(e.before)) {
            continue;
        }
        let s = unit.span;
        let moved = Span::new(s.file, shift(edits, s.file, s.start, true), shift(edits, s.file, s.end, false));
        if let Some(a) = after.iter().position(|x| x.span == moved) {
            untouched.insert(a);
        }
    }
    (0..after.len()).filter(|a| !untouched.contains(a)).collect()
}

/// Where the lexical reading of the text outside the edits differs before
/// and after a candidate (the module's documentation, 4; S-302): the tokens
/// and comments no edit falls in, but blanks, with their kinds and ranges
/// (those before moved by the edits before them), in the order of the text.
fn reading_difference(before: &str, after: &str, file: FileId, edits: &[Moved]) -> Option<String> {
    let blank = |t: &Token| matches!(t.kind, TokenKind::Whitespace | TokenKind::Newline | TokenKind::Eof);
    let mine: Vec<Moved> = edits.iter().copied().filter(|e| e.before.file == file).collect();
    let old: Vec<(TokenKind, u32, u32)> = onsa_syntax::lex(file, before)
        .tokens
        .iter()
        .filter(|t| !blank(t) && !mine.iter().any(|e| falls_in(e.before, t.span)))
        .map(|t| (t.kind, shift(&mine, file, t.span.start, true), shift(&mine, file, t.span.end, false)))
        .collect();
    // The ranges of the replacements after the candidate.
    let new_ranges: Vec<Span> = mine.iter().map(|e| e.after).collect();
    let new: Vec<(TokenKind, u32, u32)> = onsa_syntax::lex(file, after)
        .tokens
        .iter()
        .filter(|t| !blank(t) && !new_ranges.iter().any(|r| falls_in(*r, t.span)))
        .map(|t| (t.kind, t.span.start, t.span.end))
        .collect();
    let i = (0..old.len().max(new.len())).find(|&i| old.get(i) != new.get(i))?;
    let show = |text: &str, t: Option<&(TokenKind, u32, u32)>| {
        t.map_or("nothing".to_string(), |&(k, s, e)| format!("{k:?} `{}` at {s}..{e}", &text[s as usize..e as usize]))
    };
    Some(format!("token {} outside the edits: {} after, {} expected", i + 1, show(after, new.get(i)), {
        let t = old.get(i);
        t.map_or("nothing".to_string(), |&(k, s, e)| format!("{k:?} at {s}..{e}"))
    }))
}

/// What breaks the contract after one candidate (the module's documentation, 3).
fn judge(
    files: &Files,
    rank: usize,
    before: &[Unit],
    edits: &[Moved],
    after: &After,
    spec: Option<&FixSpec>,
) -> Vec<String> {
    let sources = &after.loaded.sources;
    let ranges = &after.applied.ranges;
    let units = touched(before, &after.analyzed.units, edits);
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
/// and comments (block comments too: they are what a candidate of S-247
/// rewrites), with whether a line break lies between it and the token
/// before it (not before the first one: a comment may move above the first
/// line).
fn code_shape(text: &str) -> Vec<(TokenKind, &str, bool)> {
    let mut out = Vec::new();
    let mut line_break = false;
    for t in onsa_syntax::lex(FileId(0), text).tokens {
        match t.kind {
            TokenKind::Newline => line_break = true,
            TokenKind::Whitespace
            | TokenKind::Comment
            | TokenKind::DocComment
            | TokenKind::BlockComment
            | TokenKind::Eof => {}
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

// ------------------------------------------------------------ one file

/// A single-file input checked as `onsa check` checks it (`m.onsa`, no
/// manifest): the entry of the fuzzing and of the examples of the closed
/// list of the forms of other languages ([`crate::foreign_forms`]).
pub struct TextCheck {
    pub loaded: Loaded,
    pub analyzed: Analyzed,
}

fn single_file(text: String) -> PackageInput {
    PackageInput { manifest: None, files: vec![SourceFile { path: "m.onsa".into(), text }], root: None }
}

/// Check `text` as a single-file package. `Err`: the internal error.
pub fn check_text(text: &str) -> Result<TextCheck, String> {
    let mut loaded = Loaded::from_input(single_file(text.to_string()));
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).map_err(|e| e.render(&loaded.sources))?;
    Ok(TextCheck { loaded, analyzed })
}

/// One candidate of a diagnostic of a [`TextCheck`], applied alone and the
/// text checked again.
pub struct CandidateCheck {
    /// The text after it.
    pub text: String,
    /// What the check after it reports.
    pub diagnostics: Vec<Diagnostic>,
    /// How it breaks the contract (the module's documentation, 2 to 4; the
    /// default promise: nothing left in the units it touches).
    pub problems: Vec<String>,
}

/// Apply `fix` of `d` (a diagnostic of `run`) alone and check the text again.
/// `Err`: it cannot be checked (another stage, it does not apply, an
/// internal error after it).
pub fn check_candidate(run: &TextCheck, d: &Diagnostic, fix: &Fix) -> Result<CandidateCheck, String> {
    let rank = d.stage.check_rank().ok_or_else(|| format!("a candidate of the {} stage", d.stage.name()))?;
    let applied = onsa_diag::apply_mapped(&run.loaded.sources, fix.edits())?;
    let file = FileId(0);
    let text = applied.texts.get(&file).filter(|_| applied.texts.len() == 1).cloned();
    let text = text.ok_or("it edits a file other than the input")?;
    let mut again = Loaded::from_input(single_file(text.clone()));
    let analyzed = onsa_driver::analyze_loaded(&mut again).map_err(|e| e.render(&again.sources))?;
    let files = Files { list: vec![(file, "m.onsa".into(), "m.onsa".into())], package: false };
    let edits = moved(fix, &applied);
    let mut problems = Vec::new();
    if let Some(diff) = reading_difference(run.loaded.sources.file(file).text(), &text, file, &edits) {
        problems.push(format!("the reading outside its edits changed: {diff}"));
    }
    let diagnostics = analyzed.diagnostics.clone();
    let after = After { loaded: again, analyzed, applied };
    problems.extend(judge(&files, rank, &run.analyzed.units, &edits, &after, None));
    Ok(CandidateCheck { text, diagnostics, problems })
}

/// Where the code of `after` first differs from that of `before` (the
/// promise `same_code`, S-247): `None` when the same.
pub fn same_code(before: &str, after: &str) -> Option<String> {
    code_difference(before, after)
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
/// errors an input holds (and the reading outside the edits, S-302, with the
/// kind `reading`): the file `text` checked as a single-file package
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
    let input = single_file;
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
        // The reading outside its edits stays (S-302), as in the contract.
        if let Some(diff) = reading_difference(text, new_text, FileId(0), &moved(fix, &applied)) {
            out.violations.push(violation("reading".into(), None, diff));
        }
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
        let in_place = |s: Span| in_same_place(&places, s);
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
                // The same error moved by the edits: its code and its place,
                // not its message, which may quote the source the candidate
                // changed (E0010 quotes its chain).
                let moved = applied.map_span(o.span);
                !same(o, d)
                    && !part_of_the_form
                    && o.code == d2.code
                    && moved.file == d2.span.file
                    && moved.start <= d2.span.end
                    && d2.span.start <= moved.end
                    && in_place(moved)
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

/// Whether the diagnostic at `s` starts in the same place as one of
/// `places` (the near "same place" of [`same_place`]): inside a range that is
/// not empty, half open (`start <= s.start < end`), or at the point of an
/// empty one (what a deletion or an insertion of nothing leaves). An error
/// that starts right at the end of a replacement is not in it: the input held
/// another error there, which the candidate let the check reach (the premise
/// of S-236 does not hold), as an insertion at an end of a token is not
/// inside it (S-302); a change of reading at that border is what the
/// `reading` check finds.
fn in_same_place(places: &[Span], s: Span) -> bool {
    places.iter().any(|p| {
        p.file == s.file && if p.is_empty() { s.start == p.start } else { p.start <= s.start && s.start < p.end }
    })
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

    /// An edit replacing `s..e` of file 0 with `len` characters.
    fn edit(s: u32, e: u32, len: u32) -> Moved {
        Moved { before: Span::new(FileId(0), s, e), after: Span::new(FileId(0), s, s + len) }
    }

    #[test]
    fn touched_units_are_all_but_the_untouched_ones() {
        // S-302. 0: an item 0..10; 1: an impl 20..60 with members 2 (25..35) and 3 (40..50).
        let us = units(&[(0, 10, None), (20, 60, None), (25, 35, Some(1)), (40, 50, Some(1))]);
        let t = |after: &[Unit], es: &[Moved]| touched(&us, after, es).into_iter().collect::<Vec<_>>();
        // A replacement of the same length inside the item: the units after are the same.
        assert_eq!(t(&us, &[edit(3, 4, 1)]), [0]);
        // Between the units: nothing touched, the units after it moved.
        let moved = units(&[(0, 10, None), (22, 62, None), (27, 37, Some(1)), (42, 52, Some(1))]);
        assert_eq!(t(&moved, &[edit(12, 12, 2)]), Vec::<usize>::new());
        // An insertion at a border of a unit is not inside it.
        let moved = units(&[(2, 12, None), (22, 62, None), (27, 37, Some(1)), (42, 52, Some(1))]);
        assert_eq!(t(&moved, &[edit(0, 0, 2)]), Vec::<usize>::new());
        // Inside a member: the member, not its impl (moved by the length difference).
        let longer = units(&[(0, 10, None), (20, 61, None), (25, 36, Some(1)), (41, 51, Some(1))]);
        assert_eq!(t(&longer, &[edit(27, 29, 3)]), [2]);
        // The heading of the impl.
        assert_eq!(t(&us, &[edit(21, 22, 1)]), [1]);
        // A border that moved: a unit after it that is no unit before (S-302: a
        // candidate that takes the next item into a comment); the members keep their range.
        let merged = units(&[(0, 60, None), (25, 35, Some(0)), (40, 50, Some(0))]);
        assert_eq!(t(&merged, &[edit(3, 4, 1)]), [0]);
        // Another file is not touched.
        let other = Moved { before: Span::new(FileId(1), 3, 4), after: Span::new(FileId(1), 3, 4) };
        assert_eq!(t(&us, &[other]), Vec::<usize>::new());
    }

    #[test]
    fn the_same_place_is_half_open_and_a_point_for_an_empty_range() {
        let r = |s: u32, e: u32| Span::new(FileId(0), s, e);
        assert!(in_same_place(&[r(3, 6)], r(3, 4)) && in_same_place(&[r(3, 6)], r(5, 9)));
        assert!(!in_same_place(&[r(3, 6)], r(6, 7)), "the end of a range is not in it");
        assert!(!in_same_place(&[r(3, 6)], r(2, 4)));
        assert!(in_same_place(&[r(4, 4)], r(4, 5)) && !in_same_place(&[r(4, 4)], r(5, 5)));
        let other = Span::new(FileId(1), 3, 4);
        assert!(!in_same_place(&[r(3, 6)], other));
        // The forms it caught still are: `;;` fixed by halves, and `---x` (`--`
        // and `-x`) parenthesized by its first operator alone, were violations
        // inside the original range.
        assert!(in_same_place(&[r(10, 12)], r(11, 12)));
    }

    #[test]
    fn the_reading_outside_the_edits_is_compared() {
        let e = |s: u32, e: u32, len: u32| vec![edit(s, e, len)];
        // `let mut` to `var`: the tokens outside are the same, moved.
        let before = "let mut n = 0\n";
        assert_eq!(reading_difference(before, "var n = 0\n", FileId(0), &[edit(0, 3, 3), edit(4, 8, 0)]), None);
        // A block comment written `//` in place takes the code after it (S-302).
        let before = "let a = 1 /* one */ + 2\n";
        let d = reading_difference(before, "let a = 1 // one + 2\n", FileId(0), &e(10, 19, 6)).unwrap();
        assert!(d.contains("token"), "{d}");
        // Blanks are not compared.
        assert_eq!(reading_difference("a  b\n", "a b\n", FileId(0), &e(1, 3, 1)), None);
        // Two tokens that touch after a deletion are read as one.
        assert!(reading_difference("a /*c*/ b\n", "ab\n", FileId(0), &e(1, 8, 0)).is_some());
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
        // The candidate of the E0411 gives `x.narrow_i32()`, an `Option[I32]`: an E0401 of the
        // same stage is left there (until W5-02).
        let left = same_place("pub fn f(x: I64) -> I32 {\n  x as I32\n}\n");
        assert_eq!(left.candidates, 1);
        let v: Vec<(&str, &str, Option<u32>)> =
            left.violations.iter().map(|v| (v.code.as_str(), v.left.as_str(), v.left_line)).collect();
        assert_eq!(v, [("E0411", "E0401", Some(2))], "{left:?}");
        // An E0010 there before the candidate of the E0011 is not left by it, though its message
        // quotes the chain the candidate changed.
        let before = same_place("pub fn f(a: I32, b: I32) -> I32 {\n  a as I32 * 2 % b\n}\n");
        assert!(before.violations.is_empty(), "{before:?}");
        // A stack of prefix operators is one form, fixed whole (S-248, S-297): nothing left.
        let form = same_place("pub fn f(x: I32) -> I32 {\n  - - -x\n}\n");
        assert_eq!(form.candidates, 1, "{form:?}");
        assert!(form.violations.is_empty(), "{form:?}");
        // A stray `1.` holds two errors at one place (E0020 and E0002); the E0002 is
        // reported (S-281), and it has no candidate.
        let stray = same_place("1.\n");
        assert_eq!(stray.candidates, 0, "{stray:?}");
    }
}
