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
//!    counts when it meets a replacement. Later stages are not looked at
//!    there; but the units after it that held no diagnostic before it (a
//!    rule of the tests, X-3; not of §18.1) hold none of any stage, touched
//!    or not, either ([`Before`], [`correspond`]): a unit after it holds none
//!    before when every unit before it that it comes from (the same range
//!    moved, or one that meets it at its level) is clean, and a new one
//!    (an item the candidate inserts) is clean. A unit is not clean when it
//!    or its item has a diagnostic, or when its check read what the check did
//!    not (a fix of the cause can show an error it held back:
//!    `onsa_driver::Analyzed::unread_units`). What they may hold is written
//!    in `leaves` with the rest;
//! 4. the tokens and comments outside the edits are read the same after it
//!    (kind and range, moved by the edits before them; blanks are not
//!    compared, and an insertion at an end of a token is not inside it,
//!    [`reading_difference`](reading::reading_difference));
//! 5. every edit is minimal, as far as the tokens tell (§18.1: "the edits
//!    replace only the tokens that change", S-251; X-3, X3-1g): the tokens
//!    an edit's range falls in (it replaces a character of them or inserts
//!    strictly inside them; an insertion at an end of a token is not inside
//!    it) and those its replacement falls in after it, comments included and
//!    blanks aside, compared by kind and text ([`not_minimal`](reading::not_minimal)): a comment of
//!    the range written again (the comment belongs outside the edit), the
//!    same first or last token (the edit can be shrunk; an edit that changes
//!    nothing too), or any token in both (the edit is two: `<T>` to `[T]` is
//!    the edits of `<` and `>`). An edit too large in another way (it removes
//!    a whole statement) is not seen here: the copies of the texts after the
//!    candidates (`.fixK`, Q-04) and the parent's review see it.
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
//! near "same place" of S-236 ([`same_place`](fn@same_place), `onsa_cases --fix-same-place`,
//! `tools/fuzz.py`).

use std::collections::BTreeMap;

use onsa_diag::{Applied, Code, Diagnostic, FileId, Fix, SourceMap, Span};
use onsa_driver::{Analyzed, Loaded, PackageInput};

use crate::case::{Case, CaseKind, Setup};
use crate::run::Problem;

mod reading;
mod same_place;
mod spec;
#[cfg(test)]
mod tests;
mod text;
mod units;

pub(crate) use reading::Readings;
use reading::{code_difference, edit_problems};
pub use same_place::{SamePlace, Violation, same_place};
use spec::parse_leaf;
pub use spec::{FixSpec, Place, check_specs, de_specs, locate};
pub use text::{CandidateCheck, TextCheck, Unapplied, apply_alone, check_candidate, check_text, same_code};
use units::{Before, correspond, meet};
pub(crate) use units::{Moved, moved, shift};

/// What [`check`] found in a case.
#[derive(Debug, Clone, Default)]
pub struct Checked {
    /// Every candidate checked again, by its name in `tests/pending.toml`.
    pub targets: Vec<String>,
    pub problems: Vec<Problem>,
    /// The edits whose tokens the check 5 compared (both sides not empty):
    /// the run fails when there is none at all (nothing passes vacuously).
    pub edits_compared: usize,
    /// The units after the candidates that held no diagnostic before them
    /// (the module's documentation, 3), counted once per candidate: the run
    /// fails when there is none at all.
    pub clean_units: usize,
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
    let before = Before::of(analyzed);
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
                let name = loaded.sources.file(*file).name();
                let read = Readings::of(*file, loaded.sources.file(*file).text(), text);
                let (messages, compared) = edit_problems(&read, *file, &edits, &format!("in {name}, "));
                out.edits_compared += compared;
                for m in messages {
                    out.problems.push(Problem::FixContract {
                        target: target.clone(),
                        message: format!("fix candidate {target} `{}`: {m}", fix.title()),
                    });
                }
            }
            let (messages, clean) = judge(&files, rank, &before, &edits, &after, spec);
            out.clean_units += clean;
            for message in messages {
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
    let (loaded, analyzed) =
        check_texts(setup, loaded, &applied.texts).map_err(|e| format!("the check after it {e}"))?;
    Ok(After { loaded, analyzed, applied })
}

/// The case `loaded` (as it ran from `setup`) with the files of `texts`
/// replaced, checked through the case's own entry (`Loaded::from_input`,
/// `analyze_loaded`); the other files stay. The one way of checking a case
/// again ([`recheck`], [`crate::copy_guard`]). `Err`: why it cannot be
/// checked, a phrase after "the check" ("ends in an internal error: …").
pub(crate) fn check_texts(
    setup: &Setup,
    loaded: &Loaded,
    texts: &BTreeMap<FileId, String>,
) -> Result<(Loaded, Analyzed), String> {
    let mut input: PackageInput = setup.input.clone();
    for ((id, _), f) in loaded.modules.iter().zip(input.files.iter_mut()) {
        if let Some(t) = texts.get(id) {
            f.text = t.clone();
        }
    }
    let mut again = Loaded::from_input(input).map_err(|e| format!("cannot load the case again: {e}"))?;
    if again.modules.iter().map(|(f, _)| *f).ne(loaded.modules.iter().map(|(f, _)| *f)) {
        return Err("gives the files of the case other ids when they are loaded again".into());
    }
    let analyzed = onsa_driver::analyze_loaded(&mut again).map_err(|e| {
        format!("ends in an internal error: {}", e.render(&again.sources).trim_end().replace('\n', "\n  "))
    })?;
    Ok((again, analyzed))
}

/// What breaks the contract after one candidate (the module's documentation,
/// 3), and how many units after it held no diagnostic before it.
fn judge(
    files: &Files,
    rank: usize,
    before: &Before,
    edits: &[Moved],
    after: &After,
    spec: Option<&FixSpec>,
) -> (Vec<String>, usize) {
    let sources = &after.loaded.sources;
    let ranges = &after.applied.ranges;
    let c = correspond(before.units, &after.analyzed.units, edits);
    let clean: Vec<bool> = c.origins.iter().map(|o| o.iter().all(|&u| !before.dirty[u])).collect();
    // The diagnostics of the touched units (of its stage or an earlier one), and the others of
    // the clean ones (of any stage).
    let mut touched: Vec<(Place, Code)> = Vec::new();
    let mut fresh: Vec<(Place, Code)> = Vec::new();
    let mut shown = Vec::new();
    for (d, unit) in after.analyzed.diagnostics.iter().zip(&after.analyzed.diagnostic_units) {
        // The flow checks are before the modes and the effects (§18.1, S-267): a candidate of
        // a flow code may leave a diagnostic of those (`Stage::CHECK_ORDER`).
        let early = d.stage.check_rank().is_some_and(|r| r <= rank);
        let hit = early
            && match unit {
                Some(u) => c.touched.contains(u),
                None => files.has(d.span.file) && ranges.iter().any(|r| meet(*r, d.span)),
            };
        let left = (files.place(sources, d.span), d.code);
        if hit {
            touched.push(left);
        } else if unit.is_some_and(|u| clean[u]) {
            fresh.push(left);
        } else {
            continue;
        }
        shown.push(d.clone());
    }
    touched.sort();
    fresh.sort();
    let mut left: Vec<(Place, Code)> = touched.iter().chain(&fresh).cloned().collect();
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
        let others = if fresh.is_empty() {
            String::new()
        } else {
            format!(", and the units that held no diagnostic before it hold {} besides (of any stage)", show(&fresh))
        };
        out.push(format!(
            "after it, the units its edits touch hold {} of its stage or an earlier one{others}; expected {}{}\n  {}",
            show(&touched),
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
    (out, clean.iter().filter(|&&c| c).count())
}

/// The diagnostics, briefly, in the printed order
/// ([`onsa_diag::printed_order`]): `E0020 at 3:5, E0401 at 7:1`, or `nothing`.
fn describe(files: &Files, sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    if diagnostics.is_empty() {
        return "nothing".into();
    }
    onsa_diag::printed_order(sources, diagnostics)
        .into_iter()
        .map(|i| &diagnostics[i])
        .map(|d| format!("{} at {}", d.code.as_str(), files.place(sources, d.span).show()))
        .collect::<Vec<_>>()
        .join(", ")
}
