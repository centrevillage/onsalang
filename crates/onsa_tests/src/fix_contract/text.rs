//! The entries for one text: the fuzzing and the closed list of the forms of other languages.

use onsa_diag::{Applied, Diagnostic, FileId, Fix, SourceMap};
use onsa_driver::{Analyzed, Loaded, PackageInput, SourceFile};

use super::reading::{Readings, code_difference, edit_problems};
use super::units::{Before, moved};
use super::{After, Files, judge};

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

/// Why a candidate cannot be applied to a single-file input ([`apply_alone`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unapplied {
    /// Its edits do not apply (the reason of [`onsa_diag::apply_mapped`]).
    CannotApply(String),
    /// It edits a file other than the input.
    OtherFile,
}

impl std::fmt::Display for Unapplied {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unapplied::CannotApply(e) => f.write_str(e),
            Unapplied::OtherFile => f.write_str("it edits a file other than the input"),
        }
    }
}

/// Apply `fix` alone to the one file of a single-file input whose sources
/// are `sources` (a [`TextCheck`]'s): the text after it, and where its edits
/// went. The one place of applying a candidate to a single file
/// ([`check_candidate`], [`same_place`](fn@super::same_place), [`crate::fix_loop`]; D-15); the
/// check again is [`check_text`].
pub fn apply_alone(sources: &SourceMap, fix: &Fix) -> Result<(String, Applied), Unapplied> {
    let applied = onsa_diag::apply_mapped(sources, fix.edits()).map_err(Unapplied::CannotApply)?;
    let text = applied.texts.get(&FileId(0)).filter(|_| applied.texts.len() == 1).cloned();
    let text = text.ok_or(Unapplied::OtherFile)?;
    Ok((text, applied))
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
    let (text, applied) = apply_alone(&run.loaded.sources, fix).map_err(|e| e.to_string())?;
    let file = FileId(0);
    let again = check_text(&text)?;
    let files = Files { list: vec![(file, "m.onsa".into(), "m.onsa".into())], package: false };
    let edits = moved(fix, &applied);
    let read = Readings::of(file, run.loaded.sources.file(file).text(), &text);
    let mut problems = edit_problems(&read, file, &edits, "").0;
    let diagnostics = again.analyzed.diagnostics.clone();
    let after = After { loaded: again.loaded, analyzed: again.analyzed, applied };
    problems.extend(judge(&files, rank, &Before::of(&run.analyzed), &edits, &after, None).0);
    Ok(CandidateCheck { text, diagnostics, problems })
}

/// Where the code of `after` first differs from that of `before` (the
/// promise `same_code`, S-247): `None` when the same.
pub fn same_code(before: &str, after: &str) -> Option<String> {
    code_difference(before, after)
}
