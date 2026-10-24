//! Running the cases and applying the list of pending tests.
//!
//! A case runs through the same driver functions as the CLI command of its
//! mode, and its targets through the build's own entry
//! (`onsa_driver::build_analyzed`, R-89 (3)):
//!
//! - `mode = "parse"`: `parse_only`; the markers are compared with it.
//! - `"check"` / `"test"`: the analysis of `onsa check`. When it reports a
//!   diagnostic, or the case has no target, the markers are compared with it
//!   and no build runs. Otherwise every target is built and its diagnostics
//!   are compared with the markers that apply to it (no `[targets]`, or
//!   naming it). A target that builds is compared with its golden C and kept
//!   in [`CaseRun::builds`]: the gate items of the C checks compile it with
//!   each compiler and, with `conformance`, run it in both the interpreter
//!   and C ([`crate::ccheck`], Q-07, W1-06). Then the goldens of `onsa dump
//!   --core`, `interface` and `graph`, and in `"test"` every `test` block
//!   (`onsa test`). The host sequences of `[[test.host]]` run on the builds
//!   of their targets ([`crate::host`], K-14).
//! - Every mode but `"none"`: a file without markers is canonical under `fmt`
//!   (with `canonical = false`, fmt changes it into a text that parses and
//!   that it keeps), and the parser's diagnostics match markers
//!   ([`parser_markers`]).
//! - `[test] fixes = N`: the candidates of the check's diagnostics give the
//!   files `<file>.fixK` ([`crate::fixes`]: compared token by token, ignoring
//!   the whitespace tokens).
//! - `"check"` / `"test"`: every candidate of every diagnostic of the check,
//!   applied alone and checked again, keeps the contract of §18.1 and the
//!   promises of its `[[test.fix]]` entry ([`crate::fix_contract`], S-236,
//!   W3-17). A candidate of the build or of `onsa test` cannot be checked
//!   again and fails.
//! - Every diagnostic compared with markers follows the rules of diagnostics
//!   (`onsa_syntax::diagnostic_contract`: a required fix and note, edits on
//!   token boundaries that do not overlap). A break is an internal error of
//!   the compiler, which the pending list does not silence (plan D-04).
//!
//! Every Core a case makes comes from the driver's stage functions, which run
//! the Core verifier at their boundaries (R-82); a failure fails the case.
//!
//! An internal error of the compiler (S-67: a panic, a lowering failure that
//! is not an unsupported feature, a Core the verifier rejects) is a problem
//! of its own, [`Problem::Internal`]: the pending list does not silence it,
//! unless a `test-case` entry says `expect = "internal"` (W1-04).
//!
//! The results are kept as structures ([`CaseRun`], [`CaseReport`]): which
//! markers were compared at which stage, and whether the case is pending.

use std::path::Path;
use std::sync::Arc;

use onsa_diag::{Code, FileId, SourceMap};
use onsa_driver::{Analyzed, BuildError, BuildOutput, Interface, InternalError, Loaded, LowerError};

use crate::case::{self, Case};
use crate::fragment::{GoldenKind, Mode};
use crate::golden::{self, Update};
use crate::{Expected, PanicMark, parse_markers};

mod all;
mod build;
mod markers;
mod report;
mod test_blocks;
#[cfg(test)]
mod tests;

pub use all::{run_all, run_all_with, run_each, runs_json};
use build::{BuildCtx, build_target, conformance_scope, disk_files, host_not_run, run_hosts};
use markers::{canonical, compare, negative_rules, parser_markers};
pub use report::{CaseReport, Report, reconcile};
use test_blocks::run_tests;

/// The stage a marker was compared at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Stage {
    Parse,
    Check,
    Build,
    /// `onsa test` before the tests run: E0200 for what the interpreter
    /// cannot run (S-224), in a `mode = "test"` case without targets.
    Test,
}

/// A marker that was compared with the diagnostics of a run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedMarker {
    pub code: Code,
    pub file: String,
    pub line: u32,
    pub stage: Stage,
    /// The target, for the build stage.
    pub target: Option<String>,
    /// A diagnostic of the run matched it.
    pub matched: bool,
}

/// One `test` block of a `mode = "test"` case, identified as `onsa test`
/// identifies it: its module path and its name (§11.8, R-184).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestResult {
    pub module: String,
    pub name: String,
    pub failed: bool,
    pub message: Option<String>,
    /// Marked `//~ TESTFAIL`.
    pub testfail: bool,
    /// Marked `//~ PANIC`.
    pub panic: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Problem {
    /// A `test` block failed without `TESTFAIL` (`<path>::<name>` may list
    /// it). `full` is its full name text (`dsp.voice "decays"`, §11.8).
    TestFailed { full: String, message: String },
    /// The case does not give what it expects (the list may hold it as pending).
    Failed(String),
    /// The case itself is wrong (its fragment, markers or settings): never pending.
    Case(String),
    /// An internal error of the compiler (S-67): pending only by a `test-case`
    /// entry with `expect = "internal"`.
    Internal(String),
    /// A host sequence (K-14, [`crate::host`]) did not give what it must
    /// (`<path>::<name>` may list it). The message names it.
    Host { name: String, message: String },
    /// The harness of the host steps cannot run (no compiler, a file it cannot
    /// write, records it cannot read): never pending.
    Harness(String),
    /// A fix candidate breaks the contract of §18.1 (S-236) or a promise of
    /// its `[[test.fix]]` entry ([`crate::fix_contract`]). Only an entry of
    /// kind `fix-contract` naming `target` silences it (not one of the whole case).
    FixContract { target: String, message: String },
    /// A fix candidate the runner cannot check against the contract (it edits
    /// a file outside the case, it cannot be applied, the check after it ends
    /// in an internal error, its stage is not a check): never pending.
    FixUnchecked(String),
    /// A copy of the text after the candidates (`.fixK`, [`crate::fixes`];
    /// Q-04) differs or is missing, or the guard refused rewriting it
    /// ([`crate::copy_guard`]): never a failure of the contract. A case listed
    /// as a whole does not judge, rewrite or count its copies as a reason to
    /// wait ([`reconcile`] drops them and counts them,
    /// [`Report::unjudged_copies`]); no other entry silences it
    /// (`UPDATE_GOLDEN=1` rewrites it).
    FixCopy(String),
}

impl Problem {
    /// The kind, as the JSON report names it.
    pub fn kind(&self) -> &'static str {
        match self {
            Problem::TestFailed { .. } => "test-failed",
            Problem::Failed(_) => "failed",
            Problem::Case(_) => "case",
            Problem::Internal(_) => "internal",
            Problem::Host { .. } => "host-failed",
            Problem::Harness(_) => "harness",
            Problem::FixContract { .. } => "fix-contract",
            Problem::FixUnchecked(_) => "fix-unchecked",
            Problem::FixCopy(_) => "fix-copy",
        }
    }

    pub fn text(&self) -> String {
        match self {
            Problem::TestFailed { full, message } => format!("test {full} failed: {message}"),
            Problem::Failed(m) => m.clone(),
            Problem::Case(m) => format!("error in the case: {m}"),
            Problem::Internal(m) => m.clone(),
            Problem::Host { message, .. } => message.clone(),
            Problem::Harness(m) => format!("the host steps cannot run: {m}"),
            Problem::FixContract { message, .. } => message.clone(),
            Problem::FixUnchecked(m) => format!("the contract of a fix candidate cannot be checked: {m}"),
            Problem::FixCopy(m) => m.clone(),
        }
    }
}

/// The run of one case.
#[derive(Debug, Clone, Default)]
pub struct CaseRun {
    pub path: String,
    pub mode: Mode,
    /// `false` for `mode = "none"` and for a case that cannot be read.
    pub ran: bool,
    pub checked: Vec<CheckedMarker>,
    pub tests: Vec<TestResult>,
    pub problems: Vec<Problem>,
    /// The targets that built as the case expects (no build marker applies),
    /// for the C checks (Q-07).
    pub builds: Vec<Built>,
    /// The names of the case's host sequences (`[[test.host]]`), run or not.
    pub host_names: Vec<String>,
    /// The host sequences that the run reached (K-14).
    pub hosts: Vec<crate::host::SeqResult>,
    /// Information for the reader (where `ONSA_C_KEEP` kept files).
    pub notes: Vec<String>,
    /// The fix candidates checked against the contract of §18.1, by their
    /// names in `tests/pending.toml` ([`crate::fix_contract`], W3-17).
    pub fix_targets: Vec<String>,
    /// The edits of those candidates whose tokens the check of the minimal
    /// edit compared ([`crate::fix_contract::Checked::edits_compared`]).
    pub edits_compared: usize,
    /// The units after those candidates that held no diagnostic before them
    /// ([`crate::fix_contract::Checked::clean_units`]).
    pub clean_units: usize,
    /// The copies `.fixK` compared, and those `UPDATE_GOLDEN=1` rewrote or
    /// removed ([`crate::fixes::CopyCheck`]).
    pub fix_copies: usize,
    pub copies_rewritten: Vec<String>,
    /// Those of `copies_rewritten` the guard refused and `UPDATE_GOLDEN=worse`
    /// wrote: `<path> (<what only the new texts report>)`.
    pub copies_forced: Vec<String>,
    /// The candidates K whose copies went through the guard.
    pub copies_guarded: usize,
}

/// A target of a case that built: its C, for the C checks ([`crate::ccheck`]).
#[derive(Clone)]
pub struct Built {
    pub target: String,
    pub output: Arc<BuildOutput>,
    /// `[test] conformance`: run it in both the interpreter and C.
    pub conformance: bool,
}

impl std::fmt::Debug for Built {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Built").field("target", &self.target).field("conformance", &self.conformance).finish()
    }
}

/// The driver's stages that make Core, as the runner calls them. Each runs
/// the Core verifier at its boundary (R-82). The runner uses
/// [`Stages::DRIVER`]; a test gives stages that fail, to check that every
/// failure reaches the problems of the case ([`stage_problem`]).
#[derive(Clone, Copy)]
pub struct Stages {
    pub lower_core: fn(&Analyzed) -> Result<onsa_core::Module, LowerError>,
    pub build: fn(&Loaded, &Analyzed, &str) -> Result<BuildOutput, BuildError>,
    pub interface: fn(&Analyzed) -> Result<Interface, InternalError>,
}

impl Stages {
    pub const DRIVER: Stages = Stages {
        lower_core: onsa_driver::lower_core,
        build: onsa_driver::build_analyzed,
        interface: onsa_driver::interface,
    };
}

/// A stage that gave no output, other than build diagnostics (those are
/// compared with the markers).
#[derive(Debug, Clone, Copy)]
pub enum StageFailure<'a> {
    /// `lower_core`, for the Core golden and the `test` blocks.
    Lower(&'a LowerError),
    /// The build of a target.
    Build { target: &'a str, error: &'a BuildError },
    /// `interface`, for its golden.
    Interface(&'a InternalError),
}

/// The problem of the case for a failed stage: the one place every arm of
/// the runner turns a stage's failure into a problem (R-82). An internal
/// error (S-67) is [`Problem::Internal`] with its report (for a verifier
/// failure: the stage, the item, the rule and the item's Core).
pub fn stage_problem(sources: &SourceMap, failure: StageFailure<'_>) -> Problem {
    match failure {
        StageFailure::Lower(LowerError::Diagnostics(diags)) => {
            Problem::Failed(format!("lowering failed:\n{}", onsa_diag::to_text(sources, diags).replace('\n', "\n  ")))
        }
        StageFailure::Lower(LowerError::Internal(e)) | StageFailure::Interface(e) => internal_problem(sources, e, None),
        StageFailure::Build { target, error: BuildError::Internal { sources, error } } => {
            internal_problem(sources, error, Some(target))
        }
        // The settings of the case itself are wrong.
        StageFailure::Build { target, error: BuildError::Usage(m) } => {
            Problem::Case(format!("build of `{target}`: {m}"))
        }
        StageFailure::Build { target, error: BuildError::Diagnostics { sources, diagnostics } } => Problem::Failed(
            format!("build of `{target}`:\n{}", onsa_diag::to_text(sources, diagnostics).replace('\n', "\n  ")),
        ),
    }
}

/// The problem of an internal error (S-67), with its report.
pub fn internal_problem(sources: &SourceMap, e: &InternalError, target: Option<&str>) -> Problem {
    let at = target.map(|t| format!("build of `{t}`: ")).unwrap_or_default();
    Problem::Internal(format!("{at}{}", e.render(sources).trim_end().replace('\n', "\n  ")))
}

/// Whether a run makes the host sequences of its cases (K-14, [`crate::host`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostSteps {
    Run,
    /// The C checks and the marker counts only want the builds and the markers.
    Skip,
}

/// How a case runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunOptions {
    /// Whether the case's golden files and copies are rewritten (`Off` for a pending case).
    pub golden: Update,
    pub host_steps: HostSteps,
}

/// Run one case.
pub fn run_case(root: &Path, case: &Case, opts: RunOptions) -> CaseRun {
    run_case_with(&Stages::DRIVER, root, case, opts)
}

/// [`run_case`] through `stages`.
pub fn run_case_with(stages: &Stages, root: &Path, case: &Case, opts: RunOptions) -> CaseRun {
    let RunOptions { golden: update, host_steps } = opts;
    let hosts = host_steps == HostSteps::Run;
    let mut run = CaseRun { path: case.path.clone(), ..Default::default() };
    let setup = match &case.setup {
        Ok(s) => s,
        Err(e) => {
            run.problems.push(Problem::Case(e.clone()));
            return run;
        }
    };
    run.mode = setup.test.mode;
    run.host_names = setup.test.host.iter().map(|h| h.name.clone()).collect();
    let targets = setup.targets();
    let t = &setup.test;
    if !targets.is_empty() && matches!(t.mode, Mode::None | Mode::Parse) {
        run.problems.push(Problem::Case(format!("targets need `mode = \"check\"` or `\"test\"` (not {:?})", t.mode)));
    }
    if t.golden.contains(&GoldenKind::C) && targets.is_empty() {
        run.problems.push(Problem::Case("`golden = [\"c\"]` needs a target".into()));
    }
    if t.conformance && targets.is_empty() {
        run.problems.push(Problem::Case("`conformance` needs a target".into()));
    }
    for h in &t.host {
        if !targets.contains(&h.target) {
            run.problems.push(Problem::Case(format!(
                "line {}: host \"{}\": `target = \"{}\"` is not a target of the case",
                h.line, h.name, h.target
            )));
        }
    }
    let mut loaded = match Loaded::from_input(setup.input.clone()) {
        Ok(l) => l,
        Err(e) => {
            run.problems.push(Problem::Case(e));
            return run;
        }
    };

    // Markers of every file of the case (line numbers are per file); read in
    // every mode, so a case that does not run cannot hold a broken marker.
    let mut markers: Vec<(FileId, Expected)> = Vec::new();
    // `//~ TESTFAIL "name"` names a test of the module of its file (R-184).
    let mut testfails: Vec<(String, String)> = Vec::new();
    // `//~ PANIC "name"` too, with the file of its line.
    let mut panics: Vec<(String, FileId, PanicMark)> = Vec::new();
    for (file, module) in loaded.modules.clone() {
        let f = loaded.sources.file(file);
        match parse_markers(f.text()) {
            Ok(m) => {
                markers.extend(m.expected.into_iter().map(|e| (file, e)));
                testfails.extend(m.testfails.into_iter().map(|name| (module.clone(), name)));
                panics.extend(m.panics.into_iter().map(|p| (module.clone(), file, p)));
            }
            Err(e) => run.problems.push(Problem::Case(format!("{}: bad markers: {e}", f.name()))),
        }
    }
    for (mark, used) in [("TESTFAIL", !testfails.is_empty()), ("PANIC", !panics.is_empty())] {
        if used && t.mode != Mode::Test {
            run.problems.push(Problem::Case(format!(
                "`//~ {mark}` needs `mode = \"test\"` (the case is {:?}); the test blocks do not run",
                t.mode
            )));
        }
    }
    if !run.problems.is_empty() || t.mode == Mode::None {
        return run;
    }
    run.ran = true;
    for (file, m) in &markers {
        for name in m.targets.iter().flatten() {
            if !targets.contains(name) {
                run.problems.push(Problem::Case(format!(
                    "{}:{}: the marker names `{name}`, which is not a target of the case",
                    loaded.sources.file(*file).name(),
                    m.line
                )));
            }
        }
    }
    if !run.problems.is_empty() {
        run.ran = false;
        return run;
    }
    let targeted = markers.iter().filter(|(_, m)| m.targets.is_some()).count();
    let unmarked = loaded.modules.iter().filter(|(file, _)| !loaded.sources.file(*file).text().contains("//~")).count();
    if !t.canonical() && unmarked == 0 {
        run.problems.push(Problem::Case(
            "`canonical = false` asks nothing of a case whose files all hold markers (fmt is not asked about them)"
                .into(),
        ));
    }
    // Whether fmt changed some file of the case (`canonical = false` asks it of one at least).
    let mut changed = false;
    for (file, _) in &loaded.modules {
        let f = loaded.sources.file(*file);
        // The parser and fmt run here outside the driver's stages: guard them.
        let r = onsa_driver::guard(|| {
            let mut problems = CaseRun::default();
            let changed = !f.text().contains("//~") && canonical(&mut problems, f.name(), f.text(), t.canonical());
            parser_markers(&mut problems, &loaded.sources, *file, &markers);
            (problems.problems, changed)
        });
        match r {
            Ok((p, c)) => {
                run.problems.extend(p);
                changed |= c;
            }
            Err(e) => run.problems.push(internal_problem(&loaded.sources, &e, None)),
        }
    }
    if !t.canonical() && unmarked > 0 && !changed {
        run.problems.push(Problem::Failed(
            "fmt leaves every file of the case unchanged; take `canonical = false` out of the case".into(),
        ));
    }

    if t.mode == Mode::Parse {
        match onsa_driver::parse_only(&loaded.sources) {
            Ok(result) => {
                compare(&mut run, &loaded.sources, &markers, &result.diagnostics, Stage::Parse, None);
                // Candidates are checked again only in `check` and `test` (W3-17): one here fails.
                run.problems.extend(crate::fix_contract::unchecked_in_parse(&loaded.sources, &result.diagnostics));
            }
            Err(e) => run.problems.push(internal_problem(&loaded.sources, &e, None)),
        }
        return run;
    }

    let analyzed = match onsa_driver::analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(e) => {
            run.problems.push(internal_problem(&loaded.sources, &e, None));
            return run;
        }
    };
    let check = &analyzed.diagnostics;
    // Every candidate, applied alone and checked again (§18.1, S-236, W3-17).
    let contract = crate::fix_contract::check(case, setup, &loaded, &analyzed);
    run.fix_targets = contract.targets;
    run.edits_compared = contract.edits_compared;
    run.clean_units = contract.clean_units;
    run.problems.extend(contract.problems);
    if t.fixes > 0 {
        let files = disk_files(root, case, setup, &loaded);
        let guard = |old: &_, new: &_| crate::copy_guard::case(setup, &loaded, old, new);
        let copies = crate::fixes::compare(&loaded.sources, &files, check, t.fixes, update, &guard);
        run.problems.extend(copies.problems);
        run.fix_copies = copies.copies;
        run.copies_guarded = copies.guarded;
        run.copies_rewritten = copies.rewritten.iter().map(|p| case::rel_path(root, p)).collect();
        run.copies_forced = copies.forced.iter().map(|(p, f)| format!("{} ({f})", case::rel_path(root, p))).collect();
    }
    // A `mode = "test"` case without targets that checks compares its markers
    // with what `onsa test` reports before the tests run ([`run_tests`]).
    let test_stage = check.is_empty() && targets.is_empty() && t.mode == Mode::Test;
    if !check.is_empty() || targets.is_empty() {
        if targeted > 0 {
            run.problems.push(Problem::Case(if targets.is_empty() {
                "markers name targets, but the case has none".into()
            } else {
                format!(
                    "markers name targets, but the build stage does not run (check reports {} diagnostics); \
                     a code of the check takes no `[targets]`",
                    check.len()
                )
            }));
        }
        if !test_stage && compare(&mut run, &loaded.sources, &markers, check, Stage::Check, None) {
            negative_rules(&mut run, &case.path, check);
        }
        if !check.is_empty() {
            if !t.golden.is_empty() || !t.golden_graph.is_empty() || t.conformance {
                run.problems
                    .push(Problem::Case("golden files and conformance need a check without diagnostics".into()));
            }
            if hosts {
                let why = format!("the check reports {} diagnostics", check.len());
                for h in &t.host {
                    host_not_run(&mut run, h, &why);
                }
            }
            return run;
        }
    } else {
        if t.conformance {
            conformance_scope(&mut run, &loaded, &analyzed);
        }
        for target in &targets {
            let ctx = BuildCtx { stages, root, case, setup, loaded: &loaded, analyzed: &analyzed, markers: &markers };
            build_target(&ctx, target, update, &mut run);
        }
        if hosts {
            run_hosts(&mut run, &t.host);
        }
    }

    // The check reports nothing: the outputs of the analysis, and the tests.
    let needs_core = t.golden.contains(&GoldenKind::Core) || t.mode == Mode::Test;
    let module = if needs_core {
        match (stages.lower_core)(&analyzed) {
            Ok(m) => Some(m),
            Err(e) => {
                run.problems.push(stage_problem(&loaded.sources, StageFailure::Lower(&e)));
                None
            }
        }
    } else {
        None
    };
    let gold = |run: &mut CaseRun, rel: String, actual: &str| {
        if let Some(p) = golden::compare(root, &rel, actual, update) {
            run.problems.push(Problem::Failed(p));
        }
    };
    if t.golden.contains(&GoldenKind::Core)
        && let Some(m) = &module
    {
        // `lower_core` verified it (R-82).
        gold(&mut run, golden::core_path(&case.name), &onsa_core::dump(m));
    }
    if t.golden.contains(&GoldenKind::Interface) {
        match (stages.interface)(&analyzed) {
            Ok(iface) => {
                gold(&mut run, golden::interface_path(&case.name), &onsa_driver::render_text(&iface));
                // The JSON form must parse and name the package.
                match serde_json::from_str::<serde_json::Value>(&onsa_driver::render_json(&iface)) {
                    Ok(json) if json["package"] == loaded.name.as_str() => {}
                    Ok(json) => {
                        run.problems.push(Problem::Failed(format!("interface JSON names package {}", json["package"])))
                    }
                    Err(e) => run.problems.push(Problem::Failed(format!("interface JSON does not parse: {e}"))),
                }
            }
            Err(v) => run.problems.push(stage_problem(&loaded.sources, StageFailure::Interface(&v))),
        }
    }
    for flow in &t.golden_graph {
        match onsa_driver::graph(&analyzed, flow) {
            Ok(dot) => gold(&mut run, golden::graph_path(&case.name, flow), &dot),
            Err(onsa_driver::GraphError::Usage(e)) => {
                run.problems.push(Problem::Failed(format!("graph `{flow}`: {e}")))
            }
            Err(onsa_driver::GraphError::Internal(e)) => run.problems.push(internal_problem(&loaded.sources, &e, None)),
        }
    }
    if t.mode == Mode::Test
        && let Some(m) = &module
    {
        let stage_markers: &[(FileId, Expected)] = if test_stage { &markers } else { &[] };
        run_tests(&mut run, &case.path, &loaded.sources, m, stage_markers, &testfails, &panics);
    }
    // One name space: an entry `<path>::<name>` names a test or a host sequence.
    for h in &t.host {
        if run.tests.iter().any(|x| x.name == h.name) {
            run.problems.push(Problem::Case(format!(
                "line {}: host \"{}\": a `test` block has the same name (an entry `<path>::<name>` of \
                 tests/pending.toml names one of them)",
                h.line, h.name
            )));
        }
    }
    run
}
