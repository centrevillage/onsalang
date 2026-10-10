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
//! - Every mode but `"none"`: a file without markers is canonical under `fmt`,
//!   and the parser's diagnostics match markers ([`parser_markers`]).
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

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use onsa_diag::{Code, Diagnostic, FileId, SourceMap};
use onsa_driver::{Analyzed, BuildError, BuildOutput, Interface, InternalError, Loaded, LowerError};

use crate::case::{self, Case, Setup};
use crate::fragment::{GoldenKind, Mode};
use crate::pending::{self, Pending};
use crate::{Expected, golden, parse_markers};

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
    /// `UPDATE_GOLDEN` may rewrite the case's golden files.
    pub write_golden: bool,
    pub host_steps: HostSteps,
}

/// Run one case.
pub fn run_case(root: &Path, case: &Case, opts: RunOptions) -> CaseRun {
    run_case_with(&Stages::DRIVER, root, case, opts)
}

/// [`run_case`] through `stages`.
pub fn run_case_with(stages: &Stages, root: &Path, case: &Case, opts: RunOptions) -> CaseRun {
    let RunOptions { write_golden, host_steps } = opts;
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
    let mut loaded = Loaded::from_input(setup.input.clone());

    // Markers of every file of the case (line numbers are per file); read in
    // every mode, so a case that does not run cannot hold a broken marker.
    let mut markers: Vec<(FileId, Expected)> = Vec::new();
    // `//~ TESTFAIL "name"` names a test of the module of its file (R-184).
    let mut testfails: Vec<(String, String)> = Vec::new();
    for (file, module) in loaded.modules.clone() {
        let f = loaded.sources.file(file);
        match parse_markers(f.text()) {
            Ok(m) => {
                markers.extend(m.expected.into_iter().map(|e| (file, e)));
                testfails.extend(m.testfails.into_iter().map(|name| (module.clone(), name)));
            }
            Err(e) => run.problems.push(Problem::Case(format!("{}: bad markers: {e}", f.name()))),
        }
    }
    if !testfails.is_empty() && t.mode != Mode::Test {
        run.problems.push(Problem::Case(format!(
            "`//~ TESTFAIL` needs `mode = \"test\"` (the case is {:?}); the test blocks do not run",
            t.mode
        )));
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
    for (file, _) in &loaded.modules {
        let f = loaded.sources.file(*file);
        // The parser and fmt run here outside the driver's stages: guard them.
        let r = onsa_driver::guard(|| {
            let mut problems = CaseRun::default();
            if !f.text().contains("//~") {
                canonical(&mut problems, f.name(), f.text());
            }
            parser_markers(&mut problems, &loaded.sources, *file, &markers);
            problems.problems
        });
        match r {
            Ok(p) => run.problems.extend(p),
            Err(e) => run.problems.push(internal_problem(&loaded.sources, &e, None)),
        }
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
    run.problems.extend(contract.problems);
    if t.fixes > 0 {
        let files = disk_files(root, case, setup, &loaded);
        run.problems.extend(crate::fixes::compare(&loaded.sources, &files, check, t.fixes));
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
            build_target(&ctx, target, write_golden, &mut run);
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
        if let Some(p) = golden::compare(root, &rel, actual, write_golden) {
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
        run_tests(&mut run, &case.path, &loaded.sources, m, stage_markers, &testfails);
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

/// A host sequence that did not run, for a reason of the whole case.
fn host_not_run(run: &mut CaseRun, h: &crate::host::Seq, why: &str) {
    run.problems.push(Problem::Failed(format!("host \"{}\" did not run: {why}", h.name)));
    run.hosts.push(crate::host::SeqResult {
        name: h.name.clone(),
        target: h.target.clone(),
        outcome: crate::host::Outcome::NotRun(why.into()),
    });
}

/// Run the host sequences on the builds of their targets (K-14).
fn run_hosts(run: &mut CaseRun, seqs: &[crate::host::Seq]) {
    let mut targets: Vec<&str> = Vec::new();
    for s in seqs {
        if !targets.contains(&s.target.as_str()) {
            targets.push(&s.target);
        }
    }
    for target in targets {
        let mine: Vec<&crate::host::Seq> = seqs.iter().filter(|s| s.target == target).collect();
        let Some(built) = run.builds.iter().find(|b| b.target == target).cloned() else {
            for h in mine {
                host_not_run(run, h, &format!("target `{target}` did not build"));
            }
            continue;
        };
        let r = crate::host::run_target(target, &mine, &built.output);
        run.problems.extend(r.case_errors.into_iter().map(Problem::Case));
        run.problems.extend(r.failures.into_iter().map(Problem::Failed));
        run.problems.extend(r.harness.into_iter().map(Problem::Harness));
        run.notes.extend(r.notes);
        for res in r.results {
            let seq = mine.iter().find(|s| s.name == res.name);
            match &res.outcome {
                crate::host::Outcome::Passed { .. } => {}
                crate::host::Outcome::Failed(m) => run.problems.push(Problem::Host {
                    name: res.name.clone(),
                    message: format!(
                        "host \"{}\" (line {}, target {target}, {}):\n  {}",
                        res.name,
                        seq.map_or(0, |s| s.line),
                        seq.map_or_else(String::new, |s| s.callee()),
                        m.replace('\n', "\n  ")
                    ),
                }),
                crate::host::Outcome::NotRun(why) => {
                    run.problems.push(Problem::Failed(format!("host \"{}\" did not run: {why}", res.name)))
                }
            }
            run.hosts.push(res);
        }
    }
}

/// What the builds of a case share.
struct BuildCtx<'a> {
    stages: &'a Stages,
    root: &'a Path,
    case: &'a Case,
    setup: &'a Setup,
    loaded: &'a Loaded,
    analyzed: &'a Analyzed,
    markers: &'a [(FileId, Expected)],
}

/// Build one target, compare its diagnostics with the markers that apply to
/// it, and check what it produced.
fn build_target(ctx: &BuildCtx<'_>, target: &str, write_golden: bool, run: &mut CaseRun) {
    let BuildCtx { stages, root, case, setup, loaded, analyzed, markers } = *ctx;
    let t = &setup.test;
    let expected: Vec<(FileId, Expected)> = markers
        .iter()
        .filter(|(_, m)| m.targets.as_ref().is_none_or(|ts| ts.iter().any(|x| x == target)))
        .cloned()
        .collect();
    if !expected.is_empty() && (t.golden.contains(&GoldenKind::C) || t.conformance) {
        run.problems.push(Problem::Case(format!(
            "target `{target}` expects build diagnostics, but the case declares its golden C or conformance"
        )));
    }
    if !expected.is_empty() && t.host.iter().any(|h| h.target == target) {
        run.problems.push(Problem::Case(format!(
            "target `{target}` expects build diagnostics, but host sequences run on it ([[test.host]])"
        )));
    }
    let out = match (stages.build)(loaded, analyzed, target) {
        Ok(out) => {
            compare(run, &loaded.sources, &expected, &[], Stage::Build, Some(target));
            out
        }
        Err(BuildError::Diagnostics { diagnostics, sources }) => {
            compare(run, &loaded.sources, &expected, &diagnostics, Stage::Build, Some(target));
            run.problems.extend(crate::fix_contract::unchecked(&sources, &diagnostics));
            return;
        }
        Err(error) => {
            run.problems.push(stage_problem(&loaded.sources, StageFailure::Build { target, error: &error }));
            return;
        }
    };
    if !expected.is_empty() {
        return;
    }
    if t.golden.contains(&GoldenKind::C) {
        let [c, h] = golden::c_paths(&case.name, target);
        for (rel, actual) in [(c, out.unit.source.clone()), (h, crate::c::join_headers(&out.unit))] {
            if let Some(p) = golden::compare(root, &rel, &actual, write_golden) {
                run.problems.push(Problem::Failed(p));
            }
        }
    }
    run.builds.push(Built { target: target.to_string(), output: Arc::new(out), conformance: t.conformance });
}

/// `conformance = true` covers every `pub flow` of the case: each is in
/// `[export] flows`, which is not empty.
fn conformance_scope(run: &mut CaseRun, loaded: &Loaded, analyzed: &Analyzed) {
    let export = onsa_driver::ExportSettings::from_manifest(loaded.manifest.as_ref().and_then(|m| m.export.as_ref()));
    if export.flows.is_empty() {
        run.problems.push(Problem::Case("`conformance` needs `[export] flows`".into()));
        return;
    }
    let user: BTreeSet<FileId> = loaded.modules.iter().map(|(f, _)| *f).collect();
    let a = &analyzed.analysis;
    for (i, d) in a.defs.iter().enumerate() {
        if matches!(d.kind, onsa_sema::def::DefKind::Flow(_))
            && d.vis == onsa_syntax::ast::Vis::Pub
            && d.owner.is_none()
            && user.contains(&d.span.file)
        {
            let name = a.qualified_name(onsa_sema::DefId(i as u32));
            if !export.flows.contains(&name) {
                run.problems.push(Problem::Case(format!(
                    "`conformance` covers every `pub flow`, but `{name}` is not in `[export] flows`"
                )));
            }
        }
    }
}

/// Where each source file of the case is on disk (in the order of `loaded.modules`).
fn disk_files(root: &Path, case: &Case, setup: &Setup, loaded: &Loaded) -> Vec<(FileId, std::path::PathBuf)> {
    loaded
        .modules
        .iter()
        .zip(&setup.input.files)
        .map(|((file, _), f)| {
            let p = match case.kind {
                case::CaseKind::File => root.join(&case.path),
                case::CaseKind::Package => root.join(&case.path).join(&f.path),
            };
            (*file, p)
        })
        .collect()
}

/// Compare the markers with the diagnostics, record every marker compared,
/// and report a difference. Whether they match. Every diagnostic is also
/// checked against the rules of diagnostics (a break is an internal error).
fn compare(
    run: &mut CaseRun,
    sources: &SourceMap,
    expected: &[(FileId, Expected)],
    actual: &[Diagnostic],
    stage: Stage,
    target: Option<&str>,
) -> bool {
    let actual_pos: Vec<(FileId, Code, u32, u32)> = actual
        .iter()
        .map(|d| {
            let lc = sources.file(d.span.file).line_col(d.span.start);
            (d.span.file, d.code, lc.line, lc.col)
        })
        .collect();
    for p in onsa_syntax::diagnostic_contract(sources, actual) {
        run.problems.push(Problem::Internal(format!("a diagnostic breaks the rules of diagnostics (plan D-04): {p}")));
    }
    let mut used = vec![false; actual_pos.len()];
    // Markers with a column first, so a marker without one cannot take their diagnostic.
    let mut order: Vec<usize> = (0..expected.len()).collect();
    order.sort_by_key(|&i| expected[i].1.col.is_none());
    let mut all = true;
    let mut matched = vec![false; expected.len()];
    for i in order {
        let (f, e) = &expected[i];
        let hit = actual_pos.iter().enumerate().position(|(k, (af, code, line, col))| {
            !used[k] && af == f && *code == e.code && *line == e.line && e.col.is_none_or(|c| c == *col)
        });
        match hit {
            Some(k) => {
                used[k] = true;
                matched[i] = true;
            }
            None => all = false,
        }
    }
    for (i, (f, e)) in expected.iter().enumerate() {
        run.checked.push(CheckedMarker {
            code: e.code,
            file: sources.file(*f).name().to_string(),
            line: e.line,
            stage,
            target: target.map(str::to_string),
            matched: matched[i],
        });
    }
    let ok = all && used.iter().all(|u| *u);
    if !ok {
        let render_e = |(f, e): &(FileId, Expected)| {
            let col = e.col.map(|c| format!(":{c}")).unwrap_or_default();
            format!("{}@{}:{}{col}", e.code.as_str(), sources.file(*f).name(), e.line)
        };
        let render_a = |(f, code, line, col): &(FileId, Code, u32, u32)| {
            format!("{}@{}:{line}:{col}", code.as_str(), sources.file(*f).name())
        };
        let mut msg = match target {
            Some(t) => format!("the build of `{t}` differs from the markers\n"),
            None => format!("the {stage:?} diagnostics differ from the markers\n").to_lowercase(),
        };
        let none = |v: Vec<String>| if v.is_empty() { "(none)".to_string() } else { v.join(" ") };
        let _ = writeln!(msg, "  expected: {}", none(expected.iter().map(render_e).collect()));
        let _ = writeln!(msg, "  actual:   {}", none(actual_pos.iter().map(render_a).collect()));
        let _ = write!(msg, "  {}", onsa_diag::to_text(sources, actual).replace('\n', "\n  "));
        run.problems.push(Problem::Failed(msg.trim_end().to_string()));
    }
    ok
}

/// A code only the syntax stage reports: its markers come from the parser alone.
fn syntax_only(c: Code) -> bool {
    c.stages() == [onsa_diag::Stage::Syntax]
}

/// The diagnostics of the parser alone (before the later stages; one per
/// unit, as `check` chooses, `onsa_driver::reduce`) against the markers of the
/// file: each one
/// matches a marker of its line and code, and every marker of a code only
/// the syntax stage reports is one of them. Markers of a code that later
/// stages report too (E0020, E0408, ...) are compared by the check only.
fn parser_markers(run: &mut CaseRun, sources: &SourceMap, file: FileId, markers: &[(FileId, Expected)]) {
    let f = sources.file(file);
    let parsed = onsa_syntax::parse(file, f.text());
    let reduced = onsa_driver::reduce::per_unit([(file, &parsed.units)], parsed.diagnostics.clone()).diagnostics;
    let mut actual: Vec<(u32, Code)> = reduced.iter().map(|d| (f.line_col(d.span.start).line, d.code)).collect();
    let mut expected: Vec<(u32, Code)> =
        markers.iter().filter(|(mf, _)| *mf == file).map(|(_, m)| (m.line, m.code)).collect();
    expected.sort();
    actual.sort();
    // Each parser diagnostic takes a marker of its line and code.
    let mut free = expected.clone();
    let mut unmatched = Vec::new();
    for a in &actual {
        match free.iter().position(|e| e == a) {
            Some(i) => {
                free.remove(i);
            }
            None => unmatched.push(*a),
        }
    }
    let missing: Vec<(u32, Code)> = free.into_iter().filter(|(_, c)| syntax_only(*c)).collect();
    if !unmatched.is_empty() || !missing.is_empty() {
        let show = |v: &[(u32, Code)]| {
            if v.is_empty() {
                "(none)".to_string()
            } else {
                v.iter().map(|(l, c)| format!("{}@{l}", c.as_str())).collect::<Vec<_>>().join(" ")
            }
        };
        run.problems.push(Problem::Failed(format!(
            "{}: the parser's diagnostics differ from the markers\n  without a marker: {}\n  markers of syntax-only codes the parser does not report: {}\n  {}",
            f.name(),
            show(&unmatched),
            show(&missing),
            onsa_diag::to_text(sources, &reduced).replace('\n', "\n  ")
        )));
    }
}

/// A file without markers is already canonical: `fmt` leaves it unchanged
/// and is idempotent (M1, T1-9).
fn canonical(run: &mut CaseRun, name: &str, text: &str) {
    let parsed = onsa_syntax::parse(FileId(0), text);
    let Some(out) = onsa_syntax::format(&parsed, text) else {
        run.problems.push(Problem::Failed(format!("{name}: fmt refused it (diagnostics)")));
        return;
    };
    if out != text {
        run.problems.push(Problem::Failed(format!("{name}: fmt changes it\n{}", first_diff(text, &out))));
        return;
    }
    let again = onsa_syntax::parse(FileId(0), &out);
    if onsa_syntax::format(&again, &out).as_deref() != Some(out.as_str()) {
        run.problems.push(Problem::Failed(format!("{name}: fmt is not idempotent on it")));
    }
}

fn first_diff(a: &str, b: &str) -> String {
    let (al, bl): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    for i in 0..al.len().max(bl.len()) {
        let x = al.get(i).copied().unwrap_or("<eof>");
        let y = bl.get(i).copied().unwrap_or("<eof>");
        if x != y {
            return format!("  line {}:\n  - {x}\n  + {y}", i + 1);
        }
    }
    String::from("  (no line diff; whitespace at end?)")
}

/// T2-12: every diagnostic of a negative example carries the offending source
/// (`found`, §18.1), but one whose main range is empty: there `found` is not
/// given (§18.1: an empty range or one of blanks has none; a line that ends
/// where it cannot is reported at the end of its code, W3-06). Whether a code
/// needs a fix candidate is the registry's (`Code::fix_rule`), checked on
/// every diagnostic by [`compare`].
fn negative_rules(run: &mut CaseRun, path: &str, diags: &[Diagnostic]) {
    if !path.contains("negative") {
        return;
    }
    for d in diags.iter().filter(|d| lacks_found(d)) {
        run.problems.push(Problem::Failed(format!("{} at {} has no `found` text", d.code.as_str(), d.span.start)));
    }
}

/// The diagnostic has a main range with text but no `found` ([`negative_rules`]).
fn lacks_found(d: &Diagnostic) -> bool {
    !d.span.is_empty() && d.found.as_deref().is_none_or(str::is_empty)
}

/// `mode = "test"`: every `test` block, as `onsa test` runs them (T3-8).
/// `markers` are compared with the E0200 `onsa test` reports before the
/// tests run (none when the case's markers belong to another stage).
fn run_tests(
    run: &mut CaseRun,
    path: &str,
    sources: &SourceMap,
    module: &onsa_core::Module,
    markers: &[(FileId, Expected)],
    testfails: &[(String, String)],
) {
    let report = match onsa_driver::run_tests(sources, module, &onsa_driver::TestOptions::default()) {
        Ok(onsa_driver::TestRun::Ran(r)) => r,
        // Without `--filter` every test is selected.
        Ok(onsa_driver::TestRun::NoMatch) => {
            run.problems.push(Problem::Failed("`onsa test` without `--filter` selected no test".into()));
            return;
        }
        Ok(onsa_driver::TestRun::Unsupported(diagnostics)) => {
            if compare(run, sources, markers, &diagnostics, Stage::Test, None) {
                negative_rules(run, path, &diagnostics);
            }
            run.problems.extend(crate::fix_contract::unchecked(sources, &diagnostics));
            return;
        }
        Err(e) => {
            run.problems.push(internal_problem(sources, &e, None));
            return;
        }
    };
    compare(run, sources, markers, &[], Stage::Test, None);
    for t in &report.tests {
        let failed = t.status() == onsa_driver::TestStatus::Failed;
        let testfail = testfails.iter().any(|(m, n)| *m == t.module && *n == t.name);
        match (failed, testfail) {
            (true, false) => run.problems.push(Problem::TestFailed {
                full: t.full_name(),
                message: t.message().unwrap_or_default().to_string(),
            }),
            (false, true) => {
                run.problems.push(Problem::Failed(format!("test {} passed but is marked TESTFAIL", t.full_name())))
            }
            _ => {}
        }
        run.tests.push(TestResult {
            module: t.module.clone(),
            name: t.name.clone(),
            failed,
            message: t.message().map(str::to_string),
            testfail,
        });
    }
    if report.tests.is_empty() {
        run.problems.push(Problem::Case("`mode = \"test\"` but the case has no `test` block".into()));
    }
    for (module, name) in testfails {
        if !report.tests.iter().any(|t| t.module == *module && t.name == *name) {
            run.problems.push(Problem::Case(format!("TESTFAIL names an unknown test \"{name}\" of module `{module}`")));
        }
    }
}

// ------------------------------------------------------------ the pending list

/// The full name text of a test (§11.8): what `onsa test` shows and matches.
fn full_name(t: &TestResult) -> String {
    onsa_core::TestMark { module: t.module.clone(), name: t.name.clone() }.full_name()
}

/// The test an entry `<path>::<name>` names (R-184): the test whose full name
/// text is `name` (`dsp.voice "decays"`), else the one test whose name is
/// `name`. A name of tests of several modules names none of them.
fn pending_test<'t>(tests: &'t [TestResult], name: &str) -> Result<&'t TestResult, String> {
    if let Some(t) = tests.iter().find(|t| full_name(t) == name) {
        return Ok(t);
    }
    let by_name: Vec<&TestResult> = tests.iter().filter(|t| t.name == name).collect();
    match by_name[..] {
        [t] => Ok(t),
        [] => Err(format!("tests/pending.toml lists the test \"{name}\", which the case does not have")),
        _ => Err(format!(
            "tests/pending.toml lists the test \"{name}\", a name of tests of several modules; write the full name \
             (`{}`)",
            by_name.iter().map(|t| full_name(t)).collect::<Vec<_>>().join("`, `")
        )),
    }
}

/// A case after the list of pending tests is applied.
#[derive(Debug, Clone)]
pub struct CaseReport {
    pub run: CaseRun,
    /// Listed as a whole (`<path>`) and failing as expected.
    pub pending: Option<pending::Entry>,
    /// Tests listed one by one (`<path>::<name>`) that failed as expected.
    pub pending_tests: Vec<String>,
    /// Host sequences listed one by one (`<path>::<name>`) that failed as expected.
    pub pending_hosts: Vec<String>,
    /// Fix candidates listed (kind `fix-contract`) that break the contract as expected.
    pub pending_fixes: Vec<String>,
    /// What fails the case after the list is applied.
    pub failures: Vec<String>,
}

/// Every case, and the failures that belong to no case.
#[derive(Debug, Clone, Default)]
pub struct Report {
    pub cases: Vec<CaseReport>,
    pub failures: Vec<String>,
}

impl Report {
    pub fn failed(&self) -> bool {
        !self.failures.is_empty() || self.cases.iter().any(|c| !c.failures.is_empty())
    }

    pub fn failures_text(&self) -> String {
        let mut out = self.failures.join("\n");
        for c in self.cases.iter().filter(|c| !c.failures.is_empty()) {
            let _ = write!(out, "\n{}:\n  {}", c.run.path, c.failures.join("\n").replace('\n', "\n  "));
        }
        out.trim_start().to_string()
    }

    pub fn summary(&self) -> String {
        let n = self.cases.len();
        let ran = self.cases.iter().filter(|c| c.run.ran).count();
        let none = self.cases.iter().filter(|c| c.run.mode == Mode::None && c.run.problems.is_empty()).count();
        let pending: Vec<&CaseReport> = self.cases.iter().filter(|c| c.pending.is_some()).collect();
        let tests: usize = self.cases.iter().map(|c| c.pending_tests.len()).sum();
        let failed = self.cases.iter().filter(|c| !c.failures.is_empty()).count();
        let mut by_stage: BTreeMap<Stage, usize> = BTreeMap::new();
        for c in self.cases.iter().filter(|c| c.pending.is_none()) {
            for m in &c.run.checked {
                *by_stage.entry(m.stage).or_default() += 1;
            }
        }
        let mut s = format!(
            "{n} cases: {ran} ran, {none} with mode none, {} pending, {tests} pending tests, {failed} failed",
            pending.len()
        );
        let hosts: Vec<&crate::host::SeqResult> = self.cases.iter().flat_map(|c| &c.run.hosts).collect();
        let passed: Vec<usize> = hosts
            .iter()
            .filter_map(|h| match h.outcome {
                crate::host::Outcome::Passed { compared } => Some(compared),
                _ => None,
            })
            .collect();
        let pending_hosts: usize = self.cases.iter().map(|c| c.pending_hosts.len()).sum();
        let declared: usize = self.cases.iter().map(|c| c.run.host_names.len()).sum();
        let _ = write!(
            s,
            "\nhost sequences: {declared} declared, {} passed ({} values compared), {pending_hosts} pending",
            passed.len(),
            passed.iter().sum::<usize>()
        );
        let stages: Vec<String> = by_stage.iter().map(|(k, v)| format!("{v} at {k:?}").to_lowercase()).collect();
        let _ = write!(s, "\nmarkers compared: {}", if stages.is_empty() { "none".into() } else { stages.join(", ") });
        for c in &pending {
            let e = c.pending.as_ref().expect("pending");
            let _ = write!(s, "\npending {} (until {}: {})", c.run.path, e.until, e.note);
        }
        for c in self.cases.iter().filter(|c| !c.pending_tests.is_empty()) {
            let _ = write!(s, "\npending tests of {}: {}", c.run.path, c.pending_tests.join(", "));
        }
        for c in self.cases.iter().filter(|c| !c.pending_hosts.is_empty()) {
            let _ = write!(s, "\npending host sequences of {}: {}", c.run.path, c.pending_hosts.join(", "));
        }
        let checked: usize = self.cases.iter().map(|c| c.run.fix_targets.len()).sum();
        let pending_fixes: usize = self.cases.iter().map(|c| c.pending_fixes.len()).sum();
        let breaking = self
            .cases
            .iter()
            .flat_map(|c| &c.run.problems)
            .filter(|p| matches!(p, Problem::FixContract { .. } | Problem::FixUnchecked(_)))
            .count();
        let _ = write!(
            s,
            "\nfix candidates checked against the contract (§18.1): {checked}, {pending_fixes} pending, \
             {breaking} failing"
        );
        for c in &self.cases {
            for n in &c.run.notes {
                let _ = write!(s, "\n{}: {n}", c.run.path);
            }
        }
        s
    }
}

/// Apply the `test-case` entries of the list to the runs (plan D-16 7, W1-01).
pub fn reconcile(runs: Vec<CaseRun>, list: &Pending) -> Report {
    let mut report = Report::default();
    let entries: Vec<(&pending::Entry, &str, Option<&str>)> = list
        .of_kind(pending::Kind::TestCase)
        .map(|e| match e.target.split_once("::") {
            Some((p, n)) => (e, p, Some(n)),
            None => (e, e.target.as_str(), None),
        })
        .collect();
    let paths: BTreeSet<&str> = runs.iter().map(|r| r.path.as_str()).collect();
    for (e, p, _) in &entries {
        if !paths.contains(p) {
            report.failures.push(format!(
                "tests/pending.toml: `{}` names no case (cases are the .onsa files and package directories under tests/, \
                 except {})",
                e.target,
                case::EXCLUDED.iter().map(|(x, _)| *x).collect::<Vec<_>>().join(", ")
            ));
        }
    }
    // The fix candidates (W3-17): an entry names one candidate the runner checked.
    let fix_entries: Vec<&pending::Entry> = list.of_kind(pending::Kind::FixContract).collect();
    let checked: BTreeSet<&str> = runs.iter().flat_map(|r| r.fix_targets.iter().map(String::as_str)).collect();
    for e in &fix_entries {
        if !checked.contains(e.target.as_str()) {
            report.failures.push(format!(
                "tests/pending.toml: the fix-contract entry `{}` names no fix candidate the runner checked \
                 (`<file from the root>:<line>:<col> <code> fix<K>` of a diagnostic of a case's check)",
                e.target
            ));
        }
    }
    for mut run in runs {
        let mut failures = Vec::new();
        let mut pending_fixes = Vec::new();
        for e in fix_entries.iter().filter(|e| run.fix_targets.contains(&e.target)) {
            let before = run.problems.len();
            run.problems.retain(|p| !matches!(p, Problem::FixContract { target, .. } if *target == e.target));
            if run.problems.len() < before {
                pending_fixes.push(e.target.clone());
            } else {
                failures.push(format!(
                    "the fix candidate {} keeps the contract but is listed in tests/pending.toml (until {}); \
                     remove the entry",
                    e.target, e.until
                ));
            }
        }
        let mine: Vec<&(&pending::Entry, &str, Option<&str>)> =
            entries.iter().filter(|(_, p, _)| *p == run.path).collect();
        let whole: Vec<&pending::Entry> = mine.iter().filter(|(_, _, n)| n.is_none()).map(|(e, _, _)| *e).collect();
        let named: Vec<(&pending::Entry, &str)> = mine.iter().filter_map(|(e, _, n)| n.map(|n| (*e, n))).collect();
        let mut pending_entry = None;
        let mut pending_tests = Vec::new();
        let mut pending_hosts = Vec::new();
        if !mine.is_empty() && run.mode == Mode::None && run.problems.is_empty() {
            failures.push("listed in tests/pending.toml, but `mode = \"none\"` never runs".to_string());
        } else if whole.len() > 1 || (!whole.is_empty() && !named.is_empty()) {
            failures.push("listed in tests/pending.toml more than once (as a whole and by test)".to_string());
        } else if let Some(e) = whole.first() {
            let expects_internal = e.expect == Some(pending::Expect::Internal);
            let internal = run.problems.iter().any(|p| matches!(p, Problem::Internal(_)));
            // Never silenced: the errors of the case and of the harness, an
            // internal error the entry does not expect, and the fix
            // candidates (each is listed on its own, W3-17).
            let kept = |p: &Problem| match p {
                Problem::Case(_) | Problem::Harness(_) | Problem::FixContract { .. } | Problem::FixUnchecked(_) => true,
                Problem::Internal(_) => !expects_internal,
                _ => false,
            };
            let (case_errors, others): (Vec<&Problem>, Vec<&Problem>) = run.problems.iter().partition(|p| kept(p));
            failures.extend(case_errors.iter().map(|p| p.text()));
            if others.is_empty() && case_errors.is_empty() {
                failures
                    .push(format!("passes but is listed in tests/pending.toml (until {}); remove the entry", e.until));
            } else if case_errors.is_empty() && expects_internal && !internal {
                failures.push(format!(
                    "is listed in tests/pending.toml with `expect = \"internal\"`, but fails without an internal error: {}",
                    others.iter().map(|p| p.text()).collect::<Vec<_>>().join("; ")
                ));
            } else if case_errors.is_empty() {
                pending_entry = Some((*e).clone());
            }
            run.problems.retain(kept);
        } else {
            for (e, name) in &named {
                if run.host_names.iter().any(|h| h == name) {
                    let before = run.problems.len();
                    run.problems.retain(|p| !matches!(p, Problem::Host { name: n, .. } if n == name));
                    let passed = run
                        .hosts
                        .iter()
                        .any(|h| h.name == *name && matches!(h.outcome, crate::host::Outcome::Passed { .. }));
                    if run.problems.len() < before {
                        pending_hosts.push(name.to_string());
                    } else if passed {
                        failures.push(format!(
                            "the host sequence \"{name}\" passes but is listed in tests/pending.toml (until {}); \
                             remove the entry",
                            e.until
                        ));
                    } else {
                        failures.push(format!(
                            "tests/pending.toml lists the host sequence \"{name}\", but it did not run; the entry \
                             holds only the failures of its own steps"
                        ));
                    }
                    continue;
                }
                if run.mode != Mode::Test {
                    failures.push(format!(
                        "tests/pending.toml lists the test \"{name}\", but the case is not `mode = \"test\"`"
                    ));
                    continue;
                }
                let t = match pending_test(&run.tests, name) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(e);
                        continue;
                    }
                };
                let full = full_name(t);
                if t.testfail {
                    failures.push(format!(
                        "the test \"{name}\" is both marked TESTFAIL and listed in tests/pending.toml; keep one"
                    ));
                    continue;
                }
                let before = run.problems.len();
                run.problems.retain(|p| !matches!(p, Problem::TestFailed { full: f, .. } if *f == full));
                if run.problems.len() < before {
                    pending_tests.push(name.to_string());
                } else {
                    failures.push(format!(
                        "the test \"{name}\" passes but is listed in tests/pending.toml (until {}); remove the entry",
                        e.until
                    ));
                }
            }
            failures.extend(run.problems.iter().map(Problem::text));
        }
        report.cases.push(CaseReport {
            run,
            pending: pending_entry,
            pending_tests,
            pending_hosts,
            pending_fixes,
            failures,
        });
    }
    report
}

// ------------------------------------------------------------ everything

/// Collect every case under `root/tests`, run them (in parallel), apply the
/// pending list and check the golden files (collisions, orphans).
pub fn run_all(root: &Path) -> Report {
    let (cases, scan_errors) = case::collect(root);
    let (list, list_error) = match Pending::load(root) {
        Ok(l) => (l, None),
        Err(e) => (Pending::default(), Some(e)),
    };
    let listed_whole: BTreeSet<&str> =
        list.of_kind(pending::Kind::TestCase).filter(|e| !e.target.contains("::")).map(|e| e.target.as_str()).collect();
    let mut owners: BTreeMap<String, String> = BTreeMap::new();
    let mut golden_failures = Vec::new();
    for c in &cases {
        for g in golden::declared(c) {
            if let Some(other) = owners.insert(g.clone(), c.path.clone()) {
                golden_failures.push(format!("{g} is declared by both {other} and {}; rename one case", c.path));
            }
        }
    }
    let runs = run_each(root, &cases, |c| !listed_whole.contains(c.path.as_str()), HostSteps::Run);
    let mut report = reconcile(runs, &list);
    if let Some(e) = list_error {
        report.failures.push(e);
    }
    report.failures.extend(golden_failures);
    report.failures.extend(scan_errors);
    let declared: BTreeSet<String> = owners.into_keys().collect();
    for o in golden::orphans(root, &declared) {
        report.failures.push(format!("{o}: no case declares this golden file; remove it or declare it"));
    }
    report.failures.extend(crate::fixes::orphans(root, &fix_sources(&cases)));
    // Nothing passes without a candidate checked (plan §8.5).
    if report.cases.iter().all(|c| c.run.fix_targets.is_empty()) {
        report.failures.push(
            "no fix candidate was checked against the contract of §18.1 (S-236, W3-17): the cases give none".into(),
        );
    }
    report
}

/// Every source file of a case on disk (from the root) with the case's `fixes = N`.
fn fix_sources(cases: &[Case]) -> Vec<(std::path::PathBuf, u32)> {
    let mut out = Vec::new();
    for c in cases {
        let Ok(s) = &c.setup else { continue };
        for f in &s.input.files {
            let p = match c.kind {
                case::CaseKind::File => std::path::PathBuf::from(&c.path),
                case::CaseKind::Package => Path::new(&c.path).join(&f.path),
            };
            out.push((p, s.test.fixes));
        }
    }
    out
}

/// Run every case (in parallel), in the order of `cases`, without applying the
/// pending list. `write_golden` tells whether `UPDATE_GOLDEN` may rewrite the
/// golden files of a case; `host_steps`, whether the host sequences run.
pub fn run_each(
    root: &Path,
    cases: &[Case],
    write_golden: impl Fn(&Case) -> bool + Sync,
    host_steps: HostSteps,
) -> Vec<CaseRun> {
    run_parallel(cases, |c| run_case(root, c, RunOptions { write_golden: write_golden(c), host_steps }))
}

/// The runs as JSON, for the gate's count of negative examples (K-13): what
/// each case is, and every marker it compared, at which stage and target, and
/// whether a diagnostic matched it. The pending list is not applied; the gate
/// applies it (`tools/diag_codes.py`).
///
/// ```text
/// {"cases": [{"path": "tests/spec/negative/flow.onsa", "mode": "check", "ran": true,
///             "markers": [{"code": "E0815", "file": "tests/spec/negative/flow.onsa",
///                          "line": 75, "stage": "check", "target": null, "matched": true}],
///             "problems": [{"kind": "failed", "text": "..."}]}],
///  "errors": []}
/// ```
///
/// The kinds of a problem: `failed`, `test-failed`, `case` and `internal`
/// ([`Problem::kind`]).
///
/// `file` is the file's name in the case's source map: its repository path
/// for a file without a manifest, its path inside the package otherwise.
pub fn runs_json(runs: &[CaseRun], errors: &[String]) -> serde_json::Value {
    let cases: Vec<serde_json::Value> = runs
        .iter()
        .map(|r| {
            let markers: Vec<serde_json::Value> = r
                .checked
                .iter()
                .map(|m| {
                    serde_json::json!({
                        "code": m.code.as_str(),
                        "file": m.file,
                        "line": m.line,
                        "stage": m.stage,
                        "target": m.target,
                        "matched": m.matched,
                    })
                })
                .collect();
            serde_json::json!({
                "path": r.path,
                "mode": r.mode,
                "ran": r.ran,
                "markers": markers,
                "problems": r.problems.iter().map(|p| serde_json::json!({ "kind": p.kind(), "text": p.text() })).collect::<Vec<_>>(),
            })
        })
        .collect();
    serde_json::json!({ "cases": cases, "errors": errors })
}

fn run_parallel(cases: &[Case], f: impl Fn(&Case) -> CaseRun + Sync) -> Vec<CaseRun> {
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<CaseRun>>> = Mutex::new(vec![None; cases.len()]);
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get()).min(cases.len().max(1));
    std::thread::scope(|s| {
        for _ in 0..workers {
            // The stack of a command (`onsa_diag::stack`), as in the CLI.
            onsa_diag::stack::spawn_scoped(s, "onsa-case", || {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    let Some(c) = cases.get(i) else { break };
                    // A panic outside the driver's stages: an internal error (S-67).
                    let r = onsa_driver::guard(|| f(c)).unwrap_or_else(|e| CaseRun {
                        path: c.path.clone(),
                        problems: vec![internal_problem(&SourceMap::default(), &e, None)],
                        ..Default::default()
                    });
                    results.lock().expect("results")[i] = Some(r);
                }
            })
            .expect("spawn a worker");
        }
    });
    results.into_inner().expect("results").into_iter().map(|r| r.expect("every case ran")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn a_negative_example_needs_found_but_with_an_empty_range() {
        let d = |start: u32, end: u32| {
            Diagnostic::new(
                onsa_diag::Stage::Syntax,
                onsa_diag::Code::E0002,
                onsa_diag::Span::new(onsa_diag::FileId(0), start, end),
                "m",
            )
        };
        assert!(lacks_found(&d(3, 5)), "a range with text and no `found`");
        assert!(!lacks_found(&d(3, 5).with_found("ab")));
        assert!(!lacks_found(&d(4, 4)), "an empty range has no `found` (§18.1)");
    }

    /// A made-up repository: `files` under its root, `tests/pending.toml` included.
    struct Repo(PathBuf);

    impl Repo {
        fn new(tag: &str, files: &[(&str, &str)]) -> Repo {
            let root = crate::c::scratch_dir("onsa_test", &format!("run_{tag}"));
            let _ = std::fs::remove_dir_all(&root);
            for (p, text) in files {
                let p = root.join(p);
                std::fs::create_dir_all(p.parent().unwrap()).unwrap();
                std::fs::write(p, text).unwrap();
            }
            if !root.join(pending::PATH).exists() {
                std::fs::write(root.join(pending::PATH), "").unwrap();
            }
            Repo(root)
        }

        fn run(&self) -> Report {
            run_all(&self.0)
        }
    }

    impl Drop for Repo {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn entry(target: &str) -> String {
        format!(
            "[[pending]]\nkind = \"test-case\"\ntarget = \"{target}\"\nreasons = [\"R-80\"]\nuntil = \"W9-01\"\nnote = \"n\"\n\n"
        )
    }

    const MANIFEST: &str = "// onsa.toml\n// [package]\n// name = \"m\"\n// edition = \"2026\"\n//\n// [export]\n// prefix = \"onsa_\"\n// flows = [\"m.f\"]\n//\n// [targets.a]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n// panic = \"trap\"\n// provides = []\n//\n// [targets.b]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n// panic = \"poison\"\n// provides = []\n";

    fn case<'a>(r: &'a Report, path: &str) -> &'a CaseReport {
        r.cases.iter().find(|c| c.run.path == path).unwrap_or_else(|| panic!("no case {path}"))
    }

    #[test]
    fn build_stage_markers() {
        // E0809 comes from the build of each target (the check is clean).
        let src = format!(
            "{MANIFEST}\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample {{ //~ E0809\n  x * k\n}}\n"
        );
        let targeted = src.replace("//~ E0809", "//~ E0809 [a] //~ E0809 [b]");
        let only_a = src.replace("//~ E0809", "//~ E0809 [a]");
        let repo = Repo::new(
            "build",
            &[("tests/all/m.onsa", &src), ("tests/each/m.onsa", &targeted), ("tests/only_a/m.onsa", &only_a)],
        );
        let r = repo.run();
        // The E0809 of the build has a candidate (add `@param`), which the runner cannot
        // check again (W3-17): it fails on each build, never silenced.
        let unchecked = |f: &String| f.contains("m.onsa:24:30 E0809 fix1: a candidate of the build stage");
        for p in ["tests/all/m.onsa", "tests/each/m.onsa"] {
            let c = case(&r, p);
            assert!(c.failures.len() == 2 && c.failures.iter().all(unchecked), "{p}: {:?}", c.failures);
            let stages: Vec<(Stage, Option<&str>, bool)> =
                c.run.checked.iter().map(|m| (m.stage, m.target.as_deref(), m.matched)).collect();
            assert_eq!(stages, [(Stage::Build, Some("a"), true), (Stage::Build, Some("b"), true)], "{p}");
        }
        // `b` reports E0809 too, but no marker expects it there.
        let c = case(&r, "tests/only_a/m.onsa");
        let differs: Vec<&String> = c.failures.iter().filter(|f| !unchecked(f)).collect();
        assert_eq!(differs.len(), 1, "{:?}", c.failures);
        assert!(differs[0].contains("the build of `b` differs"), "{:?}", c.failures);
    }

    #[test]
    fn errors_of_the_case() {
        let check_error = format!("{MANIFEST}\npub fn g() -> I32 {{ x }} //~ E0302 [a]\n");
        let unknown_target = format!(
            "{MANIFEST}\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample {{ //~ E0809 [z]\n  x * k\n}}\n"
        );
        let golden_and_build = MANIFEST.to_string()
            + "//\n// [test]\n// golden = [\"c\"]\n\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample { //~ E0809\n  x * k\n}\n";
        let old_mode = "//! mode: parse\nfn f() {}\n";
        let repo = Repo::new(
            "errors",
            &[
                ("tests/check_error/m.onsa", &check_error),
                ("tests/unknown_target/m.onsa", &unknown_target),
                ("tests/golden_and_build/m.onsa", &golden_and_build),
                ("tests/old_mode.onsa", old_mode),
                ("tests/golden/c/stale.c", "x"),
                (pending::PATH, &entry("tests/old_mode.onsa")),
            ],
        );
        let r = repo.run();
        let has = |p: &str, needle: &str| {
            let c = case(&r, p);
            assert!(c.failures.iter().any(|f| f.contains(needle)), "{p}: {:?}", c.failures);
        };
        has("tests/check_error/m.onsa", "the build stage does not run");
        has("tests/unknown_target/m.onsa", "not a target of the case");
        has("tests/golden_and_build/m.onsa", "expects build diagnostics, but the case declares its golden C");
        // an error of the case is never pending
        has("tests/old_mode.onsa", "`//! mode:` is gone");
        assert!(r.failures.iter().any(|f| f.contains("tests/golden/c/stale.c: no case declares")), "{:?}", r.failures);
    }

    #[test]
    fn fmt_and_parser_checks() {
        let repo = Repo::new(
            "fmt",
            &[
                ("tests/ugly.onsa", "pub fn f()->I32{1}\n"),
                ("tests/none.onsa", "// onsa.toml\n// [test]\n// mode = \"none\"\n\nif c { a }\n"),
                (
                    "tests/syntax.onsa",
                    // E0003 only the syntax stage reports: its marker must come from the parser.
                    "// onsa.toml\n// [test]\n// mode = \"parse\"\n\npub fn f() -> I32 { 1 } //~ E0003\n",
                ),
            ],
        );
        let r = repo.run();
        assert!(case(&r, "tests/ugly.onsa").failures.iter().any(|f| f.contains("fmt changes it")));
        assert!(case(&r, "tests/none.onsa").failures.is_empty());
        assert!(
            case(&r, "tests/syntax.onsa").failures.iter().any(|f| f.contains("the parser's diagnostics differ")),
            "{:?}",
            case(&r, "tests/syntax.onsa").failures
        );
    }

    #[test]
    fn fix_files() {
        // `fixes = 1`: the candidate of `let mut` gives the `.fix1` file, compared
        // without the whitespace tokens; a wrong one, a missing count and an orphan fail.
        let src = "// onsa.toml\n// [test]\n// fixes = 1\n\npub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n";
        let good = src.replace("let mut n = 0 ", "var  n = 0 ");
        let bad = src.replace("let mut n = 0 ", "var n = 1 ");
        let two = src.replace("fixes = 1", "fixes = 2");
        let repo = Repo::new(
            "fixes",
            &[
                ("tests/good.onsa", src),
                ("tests/good.onsa.fix1", &good),
                ("tests/bad.onsa", src),
                ("tests/bad.onsa.fix1", &bad),
                ("tests/two.onsa", &two),
                ("tests/two.onsa.fix1", &good),
                ("tests/stray.onsa.fix1", "x"),
                ("tests/good.onsa.fix2", "x"),
            ],
        );
        let r = repo.run();
        assert!(case(&r, "tests/good.onsa").failures.is_empty(), "{:?}", case(&r, "tests/good.onsa").failures);
        let bad = &case(&r, "tests/bad.onsa").failures;
        assert!(
            bad.iter().any(|f| f.contains("differs from bad.onsa.fix1: expected `1` (line 6), got `0`")),
            "{bad:?}"
        );
        let two = &case(&r, "tests/two.onsa").failures;
        assert!(two.iter().any(|f| f.contains("no diagnostic has a candidate 2")), "{two:?}");
        assert!(r.failures.iter().any(|f| f.contains("tests/stray.onsa.fix1: no case declares")), "{:?}", r.failures);
        assert!(r.failures.iter().any(|f| f.contains("tests/good.onsa.fix2: its case declares `fixes = 1`")));
    }

    fn fix_entry(target: &str) -> String {
        format!(
            "[[pending]]\nkind = \"fix-contract\"\ntarget = \"{target}\"\nreasons = [\"S-236\"]\nuntil = \"W9-01\"\nnote = \"n\"\n\n"
        )
    }

    /// W3-17: every candidate is applied alone and the case checked again
    /// (§18.1, S-236); `[[test.fix]]` and the entries of kind `fix-contract`.
    #[test]
    fn fix_contract() {
        // The candidate of the E0411 gives `x.narrow_i32()`, an `Option[I32]`: an E0401 is left
        // (until W5-02, a candidate that breaks the contract).
        let breaks = "pub fn f(x: I64) -> I32 {\n  x as I32 //~ E0411\n}\n";
        let keeps = "pub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n";
        // Two errors in one unit: the candidate of `i32` leaves the E0020 of `f32`.
        let two = |leaves: &str| {
            format!(
                "// onsa.toml\n// [[test.fix]]\n// at = \"8:13\"\n// code = \"E0020\"\n// candidate = 1\n// leaves = [{leaves}]\n\n\
                 pub fn g(x: i32) -> f32 {{ //~ E0020\n  1.0\n}}\n"
            )
        };
        let promise = |what: &str, at: &str, body: &str| {
            format!(
                "// onsa.toml\n// [[test.fix]]\n// at = \"{at}\"\n// code = \"E0020\"\n// candidate = 1\n// {what} = true\n\n{body}"
            )
        };
        let two_units = "pub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n\npub fn g() -> I32 {\n  let mut m = 0 //~ E0020\n  m\n}\n";
        let list = [
            fix_entry("tests/listed.onsa:2:3 E0411 fix1"),
            fix_entry("tests/keeps_listed.onsa:2:3 E0020 fix1"),
            fix_entry("tests/nothing.onsa:2:3 E0411 fix1"),
            fix_entry("tests/breaks.onsa:2:3 E0411 fix2"),
            entry("tests/whole.onsa"),
        ]
        .concat();
        let repo = Repo::new(
            "fix_contract",
            &[
                ("tests/breaks.onsa", breaks),
                ("tests/listed.onsa", breaks),
                ("tests/whole.onsa", &breaks.replace("//~ E0411", "")),
                ("tests/keeps.onsa", keeps),
                ("tests/keeps_listed.onsa", keeps),
                ("tests/leaves_right.onsa", &two("\"8:21 E0020\"")),
                ("tests/leaves_wrong.onsa", &two("\"8:22 E0020\"")),
                // The candidate of `let mut` changes the code: `same_code` does not hold.
                ("tests/same_code.onsa", &promise("same_code", "9:3", keeps)),
                ("tests/clean.onsa", &promise("clean", "9:3", two_units)),
                ("tests/clean_ok.onsa", &promise("clean", "9:3", keeps)),
                ("tests/no_diagnostic.onsa", &promise("clean", "9:3", "pub fn f() -> I32 {\n  1\n}\n")),
                (pending::PATH, &list),
            ],
        );
        let r = repo.run();
        let failures = |p: &str| case(&r, p).failures.clone();
        let has = |p: &str, needle: &str| {
            let f = failures(p);
            assert!(f.iter().any(|x| x.contains(needle)), "{p}: {f:?}");
        };
        has("tests/breaks.onsa", "fix candidate tests/breaks.onsa:2:3 E0411 fix1");
        has("tests/breaks.onsa", "hold 2:3 E0401 of its stage or an earlier one; expected none");
        // An entry silences its candidate only.
        let listed = case(&r, "tests/listed.onsa");
        assert!(listed.failures.is_empty(), "{:?}", listed.failures);
        assert_eq!(listed.pending_fixes, ["tests/listed.onsa:2:3 E0411 fix1"]);
        // A whole-case entry does not silence a candidate.
        has("tests/whole.onsa", "fix candidate tests/whole.onsa:2:3 E0411 fix1");
        assert!(case(&r, "tests/keeps.onsa").failures.is_empty(), "{:?}", failures("tests/keeps.onsa"));
        has("tests/keeps_listed.onsa", "keeps the contract but is listed");
        for t in ["tests/nothing.onsa:2:3 E0411 fix1", "tests/breaks.onsa:2:3 E0411 fix2"] {
            assert!(
                r.failures.iter().any(|f| f.contains(t) && f.contains("names no fix candidate")),
                "{t}: {:?}",
                r.failures
            );
        }
        assert!(failures("tests/leaves_right.onsa").is_empty(), "{:?}", failures("tests/leaves_right.onsa"));
        has(
            "tests/leaves_wrong.onsa",
            "hold 8:21 E0020 of its stage or an earlier one; expected 8:22 E0020 (`leaves`)",
        );
        has("tests/same_code.onsa", "`same_code`: in tests/same_code.onsa, token 9: `let` before, `var` after");
        has("tests/clean.onsa", "`clean`: the check after it reports E0020 at 14:3");
        assert!(failures("tests/clean_ok.onsa").is_empty(), "{:?}", failures("tests/clean_ok.onsa"));
        has("tests/no_diagnostic.onsa", "error in the case: line 2: [[test.fix]]: no diagnostic E0020 at 9:3");
        let checked: usize = r.cases.iter().map(|c| c.run.fix_targets.len()).sum();
        assert_eq!(checked, 11, "{:?}", r.cases.iter().map(|c| &c.run.fix_targets).collect::<Vec<_>>());
        assert!(!r.failures.iter().any(|f| f.contains("no fix candidate was checked")), "{:?}", r.failures);
        // A package names the file of a place; its candidates are named from the root.
        let toml = "[package]\nname = \"p\"\nedition = \"2026\"\n";
        let in_pkg = |at: &str, leaf: &str| {
            format!(
                "// onsa.toml\n// [[test.fix]]\n// at = \"{at}\"\n// code = \"E0020\"\n// candidate = 1\n// leaves = [\"{leaf}\"]\n\n\
                 pub fn g(x: i32) -> f32 {{ //~ E0020\n  1.0\n}}\n"
            )
        };
        let pkg = Repo::new(
            "fix_contract_pkg",
            &[
                ("tests/right/onsa.toml", toml),
                ("tests/right/a.onsa", &in_pkg("a.onsa:8:13", "a.onsa:8:21 E0020")),
                ("tests/bare/onsa.toml", toml),
                ("tests/bare/a.onsa", &in_pkg("8:13", "8:21 E0020")),
            ],
        );
        let r = pkg.run();
        let right = case(&r, "tests/right");
        assert!(right.failures.is_empty(), "{:?}", right.failures);
        assert_eq!(right.run.fix_targets, ["tests/right/a.onsa:8:13 E0020 fix1"]);
        let bare = &case(&r, "tests/bare").failures;
        assert!(bare.iter().any(|f| f.contains("a package names the file")), "{bare:?}");
        // A candidate in a `mode = "parse"` case cannot be checked: it fails.
        let parse = Repo::new(
            "fix_contract_parse",
            &[(
                "tests/p.onsa",
                "// onsa.toml\n// [test]\n// mode = \"parse\"\n\npub fn g(x: i32) -> I32 { //~ E0020\n  1\n}\n",
            )],
        );
        let r = parse.run();
        let p = &case(&r, "tests/p.onsa").failures;
        assert!(
            p.iter().any(|f| f.contains("tests/p.onsa:5:13 E0020 fix1") && f.contains("mode = \"parse\"")),
            "{p:?}"
        );
        // Nothing passes without a candidate checked.
        let none = Repo::new("fix_contract_none", &[("tests/plain.onsa", "pub fn f() -> I32 {\n  1\n}\n")]);
        let r = none.run();
        assert!(r.failures.iter().any(|f| f.contains("no fix candidate was checked")), "{:?}", r.failures);
    }

    #[test]
    fn conformance_scope() {
        let head = |flows: &str| {
            format!(
                "// onsa.toml\n// [package]\n// name = \"m\"\n// edition = \"2026\"\n//\n// [export]\n// prefix = \"onsa_\"\n\
                 // flows = [{flows}]\n//\n// [targets.t]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n\
                 // panic = \"trap\"\n// provides = []\n//\n// [test]\n// conformance = true\n\n"
            )
        };
        let two = "pub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n\npub flow g(x: F32 at sample) -> F32 at sample {\n  x * 2.0\n}\n";
        let init_only = "pub flow f(x: F32 at sample, n: F32 at init) -> F32 at sample {\n  x * n\n}\n";
        let repo = Repo::new(
            "conformance",
            &[
                ("tests/partial/m.onsa", &(head("\"m.f\"") + two)),
                ("tests/empty/m.onsa", &(head("") + two)),
                ("tests/init/m.onsa", &(head("\"m.f\"") + init_only)),
                ("tests/full/m.onsa", &(head("\"m.f\", \"m.g\"") + two)),
            ],
        );
        let r = repo.run();
        let has = |p: &str, needle: &str| {
            let c = case(&r, p);
            assert!(c.failures.iter().any(|f| f.contains(needle)), "{p}: {:?}", c.failures);
        };
        has("tests/partial/m.onsa", "`m.g` is not in `[export] flows`");
        has("tests/empty/m.onsa", "needs `[export] flows`");
        // The C checks run the builds (`crate::ccheck`); the runner keeps them.
        for p in ["tests/init/m.onsa", "tests/full/m.onsa"] {
            let c = case(&r, p);
            assert!(c.failures.is_empty(), "{p}: {:?}", c.failures);
            let builds: Vec<(&str, bool)> = c.run.builds.iter().map(|b| (b.target.as_str(), b.conformance)).collect();
            assert_eq!(builds, [("t", true)], "{p}");
        }
    }

    #[test]
    fn small_holes() {
        let bad_target = MANIFEST.replace("panic = \"poison\"", "panic = \"boom\"") + "\npub fn f() -> I32 {\n  1\n}\n";
        let flow = |name: &str| {
            MANIFEST.replace("name = \"m\"", &format!("name = \"{name}\"")).replace("m.f", &format!("{name}.f"))
                + "\npub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n"
        };
        let repo = Repo::new(
            "holes",
            &[
                ("tests/testfail.onsa", "test \"x\" { //~ TESTFAIL \"x\"\n  assert 1 == 2\n}\n"),
                ("tests/none.onsa", "// onsa.toml\n// [test]\n// mode = \"none\"\n\nx //~ E9999\n"),
                ("tests/no_tests.onsa", "// onsa.toml\n// [test]\n// mode = \"test\"\n\npub fn f() -> I32 {\n  1\n}\n"),
                ("tests/bad_target/m.onsa", &bad_target),
                ("tests/a_b.onsa", &flow("a_b")),
                ("tests/a/b.onsa", &flow("b")),
                ("tests/onsa.toml", "[package]\nname = \"all\"\nedition = \"2026\"\n"),
                ("tests/locked/x.onsa", "pub fn f() -> I32 {\n  1\n}\n"),
                (pending::PATH, &entry("tests/bad_target/m.onsa")),
            ],
        );
        let locked = repo.0.join("tests/locked");
        let mut perm = std::fs::metadata(&locked).unwrap().permissions();
        std::os::unix::fs::PermissionsExt::set_mode(&mut perm, 0o000);
        std::fs::set_permissions(&locked, perm.clone()).unwrap();
        let r = repo.run();
        std::os::unix::fs::PermissionsExt::set_mode(&mut perm, 0o755);
        std::fs::set_permissions(&locked, perm).unwrap();
        let has = |p: &str, needle: &str| {
            let c = case(&r, p);
            assert!(c.failures.iter().any(|f| f.contains(needle)), "{p}: {:?}", c.failures);
        };
        has("tests/testfail.onsa", "`//~ TESTFAIL` needs `mode = \"test\"`");
        has("tests/none.onsa", "unknown code `E9999`");
        has("tests/no_tests.onsa", "has no `test` block");
        // the case's own settings are wrong: never pending
        has("tests/bad_target/m.onsa", "unknown panic setting `boom`");
        assert!(case(&r, "tests/bad_target/m.onsa").pending.is_none());
        // the two flatten to the same name; each has its own scratch directory
        for p in ["tests/a_b.onsa", "tests/a/b.onsa"] {
            assert!(case(&r, p).failures.is_empty(), "{p}: {:?}", case(&r, p).failures);
        }
        assert!(r.failures.iter().any(|f| f.contains("the root of the cases is not a package")), "{:?}", r.failures);
        assert!(r.failures.iter().any(|f| f.contains("tests/locked: cannot read the directory")), "{:?}", r.failures);
    }

    #[test]
    fn pending_list() {
        let failing = "pub fn f() -> I32 { 1 } //~ E0302\n";
        let passing = "pub fn f() -> I32 { 1 }\n";
        let tests = "// onsa.toml\n// [test]\n// mode = \"test\"\n\ntest \"bad\" {\n  assert 1 == 2\n}\n\ntest \"good\" {\n  assert 1 == 1\n}\n";
        let list = [
            entry("tests/failing.onsa"),
            entry("tests/passing.onsa"),
            entry("tests/gone.onsa"),
            entry("tests/tests.onsa::bad"),
            entry("tests/tests.onsa::good"),
            entry("tests/tests.onsa::missing"),
        ]
        .concat();
        let repo = Repo::new(
            "pending",
            &[
                ("tests/failing.onsa", failing),
                ("tests/passing.onsa", passing),
                ("tests/tests.onsa", tests),
                (pending::PATH, &list),
            ],
        );
        let r = repo.run();
        let c = case(&r, "tests/failing.onsa");
        assert!(c.failures.is_empty() && c.pending.is_some(), "{:?}", c.failures);
        let c = case(&r, "tests/passing.onsa");
        assert!(c.failures.iter().any(|f| f.contains("passes but is listed")), "{:?}", c.failures);
        assert!(r.failures.iter().any(|f| f.contains("`tests/gone.onsa` names no case")), "{:?}", r.failures);
        let c = case(&r, "tests/tests.onsa");
        assert_eq!(c.pending_tests, ["bad"]);
        assert_eq!(c.failures.len(), 2, "{:?}", c.failures);
        assert!(c.failures[0].contains("\"good\" passes but is listed"), "{:?}", c.failures);
        assert!(c.failures[1].contains("does not have"), "{:?}", c.failures);
    }

    /// R-184: a test is identified by its module path and name (§11.8):
    /// `TESTFAIL` names the test of the module of its file, an entry names a
    /// test by its full name text, and a bare name of tests of several
    /// modules names none of them.
    #[test]
    fn tests_are_identified_by_module_and_name() {
        let manifest = "[package]\nname = \"p\"\nedition = \"2026\"\n";
        let a = "// onsa.toml\n// [test]\n// mode = \"test\"\n\ntest \"same\" { //~ TESTFAIL \"same\"\n  assert 1 == 2\n}\n";
        let b = "test \"same\" {\n  assert 1 == 2\n}\n";
        let run = |tag: &str, target: &str| {
            let list = entry(target);
            let files =
                [("tests/p/onsa.toml", manifest), ("tests/p/a.onsa", a), ("tests/p/b.onsa", b), (pending::PATH, &list)];
            Repo::new(tag, &files).run()
        };
        // The entry is TOML: the quotes of the full name text are escaped.
        let r = run("by_module", r#"tests/p::b \"same\""#);
        let c = case(&r, "tests/p");
        assert!(c.failures.is_empty(), "{:?}", c.failures);
        assert_eq!(c.pending_tests, [r#"b "same""#]);

        let r = run("by_module_bare", "tests/p::same");
        let c = case(&r, "tests/p");
        assert!(c.failures.iter().any(|f| f.contains("several modules")), "{:?}", c.failures);
        assert!(c.failures.iter().any(|f| f.contains(r#"test b "same" failed"#)), "{:?}", c.failures);
    }

    /// W1-04: an internal error is not silenced by the list, unless the entry
    /// expects it (`expect = "internal"`).
    #[test]
    fn internal_errors_and_the_list() {
        let run = |path: &str, problems: Vec<Problem>| CaseRun {
            path: path.into(),
            mode: Mode::Check,
            ran: true,
            problems,
            ..Default::default()
        };
        let internal = || Problem::Internal("internal error: boom".into());
        let failed = || Problem::Failed("the check diagnostics differ".into());
        let expect = |e: String| e.replace("note = \"n\"\n", "note = \"n\"\nexpect = \"internal\"\n");
        let list = Pending::parse(
            &[
                entry("tests/plain.onsa"),
                entry("tests/plain_failed.onsa"),
                expect(entry("tests/expected.onsa")),
                expect(entry("tests/expected_other.onsa")),
                expect(entry("tests/expected_passes.onsa")),
            ]
            .concat(),
        )
        .unwrap();
        let runs = vec![
            run("tests/plain.onsa", vec![failed(), internal()]),
            run("tests/plain_failed.onsa", vec![failed()]),
            run("tests/expected.onsa", vec![failed(), internal()]),
            run("tests/expected_other.onsa", vec![failed()]),
            run("tests/expected_passes.onsa", vec![]),
            run("tests/unlisted.onsa", vec![internal()]),
        ];
        let r = reconcile(runs, &list);
        let c = |p: &str| r.cases.iter().find(|c| c.run.path == p).unwrap();
        // without `expect`: the internal error is never pending
        assert_eq!(c("tests/plain.onsa").failures, ["internal error: boom"]);
        assert!(c("tests/plain.onsa").pending.is_none());
        assert!(c("tests/plain_failed.onsa").failures.is_empty() && c("tests/plain_failed.onsa").pending.is_some());
        // with it: pending only while the case ends in an internal error
        assert!(c("tests/expected.onsa").failures.is_empty(), "{:?}", c("tests/expected.onsa").failures);
        assert!(c("tests/expected.onsa").pending.is_some());
        let other = &c("tests/expected_other.onsa").failures;
        assert!(other.len() == 1 && other[0].contains("fails without an internal error"), "{other:?}");
        let passes = &c("tests/expected_passes.onsa").failures;
        assert!(passes.len() == 1 && passes[0].contains("passes but is listed"), "{passes:?}");
        assert_eq!(c("tests/unlisted.onsa").failures, ["internal error: boom"]);
    }

    #[test]
    fn runs_as_json() {
        let src = format!(
            "{MANIFEST}\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample {{ //~ E0809\n  x * k\n}}\n"
        );
        let repo = Repo::new(
            "json",
            &[
                ("tests/build/m.onsa", &src),
                ("tests/check.onsa", "pub fn f() -> I32 { y } //~ E0302\n"),
                ("tests/wrong.onsa", "pub fn f() -> I32 { 1 } //~ E0302\n"),
                ("tests/none.onsa", "// onsa.toml\n// [test]\n// mode = \"none\"\n\nx //~ E0302\n"),
            ],
        );
        let (cases, errors) = case::collect(&repo.0);
        let runs = run_each(&repo.0, &cases, |_| false, HostSteps::Skip);
        let json = runs_json(&runs, &errors);
        let case = |p: &str| json["cases"].as_array().unwrap().iter().find(|c| c["path"] == p).unwrap().clone();
        // a marker without targets is compared once per target
        let b = case("tests/build/m.onsa");
        assert_eq!(b["mode"], "check");
        assert_eq!(b["ran"], true);
        let m = b["markers"].as_array().unwrap();
        assert_eq!(m.len(), 2, "{b}");
        assert_eq!(m[0]["code"], "E0809");
        assert_eq!(m[0]["file"], "m.onsa");
        assert_eq!(m[0]["stage"], "build");
        assert_eq!(m[0]["target"], "a");
        assert_eq!(m[1]["target"], "b");
        assert_eq!(m[0]["matched"], true);
        let c = case("tests/check.onsa");
        assert_eq!(c["markers"][0]["file"], "tests/check.onsa");
        assert_eq!(c["markers"][0]["stage"], "check");
        assert_eq!(c["markers"][0]["target"], serde_json::Value::Null);
        assert_eq!(c["markers"][0]["matched"], true);
        assert_eq!(c["problems"].as_array().unwrap().len(), 0);
        // a marker that no diagnostic matched is listed as not matched, with the problem
        let w = case("tests/wrong.onsa");
        assert_eq!(w["markers"][0]["matched"], false);
        assert_eq!(w["problems"].as_array().unwrap().len(), 1);
        assert_eq!(w["problems"][0]["kind"], "failed");
        assert!(w["problems"][0]["text"].as_str().unwrap().contains("differ from the markers"), "{w}");
        // `mode = "none"` compares nothing
        let n = case("tests/none.onsa");
        assert_eq!(n["mode"], "none");
        assert_eq!(n["ran"], false);
        assert_eq!(n["markers"].as_array().unwrap().len(), 0);
        assert_eq!(json["errors"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn package_fragments() {
        let toml = "[package]\nname = \"p\"\nedition = \"2026\"\n";
        let frag = "// onsa.toml\n// [test]\n// spec = [\"§15.1\"]\n\npub fn f() -> I32 { 1 }\n";
        let repo = Repo::new(
            "packages",
            &[
                ("tests/one/onsa.toml", toml),
                ("tests/one/a.onsa", frag),
                ("tests/one/b.onsa", "pub fn g() -> I32 { 2 }\n"),
                ("tests/two/onsa.toml", toml),
                ("tests/two/a.onsa", frag),
                ("tests/two/b.onsa", frag),
                ("tests/three/onsa.toml", toml),
                ("tests/three/m.onsa", &format!("{MANIFEST}\npub fn f() -> I32 {{ 1 }}\n")),
            ],
        );
        let r = repo.run();
        let c = case(&r, "tests/one");
        assert!(c.failures.is_empty(), "{:?}", c.failures);
        assert!(case(&r, "tests/two").failures.iter().any(|f| f.contains("a second fragment")));
        assert!(case(&r, "tests/three").failures.iter().any(|f| f.contains("holds only `[test]`")));
    }
}
