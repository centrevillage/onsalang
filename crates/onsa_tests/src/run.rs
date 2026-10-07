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
//!   naming it). A target that builds is compared with its golden C, compiled
//!   with `cc` and, with `conformance`, run in both the interpreter and C.
//!   Then the goldens of `onsa dump --core`, `interface` and `graph`, and in
//!   `"test"` every `test` block (`onsa test`).
//! - Every mode but `"none"`: a file without markers is canonical under `fmt`,
//!   and the parser alone reports exactly the markers of the syntax codes.
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
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

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

/// One `test` block of a `mode = "test"` case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestResult {
    pub name: String,
    pub failed: bool,
    pub message: Option<String>,
    /// Marked `//~ TESTFAIL`.
    pub testfail: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Problem {
    /// A `test` block failed without `TESTFAIL` (`<path>::<name>` may list it).
    TestFailed { name: String, message: String },
    /// The case does not give what it expects (the list may hold it as pending).
    Failed(String),
    /// The case itself is wrong (its fragment, markers or settings): never pending.
    Case(String),
    /// An internal error of the compiler (S-67): pending only by a `test-case`
    /// entry with `expect = "internal"`.
    Internal(String),
}

impl Problem {
    /// The kind, as the JSON report names it.
    pub fn kind(&self) -> &'static str {
        match self {
            Problem::TestFailed { .. } => "test-failed",
            Problem::Failed(_) => "failed",
            Problem::Case(_) => "case",
            Problem::Internal(_) => "internal",
        }
    }

    pub fn text(&self) -> String {
        match self {
            Problem::TestFailed { name, message } => format!("test \"{name}\" failed: {message}"),
            Problem::Failed(m) => m.clone(),
            Problem::Case(m) => format!("error in the case: {m}"),
            Problem::Internal(m) => m.clone(),
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
    /// Information (conformance lines, a skipped compile).
    pub notes: Vec<String>,
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

/// Run one case. `scratch` is a directory of its own for the C files;
/// `write_golden` lets `UPDATE_GOLDEN` rewrite its golden files.
pub fn run_case(root: &Path, case: &Case, scratch: &Path, write_golden: bool) -> CaseRun {
    run_case_with(&Stages::DRIVER, root, case, scratch, write_golden)
}

/// [`run_case`] through `stages`.
pub fn run_case_with(stages: &Stages, root: &Path, case: &Case, scratch: &Path, write_golden: bool) -> CaseRun {
    let mut run = CaseRun { path: case.path.clone(), ..Default::default() };
    let setup = match &case.setup {
        Ok(s) => s,
        Err(e) => {
            run.problems.push(Problem::Case(e.clone()));
            return run;
        }
    };
    run.mode = setup.test.mode;
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
    let mut loaded = Loaded::from_input(setup.input.clone());

    // Markers of every file of the case (line numbers are per file); read in
    // every mode, so a case that does not run cannot hold a broken marker.
    let mut markers: Vec<(FileId, Expected)> = Vec::new();
    let mut testfails: Vec<String> = Vec::new();
    for (file, _) in loaded.modules.clone() {
        let f = loaded.sources.file(file);
        match parse_markers(f.text()) {
            Ok(m) => {
                markers.extend(m.expected.into_iter().map(|e| (file, e)));
                testfails.extend(m.testfails);
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
        if compare(&mut run, &loaded.sources, &markers, check, Stage::Check, None) {
            negative_rules(&mut run, &case.path, check);
        }
        if !check.is_empty() {
            if !t.golden.is_empty() || !t.golden_graph.is_empty() || t.conformance {
                run.problems
                    .push(Problem::Case("golden files and conformance need a check without diagnostics".into()));
            }
            return run;
        }
    } else {
        if t.conformance {
            conformance_scope(&mut run, &loaded, &analyzed);
        }
        for target in &targets {
            let ctx = BuildCtx { stages, root, case, setup, loaded: &loaded, analyzed: &analyzed, markers: &markers };
            build_target(&ctx, target, scratch, write_golden, &mut run);
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
        run_tests(&mut run, &loaded.sources, m, &testfails);
    }
    run
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
fn build_target(ctx: &BuildCtx<'_>, target: &str, scratch: &Path, write_golden: bool, run: &mut CaseRun) {
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
    let out = match (stages.build)(loaded, analyzed, target) {
        Ok(out) => {
            compare(run, &loaded.sources, &expected, &[], Stage::Build, Some(target));
            out
        }
        Err(BuildError::Diagnostics { diagnostics, .. }) => {
            compare(run, &loaded.sources, &expected, &diagnostics, Stage::Build, Some(target));
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
    if !crate::c::has_cc() {
        run.notes.push(format!("{target}: no `cc` on the PATH; the C is not compiled"));
        return;
    }
    let dir = scratch.join(target);
    let source = out.files.last().map(|(n, _)| n.clone()).unwrap_or_default();
    if let Err(e) = crate::c::write_files(&dir, &out.files).and_then(|()| crate::c::compile_object(&dir, &source)) {
        run.problems.push(Problem::Failed(format!("{target}: {e}")));
        return;
    }
    if t.conformance {
        let outcome = crate::conformance::run(&out, &dir.join("conformance"));
        run.notes.extend(outcome.report.into_iter().map(|l| format!("{target}: {l}")));
        run.problems.extend(outcome.problems.into_iter().map(|p| Problem::Failed(format!("{target}: {p}"))));
        if outcome.compared == 0 {
            run.problems.push(Problem::Case(format!(
                "{target}: conformance compared no flow (every exported flow was skipped)"
            )));
        }
    }
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

/// Compare the markers with the diagnostics, record every marker compared,
/// and report a difference. Whether they match.
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

/// The parser alone reports exactly the markers of the syntax codes (`E00xx`,
/// `E0320`) of the file; the rest belong to later stages (M1, T1-11).
fn parser_markers(run: &mut CaseRun, sources: &SourceMap, file: FileId, markers: &[(FileId, Expected)]) {
    let f = sources.file(file);
    let syntax = |c: Code| c.as_str().starts_with("E00") || c == Code::E0320;
    let mut expected: Vec<(u32, Code)> =
        markers.iter().filter(|(mf, m)| *mf == file && syntax(m.code)).map(|(_, m)| (m.line, m.code)).collect();
    let parsed = onsa_syntax::parse(file, f.text());
    let mut actual: Vec<(u32, Code)> =
        parsed.diagnostics.iter().map(|d| (f.line_col(d.span.start).line, d.code)).collect();
    expected.sort();
    actual.sort();
    if expected != actual {
        let show =
            |v: &[(u32, Code)]| v.iter().map(|(l, c)| format!("{}@{l}", c.as_str())).collect::<Vec<_>>().join(" ");
        run.problems.push(Problem::Failed(format!(
            "{}: the parser's diagnostics differ from the markers of the syntax codes\n  expected: {}\n  actual:   {}\n  {}",
            f.name(),
            show(&expected),
            show(&actual),
            onsa_diag::to_text(sources, &parsed.diagnostics).replace('\n', "\n  ")
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
/// (`found`), and codes with a unique repair carry a fix (§18.1).
fn negative_rules(run: &mut CaseRun, path: &str, diags: &[Diagnostic]) {
    if !path.contains("negative") {
        return;
    }
    for d in diags {
        if d.found.as_deref().is_none_or(str::is_empty) {
            run.problems.push(Problem::Failed(format!("{} at {} has no `found` text", d.code.as_str(), d.span.start)));
        }
        if matches!(d.code.as_str(), "E0713" | "E0714" | "E0703" | "E0811" | "E0812" | "E0411" | "E0020")
            && d.fixes.is_empty()
        {
            run.problems.push(Problem::Failed(format!("{} at {} has no fix", d.code.as_str(), d.span.start)));
        }
    }
}

/// `mode = "test"`: every `test` block, as `onsa test` runs them (T3-8).
fn run_tests(run: &mut CaseRun, sources: &SourceMap, module: &onsa_core::Module, testfails: &[String]) {
    let report = match onsa_driver::run_tests(module, &onsa_driver::TestOptions::default()) {
        Ok(r) => r,
        Err(e) => {
            run.problems.push(internal_problem(sources, &e, None));
            return;
        }
    };
    for t in &report.tests {
        let failed = t.status == onsa_driver::TestStatus::Failed;
        let testfail = testfails.contains(&t.name);
        match (failed, testfail) {
            (true, false) => run
                .problems
                .push(Problem::TestFailed { name: t.name.clone(), message: t.message.clone().unwrap_or_default() }),
            (false, true) => {
                run.problems.push(Problem::Failed(format!("test \"{}\" passed but is marked TESTFAIL", t.name)))
            }
            _ => {}
        }
        run.tests.push(TestResult { name: t.name.clone(), failed, message: t.message.clone(), testfail });
    }
    if report.tests.is_empty() {
        run.problems.push(Problem::Case("`mode = \"test\"` but the case has no `test` block".into()));
    }
    for name in testfails {
        if !report.tests.iter().any(|t| &t.name == name) {
            run.problems.push(Problem::Case(format!("TESTFAIL names an unknown test \"{name}\"")));
        }
    }
}

// ------------------------------------------------------------ the pending list

/// A case after the list of pending tests is applied.
#[derive(Debug, Clone)]
pub struct CaseReport {
    pub run: CaseRun,
    /// Listed as a whole (`<path>`) and failing as expected.
    pub pending: Option<pending::Entry>,
    /// Tests listed one by one (`<path>::<name>`) that failed as expected.
    pub pending_tests: Vec<String>,
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
        let stages: Vec<String> = by_stage.iter().map(|(k, v)| format!("{v} at {k:?}").to_lowercase()).collect();
        let _ = write!(s, "\nmarkers compared: {}", if stages.is_empty() { "none".into() } else { stages.join(", ") });
        for c in &pending {
            let e = c.pending.as_ref().expect("pending");
            let _ = write!(s, "\npending {} (until {}: {})", c.run.path, e.until, e.note);
        }
        for c in self.cases.iter().filter(|c| !c.pending_tests.is_empty()) {
            let _ = write!(s, "\npending tests of {}: {}", c.run.path, c.pending_tests.join(", "));
        }
        for c in &self.cases {
            for note in &c.run.notes {
                let _ = write!(s, "\n{}: {note}", c.run.path);
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
    for mut run in runs {
        let mut failures = Vec::new();
        let mine: Vec<&(&pending::Entry, &str, Option<&str>)> =
            entries.iter().filter(|(_, p, _)| *p == run.path).collect();
        let whole: Vec<&pending::Entry> = mine.iter().filter(|(_, _, n)| n.is_none()).map(|(e, _, _)| *e).collect();
        let named: Vec<(&pending::Entry, &str)> = mine.iter().filter_map(|(e, _, n)| n.map(|n| (*e, n))).collect();
        let mut pending_entry = None;
        let mut pending_tests = Vec::new();
        if !mine.is_empty() && run.mode == Mode::None && run.problems.is_empty() {
            failures.push("listed in tests/pending.toml, but `mode = \"none\"` never runs".to_string());
        } else if whole.len() > 1 || (!whole.is_empty() && !named.is_empty()) {
            failures.push("listed in tests/pending.toml more than once (as a whole and by test)".to_string());
        } else if let Some(e) = whole.first() {
            let expects_internal = e.expect == Some(pending::Expect::Internal);
            let internal = run.problems.iter().any(|p| matches!(p, Problem::Internal(_)));
            // Never silenced: the errors of the case, and an internal error
            // the entry does not expect.
            let kept = |p: &Problem| match p {
                Problem::Case(_) => true,
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
                if run.mode != Mode::Test {
                    failures.push(format!(
                        "tests/pending.toml lists the test \"{name}\", but the case is not `mode = \"test\"`"
                    ));
                    continue;
                }
                let Some(t) = run.tests.iter().find(|t| t.name == *name) else {
                    failures
                        .push(format!("tests/pending.toml lists the test \"{name}\", which the case does not have"));
                    continue;
                };
                if t.testfail {
                    failures.push(format!(
                        "the test \"{name}\" is both marked TESTFAIL and listed in tests/pending.toml; keep one"
                    ));
                    continue;
                }
                let before = run.problems.len();
                run.problems.retain(|p| !matches!(p, Problem::TestFailed { name: n, .. } if n == name));
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
        report.cases.push(CaseReport { run, pending: pending_entry, pending_tests, failures });
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
    let runs = run_each(root, &cases, |c| !listed_whole.contains(c.path.as_str()));
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
    report
}

/// Run every case (in parallel), in the order of `cases`, without applying the
/// pending list. `write_golden` tells whether `UPDATE_GOLDEN` may rewrite the
/// golden files of a case.
pub fn run_each(root: &Path, cases: &[Case], write_golden: impl Fn(&Case) -> bool + Sync) -> Vec<CaseRun> {
    // A scratch directory of this run (several runs may share the process).
    static RUNS: AtomicUsize = AtomicUsize::new(0);
    let n = RUNS.fetch_add(1, Ordering::SeqCst);
    let scratch = std::env::temp_dir().join(format!("onsa_cases_{}_{n}", std::process::id()));
    // One scratch directory per case, named by its index (paths could collide once flattened).
    let runs = run_parallel(cases, |i, c| {
        let dir = scratch.join(i.to_string());
        run_case(root, c, &dir, write_golden(c))
    });
    let _ = std::fs::remove_dir_all(&scratch);
    runs
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

fn run_parallel(cases: &[Case], f: impl Fn(usize, &Case) -> CaseRun + Sync) -> Vec<CaseRun> {
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<CaseRun>>> = Mutex::new(vec![None; cases.len()]);
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get()).min(cases.len().max(1));
    std::thread::scope(|s| {
        for _ in 0..workers {
            std::thread::Builder::new()
                // SPEC-GAP(S-183): the nesting depth is bounded only by this stack.
                .stack_size(onsa_driver::STACK_SIZE)
                .spawn_scoped(s, || {
                    loop {
                        let i = next.fetch_add(1, Ordering::SeqCst);
                        let Some(c) = cases.get(i) else { break };
                        // A panic outside the driver's stages: an internal error (S-67).
                        let r = onsa_driver::guard(|| f(i, c)).unwrap_or_else(|e| CaseRun {
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

    /// A made-up repository: `files` under its root, `tests/pending.toml` included.
    struct Repo(PathBuf);

    impl Repo {
        fn new(tag: &str, files: &[(&str, &str)]) -> Repo {
            let root = std::env::temp_dir().join(format!("onsa_run_test_{}_{tag}", std::process::id()));
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
        let src = format!("{MANIFEST}\npub flow f(x: Sig[F32], k: Ctl[F32]) -> Sig[F32] {{ //~ E0809\n  x * k\n}}\n");
        let targeted = src.replace("//~ E0809", "//~ E0809 [a] //~ E0809 [b]");
        let only_a = src.replace("//~ E0809", "//~ E0809 [a]");
        let repo = Repo::new(
            "build",
            &[("tests/all/m.onsa", &src), ("tests/each/m.onsa", &targeted), ("tests/only_a/m.onsa", &only_a)],
        );
        let r = repo.run();
        for p in ["tests/all/m.onsa", "tests/each/m.onsa"] {
            let c = case(&r, p);
            assert!(c.failures.is_empty(), "{p}: {:?}", c.failures);
            let stages: Vec<(Stage, Option<&str>, bool)> =
                c.run.checked.iter().map(|m| (m.stage, m.target.as_deref(), m.matched)).collect();
            assert_eq!(stages, [(Stage::Build, Some("a"), true), (Stage::Build, Some("b"), true)], "{p}");
        }
        // `b` reports E0809 too, but no marker expects it there.
        let c = case(&r, "tests/only_a/m.onsa");
        assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
        assert!(c.failures[0].contains("the build of `b` differs"), "{:?}", c.failures);
    }

    #[test]
    fn errors_of_the_case() {
        let check_error = format!("{MANIFEST}\npub fn g() -> I32 {{ x }} //~ E0302 [a]\n");
        let unknown_target =
            format!("{MANIFEST}\npub flow f(x: Sig[F32], k: Ctl[F32]) -> Sig[F32] {{ //~ E0809 [z]\n  x * k\n}}\n");
        let golden_and_build = MANIFEST.to_string()
            + "//\n// [test]\n// golden = [\"c\"]\n\npub flow f(x: Sig[F32], k: Ctl[F32]) -> Sig[F32] { //~ E0809\n  x * k\n}\n";
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
                    "// onsa.toml\n// [test]\n// mode = \"parse\"\n\npub fn f() -> I32 { 1 } //~ E0002\n",
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
    fn conformance_scope() {
        let head = |flows: &str| {
            format!(
                "// onsa.toml\n// [package]\n// name = \"m\"\n// edition = \"2026\"\n//\n// [export]\n// prefix = \"onsa_\"\n\
                 // flows = [{flows}]\n//\n// [targets.t]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n\
                 // panic = \"trap\"\n// provides = []\n//\n// [test]\n// conformance = true\n\n"
            )
        };
        let two =
            "pub flow f(x: Sig[F32]) -> Sig[F32] {\n  x\n}\n\npub flow g(x: Sig[F32]) -> Sig[F32] {\n  x * 2.0\n}\n";
        let init_only = "pub flow f(x: Sig[F32], n: Init[F32]) -> Sig[F32] {\n  x * n\n}\n";
        let repo = Repo::new(
            "conformance",
            &[
                ("tests/partial/m.onsa", &(head("\"m.f\"") + two)),
                ("tests/empty/m.onsa", &(head("") + two)),
                ("tests/skipped/m.onsa", &(head("\"m.f\"") + init_only)),
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
        if crate::c::has_cc() {
            has("tests/skipped/m.onsa", "compared no flow");
            let c = case(&r, "tests/full/m.onsa");
            assert!(c.failures.is_empty(), "{:?}", c.failures);
        }
    }

    #[test]
    fn small_holes() {
        let bad_target = MANIFEST.replace("panic = \"poison\"", "panic = \"boom\"") + "\npub fn f() -> I32 {\n  1\n}\n";
        let flow = |name: &str| {
            MANIFEST.replace("name = \"m\"", &format!("name = \"{name}\"")).replace("m.f", &format!("{name}.f"))
                + "\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  x\n}\n"
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
        let src = format!("{MANIFEST}\npub flow f(x: Sig[F32], k: Ctl[F32]) -> Sig[F32] {{ //~ E0809\n  x * k\n}}\n");
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
        let runs = run_each(&repo.0, &cases, |_| false);
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
