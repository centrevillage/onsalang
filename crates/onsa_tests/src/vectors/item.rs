//! The item of an implementation: the fixture's packages built and run,
//! the cases applied to the list, the report.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use onsa_core::Module;

use super::data::Data;
use super::{DIR, FIXTURE, Impl, REGISTRY, c, interp};
use crate::ccheck::{ItemReport, ItemRun};
use crate::pending::{self, Pending};

/// A package of the fixture that is not run.
#[derive(Debug, Clone)]
pub struct NotRun {
    pub pkg: String,
    pub ops: usize,
    pub until: String,
}

/// What an implementation's run found, before the list is applied.
#[derive(Debug, Default)]
pub struct VectorsRun {
    pub run: ItemRun,
    pub not_run: Vec<NotRun>,
    /// Per implementation (and toolchain): `(label, operations, rows compared, held rows)`.
    pub counts: Vec<(String, usize, usize, usize)>,
}

/// The fixture package directory of `pkg`, from the repository root.
pub fn package_path(pkg: &str) -> String {
    format!("{DIR}/{FIXTURE}/{pkg}")
}

/// Why a package of the fixture does not build, and whether that is an
/// internal error of the compiler (S-67).
#[derive(Debug, Clone)]
pub struct BuildFailure {
    pub why: String,
    pub internal: bool,
}

impl BuildFailure {
    pub(super) fn of(why: String) -> BuildFailure {
        BuildFailure { why, internal: false }
    }

    pub(super) fn internal(sources: &onsa_diag::SourceMap, e: &onsa_driver::InternalError) -> BuildFailure {
        BuildFailure { why: e.render(sources).trim_end().to_string(), internal: true }
    }
}

/// A package of the fixture, checked.
pub struct Fixture {
    pub loaded: onsa_driver::Loaded,
    pub analyzed: onsa_driver::Analyzed,
    /// `[export] fns`.
    pub exported: Vec<String>,
}

/// Load and check the fixture package `pkg` (no diagnostics).
pub fn load_fixture(root: &Path, pkg: &str) -> Result<Fixture, BuildFailure> {
    let dir = root.join(package_path(pkg));
    let mut loaded = onsa_driver::load(&[dir]).map_err(BuildFailure::of)?;
    let analyzed = match onsa_driver::analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(e) => return Err(BuildFailure::internal(&loaded.sources, &e)),
    };
    if !analyzed.diagnostics.is_empty() {
        return Err(BuildFailure::of(format!(
            "`onsa check` reports {} diagnostics:\n{}",
            analyzed.diagnostics.len(),
            crate::c::head(&onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics))
        )));
    }
    let exported =
        onsa_driver::ExportSettings::from_manifest(loaded.manifest.as_ref().and_then(|m| m.export.as_ref())).fns;
    Ok(Fixture { loaded, analyzed, exported })
}

/// Lower a checked fixture to Core (`onsa test`'s path).
pub fn lower_fixture(f: &Fixture) -> Result<Module, BuildFailure> {
    match onsa_driver::lower_core(&f.analyzed) {
        Ok(m) => Ok(m),
        Err(onsa_driver::LowerError::Diagnostics(d)) => Err(BuildFailure::of(format!(
            "lowering reports {} diagnostics:\n{}",
            d.len(),
            crate::c::head(&onsa_diag::to_text(&f.loaded.sources, &d))
        ))),
        Err(onsa_driver::LowerError::Internal(e)) => Err(BuildFailure::internal(&f.loaded.sources, &e)),
    }
}

/// Why a package of the fixture does not build: an error of the item, or,
/// when the list holds the package as a whole test case, a package not run
/// (an internal error only with the entry's `expect = "internal"`, W1-04).
pub fn package_failure(out: &mut VectorsRun, data: &Data, list: &Pending, pkg: &str, f: BuildFailure) {
    let path = package_path(pkg);
    let entry =
        list.get(pending::Kind::TestCase, &path).filter(|e| !f.internal || e.expect == Some(pending::Expect::Internal));
    match entry {
        Some(e) => out.not_run.push(NotRun {
            pkg: pkg.to_string(),
            ops: data.ops.iter().filter(|o| o.pkg == pkg).count(),
            until: e.until.clone(),
        }),
        None => out.run.errors.push(format!("{path}: {}", f.why)),
    }
}

/// Check the packages of the registry against the fixture's directories.
pub fn check_packages(root: &Path, data: &Data) -> Vec<String> {
    let dir = root.join(DIR).join(FIXTURE);
    let mut errors = Vec::new();
    let found: BTreeSet<String> = match std::fs::read_dir(&dir) {
        Ok(d) => d
            .filter_map(|e| e.ok())
            .filter(|e| e.path().is_dir())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .collect(),
        Err(e) => return vec![format!("{DIR}/{FIXTURE}: cannot read: {e}")],
    };
    let named: BTreeSet<String> = data.packages().into_iter().map(str::to_string).collect();
    for p in named.difference(&found) {
        errors.push(format!("{REGISTRY} names the package `{p}`, which {DIR}/{FIXTURE} does not have"));
    }
    for p in found.difference(&named) {
        errors.push(format!("{DIR}/{FIXTURE}/{p}: no operation of {REGISTRY} is in it"));
    }
    errors
}

/// Run the item of `which` over the data under `root` and apply the list.
pub fn run_item(root: &Path, which: Impl) -> ItemReport {
    run_item_with(root, which, &c::toolchains())
}

/// [`run_item`] with the C toolchains `tools`.
pub fn run_item_with(root: &Path, which: Impl, tools: &[&'static crate::c::Item]) -> ItemReport {
    let list = Pending::load(root);
    let mut v = match (&list, Data::load(root)) {
        (Err(e), _) => {
            VectorsRun { run: ItemRun { errors: vec![e.clone()], ..Default::default() }, ..Default::default() }
        }
        (_, Err(errors)) => VectorsRun { run: ItemRun { errors, ..Default::default() }, ..Default::default() },
        (Ok(list), Ok(data)) => {
            let errors = check_packages(root, &data);
            if errors.is_empty() {
                let mut v = match which {
                    Impl::Interp => interp::run(root, &data, list),
                    Impl::C => c::run_with(root, &data, list, tools),
                };
                v.run.errors.extend(entries_of_packages_not_run(&data, list, which, &v.not_run));
                if v.run.results.is_empty() && v.run.errors.is_empty() {
                    // Nothing runs: every package is held by the list (never a pass).
                    v.run.errors.push(format!("no operation ran ({} of {REGISTRY})", data.ops.len()));
                }
                v
            } else {
                VectorsRun { run: ItemRun { errors, ..Default::default() }, ..Default::default() }
            }
        }
    };
    let list = list.unwrap_or_default();
    let notes = std::mem::take(&mut v.run.notes);
    let mut report = crate::ccheck::reconcile_cases(which.item(), v.run, &list, which.form());
    report.run.notes = notes;
    report.run.notes.extend(summary(&v.not_run, &v.counts));
    report
}

/// The entries of the item that name an operation of a package not run: errors
/// (they hold nothing; the package's own entry does).
fn entries_of_packages_not_run(data: &Data, list: &Pending, which: Impl, not_run: &[NotRun]) -> Vec<String> {
    let prefix = format!("{}/", which.item());
    let pkgs: BTreeSet<&str> = not_run.iter().map(|n| n.pkg.as_str()).collect();
    list.of_kind(pending::Kind::Gate)
        .filter_map(|e| {
            let case = e.target.strip_prefix(&prefix)?;
            let op = case.split_once('[').map_or(case, |(o, _)| o);
            let o = data.ops.iter().find(|o| o.id == op)?;
            pkgs.contains(o.pkg.as_str()).then(|| {
                format!(
                    "tests/pending.toml: `{}` names an operation of {}, which does not run (the list holds the package \
                     as a whole)",
                    e.target,
                    package_path(&o.pkg)
                )
            })
        })
        .collect()
}

fn summary(not_run: &[NotRun], counts: &[(String, usize, usize, usize)]) -> Vec<String> {
    let mut lines = Vec::new();
    for (label, ops, rows, held) in counts {
        lines.push(format!("{label}: {ops} operations run, {rows} rows compared, {held} held rows run"));
    }
    if !not_run.is_empty() {
        let n: usize = not_run.iter().map(|x| x.ops).sum();
        let pkgs: Vec<String> = not_run.iter().map(|x| format!("{} ({}, until {})", x.pkg, x.ops, x.until)).collect();
        lines.push(format!(
            "not run: {n} operations of the packages the list holds as a whole test case: {}",
            pkgs.join(", ")
        ));
    }
    lines
}

/// The text of a report: the failing and pending cases, the errors, the counts.
pub fn text(r: &ItemReport) -> String {
    let mut s = String::new();
    let pending: BTreeMap<&str, (&str, &str)> =
        r.pending.iter().map(|(c, u, n)| (c.as_str(), (u.as_str(), n.as_str()))).collect();
    for c in r.run.results.iter().filter(|c| !c.problems.is_empty()) {
        let status = if pending.contains_key(c.id.as_str()) { "PENDING" } else { "FAIL" };
        let _ = writeln!(s, "{status:<7} {}/{}", r.item, c.id);
        if let Some((until, note)) = pending.get(c.id.as_str()) {
            // A pending case: its count and its first row.
            let _ = writeln!(s, "          (until {until}, rows = {}: {note})", c.rows.unwrap_or(0));
            for l in c.problems.iter().flat_map(|p| p.lines()).take(2) {
                let _ = writeln!(s, "          {l}");
            }
            continue;
        }
        for p in &c.problems {
            let _ = writeln!(s, "          {}", p.replace('\n', "\n          "));
        }
    }
    for n in &r.run.notes {
        let _ = writeln!(s, "{n}");
    }
    for f in r.run.errors.iter().chain(&r.failures) {
        let _ = writeln!(s, "error: {}", f.replace('\n', "\n  "));
    }
    let failed = r.run.results.iter().filter(|c| !c.problems.is_empty()).count();
    let _ = write!(
        s,
        "{}: {} cases, {failed} failing ({} pending), {} errors: {}",
        r.item,
        r.run.results.len(),
        r.pending.len(),
        r.run.errors.len() + r.failures.len(),
        match r.exit_code() {
            0 => "PASS",
            1 => "FAIL",
            _ => "CANNOT RUN",
        }
    );
    s
}
