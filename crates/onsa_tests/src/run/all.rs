//! Every case of the repository: collected, run in parallel and reported.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use onsa_diag::SourceMap;

use crate::case::{self, Case};
use crate::golden::{self, Update};
use crate::pending::{self, Pending};

use super::report::{Report, reconcile};
use super::{CaseRun, HostSteps, RunOptions, internal_problem, run_case};

// ------------------------------------------------------------ everything

/// Collect every case under `root/tests`, run them (in parallel), apply the
/// pending list and check the golden files (collisions, orphans), rewriting
/// them as `UPDATE_GOLDEN` says ([`Update::from_env`]).
pub fn run_all(root: &Path) -> Report {
    run_all_with(root, Update::from_env())
}

/// [`run_all`], rewriting as `update` says (the cases listed as a whole never).
pub fn run_all_with(root: &Path, update: Update) -> Report {
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
    let golden_of = |c: &Case| if listed_whole.contains(c.path.as_str()) { Update::Off } else { update };
    let runs = run_each(root, &cases, golden_of, HostSteps::Run);
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
    if report.cases.iter().all(|c| c.run.edits_compared == 0) {
        report.failures.push("the check of the minimal edit (§18.1, S-251) compared no edit".into());
    }
    if report.cases.iter().all(|c| c.run.clean_units == 0) {
        report.failures.push(
            "the contract of the fix candidates looked at no unit that held no diagnostic before its candidate (X-3)"
                .into(),
        );
    }
    if report.cases.iter().all(|c| c.run.fix_copies == 0 && c.run.copies_rewritten.is_empty()) {
        report.failures.push("no copy of the text after the candidates (.fixK) was compared".into());
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
/// pending list. `golden` tells whether the golden files and copies of a case
/// are rewritten; `host_steps`, whether the host sequences run.
pub fn run_each(
    root: &Path,
    cases: &[Case],
    golden: impl Fn(&Case) -> Update + Sync,
    host_steps: HostSteps,
) -> Vec<CaseRun> {
    run_parallel(cases, |c| run_case(root, c, RunOptions { golden: golden(c), host_steps }))
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
/// ([`Problem::kind`](super::Problem::kind)).
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
