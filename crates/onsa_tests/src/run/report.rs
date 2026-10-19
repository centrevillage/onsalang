//! The pending list applied to the runs, and the report of them.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::case;
use crate::fragment::Mode;
use crate::pending::{self, Pending};

use super::{CaseRun, Problem, Stage, TestResult};

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
    /// The problems of the copies (`FixCopy`) of the cases listed as a whole,
    /// not judged ([`reconcile`]).
    pub unjudged_copies: usize,
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
             {breaking} failing; edits compared for the minimal edit: {}; units after them that held no \
             diagnostic before them: {}",
            self.cases.iter().map(|c| c.run.edits_compared).sum::<usize>(),
            self.cases.iter().map(|c| c.run.clean_units).sum::<usize>()
        );
        let copies: usize = self.cases.iter().map(|c| c.run.fix_copies).sum();
        let rewritten: Vec<&String> = self.cases.iter().flat_map(|c| &c.run.copies_rewritten).collect();
        let _ = write!(
            s,
            "\ncopies of the texts after the candidates (.fixK) compared: {copies}; not judged (cases listed as a \
             whole): {}",
            self.unjudged_copies
        );
        let list = |v: &[&String]| v.iter().map(|p| p.as_str()).collect::<Vec<_>>().join(", ");
        if !rewritten.is_empty() {
            let _ = write!(
                s,
                "\ncopies rewritten or removed by UPDATE_GOLDEN=1 ({}): {}",
                rewritten.len(),
                list(&rewritten)
            );
        }
        let forced: Vec<&String> = self.cases.iter().flat_map(|c| &c.run.copies_forced).collect();
        if !forced.is_empty() {
            let _ = write!(
                s,
                "\ncopies rewritten over the guard by UPDATE_GOLDEN=worse ({}): {}",
                forced.len(),
                list(&forced)
            );
        }
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
            // The copies of a pending case are not the output to keep: not
            // judged, neither a failure nor a reason to wait (X-3); counted.
            let before = run.problems.len();
            run.problems.retain(|p| !matches!(p, Problem::FixCopy(_)));
            report.unjudged_copies += before - run.problems.len();
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
                if t.testfail || t.panic {
                    let mark = if t.testfail { "TESTFAIL" } else { "PANIC" };
                    failures.push(format!(
                        "the test \"{name}\" is both marked {mark} and listed in tests/pending.toml; keep one"
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
