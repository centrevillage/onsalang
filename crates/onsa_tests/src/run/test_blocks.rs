//! The `test` blocks of a case of `mode = "test"`.

use onsa_diag::{FileId, SourceMap};

use crate::{Expected, PanicMark};

use super::markers::{compare, negative_rules};
use super::{CaseRun, Problem, Stage, TestResult, internal_problem};

/// `mode = "test"`: every `test` block, as `onsa test` runs them (T3-8).
/// `markers` are compared with the E0200 `onsa test` reports before the
/// tests run (none when the case's markers belong to another stage).
pub(super) fn run_tests(
    run: &mut CaseRun,
    path: &str,
    sources: &SourceMap,
    module: &onsa_core::Module,
    markers: &[(FileId, Expected)],
    testfails: &[(String, String)],
    panics: &[(String, FileId, PanicMark)],
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
        let panic = panics.iter().find(|(m, _, p)| *m == t.module && p.name == t.name);
        match (&t.failure, testfail, panic) {
            (_, true, Some(_)) => run
                .problems
                .push(Problem::Case(format!("test {} is marked both TESTFAIL and PANIC; keep one", t.full_name()))),
            (Some(f), false, None) => {
                run.problems.push(Problem::TestFailed { full: t.full_name(), message: f.message.clone() })
            }
            (None, true, _) => {
                run.problems.push(Problem::Failed(format!("test {} passed but is marked TESTFAIL", t.full_name())))
            }
            (None, _, Some(_)) => {
                run.problems.push(Problem::Failed(format!("test {} passed but is marked PANIC", t.full_name())))
            }
            (Some(f), _, Some((_, file, p))) => {
                let col = p.col.map(|c| format!(" @{c}")).unwrap_or_default();
                run.problems.extend(panic_mismatch(sources, f, *file, p).map(|e| {
                    Problem::Failed(format!("test {} is marked PANIC at line {}{col}, but {e}", t.full_name(), p.line))
                }))
            }
            _ => {}
        }
        run.tests.push(TestResult {
            module: t.module.clone(),
            name: t.name.clone(),
            failed,
            message: t.message().map(str::to_string),
            testfail,
            panic: panic.is_some(),
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
    for (i, (module, _, p)) in panics.iter().enumerate() {
        let name = &p.name;
        if !report.tests.iter().any(|t| t.module == *module && t.name == *name) {
            run.problems.push(Problem::Case(format!("PANIC names an unknown test \"{name}\" of module `{module}`")));
        } else if panics[..i].iter().any(|(m, _, q)| m == module && q.name == *name) {
            run.problems.push(Problem::Case(format!("PANIC names the test \"{name}\" of module `{module}` twice")));
        }
    }
}

/// How the failure `f` differs from its `//~ PANIC` mark `p` in `file`, if
/// it does (X9-36): it must be a panic at the mark's line (and column) as the
/// body of the test sees it: the outermost of `calls`, or `span` when the
/// panic is in the body (§18.1). A failed assertion of the body itself (an
/// `assert`, a call of `assert_near`: `calls` is empty) is not a panic; one
/// inside a called function is that call's failure, matched by its position.
fn panic_mismatch(sources: &SourceMap, f: &onsa_driver::TestFailure, file: FileId, p: &PanicMark) -> Option<String> {
    if f.calls.is_empty() && f.origin == onsa_core::PanicOrigin::Assert {
        return Some(format!("it failed by an assert: {}", f.message));
    }
    let at = f.calls.last().copied().unwrap_or(f.span);
    let src = sources.file(at.file);
    let lc = src.line_col(at.start);
    if at.file == file && lc.line == p.line && p.col.is_none_or(|c| c == lc.col) {
        return None;
    }
    Some(format!("it panicked at {}:{}:{}: {}", src.name(), lc.line, lc.col, f.message))
}
