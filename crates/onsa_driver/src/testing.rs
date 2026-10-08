//! `onsa test` (spec §11.8, §18.1, §18.2; T3-8, W2-10): which tests run,
//! running them in the interpreter, and their results as the text of
//! `docs/onsa-tools.md` §4 and the JSON document of §18.1.
//!
//! A test is a function of Core with a [`onsa_core::TestMark`]: its module
//! path and name identify it (S-55, R-68). The order of the steps (§18.2,
//! S-242): the checks and the E0200 that do not depend on the target come
//! first, on the whole package (the caller has lowered it), then `--filter`
//! is matched, then the E0200 of the interpreter that the selected tests
//! reach (§15.2, W2-13), then the tests run.

use onsa_diag::{Diagnostic, SourceMap, Span};
use serde::Serialize;

use crate::{InternalError, debug_contract, fill_found, guard_on_stack, reduce};

/// Options of `onsa test`.
#[derive(Debug, Default, Clone)]
pub struct TestOptions {
    /// Run only the tests whose full name text (§11.8) holds this text.
    pub filter: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TestStatus {
    Ok,
    Failed,
}

/// Outcome of one `test` block.
#[derive(Debug, Clone)]
pub struct TestOutcome {
    /// The module path (`dsp.voice`).
    pub module: String,
    /// The value of the name.
    pub name: String,
    /// What a failed test reports; `None` for one that passed.
    pub failure: Option<TestFailure>,
}

/// How a test failed (§18.1, S-233).
#[derive(Debug, Clone)]
pub struct TestFailure {
    /// `assert <source of the expression>` for an `assert`, the message of
    /// the panic otherwise.
    pub message: String,
    /// The position of the expression that panicked (the whole statement for
    /// an `assert`).
    pub span: Span,
    /// The positions of the calls from the panic back to the body of the
    /// test, innermost first; empty when `span` is in the body of the test.
    pub calls: Vec<Span>,
}

impl TestOutcome {
    /// The full name text (§11.8): `dsp.voice "decays"`.
    pub fn full_name(&self) -> String {
        onsa_core::TestMark { module: self.module.clone(), name: self.name.clone() }.full_name()
    }

    /// `failed` when it has a failure (§18.1: only a failed record has one).
    pub fn status(&self) -> TestStatus {
        if self.failure.is_some() { TestStatus::Failed } else { TestStatus::Ok }
    }

    /// The message of a failed test.
    pub fn message(&self) -> Option<&str> {
        self.failure.as_ref().map(|f| f.message.as_str())
    }
}

/// The outcomes of the tests that ran, ordered by module, then name, as
/// strings by code points (§18.1, S-233).
#[derive(Debug, Clone, Default)]
pub struct TestReport {
    pub tests: Vec<TestOutcome>,
}

impl TestReport {
    pub fn failed(&self) -> usize {
        self.tests.iter().filter(|t| t.status() == TestStatus::Failed).count()
    }

    pub fn passed(&self) -> usize {
        self.tests.len() - self.failed()
    }

    /// The text (`docs/onsa-tools.md` §4): a line for each test, `test <full
    /// name text> ok` or `test <full name text> failed at <file>:<line>:
    /// <message>`, then a summary. The file and the line are those of the
    /// `span` of the JSON record. A message of several lines (an `assert` of
    /// an expression written on several lines, S-284) puts its first line on
    /// the line of the test and each of the others on a line of its own,
    /// indented, so that every line that starts with `test` is the line of a
    /// test.
    pub fn render_text(&self, sources: &SourceMap) -> String {
        let mut out = String::new();
        for t in &self.tests {
            match &t.failure {
                None => out.push_str(&format!("test {} ok\n", t.full_name())),
                Some(f) => {
                    let file = sources.file(f.span.file);
                    let line = file.line_col(f.span.start).line;
                    let mut lines = message_lines(&f.message);
                    let first = lines.next().unwrap_or_default();
                    out.push_str(&format!("test {} failed at {}:{line}: {first}\n", t.full_name(), file.name()));
                    for rest in lines {
                        out.push_str(&format!("{CONTINUATION}{rest}\n"));
                    }
                }
            }
        }
        out.push_str(&format!("{} passed, {} failed\n", self.passed(), self.failed()));
        out
    }

    /// The JSON document of `onsa test --json` (§18.1, S-233): the object of
    /// `check --json` with `diagnostics`, and the `tests` array of this
    /// report (empty when no test ran: the run stopped at a diagnostic).
    pub fn render_json(&self, sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
        #[derive(Serialize)]
        struct Document<'a> {
            tests: Vec<Record<'a>>,
        }
        #[derive(Serialize)]
        struct Record<'a> {
            module: &'a str,
            name: &'a str,
            status: &'static str,
            #[serde(skip_serializing_if = "Option::is_none")]
            failure: Option<Failure<'a>>,
        }
        #[derive(Serialize)]
        struct Failure<'a> {
            message: &'a str,
            span: onsa_diag::JsonSpan<'a>,
            calls: Vec<Call<'a>>,
        }
        #[derive(Serialize)]
        struct Call<'a> {
            span: onsa_diag::JsonSpan<'a>,
        }
        let tests = self
            .tests
            .iter()
            .map(|t| Record {
                module: &t.module,
                name: &t.name,
                status: match t.status() {
                    TestStatus::Ok => "ok",
                    TestStatus::Failed => "failed",
                },
                failure: t.failure.as_ref().map(|f| Failure {
                    message: &f.message,
                    span: onsa_diag::json_span(sources, f.span),
                    calls: f.calls.iter().map(|&s| Call { span: onsa_diag::json_span(sources, s) }).collect(),
                }),
            })
            .collect();
        onsa_diag::to_json_document(sources, diagnostics, &Document { tests })
    }
}

/// The indentation of the lines of a message after its first in the text
/// (`docs/onsa-tools.md` §4 does not fix its width).
const CONTINUATION: &str = "    ";

/// The lines of `message`, split at the line breaks of spec §2.5 (LF, and CR
/// LF as one). A CR that no LF follows is not a line break.
fn message_lines(message: &str) -> impl Iterator<Item = &str> {
    message.split('\n').map(|l| l.strip_suffix('\r').unwrap_or(l))
}

/// What `onsa test` did with a lowered module.
#[derive(Debug, Clone)]
pub enum TestRun {
    /// The tests `--filter` selected (every test without it) ran.
    Ran(TestReport),
    /// `--filter` selected no test: a usage error, exit code 2 (§18.2).
    NoMatch,
    /// The selected tests reach forms the interpreter of this version cannot
    /// run: E0200 for each (spec §15.2, §18.1, S-224, S-242), and no test ran.
    Unsupported(Vec<Diagnostic>),
}

/// Run the tests of the lowered module that `opts` selects (T3-8). `assert`
/// failures and panics (spec §9.2) fail the test and name the position; a
/// failure of the interpreter itself is an internal error (S-67, R-137).
///
/// `--filter` is matched first (S-242): a filter that selects no test is
/// [`TestRun::NoMatch`]; an empty one, as no filter, selects every test, so
/// a package without tests runs nothing and is not a usage error (S-286).
/// Then, before any test runs, the forms the interpreter cannot run that the
/// selected tests reach (spec §15.2: the tests are the entries of the run)
/// are E0200, all at once ([`onsa_interp::unsupported`]). The interpreter
/// evaluates a `const` only when the run reads it, so no `const` outside
/// that reach is evaluated. The interpreter runs on the stack of a command
/// (R-05).
pub fn run_tests(
    sources: &SourceMap,
    module: &onsa_core::Module,
    opts: &TestOptions,
) -> Result<TestRun, InternalError> {
    guard_on_stack(|| {
        let selected = select(module, opts.filter.as_deref());
        if selected.is_empty() && opts.filter.as_deref().is_some_and(|f| !f.is_empty()) {
            return TestRun::NoMatch;
        }
        let roots: Vec<onsa_core::FnId> = selected.iter().map(|&(id, _)| id).collect();
        let unsupported = onsa_interp::unsupported(module, &roots);
        if unsupported.is_empty() {
            return TestRun::Ran(run_selected(module, &selected));
        }
        // SPEC-GAP(S-309): a use that several tests, or several instances of
        // a generic function, reach is one E0200: the same position, code and
        // message are reported once.
        let mut diagnostics = reduce::exact(unsupported.iter().map(onsa_interp::Unsupported::diagnostic).collect());
        fill_found(sources, &mut diagnostics);
        debug_contract(sources, &diagnostics);
        TestRun::Unsupported(diagnostics)
    })
}

/// The tests of `module` whose full name text holds `filter` (all of them
/// without one: an empty filter is a part of every text), ordered by module,
/// then name (§18.1).
fn select<'m>(module: &'m onsa_core::Module, filter: Option<&str>) -> Vec<(onsa_core::FnId, &'m onsa_core::TestMark)> {
    let mut tests: Vec<(onsa_core::FnId, &onsa_core::TestMark)> = module
        .fns
        .iter()
        .enumerate()
        .filter_map(|(i, f)| Some((onsa_core::FnId(i as u32), f.test.as_ref()?)))
        .filter(|(_, mark)| filter.is_none_or(|text| mark.full_name().contains(text)))
        .collect();
    tests.sort_by(|a, b| (&a.1.module, &a.1.name).cmp(&(&b.1.module, &b.1.name)));
    tests
}

fn run_selected(module: &onsa_core::Module, tests: &[(onsa_core::FnId, &onsa_core::TestMark)]) -> TestReport {
    let interp = onsa_interp::Interp::new(module);
    let mut report = TestReport::default();
    for &(id, mark) in tests {
        let failure = match interp.call(id, Vec::new()) {
            Ok(_) => None,
            Err(onsa_interp::Failure::Panic(p)) => Some(failure_of(module, id, p)),
            // `run_tests` found every one before the tests ran.
            Err(onsa_interp::Failure::Unsupported(u)) => onsa_diag::internal::bug(
                Some(u.span),
                format!("the interpreter reached `{}`, which the check before the tests did not find", u.std_fn),
            ),
        };
        report.tests.push(TestOutcome { module: mark.module.clone(), name: mark.name.clone(), failure });
    }
    report
}

/// The failure of the test `test` from the panic `p`. Its message is the
/// panic's as it is: an `assert` lowers to the panic with the message §11.8
/// gives it (`assert <source>`, `onsa_core` lowering, R-183).
fn failure_of(module: &onsa_core::Module, test: onsa_core::FnId, p: onsa_interp::Panic) -> TestFailure {
    TestFailure { message: p.message, span: p.span, calls: source_calls(module, test, &p.calls) }
}

/// The positions of the calls of `calls` (innermost first, the outermost
/// made by the function `test`) that are calls of the source (§18.1, S-233).
/// A call one generated function of a flow makes to another of the same flow
/// (`render` to `process`, `process` to `tick`) is not written in the source;
/// it is left out, so that the list names no generated function and has the
/// positions of the source only (the flow's call in the test, a `~` call in a
/// flow). The generated functions are those of `module.flows`.
// A call position is the span of the whole call expression (from the
// receiver of a method), as Core holds it (S-283).
fn source_calls(module: &onsa_core::Module, test: onsa_core::FnId, calls: &[onsa_interp::CallSite]) -> Vec<Span> {
    calls
        .iter()
        .enumerate()
        .filter(|&(i, c)| {
            let caller = calls.get(i + 1).map_or(test, |outer| outer.callee);
            !matches!((module.flow_of(caller), module.flow_of(c.callee)), (Some(a), Some(b)) if a == b)
        })
        .map(|(_, c)| c.span)
        .collect()
}
