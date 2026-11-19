//! The reference evaluator on the cases of W1-09 (W7-19 U2a): every `test` of the cases of `ROOTS` that the checker passes
//! (or stops only with E0200, a feature that is not in yet) is taken apart and run on the evaluator
//! (`onsa_tests::flow_ref::walk`), its asserts and its marks (`TESTFAIL`, `PANIC`) against what the evaluator gives. The
//! numbers are printed (`--nocapture`); a run that finds nothing, or a case that cannot be lowered and is not in the list
//! of things pending, fails. The data of `tests/flow_ref/` (U2c) is made from what the evaluator gave and compared with the
//! files: `UPDATE_GOLDEN=1` rewrites them, but not when the evaluator and an assert of a case disagree. Then what the
//! evaluator gave is printed as tests of Onsa and run through the interpreter (`compare.rs`, `print.rs`, U3).

use std::collections::BTreeMap;
use std::sync::Mutex;

use onsa_driver::PackageInput;
use onsa_tests::Mode;
use onsa_tests::case::{self, repo_root};
use onsa_tests::flow_ref::data::{self, Counts};
use onsa_tests::flow_ref::flow::PanicAt;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Panic, Skip, Verdict, run_case};
use onsa_tests::golden::{self, Update};
use onsa_tests::pending::{Kind, Pending};

#[path = "flow_ref/compare.rs"]
mod compare;
#[path = "flow_ref/compare_tests.rs"]
mod compare_tests;
#[path = "flow_ref/print.rs"]
mod print;
#[path = "flow_ref/print_tests.rs"]
mod print_tests;

/// The roots of the cases that are run on the evaluator, from the repository root (one place; a root is added here).
const ROOTS: &[&str] = &["tests/spec/flow_semantics/"];

/// The directory of the data, and the files of the cases the parts have run (the last part to finish writes or compares
/// the `MANIFEST`, which is of all of them).
const DATA: &str = "tests/flow_ref";
static DONE: Mutex<BTreeMap<String, (String, Counts)>> = Mutex::new(BTreeMap::new());

#[derive(Default)]
struct Tally {
    cases: usize,
    not_read: Vec<String>,
    waiting: usize,
    tests: usize,
    asserts: usize,
    evaluated: usize,
    unavailable: BTreeMap<&'static str, usize>,
    skipped: BTreeMap<Skip, usize>,
    failures: Vec<String>,
    /// The tests that panic in the `init` stage (`path: "name"`).
    at_init: Vec<String>,
    /// The data of each case: its name, its text and counts.
    files: Vec<(String, String, Counts)>,
    /// How many cases of the roots all the parts have.
    total: usize,
}

/// The whole run on a thread of a large stack, the wrappers made and kept in it (the interpreter's values are not `Send`).
fn run(part: usize) -> Tally {
    onsa_diag::stack::run(move || run_all(part))
}

/// How many parts the cases are split in (every `PARTS`-th one of the sorted cases to a part, so that one `#[test]` stays
/// under a second).
const PARTS: usize = 4;

/// The cases of the part `part` (below `PARTS`) that are tests (path, name, input), and how many cases of the roots all
/// the parts have.
fn cases_of(part: usize) -> (Vec<(String, String, PackageInput)>, usize) {
    let (cases, errors) = case::collect(&repo_root());
    assert!(errors.is_empty(), "{errors:?}");
    let mine = cases.iter().filter(|c| ROOTS.iter().any(|r| c.path.starts_with(r)));
    let tests = |c: &&case::Case| c.setup.as_ref().is_ok_and(|s| s.test.mode == Mode::Test);
    let total = mine.clone().filter(tests).count();
    let of_part = mine.enumerate().filter(|(i, _)| i % PARTS == part).map(|(_, c)| c);
    let setup = |c: &case::Case| c.setup.as_ref().unwrap_or_else(|e| panic!("{}: {e}", c.path)).clone();
    let all = of_part.map(|c| (c, setup(c))).filter(|(_, s)| s.test.mode == Mode::Test);
    (all.map(|(c, s)| (c.path.clone(), c.name.clone(), s.input)).collect(), total)
}

fn run_all(part: usize) -> Tally {
    let pending = Pending::load(&repo_root()).expect("the list of things pending");
    let wrappers = Wrappers::default();
    let (cases, total) = cases_of(part);
    let mut t = Tally { total, ..Tally::default() };
    for (path, name, input) in cases {
        tally_case(&mut t, &pending, &wrappers, (&path, &name), input);
    }
    t
}

/// The case `path` (named `name`) run and counted in `t`: a case that is not read is a failure (never a silent drop).
fn tally_case(t: &mut Tally, pending: &Pending, wrappers: &Wrappers, (path, name): (&str, &str), input: PackageInput) {
    t.cases += 1;
    let run = match run_case(input, wrappers) {
        Ok(run) => run,
        Err(e) => return t.not_read.push(format!("{path}: {e}")),
    };
    if run.e0200 || !run.lowered {
        t.waiting += 1;
        if pending.get(Kind::TestCase, path).is_none() {
            t.failures.push(format!("{path}: it does not lower and is not in the list of things pending"));
        }
    }
    let (text, counts) = data::case_text(path, &run, run.e0200 || !run.lowered);
    t.files.push((name.to_string(), text, counts));
    for r in run.tests {
        t.tests += 1;
        t.asserts += r.asserts;
        if r.panic == Some(Panic::Call(PanicAt::Init)) {
            t.at_init.push(format!("{path}: \"{}\"", r.name));
        }
        match r.verdict {
            Verdict::Ok => t.evaluated += 1,
            Verdict::Unavailable(why) => *t.unavailable.entry(why).or_default() += 1,
            Verdict::Skipped(s) => *t.skipped.entry(s).or_default() += 1,
            Verdict::Failed(m) => t.failures.push(format!("{path}: \"{}\": {m}", r.name)),
        }
    }
}

#[test]
fn the_cases_of_the_flow_semantics_run_on_the_evaluator_part_0() {
    report(run(0));
}

#[test]
fn the_cases_of_the_flow_semantics_run_on_the_evaluator_part_1() {
    report(run(1));
}

#[test]
fn the_cases_of_the_flow_semantics_run_on_the_evaluator_part_2() {
    report(run(2));
}

#[test]
fn the_cases_of_the_flow_semantics_run_on_the_evaluator_part_3() {
    report(run(3));
}

/// The data of the cases of one part against the files (or into them), and when the last part is done, the `MANIFEST`
/// and the files no case makes (a case that went away). Nothing is written when a case disagrees with its asserts.
fn publish(files: Vec<(String, String, Counts)>, total: usize) -> Vec<String> {
    let (root, update) = (repo_root(), Update::from_env());
    let mut problems: Vec<String> = Vec::new();
    for (name, text, _) in &files {
        problems.extend(golden::compare(&root, &format!("{DATA}/{name}.tsv"), text, update));
    }
    let mut done = DONE.lock().unwrap_or_else(|e| e.into_inner());
    for (name, text, counts) in files {
        if done.insert(name.clone(), (text, counts)).is_some() {
            problems.push(format!("{name}: two cases have the name"));
        }
    }
    if done.len() == total {
        let all: Vec<_> = done.iter().map(|(n, (t, c))| (n.clone(), t.clone(), *c)).collect();
        problems.extend(golden::compare(&root, &format!("{DATA}/MANIFEST"), &data::manifest(&all), update));
        for f in std::fs::read_dir(root.join(DATA)).into_iter().flatten().flatten() {
            let name = f.file_name().to_string_lossy().into_owned();
            let stale = name.strip_suffix(".tsv").is_some_and(|n| !done.contains_key(n));
            if stale && update.writes() {
                problems.extend(std::fs::remove_file(f.path()).err().map(|e| format!("{name}: {e}")));
            } else if stale {
                problems.push(format!("{DATA}/{name} is of no case (run with UPDATE_GOLDEN=1 to remove it)"));
            }
        }
    }
    problems
}

/// What fails the run before the data is looked at: a test the evaluator and its asserts disagree on, and a case not read.
fn failures(t: &Tally) -> Vec<String> {
    t.failures.iter().cloned().chain(t.not_read.iter().map(|m| format!("not read: {m}"))).collect()
}

fn report(mut t: Tally) {
    println!(
        "{} cases ({} not read, {} waiting), {} tests, {} asserts: {} evaluated, {} unavailable, {} skipped",
        t.cases,
        t.not_read.len(),
        t.waiting,
        t.tests,
        t.asserts,
        t.evaluated,
        t.unavailable.values().sum::<usize>(),
        t.skipped.values().sum::<usize>()
    );
    t.unavailable.iter().for_each(|(why, n)| println!("  unavailable {n}: {why}"));
    t.skipped.iter().for_each(|(why, n)| println!("  skipped {n}: {why:?}"));
    t.not_read.iter().for_each(|m| println!("  not read: {m}"));
    let failed = failures(&t);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
    t.failures = publish(std::mem::take(&mut t.files), t.total);
    assert!(t.failures.is_empty(), "{}", t.failures.join("\n"));
    assert!(t.cases > 0 && t.tests > 0 && t.evaluated > 0 && t.asserts > 0, "nothing was run");
}

/// What the interpreter did with the tests the evaluator evaluated, in the cases of one part.
#[derive(Default)]
struct Compared {
    cases: usize,
    /// The cases that do not lower (the list of things pending), and their tests: not compared.
    waiting: usize,
    held: usize,
    /// The tests of the other cases the evaluator evaluated (only these are compared), and those it did not
    /// (unavailable or skipped).
    evaluated: usize,
    left: usize,
    ran: usize,
    asserts: usize,
    panicked: usize,
    unprintable: BTreeMap<String, usize>,
    failures: Vec<String>,
}

fn compare_one(t: &mut Compared, wrappers: &Wrappers, path: &str, input: PackageInput) {
    t.cases += 1;
    let run = match run_case(input.clone(), wrappers) {
        Ok(run) => run,
        Err(e) => return t.failures.push(format!("not read: {path}: {e}")),
    };
    if run.e0200 || !run.lowered {
        (t.waiting, t.held) = (t.waiting + 1, t.held + run.tests.len());
        return;
    }
    let evaluated = run.tests.iter().filter(|r| r.verdict == Verdict::Ok).count();
    (t.evaluated, t.left) = (t.evaluated + evaluated, t.left + run.tests.len() - evaluated);
    let c = compare::compare_case(path, input, &run);
    (t.ran, t.asserts) = (t.ran + c.ran, t.asserts + c.asserts);
    t.panicked += c.panicked;
    c.unprintable.into_iter().for_each(|(why, n)| *t.unprintable.entry(why).or_default() += n);
    t.failures.extend(c.failures);
}

fn compare_part(part: usize) -> Compared {
    onsa_diag::stack::run(move || {
        let (mut t, wrappers) = (Compared::default(), Wrappers::default());
        cases_of(part).0.into_iter().for_each(|(path, _, input)| compare_one(&mut t, &wrappers, &path, input));
        t
    })
}

fn report_compared(t: Compared) {
    let unprintable: usize = t.unprintable.values().sum();
    println!(
        "{} cases ({} waiting with {} tests, not compared): {} tests compared with {} asserts ({} panicked at their last \
         call), {} not printed, {} not evaluated (unavailable or skipped)",
        t.cases, t.waiting, t.held, t.ran, t.asserts, t.panicked, unprintable, t.left
    );
    t.unprintable.iter().for_each(|(why, n)| println!("  not printed {n}: {why}"));
    assert!(t.failures.is_empty(), "{}", t.failures.join("\n"));
    assert_eq!(t.evaluated, t.ran + unprintable, "a test of the evaluator was neither compared nor counted");
    assert!(t.ran > 0 && t.asserts > 0, "nothing was compared");
}

#[test]
#[should_panic(expected = "nothing was compared")]
fn a_run_that_compared_nothing_fails() {
    report_compared(Compared::default());
}

#[test]
#[should_panic(expected = "neither compared nor counted")]
fn a_test_of_the_evaluator_that_was_dropped_fails() {
    // Three tests were evaluated, one was compared and none is counted as not printed.
    report_compared(Compared { evaluated: 3, ran: 1, ..Compared::default() });
}

#[test]
#[should_panic(expected = "a failure of the case")]
fn a_failure_fails_even_when_everything_is_counted() {
    let failures = vec!["a failure of the case".to_string()];
    report_compared(Compared { evaluated: 1, ran: 1, asserts: 1, failures, ..Compared::default() });
}

#[test]
fn the_tests_the_evaluator_evaluated_pass_in_the_interpreter_part_0() {
    report_compared(compare_part(0));
}

#[test]
fn the_tests_the_evaluator_evaluated_pass_in_the_interpreter_part_1() {
    report_compared(compare_part(1));
}

#[test]
fn the_tests_the_evaluator_evaluated_pass_in_the_interpreter_part_2() {
    report_compared(compare_part(2));
}

#[test]
fn the_tests_the_evaluator_evaluated_pass_in_the_interpreter_part_3() {
    report_compared(compare_part(3));
}

/// A case of the flow `acc` (a running sum) and one test with the one `assert`.
fn tally_of_one_case(assert: &str) -> Tally {
    let src = format!(
        "flow acc(x: F32 at sample) -> F32 at sample {{\n  let y = x + prev~(^y)\n  y\n}}\n\
         test \"t\" {{\n  let xs: [F32; 3] = [1.0, 2.0, 3.0]\n  let o = acc.render(xs, 8.0)\n  assert {assert}\n}}\n"
    );
    onsa_diag::stack::run(move || {
        let (mut t, pending) = (Tally::default(), Pending::load(&repo_root()).expect("the list of things pending"));
        let input = PackageInput::single_file("zz_case.onsa", &src);
        tally_case(&mut t, &pending, &Wrappers::default(), ("zz_case.onsa", "zz_case"), input);
        t
    })
}

#[test]
fn a_case_that_is_not_read_fails_the_run() {
    // acc sums its input: 1 3 6, so out[2] is 6.0 (a float); `6` is an integer, which the checker refuses (E0401).
    let ok = tally_of_one_case("o.out[2] == 6.0");
    assert_eq!((ok.cases, ok.evaluated, failures(&ok)), (1, 1, Vec::<String>::new()));
    let bad = tally_of_one_case("o.out[2] == 6");
    assert_eq!((bad.cases, bad.evaluated, bad.files.len()), (1, 0, 0));
    let failed = failures(&bad);
    assert!(failed.len() == 1 && failed[0].starts_with("not read: zz_case.onsa: E0"), "{failed:?}");
}

/// The fixed inputs of the generated flows (W7-19 U4, `tests/flow_ref/corpus/`, not cases: [`case::EXCLUDED`]): each file
/// with its tests and how many of them the evaluator evaluates (the rest is counted, never dropped). A file that is added
/// or made again is a new line here.
const CORPUS: &str = "tests/flow_ref/corpus";
const CORPUS_COUNTS: &[(&str, usize, usize)] =
    &[("clock_twins.onsa", 50, 50), ("expr_a.onsa", 154, 154), ("expr_b.onsa", 141, 141), ("guards.onsa", 40, 40)];

fn corpus() -> Vec<(String, PackageInput)> {
    let root = repo_root();
    let files = case::onsa_files(&root, CORPUS).unwrap_or_else(|e| panic!("{e}"));
    let read = |p: &std::path::Path| std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
    let path = |p: &std::path::Path| case::rel_path(&root, p);
    files.iter().map(|p| (path(p), PackageInput::single_file(path(p), read(p)))).collect()
}

/// What the files of the corpus come to on the evaluator, against `CORPUS_COUNTS`.
fn corpus_failures(files: &[(String, Tally)], expected: &[(&str, usize, usize)]) -> Vec<String> {
    let mut out: Vec<String> =
        files.iter().flat_map(|(p, t)| failures(t).into_iter().map(move |m| format!("{p}: {m}"))).collect();
    // The flows have no `init` input: a panic in `init` is of a constant-clock expression, E0419 at compile time (§11.3), and
    // no test; the interpreter does not give it (a `let` nothing reads is not run).
    out.extend(
        files.iter().flat_map(|(_, t)| t.at_init.iter().map(|m| format!("{m}: it panics in init (E0419, §11.3)"))),
    );
    out.extend(files.iter().filter(|(_, t)| t.waiting > 0).map(|(p, _)| format!("{p}: it does not lower")));
    let got: Vec<(String, usize, usize)> = files.iter().map(|(p, t)| (p.clone(), t.tests, t.evaluated)).collect();
    let want: Vec<(String, usize, usize)> =
        expected.iter().map(|(n, t, e)| (format!("{CORPUS}/{n}"), *t, *e)).collect();
    if got != want {
        out.push(format!("the files, their tests and the tests evaluated are {got:?}, not {want:?}"));
    }
    out
}

fn corpus_on_the_evaluator() -> Vec<(String, Tally)> {
    onsa_diag::stack::run(|| {
        let (pending, wrappers) =
            (Pending::load(&repo_root()).expect("the list of things pending"), Wrappers::default());
        let one = |(path, input): (String, PackageInput)| {
            let mut t = Tally::default();
            tally_case(&mut t, &pending, &wrappers, (&path, &path), input);
            (path, t)
        };
        corpus().into_iter().map(one).collect()
    })
}

#[test]
fn the_corpus_of_generated_flows_runs_on_the_evaluator() {
    let files = corpus_on_the_evaluator();
    for (p, t) in &files {
        let (un, sk) = (t.unavailable.values().sum::<usize>(), t.skipped.values().sum::<usize>());
        println!(
            "{p}: {} tests, {} evaluated, {un} unavailable, {sk} skipped, {} asserts",
            t.tests, t.evaluated, t.asserts
        );
        t.unavailable.iter().for_each(|(why, n)| println!("  unavailable {n}: {why}"));
        t.skipped.iter().for_each(|(why, n)| println!("  skipped {n}: {why:?}"));
    }
    let problems = corpus_failures(&files, CORPUS_COUNTS);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    assert!(!files.is_empty(), "no file of the corpus");
}

#[test]
fn the_corpus_of_generated_flows_passes_in_the_interpreter() {
    let t = onsa_diag::stack::run(|| {
        let (mut t, wrappers) = (Compared::default(), Wrappers::default());
        corpus().into_iter().for_each(|(path, input)| compare_one(&mut t, &wrappers, &path, input));
        t
    });
    let evaluated: usize = CORPUS_COUNTS.iter().map(|(_, _, e)| e).sum();
    assert_eq!(t.evaluated, evaluated, "the tests of the corpus that were evaluated and compared");
    report_compared(t);
}
