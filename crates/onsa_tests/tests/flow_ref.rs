//! The reference evaluator on the cases of W1-09 (W7-19 U2a): every `test` of the cases of `ROOTS` that the checker passes
//! (or stops only with E0200, a feature that is not in yet) is taken apart and run on the evaluator
//! (`onsa_tests::flow_ref::walk`), its asserts and its marks (`TESTFAIL`, `PANIC`) against what the evaluator gives. The
//! numbers are printed (`--nocapture`); a run that finds nothing, or a case that cannot be lowered and is not in the list
//! of things pending, fails. The data of `tests/flow_ref/` (U2c) is made from what the evaluator gave and compared with the
//! files: `UPDATE_GOLDEN=1` rewrites them, but not when the evaluator and an assert of a case disagree.

use std::collections::BTreeMap;
use std::sync::Mutex;

use onsa_driver::PackageInput;
use onsa_tests::Mode;
use onsa_tests::case::{self, repo_root};
use onsa_tests::flow_ref::data::{self, Counts};
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Skip, Verdict, run_case};
use onsa_tests::golden::{self, Update};
use onsa_tests::pending::{Kind, Pending};

/// The roots of the cases that are run on the evaluator, from the repository root (one place; a root is added here).
const ROOTS: &[&str] = &["tests/spec/flow_semantics/"];

/// The directory of the data, and the files of the cases the halves have run (the last half to finish writes or compares
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
    /// The data of each case: its name, its text and counts.
    files: Vec<(String, String, Counts)>,
    /// How many cases of the roots both halves have.
    total: usize,
}

/// The whole run on a thread of a large stack, the wrappers made and kept in it (the interpreter's values are not `Send`).
fn run(half: usize) -> Tally {
    onsa_diag::stack::run(move || run_all(half))
}

/// The cases of `half` (0 or 1: every other one of the sorted cases, so that one `#[test]` stays under a second).
fn run_all(half: usize) -> Tally {
    let root = repo_root();
    let pending = Pending::load(&root).expect("the list of things pending");
    let (cases, errors) = case::collect(&root);
    assert!(errors.is_empty(), "{errors:?}");
    let wrappers = Wrappers::default();
    let mut t = Tally::default();
    let mine = cases.iter().filter(|c| ROOTS.iter().any(|r| c.path.starts_with(r)));
    let tests = |c: &&case::Case| c.setup.as_ref().is_ok_and(|s| s.test.mode == Mode::Test);
    t.total = mine.clone().filter(tests).count();
    for c in mine.enumerate().filter(|(i, _)| i % 2 == half).map(|(_, c)| c) {
        let setup = c.setup.as_ref().unwrap_or_else(|e| panic!("{}: {e}", c.path));
        if setup.test.mode == Mode::Test {
            tally_case(&mut t, &pending, &wrappers, (&c.path, &c.name), setup.input.clone());
        }
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
        match r.verdict {
            Verdict::Ok => t.evaluated += 1,
            Verdict::Unavailable(why) => *t.unavailable.entry(why).or_default() += 1,
            Verdict::Skipped(s) => *t.skipped.entry(s).or_default() += 1,
            Verdict::Failed(m) => t.failures.push(format!("{path}: \"{}\": {m}", r.name)),
        }
    }
}

#[test]
fn the_cases_of_the_flow_semantics_run_on_the_evaluator_first_half() {
    report(run(0));
}

#[test]
fn the_cases_of_the_flow_semantics_run_on_the_evaluator_second_half() {
    report(run(1));
}

/// The data of the cases of one half against the files (or into them), and when the last half is done, the `MANIFEST`
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
