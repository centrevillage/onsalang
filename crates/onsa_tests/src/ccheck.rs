//! The gate items of the C checks (Q-07, W1-06): `onsa_cases --c <item>`
//! runs one row of [`crate::c::ITEMS`] over every build of the cases.
//!
//! The builds are the case runner's ([`crate::run::CaseRun::builds`]):
//! every target of a case that built as the case expects (no build marker
//! applies to it), with its golden C or not. An item turns each into cases
//! of its own:
//!
//! ```text
//! <path>[<target>]             a build: compiled with the item's compiler and
//!                              flags; with `[test] conformance`, every flow run
//!                              in the interpreter and in C       (c-clang, c-gcc, c-sanitize, c-x86)
//! <path>[<target>]/<compiler>  the public headers of a build, alone, with one
//!                              compiler of the header check      (c-header, c-header-strict)
//! ```
//!
//! For example `c-gcc/tests/conformance/voice.onsa[host]` and
//! `c-header/tests/conformance/voice.onsa[host]/c++11-g++-15`.
//!
//! ## The pending list (`tests/pending.toml`, kind `gate`)
//!
//! An entry `<item>` (the whole item) is the gate's to apply (`tools/gate.py`):
//! the item only reports. Entries `<item>/<case>` are the item's to apply,
//! case by case:
//!
//! - a listed case that fails is pending (shown, not a failure);
//! - a listed case that passes fails (remove the entry);
//! - an unlisted case that fails fails;
//! - an entry that names no case of the item fails (fix or remove it);
//! - an item listed both whole and by case fails;
//! - what is not a case (a compiler not on the PATH, no build at all, a list
//!   that cannot be read) always fails, with exit code 2: the gate does not
//!   make an item that cannot run pending even when the whole item is listed
//!   (`tools/gate.py`, `CANNOT_RUN`).
//!
//! A flow that conformance cannot drive is counted and shown with the
//! reason, never dropped (R-113 3).

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::c::{self, Check, HeaderCompiler, Item, Toolchain};
use crate::case;
use crate::pending::{self, Pending};
use crate::run::{self, Built};

/// What the failures of a case are, for the entries that may hold them.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum FailureKind {
    /// None is an internal error of the compiler: an entry holds them.
    #[default]
    Ordinary,
    /// Every failure is an internal error (S-67): only an entry with
    /// `expect = "internal"` holds them (W1-04).
    Internal,
    /// Internal errors and other failures: no entry holds them.
    Mixed,
}

/// The result of one case of an item.
#[derive(Debug, Clone, Default)]
pub struct CaseResult {
    pub id: String,
    pub problems: Vec<String>,
    /// What the problems are (the C checks: always ordinary).
    pub failure: FailureKind,
    /// The failing rows the case counts (the test vectors: the rows that
    /// fail, and those a run that ended did not make). `Some`: an entry holds
    /// the case only with `rows` equal to it (more or fewer fail: a new
    /// failure, or one that went away). `None`: the item counts nothing.
    pub rows: Option<usize>,
    /// Which rows fail ([`crate::vectors::judge::digest`]), with `rows`: an
    /// entry holds the case only with the same `digest` (another row failing
    /// instead of one that passes now is a change too).
    pub digest: Option<String>,
    /// The failing rows (their ids, sorted), for the message of an entry to fix.
    pub failing: Vec<String>,
    /// Information (the conformance line of each flow).
    pub notes: Vec<String>,
    /// Flows conformance did not compare: `(flow, reason)`.
    pub skipped: Vec<(String, String)>,
    pub compared: usize,
}

/// What an item found, before the list is applied.
#[derive(Debug, Default)]
pub struct ItemRun {
    pub results: Vec<CaseResult>,
    /// Failures that are not of a case: never pending.
    pub errors: Vec<String>,
    pub notes: Vec<String>,
}

/// Set, it keeps the files of the checks (the build's C, the conformance
/// programs) for a person to read.
pub const KEEP: &str = "ONSA_C_KEEP";

/// The run of an item with the list applied.
#[derive(Debug, Default)]
pub struct ItemReport {
    pub item: String,
    pub run: ItemRun,
    /// `(case, until, note)` of the listed cases that fail as expected.
    pub pending: Vec<(String, String, String)>,
    pub failures: Vec<String>,
    /// The whole item is listed: the gate applies it.
    pub listed_whole: bool,
}

impl ItemReport {
    pub fn failed(&self) -> bool {
        !self.failures.is_empty() || !self.run.errors.is_empty()
    }

    /// 0 passes, 1 fails, 2 cannot run (module docs).
    pub fn exit_code(&self) -> u8 {
        if !self.run.errors.is_empty() {
            2
        } else if self.failed() {
            1
        } else {
            0
        }
    }

    pub fn text(&self) -> String {
        let mut s = String::new();
        let pending: BTreeSet<&str> = self.pending.iter().map(|(c, _, _)| c.as_str()).collect();
        for r in &self.run.results {
            let status = if r.problems.is_empty() {
                "PASS"
            } else if pending.contains(r.id.as_str()) {
                "PENDING"
            } else {
                "FAIL"
            };
            let _ = writeln!(s, "{status:<7} {}", r.id);
            for n in &r.notes {
                let _ = writeln!(s, "          {n}");
            }
            for p in &r.problems {
                let _ = writeln!(s, "          {}", p.replace('\n', "\n          "));
            }
        }
        let compared: usize = self.run.results.iter().map(|r| r.compared).sum();
        let skipped: Vec<String> = self
            .run
            .results
            .iter()
            .flat_map(|r| r.skipped.iter().map(move |(f, why)| format!("{} {f}: {why}", r.id)))
            .collect();
        if compared > 0 || !skipped.is_empty() {
            let _ = writeln!(s, "conformance: {compared} flows compared, {} skipped", skipped.len());
            for k in &skipped {
                let _ = writeln!(s, "  skipped {k}");
            }
        }
        for (c, until, note) in &self.pending {
            let _ = writeln!(s, "pending {}/{c} (until {until}: {note})", self.item);
        }
        for n in &self.run.notes {
            let _ = writeln!(s, "{n}");
        }
        if self.listed_whole {
            let _ = writeln!(s, "the whole item is listed in tests/pending.toml; the gate applies the entry");
        }
        for f in self.run.errors.iter().chain(&self.failures) {
            let _ = writeln!(s, "error: {}", f.replace('\n', "\n  "));
        }
        let n = self.run.results.len();
        let failed = self.run.results.iter().filter(|r| !r.problems.is_empty()).count();
        let _ = write!(
            s,
            "{}: {n} cases, {failed} failing ({} pending), {} errors: {}",
            self.item,
            self.pending.len(),
            self.run.errors.len() + self.failures.len(),
            match self.exit_code() {
                0 => "PASS",
                1 => "FAIL",
                _ => "CANNOT RUN",
            }
        );
        s
    }
}

/// Run `item` over the builds of every case under `root/tests`, and apply the list.
pub fn run_item(root: &Path, item: &Item) -> ItemReport {
    let run = match collect_builds(root) {
        Ok((builds, note)) => {
            let mut run = check(item, &builds);
            run.notes.insert(0, note);
            run
        }
        Err(e) => ItemRun { errors: vec![e], ..Default::default() },
    };
    match Pending::load(root) {
        Ok(list) => reconcile(item.name, run, &list),
        Err(e) => {
            let mut run = run;
            run.errors.push(e);
            reconcile(item.name, run, &Pending::default())
        }
    }
}

/// The builds of the cases with targets, as `(case path, build)`, and a line
/// that counts the targets that gave no build (they expect build
/// diagnostics, or do not build yet: the case runner reports those cases).
pub fn collect_builds(root: &Path) -> Result<(Vec<(String, Built)>, String), String> {
    let (cases, errors) = case::collect(root);
    if !errors.is_empty() {
        return Err(format!("the cases cannot be read:\n{}", errors.join("\n")));
    }
    let cases: Vec<case::Case> =
        cases.into_iter().filter(|c| c.setup.as_ref().is_ok_and(|s| !s.targets().is_empty())).collect();
    let targets: usize = cases.iter().filter_map(|c| c.setup.as_ref().ok()).map(|s| s.targets().len()).sum();
    let runs = run::run_each(root, &cases, |_| false, run::HostSteps::Skip);
    let builds: Vec<(String, Built)> =
        runs.into_iter().flat_map(|r| r.builds.into_iter().map(move |b| (r.path.clone(), b))).collect();
    if builds.is_empty() {
        return Err("no case builds a target; the C checks have nothing to check".into());
    }
    let note = format!(
        "builds: {} of the {targets} targets of {} cases ({} expect build diagnostics or do not build yet; \
         the case runner reports them)",
        builds.len(),
        cases.len(),
        targets - builds.len()
    );
    Ok((builds, note))
}

/// Run the checks of `item` over `builds` (the list is not applied).
pub fn check(item: &Item, builds: &[(String, Built)]) -> ItemRun {
    let mut out = ItemRun { errors: item.cannot_run(), ..Default::default() };
    if !out.errors.is_empty() {
        return out;
    }
    let scratch = c::scratch_dir("onsa_ccheck", item.name);
    let results = parallel(builds.len(), |i| {
        let (path, b) = &builds[i];
        let id = format!("{path}[{}]", b.target);
        let dir = scratch.join(i.to_string());
        match item.check {
            Check::Unit(t) => vec![unit(&id, b, &t, &dir)],
            Check::Headers(cs) => headers(&id, b, cs, &dir),
        }
    });
    out.notes.extend(c::keep_or_remove(&scratch, "the files"));
    out.results = results.into_iter().flatten().collect();
    out
}

fn unit(id: &str, b: &Built, t: &Toolchain, dir: &Path) -> CaseResult {
    let mut r = CaseResult { id: id.to_string(), ..Default::default() };
    let out = &b.output;
    if !out.settings.platform.is_host() {
        r.problems.push(format!(
            "the platform `{}` is not the host; the C checks compile for the host",
            out.settings.platform.triple
        ));
        return r;
    }
    let source = out.files.last().map(|(n, _)| n.clone()).unwrap_or_default();
    if let Err(e) =
        c::write_files(dir, &out.files).and_then(|()| c::compile_object(t, &out.settings.platform.cflags, dir, &source))
    {
        r.problems.push(e);
        return r;
    }
    if b.conformance {
        let o = crate::conformance::run(out, t, &dir.join("conformance"));
        r.notes = o.report;
        r.problems.extend(o.problems);
        r.skipped = o.skipped;
        r.compared = o.compared;
        if o.compared == 0 {
            r.problems.push("conformance compared no flow (every exported flow was skipped)".into());
        }
    }
    r
}

/// Every public header of the build (`CUnit::public_headers`), each alone and twice.
fn headers(id: &str, b: &Built, cs: &[HeaderCompiler], dir: &Path) -> Vec<CaseResult> {
    let out = &b.output;
    let names: Vec<&str> = out.unit.public_headers().into_iter().map(|(n, _)| n).collect();
    let written = c::write_files(dir, &out.files);
    cs.iter()
        .map(|h| {
            let mut r = CaseResult { id: format!("{id}/{}", h.label), ..Default::default() };
            match &written {
                Err(e) => r.problems.push(e.clone()),
                Ok(()) => r.problems.extend(names.iter().filter_map(|n| c::compile_header(h, dir, n).err())),
            }
            r
        })
        .collect()
}

/// Apply the `gate` entries of `item` (module docs).
pub fn reconcile(item: &str, run: ItemRun, list: &Pending) -> ItemReport {
    let form = if matches!(c::item(item).map(|i| i.check), Some(Check::Headers(_))) {
        "`<path>[<target>]/<compiler>`"
    } else {
        "`<path>[<target>]`"
    };
    reconcile_cases(item, run, list, form)
}

/// [`reconcile`] for an item whose cases have the form `form` (for the
/// message of an entry that names no case). An entry holds a failing case
/// only when the kind of its failures fits the entry ([`FailureKind`]).
pub fn reconcile_cases(item: &str, run: ItemRun, list: &Pending, form: &str) -> ItemReport {
    let mut report = ItemReport { item: item.to_string(), ..Default::default() };
    let prefix = format!("{item}/");
    let entries: Vec<&pending::Entry> = list.of_kind(pending::Kind::Gate).collect();
    let whole = entries.iter().any(|e| e.target == item);
    let cases: Vec<(&str, &pending::Entry)> =
        entries.iter().filter_map(|e| e.target.strip_prefix(&prefix).map(|c| (c, *e))).collect();
    if whole && !cases.is_empty() {
        report.failures.push(format!("tests/pending.toml lists `{item}` both as a whole and by case; keep one"));
    }
    report.listed_whole = whole;
    let ids: BTreeSet<&str> = run.results.iter().map(|r| r.id.as_str()).collect();
    for (c, e) in &cases {
        if !ids.contains(c) && run.errors.is_empty() {
            report.failures.push(format!(
                "tests/pending.toml: `{}` names no case of `{item}` (the cases are {form}; until {})",
                e.target, e.until
            ));
        }
    }
    for r in &run.results {
        let listed = cases.iter().find(|(c, _)| *c == r.id).map(|(_, e)| *e);
        match (r.problems.is_empty(), listed) {
            (true, Some(e)) => report.failures.push(format!(
                "{item}/{}: passes but is listed in tests/pending.toml (until {}); remove the entry",
                r.id, e.until
            )),
            (false, Some(e)) if e.rows != r.rows || e.digest != r.digest => {
                report.failures.push(rows_mismatch(item, r, e))
            }
            (false, Some(e)) => {
                let internal = e.expect == Some(pending::Expect::Internal);
                match (r.failure, internal) {
                    (FailureKind::Ordinary, false) | (FailureKind::Internal, true) => {
                        report.pending.push((r.id.clone(), e.until.clone(), e.note.clone()))
                    }
                    (FailureKind::Ordinary, true) => report.failures.push(format!(
                        "{item}/{}: is listed with `expect = \"internal\"` (until {}), but fails otherwise",
                        r.id, e.until
                    )),
                    (FailureKind::Internal, false) => report.failures.push(format!(
                        "{item}/{}: an internal error of the compiler (S-67); the list holds it only with \
                         `expect = \"internal\"` (W1-04)",
                        r.id
                    )),
                    (FailureKind::Mixed, _) => report.failures.push(format!(
                        "{item}/{}: fails both with internal errors and otherwise; no entry holds both",
                        r.id
                    )),
                }
            }
            (false, None) if !whole => report.failures.push(format!("{item}/{}: fails", r.id)),
            _ => {}
        }
    }
    // With the whole item listed, a failing case fails the item: the gate shows it as pending.
    if whole && run.results.iter().any(|r| !r.problems.is_empty()) && report.failures.is_empty() {
        report.failures.push(format!("{item}: fails (the whole item is listed in tests/pending.toml)"));
    }
    report.run = run;
    report
}

/// The failure of an entry whose `rows` / `digest` are not the case's.
fn rows_mismatch(item: &str, r: &CaseResult, e: &pending::Entry) -> String {
    let (Some(n), Some(d)) = (r.rows, r.digest.as_deref()) else {
        return format!("{item}/{}: `rows` and `digest` are not fields of this item's entries", r.id);
    };
    const SHOWN: usize = 5;
    let mut rows: Vec<&str> = r.failing.iter().take(SHOWN).map(String::as_str).collect();
    let more = r.failing.len().saturating_sub(SHOWN);
    let more = if more > 0 { format!("\n  ... {more} more ({} in all)", r.failing.len()) } else { String::new() };
    rows.insert(0, "");
    let entry = match (e.rows, e.digest.as_deref()) {
        (None, None) => "has neither".to_string(),
        (rows, digest) => format!(
            "holds `rows = {}`, `digest = \"{}\"`",
            rows.map_or_else(|| "?".into(), |x| x.to_string()),
            digest.unwrap_or("?")
        ),
    };
    format!(
        "{item}/{}: the failing rows are not the entry's (until {}): the entry {entry}; now `rows = {n}`, \
         `digest = \"{d}\"` (a failure came, went or moved: read the report, then fix the entry). The failing rows:{}{more}",
        r.id,
        e.until,
        rows.join("\n  ")
    )
}

/// `f(0..n)` on worker threads, in order.
fn parallel<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<T>>> = Mutex::new((0..n).map(|_| None).collect());
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get()).min(n.max(1));
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    if i >= n {
                        break;
                    }
                    let r = f(i);
                    results.lock().expect("results")[i] = Some(r);
                }
            });
        }
    });
    results.into_inner().expect("results").into_iter().map(|r| r.expect("every task ran")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn result(id: &str, ok: bool) -> CaseResult {
        CaseResult { id: id.into(), problems: if ok { Vec::new() } else { vec!["boom".into()] }, ..Default::default() }
    }

    fn list(targets: &[&str]) -> Pending {
        let mut text = String::new();
        for t in targets {
            let _ = write!(
                text,
                "[[pending]]\nkind = \"gate\"\ntarget = \"{t}\"\nreasons = [\"R-67\"]\nuntil = \"W2-09\"\nnote = \"n\"\n\n"
            );
        }
        Pending::parse(&text).unwrap()
    }

    fn run_of(results: Vec<CaseResult>) -> ItemRun {
        ItemRun { results, ..Default::default() }
    }

    #[test]
    fn cases_against_the_list() {
        let r = reconcile(
            "c-gcc",
            run_of(vec![result("a[t]", false), result("b[t]", true), result("c[t]", false), result("d[t]", true)]),
            &list(&["c-gcc/a[t]", "c-gcc/b[t]", "c-gcc/z[t]", "c-clang/c[t]"]),
        );
        assert_eq!(r.pending.iter().map(|p| p.0.as_str()).collect::<Vec<_>>(), ["a[t]"]);
        let f = r.failures.join("\n");
        assert!(f.contains("c-gcc/b[t]: passes but is listed"), "{f}");
        assert!(f.contains("`c-gcc/z[t]` names no case"), "{f}");
        assert!(f.contains("c-gcc/c[t]: fails"), "{f}");
        assert_eq!(r.failures.len(), 3, "{f}");
        assert!(r.failed());
        let ok = reconcile("c-gcc", run_of(vec![result("a[t]", false)]), &list(&["c-gcc/a[t]"]));
        assert!(!ok.failed(), "{:?}", ok.failures);
        assert!(ok.text().contains("PENDING a[t]"), "{}", ok.text());
    }

    #[test]
    fn internal_errors_need_their_entry() {
        let kind = |id: &str, failure| CaseResult { failure, ..result(id, false) };
        let internal = |t: &str| {
            let mut l = list(&[t]);
            l.pending[0].expect = Some(pending::Expect::Internal);
            l
        };
        let form = "`<op>`";
        // an internal error is held only by an entry with `expect = "internal"` (W1-04)
        let r = reconcile_cases("v", run_of(vec![kind("a", FailureKind::Internal)]), &list(&["v/a"]), form);
        assert!(r.failures.iter().any(|f| f.contains("only with `expect = \"internal\"`")), "{:?}", r.failures);
        let r = reconcile_cases("v", run_of(vec![kind("a", FailureKind::Internal)]), &internal("v/a"), form);
        assert!(!r.failed(), "{:?}", r.failures);
        // such an entry does not hold another failure, nor both
        let r = reconcile_cases("v", run_of(vec![kind("a", FailureKind::Ordinary)]), &internal("v/a"), form);
        assert!(r.failures.iter().any(|f| f.contains("fails otherwise")), "{:?}", r.failures);
        for l in [list(&["v/a"]), internal("v/a")] {
            let r = reconcile_cases("v", run_of(vec![kind("a", FailureKind::Mixed)]), &l, form);
            assert!(r.failures.iter().any(|f| f.contains("no entry holds both")), "{:?}", r.failures);
        }
        // an internal error is never held by the absence of an entry
        let r = reconcile_cases("v", run_of(vec![kind("a", FailureKind::Internal)]), &list(&[]), form);
        assert!(r.failures.iter().any(|f| f.contains("v/a: fails")), "{:?}", r.failures);
    }

    #[test]
    fn an_entry_holds_exactly_its_rows() {
        let counted = |id: &str, rows: &[&str]| CaseResult {
            rows: Some(rows.len()),
            digest: Some(format!("{:016x}", rows.len())),
            failing: rows.iter().map(|s| s.to_string()).collect(),
            ..result(id, false)
        };
        let with = |t: &str, rows: Option<usize>, digest: Option<&str>| {
            let mut l = list(&[t]);
            l.pending[0].rows = rows;
            l.pending[0].digest = digest.map(str::to_string);
            l
        };
        let form = "`<op>`";
        let three = ["r1", "r2", "r3"];
        let d3 = format!("{:016x}", 3);
        let r = reconcile_cases("v", run_of(vec![counted("a", &three)]), &with("v/a", Some(3), Some(&d3)), form);
        assert!(!r.failed(), "{:?}", r.failures);
        for (rows, digest) in
            [(Some(2), Some(d3.as_str())), (Some(3), Some("0000000000000009")), (None, None), (Some(3), None)]
        {
            let r = reconcile_cases("v", run_of(vec![counted("a", &three)]), &with("v/a", rows, digest), form);
            let f = r.failures.join("\n");
            assert!(f.contains("the failing rows are not the entry's"), "{f}");
            assert!(f.contains(&format!("now `rows = 3`, `digest = \"{d3}\"`")), "{f}");
            assert!(f.contains("\n  r1\n  r2\n  r3"), "{f}");
        }
        // many rows: the first ones and the count
        let many: Vec<String> = (0..9).map(|i| format!("r{i}")).collect();
        let many: Vec<&str> = many.iter().map(String::as_str).collect();
        let r = reconcile_cases("v", run_of(vec![counted("a", &many)]), &with("v/a", None, None), form);
        assert!(r.failures.join("\n").contains("... 4 more (9 in all)"), "{:?}", r.failures);
        // an item that counts nothing: `rows` is not its field
        let r = reconcile_cases("v", run_of(vec![result("a", false)]), &with("v/a", Some(1), None), form);
        assert!(r.failures.iter().any(|f| f.contains("are not fields")), "{:?}", r.failures);
    }

    #[test]
    fn the_whole_item() {
        // The gate applies a whole entry: the item fails when a case fails, passes otherwise.
        let failing = reconcile("c-header", run_of(vec![result("a[t]/c99-clang", false)]), &list(&["c-header"]));
        assert!(failing.failed() && failing.listed_whole);
        let passing = reconcile("c-header", run_of(vec![result("a[t]/c99-clang", true)]), &list(&["c-header"]));
        assert!(!passing.failed(), "{:?}", passing.failures);
        let both =
            reconcile("c-header", run_of(vec![result("a[t]/c99-clang", true)]), &list(&["c-header", "c-header/x"]));
        assert!(both.failures.iter().any(|f| f.contains("both as a whole and by case")), "{:?}", both.failures);
    }

    #[test]
    fn errors_are_never_pending() {
        let run = ItemRun { errors: vec!["`gcc-15` is not on the PATH".into()], ..Default::default() };
        let r = reconcile("c-gcc", run, &list(&["c-gcc/a[t]"]));
        assert!(r.failures.is_empty(), "{:?}", r.failures);
        assert_eq!(r.exit_code(), 2);
        assert!(r.text().contains("error: `gcc-15` is not on the PATH"), "{}", r.text());
        // with the whole item listed too
        let run = ItemRun { errors: vec!["`gcc-15` is not on the PATH".into()], ..Default::default() };
        assert_eq!(reconcile("c-gcc", run, &list(&["c-gcc"])).exit_code(), 2);
    }

    #[test]
    fn a_missing_program_fails_the_item() {
        let item = Item {
            name: "c-none",
            check: Check::Unit(Toolchain { cc: "onsa-no-such-cc", flags: &[], off: &[], runner: c::Runner::Native }),
        };
        let r = check(&item, &[]);
        assert!(r.results.is_empty());
        assert!(r.errors.iter().any(|e| e.contains("`onsa-no-such-cc` is not on the PATH")), "{:?}", r.errors);
    }
}
