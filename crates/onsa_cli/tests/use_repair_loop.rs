//! The repair loop on real packages: take `use` lines out of a package that has no fault, and apply the
//! first candidate of the first E0302 that has one, again and again (spec §15.1, §18.1; S-37, S-594,
//! S-663, S-673, S-679, R-268; W4-03 U3a2/t2). The sweep moved here from the script of the break side
//! (`mut.py`) that checked what the gate did not: that a loop of candidates ends, and ends without a
//! fault the candidates made.
//!
//! What is fixed, and so what is checked:
//! - §18.1: a candidate applied alone leaves no diagnostic of the same stage or before in what it
//!   touches; a loop of them therefore stops: each candidate takes an E0302 away, so the loop is done in
//!   as many steps as the paths that name a module with no `use` (the unit reports one path, so the next
//!   path of the unit is let through after the first candidate: a path is a step, and a unit with
//!   several paths takes several). The cap is four steps for each `use` line taken out and ten more;
//!   the loop that reaches it is a loop that does not stop;
//! - §15.1, §18.1: a candidate does not close a cycle and does not bind a name twice: after any step the
//!   diagnostics of the names stage that are not E0302 (E0303, E0304, E0305, E0310) are none, as in the
//!   package before the `use` lines were taken out;
//! - §18.1: a candidate does not break the text: after any step the codes of the diagnostics are the
//!   codes there were with the `use` lines out (a `use` put in the wrong place is a syntax error, a name
//!   bound twice an E0304);
//! - every step ends the command as a check does (exit code 0 or 1, no `internal error`).
//!
//! What is not asked: that the loop ends clean. A residual E0302 without a candidate (the name of an
//! item that a `use` took, a path whose head names nothing) is a diagnostic the spec gives no candidate
//! (§15.1: the candidates are for the head of a path, not for the name of an item).
//!
//! The packages: the faultless ones of `tests/spec/packages` (a package whose `onsa check` has a
//! diagnostic is left out, as is a package inside a package) and `examples`, in a scratch copy each. The
//! `use` lines are the lines that start with `use ` at the left edge, with the lines of a list that goes
//! on to the closing `}`. Two tests: every `use` line out at once (the script's mode `all`), and one
//! `use` line out at a time for each line of each package (the mode `one`, which the script named and
//! did not run): the second is where a candidate restores what was there, and where the loop has the
//! most steps. About 2 seconds each in a debug build.

mod test_support;

use std::path::{Path, PathBuf};

use test_support::sweep::*;
use test_support::*;

/// The diagnostics of the names stage that a candidate must not make (E0302 is what the loop repairs).
const NAMES_STAGE_OTHERS: [&str; 4] = ["E0303", "E0304", "E0305", "E0310"];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The directories of the packages to take the `use` lines out of, in a fixed order.
fn packages() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for base in ["tests/spec/packages", "examples"] {
        let mut dirs: Vec<PathBuf> = std::fs::read_dir(repo_root().join(base))
            .unwrap_or_else(|e| panic!("read {base}: {e}"))
            .map(|e| e.unwrap().path())
            .filter(|p| p.is_dir() && p.join("onsa.toml").is_file())
            .collect();
        dirs.sort();
        out.extend(dirs);
    }
    out
}

/// `text` without its `use` lines (the lines that start with `use ` and, for a list that goes on over
/// lines, the lines to the closing `}`), and how many `use` lines it had. `first` is the number of the
/// `use` lines before this text in the package; with `only`, the one `use` line of that number is taken
/// out and the others stay.
fn without_uses(text: &str, first: usize, only: Option<usize>) -> (String, usize) {
    let mut out = String::new();
    let mut n = 0;
    let mut in_list = false;
    let mut dropping = false;
    for line in text.split_inclusive('\n') {
        if in_list {
            in_list = !line.contains('}');
            if !dropping {
                out.push_str(line);
            }
            continue;
        }
        if line.starts_with("use ") {
            dropping = only.is_none_or(|k| k == first + n);
            n += 1;
            in_list = line.contains('{') && !line.contains('}');
            if !dropping {
                out.push_str(line);
            }
            continue;
        }
        out.push_str(line);
    }
    (out, n)
}

/// What the loop did to one package.
struct Outcome {
    steps: usize,
    clean_at_the_end: bool,
}

/// The number of `use` lines of the package at `src`.
fn count_uses(src: &Path) -> usize {
    let mut uses = 0;
    for (file, text) in read_tree(src) {
        if file.ends_with(".onsa") {
            uses += without_uses(&text, uses, None).1;
        }
    }
    uses
}

/// Take the `use` lines (all, or the one of the number `only`) out of the package at `src` and repair it
/// with the candidates. Problems found go to `problems`. `None` when the package is not one to use (it
/// has a fault to begin with).
fn repair(tag: &str, src: &Path, only: Option<usize>, problems: &mut Vec<String>) -> Option<Outcome> {
    let name = format!(
        "{}{}",
        src.file_name().unwrap().to_string_lossy(),
        only.map(|k| format!(" (use #{k})")).unwrap_or_default()
    );
    let d = Dir::bare(tag);
    let mut texts = read_tree(src);
    write_texts(&d, &texts);
    let base = check_package(d.root());
    if !ended_well(&base) || !base.diags.is_empty() {
        return None;
    }
    let mut uses = 0;
    for (file, text) in texts.iter_mut() {
        if file.ends_with(".onsa") {
            let (t, n) = without_uses(text, uses, only);
            *text = t;
            uses += n;
        }
    }
    if uses == 0 {
        return None;
    }
    write_texts(&d, &texts);
    let taken = if only.is_some() { 1 } else { uses };
    let cap = 4 * taken + 10;
    let mut steps = 0;
    let mut first_codes: Option<std::collections::BTreeSet<String>> = None;
    loop {
        let c = check_package(d.root());
        if !ended_well(&c) {
            problems.push(format!("{name}: step {steps}: ended with code {} {:?}", c.code, c.stderr.lines().next()));
            return Some(Outcome { steps, clean_at_the_end: false });
        }
        let others: Vec<String> = c
            .diags
            .iter()
            .filter(|x| NAMES_STAGE_OTHERS.contains(&x.code.as_str()))
            .map(|x| format!("{} {}:{} {}", x.code, x.file, x.line, x.message))
            .collect();
        if !others.is_empty() {
            problems
                .push(format!("{name}: step {steps}: a diagnostic of the names stage that is not E0302: {others:?}"));
            return Some(Outcome { steps, clean_at_the_end: false });
        }
        // §18.1: a candidate leaves nothing of the stages before it and makes no fault of a later one: the
        // codes of the text with the `use` lines out are all there is.
        let codes: std::collections::BTreeSet<String> = c.diags.iter().map(|x| x.code.clone()).collect();
        let first = first_codes.get_or_insert_with(|| codes.clone());
        let new: Vec<&String> = codes.difference(first).collect();
        if !new.is_empty() {
            problems.push(format!("{name}: step {steps}: a candidate made the diagnostics {new:?}, which the text without the `use` lines did not have"));
            return Some(Outcome { steps, clean_at_the_end: false });
        }
        let next = c.diags.iter().find(|x| x.code == "E0302" && !x.fixes.is_empty());
        let Some(diag) = next else {
            return Some(Outcome { steps, clean_at_the_end: c.diags.is_empty() });
        };
        if steps >= cap {
            problems.push(format!(
                "{name}: {cap} steps (four for each of the {taken} `use` lines taken out, and ten) and a candidate is still given for {} {}:{} {:?}",
                diag.code, diag.file, diag.line, diag.message
            ));
            return Some(Outcome { steps, clean_at_the_end: false });
        }
        apply_fix_texts(&mut texts, &diag.fixes[0]);
        write_texts(&d, &texts);
        steps += 1;
    }
}

/// The sums of a sweep.
#[derive(Default)]
struct Totals {
    used: usize,
    steps: usize,
    clean: usize,
    ended_by_a_step: usize,
}

fn sweep(tag: &str, only_each: bool) -> (Totals, Vec<String>) {
    let mut problems = Vec::new();
    let mut t = Totals::default();
    for (i, src) in packages().iter().enumerate() {
        let modes: Vec<Option<usize>> = if only_each { (0..count_uses(src)).map(Some).collect() } else { vec![None] };
        for only in modes {
            let tag = format!("{tag}_{i}_{}", only.map(|k| k as i64).unwrap_or(-1));
            if let Some(o) = repair(&tag, src, only, &mut problems) {
                t.used += 1;
                t.steps += o.steps;
                t.clean += o.clean_at_the_end as usize;
                t.ended_by_a_step += (o.steps > 0) as usize;
            }
        }
    }
    (t, problems)
}

/// §18.1: every `use` line taken out; the loop of the first candidates over the packages of the spec and
/// the examples stops, and the candidates make no cycle (E0310), no clash (E0304) and no other fault of
/// the names stage on the way.
#[test]
fn the_loop_of_candidates_stops_without_a_fault_of_the_names_stage() {
    let (t, problems) = sweep("repair_all", false);
    assert!(problems.is_empty(), "{} problems in {} packages:\n{}", problems.len(), t.used, problems.join("\n"));
    // The sweep must have a subject: many packages with `use` lines and candidates really applied.
    assert!(t.used >= 20, "only {} packages were used", t.used);
    assert!(t.steps >= 5, "only {} candidates were applied", t.steps);
}

/// §18.1: one `use` line taken out at a time, for each `use` line of each package. A `use` of a module
/// whose name a body path starts with gets back as the candidate of that path (the loop ends in the
/// package that was there), and the candidates add no fault of the names stage on the way.
#[test]
fn the_loop_of_candidates_stops_when_one_use_line_is_taken_out() {
    let (t, problems) = sweep("repair_one", true);
    assert!(problems.is_empty(), "{} problems in {} runs:\n{}", problems.len(), t.used, problems.join("\n"));
    assert!(t.used >= 60, "only {} runs were used", t.used);
    assert!(t.steps >= 5, "only {} candidates were applied", t.steps);
    assert!(t.clean >= 5, "only {} runs ended clean", t.clean);
}
