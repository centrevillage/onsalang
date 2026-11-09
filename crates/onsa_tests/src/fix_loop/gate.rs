//! The gate item `fix-loop` (the module's documentation of [`super`]).

use std::path::Path;
use std::time::{Duration, Instant};

use std::collections::BTreeMap;

use super::{Options, Pick, Report, Stop, text, walk_texts};
use crate::case::{self, CaseKind};
use crate::pending::{self, Pending};
use crate::single_files::read_input;

/// The name of the item: its case entries in `tests/pending.toml` are `fix-loop/<file from the root>`.
const ITEM: &str = "fix-loop";
/// The cases walked: the single-file ones (a package case is counted, not walked).
const FIXES: &str = "tests/spec/fixes";
/// The saved inputs of the fuzzing (not cases, [`case::EXCLUDED`]).
const FUZZ: &str = "tests/fuzz";

/// What the gate item found: its text, and whether it failed.
pub struct Gate {
    pub text: String,
    pub failed: bool,
}

/// The inputs of the item, by their names from the root, the package cases
/// it does not walk, and what keeps it from walking every input it says.
pub(super) struct Inputs {
    pub(super) texts: Vec<(String, String)>,
    pub(super) packages: usize,
    pub(super) problems: Vec<String>,
}

fn inputs(root: &Path) -> Inputs {
    let (cases, mut problems) = case::collect(root);
    let mut texts = Vec::new();
    let mut packages = 0;
    for c in cases.iter().filter(|c| c.path.starts_with(&format!("{FIXES}/"))) {
        match (&c.kind, &c.setup) {
            (CaseKind::Package, _) => packages += 1,
            (CaseKind::File, Ok(s)) => texts.push((c.path.clone(), s.input.files[0].text.clone())),
            (CaseKind::File, Err(e)) => problems.push(format!("{}: {e}", c.path)),
        }
    }
    if texts.is_empty() {
        problems.push(format!("no single-file case under {FIXES}"));
    }
    match case::onsa_files(root, FUZZ) {
        Err(e) => problems.push(e),
        Ok(files) if files.is_empty() => problems.push(format!("no saved input under {FUZZ}")),
        Ok(files) => {
            for p in files {
                let name = case::rel_path(root, &p);
                match read_input(&p.to_string_lossy()) {
                    Ok(text) => texts.push((name, text)),
                    Err(e) => problems.push(format!("{name}: cannot read it: {e}")),
                }
            }
        }
    }
    Inputs { texts, packages, problems }
}

/// The gate item `fix-loop` over `root`, within `budget`. It fails when an
/// input is missing or cannot be read, `tests/pending.toml` cannot be read,
/// no walk takes a step, the time runs out, a walk ends in an internal error
/// or a candidate that does not apply, or in a cycle or at the limit of the
/// steps (S-475) on an input the list does not hold ([`verdict`]).
pub fn gate(root: &Path, budget: Duration) -> Gate {
    let mut inputs = inputs(root);
    let list = Pending::load(root).unwrap_or_else(|e| {
        inputs.problems.push(e);
        Pending::default()
    });
    let deadline = Instant::now() + budget;
    let mut reports = Vec::new();
    for pick in [Pick::First, Pick::Last] {
        reports.extend(walk_texts(&inputs.texts, &options(pick, deadline)));
    }
    verdict(inputs, &reports, &list, budget)
}

/// The options of the gate's walks: no divergence stops a walk (S-475: it is
/// no breach, a sound walk shows errors that were hidden; a growth that goes
/// on stops at the limit, which is one).
pub(super) fn options(pick: Pick, deadline: Instant) -> Options {
    Options { pick, branches: true, deadline: Some(deadline), diverge: usize::MAX, ..Options::default() }
}

/// The text and the verdict of the walks of `inputs` (the module's
/// documentation of [`gate`]). An entry `fix-loop/<file>` of the kind `gate`
/// in `list` holds the cycles and the limits of that file, nothing else; it
/// fails when the file is not walked, or has none.
pub(super) fn verdict(inputs: Inputs, reports: &[Report], list: &Pending, budget: Duration) -> Gate {
    let Inputs { texts, packages, mut problems } = inputs;
    let prefix = format!("{ITEM}/");
    let held: BTreeMap<&str, &pending::Entry> =
        list.of_kind(pending::Kind::Gate).filter_map(|e| Some((e.target.strip_prefix(&prefix)?, e))).collect();
    let mut out = String::new();
    let failing = |r: &Report| r.internal.is_some() || r.count(Stop::Internal) + r.count(Stop::CannotApply) > 0;
    let breaks = |r: &Report| r.count(Stop::Cycle) + r.count(Stop::Limit) > 0;
    for r in reports.iter().filter(|r| failing(r) || breaks(r)) {
        out += &text(std::slice::from_ref(r));
        let pick = r.pick.name();
        if failing(r) {
            problems.push(format!("{} (--pick {pick}): an internal error or a candidate that does not apply", r.file));
        }
        if breaks(r) && !held.contains_key(r.file.as_str()) {
            problems.push(format!(
                "{} (--pick {pick}): a cycle or the limit of the steps (S-475); a known one is listed in {} as \
                 `{ITEM}/{}`, with an R and an until",
                r.file,
                pending::PATH,
                r.file
            ));
        }
    }
    for (file, e) in &held {
        let of_file: Vec<&Report> = reports.iter().filter(|r| r.file == *file).collect();
        if of_file.is_empty() {
            problems.push(format!("{}: `{}` names no input of the item (until {})", pending::PATH, e.target, e.until));
        } else if !of_file.iter().any(|r| breaks(r)) {
            problems.push(format!(
                "{}: no cycle and no limit, but listed in {} (until {}); remove the entry",
                e.target,
                pending::PATH,
                e.until
            ));
        }
    }
    let late = reports.iter().filter(|r| r.timed_out).count();
    if late > 0 {
        problems.push(format!("the time budget ({} s) ran out: {late} walks did not end", budget.as_secs()));
    }
    if reports.iter().all(|r| r.longest == 0) {
        problems.push("no walk took a step: no input holds an error with a candidate".into());
    }
    for p in &problems {
        out += &format!("FAIL {p}\n");
    }
    let runs = |f: &dyn Fn(&Report) -> bool| reports.iter().filter(|r| f(r)).count();
    out += &format!(
        "fix-loop: {} files ({packages} packages not walked), walked with --branches in both orders: cycles (state) \
         {}, cycles (undo) {}, limits {}, truncated {} (walks of a file and an order); breaches (cycles and limits) \
         {}, held by {} {}",
        texts.len(),
        runs(&|r| r.count(Stop::Cycle) > r.undos),
        runs(&|r| r.undos > 0),
        runs(&|r| r.count(Stop::Limit) > 0),
        runs(&|r| r.truncated),
        runs(&breaks),
        pending::PATH,
        runs(&|r| breaks(r) && held.contains_key(r.file.as_str())),
    );
    Gate { text: out, failed: !problems.is_empty() }
}
