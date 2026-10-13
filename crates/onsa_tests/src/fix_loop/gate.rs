//! The gate item `fix-loop` (the module's documentation of [`super`]).

use std::path::Path;
use std::time::{Duration, Instant};

use super::{Options, Pick, Report, Stop, text, walk_texts};
use crate::case::{self, CaseKind};
use crate::single_files::read_input;

/// The cases walked: the single-file ones (a package case is counted, not walked).
const FIXES: &str = "tests/spec/fixes";
/// The saved inputs of the fuzzing (not cases, [`case::EXCLUDED`]).
const FUZZ: &str = "tests/fuzz";

/// What the gate item found: its text, and whether it failed to walk what
/// it says (it never fails on what the walks find).
pub struct Gate {
    pub text: String,
    pub failed: bool,
}

/// The inputs of the item, by their names from the root, the package cases
/// it does not walk, and what keeps it from walking every input it says.
struct Inputs {
    texts: Vec<(String, String)>,
    packages: usize,
    problems: Vec<String>,
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
/// input is missing or cannot be read, no walk takes a step, the time runs
/// out, or a walk ends in an internal error or a candidate that does not
/// apply; it shows the cycles, the divergences and the limits, and does not
/// fail on them.
pub fn gate(root: &Path, budget: Duration) -> Gate {
    let Inputs { texts, packages, mut problems } = inputs(root);
    let deadline = Instant::now() + budget;
    let mut reports = Vec::new();
    for pick in [Pick::First, Pick::Last] {
        let options = Options { pick, branches: true, deadline: Some(deadline), ..Options::default() };
        reports.extend(walk_texts(&texts, &options));
    }
    let mut out = String::new();
    let failing = |r: &Report| r.internal.is_some() || r.count(Stop::Internal) + r.count(Stop::CannotApply) > 0;
    let shown =
        |r: &Report| failing(r) || [Stop::Cycle, Stop::Diverge, Stop::Limit].into_iter().any(|s| r.count(s) > 0);
    for r in reports.iter().filter(|r| shown(r)) {
        out += &text(std::slice::from_ref(r));
        if failing(r) {
            problems.push(format!(
                "{} (--pick {}): an internal error or a candidate that does not apply",
                r.file,
                r.pick.name()
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
         {}, cycles (undo) {}, divergences {}, limits {}, truncated {} (walks of a file and an order; report only, \
         W3-22)",
        texts.len(),
        runs(&|r| r.count(Stop::Cycle) > r.undos),
        runs(&|r| r.undos > 0),
        runs(&|r| r.count(Stop::Diverge) > 0),
        runs(&|r| r.count(Stop::Limit) > 0),
        runs(&|r| r.truncated),
    );
    Gate { text: out, failed: !problems.is_empty() }
}
