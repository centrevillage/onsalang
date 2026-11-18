//! The tests of a case that the evaluator ran, run again through the interpreter (W7-19 U3): each is printed as a `test`
//! of Onsa (`print.rs`), appended to the file of the original, and the case is analyzed, lowered and run as `onsa test`
//! runs it, only the printed tests selected. A test that fails goes back by its line to the call and the leaf it is about.

use std::collections::{BTreeMap, HashMap};

use onsa_driver::{Loaded, PackageInput, TestOptions, TestRun as Ran, analyze_loaded, lower_core, run_tests};
use onsa_tests::flow_ref::flow::stage_at;
use onsa_tests::flow_ref::sema_view::View;
use onsa_tests::flow_ref::walk::{CaseRun, Verdict};

use super::print::{LOCAL, PREFIX, Printed, print_test};

/// What the printed tests of a case came to.
#[derive(Debug, Default)]
pub struct Compared {
    /// The printed tests the interpreter ran.
    pub ran: usize,
    /// The asserts of them (one for each frame of each leaf of each call).
    pub asserts: usize,
    /// Of them, those that panicked at their last call as the original did.
    pub panicked: usize,
    /// The tests that are not printed, by the reason.
    pub unprintable: BTreeMap<String, usize>,
    /// The tests that disagree, each back at its call and leaf (and what is wrong with the case itself).
    pub failures: Vec<String>,
}

/// Where a printed test is: its file, the line its text starts at, the text and the name of the original.
struct Placed {
    start: usize,
    printed: Printed,
    original: String,
}

/// The tests of `run` that the evaluator evaluated, printed, run in the interpreter and judged. `input` is the case.
pub fn compare_case(path: &str, mut input: PackageInput, run: &CaseRun) -> Compared {
    let mut out = Compared::default();
    let mut placed: HashMap<String, Placed> = HashMap::new();
    let clash = input.files.iter().any(|f| f.text.contains(LOCAL));
    for (index, t) in run.tests.iter().enumerate().filter(|(_, t)| t.verdict == Verdict::Ok) {
        let Some(file) = input.files.iter_mut().find(|f| f.path == t.file) else {
            out.failures.push(format!("{path}: \"{}\": its file {} is not a file of the case", t.name, t.file));
            continue;
        };
        let printed = if clash {
            Err(format!("a case that writes a name that starts with `{LOCAL}`"))
        } else {
            print_test(index, t)
        };
        match printed {
            Ok(printed) => {
                if !file.text.ends_with('\n') {
                    file.text.push('\n');
                }
                let start = file.text.matches('\n').count() + 1;
                file.text += &printed.text;
                placed.insert(printed.name.clone(), Placed { start, printed, original: t.name.clone() });
            }
            Err(why) => *out.unprintable.entry(why).or_default() += 1,
        }
    }
    if !placed.is_empty() {
        judge(path, input, &placed, &mut out);
    }
    out
}

fn judge(path: &str, input: PackageInput, placed: &HashMap<String, Placed>, out: &mut Compared) {
    let mut loaded = match Loaded::from_input(input) {
        Ok(l) => l,
        Err(e) => return out.failures.push(format!("{path}: {e}")),
    };
    let analyzed = match analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(e) => return out.failures.push(format!("{path}: {}", e.render(&loaded.sources))),
    };
    if !analyzed.diagnostics.is_empty() {
        return out.failures.push(format!("{path}: {}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics)));
    }
    let module = match lower_core(&analyzed) {
        Ok(m) => m,
        Err(e) => return out.failures.push(format!("{path}: {}", e.render(&loaded.sources))),
    };
    let opts = TestOptions { filter: Some(PREFIX.to_string()), module: None };
    let report = match run_tests(&loaded.sources, &module, &opts) {
        Ok(Ran::Ran(r)) => r,
        Ok(Ran::NoMatch) => return out.failures.push(format!("{path}: no printed test was selected")),
        Ok(Ran::Unsupported(d)) => {
            return out.failures.push(format!(
                "{path}: the interpreter does not run them: {}",
                onsa_diag::to_text(&loaded.sources, &d)
            ));
        }
        Err(e) => return out.failures.push(format!("{path}: {}", e.render(&loaded.sources))),
    };
    let view = View::new(&analyzed);
    for t in &report.tests {
        let Some(p) = placed.get(&t.name) else {
            out.failures.push(format!("{path}: the interpreter ran a test that was not printed: {}", t.name));
            continue;
        };
        out.ran += 1;
        out.asserts += p.printed.lines.iter().filter(|o| o.assert.is_some()).count();
        let failed_at = t.failure.as_ref().map(|f| {
            let at = f.calls.last().copied().unwrap_or(f.span);
            let line = loaded.sources.file(at.file).line_col(at.start).line as usize;
            let origin = line.checked_sub(p.start).and_then(|i| p.printed.lines.get(i)).cloned().unwrap_or_default();
            (f, line, origin)
        });
        let wrong = match (&p.printed.panic_call, failed_at) {
            (None, None) => None,
            (Some(call), None) => Some(format!("it did not panic at {call}")),
            (Some(call), Some((f, _, o)))
                if f.origin == onsa_core::PanicOrigin::Panic && o.assert.is_none() && o.call == *call =>
            {
                // The stage is that of the first place of the failure (the panic, then the calls outwards) that a flow has;
                // none is the start of a `process`. Which frame, and the kind of the panic, the record does not tell.
                let places = std::iter::once(f.span).chain(f.calls.iter().copied());
                let stage = places.into_iter().find_map(|s| stage_at(view, s));
                match p.printed.panic_at.map(|at| at.stage()) {
                    Some(want) if want != stage => {
                        Some(format!("it panicked at {stage:?}, the evaluator at {want:?}, at {call}"))
                    }
                    _ => {
                        out.panicked += 1;
                        None
                    }
                }
            }
            (_, Some((f, line, o))) => Some(format!(
                "{}{} (line {line}): {}",
                o.call,
                o.assert.map(|a| format!(", {a}")).unwrap_or_default(),
                f.message
            )),
        };
        if let Some(w) = wrong {
            out.failures.push(format!("{path}: \"{}\": {w}", p.original));
        }
    }
    let missing = placed.len().saturating_sub(report.tests.len());
    if missing > 0 {
        out.failures.push(format!("{path}: {missing} printed tests did not run"));
    }
}
