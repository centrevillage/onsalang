//! `onsa_cases --phases`: the time of each phase of the compiler
//! (`onsa_diag::timing`) on an input, as `onsa check` checks it and, with
//! `--lower`, lowered to Core and verified when the check reports nothing
//! (X-20; the script is `issues/X/X-20/measure_stages.py`).

use std::time::Duration;

use onsa_diag::timing::{self, Times};
use onsa_driver::PackageInput;

/// What a measured input came to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The manifest has diagnostics: nothing was analyzed or timed.
    Manifest,
    Clean,
    Diagnostics,
    Lowered,
    LowerDiagnostics,
    Internal,
}

/// The least time of each phase and of the whole over `rounds` runs (each
/// on a fresh load of `input`).
pub fn measure(input: &PackageInput, lower: bool, rounds: u32) -> Result<(Outcome, Times), String> {
    let mut best: Option<(Outcome, Times)> = None;
    for _ in 0..rounds.max(1) {
        let mut loaded = onsa_driver::Loaded::from_input(input.clone())?;
        if !loaded.manifest_diagnostics().is_empty() {
            return Ok((Outcome::Manifest, Times::default()));
        }
        let (outcome, times) = onsa_diag::stack::run(|| timing::record(|| run(&mut loaded, lower)));
        best = Some(match best {
            None => (outcome, times),
            Some((o, b)) => (o, least(b, times)),
        });
    }
    best.ok_or_else(|| "no round".to_string())
}

fn run(loaded: &mut onsa_driver::Loaded, lower: bool) -> Outcome {
    let Ok(analyzed) = onsa_driver::analyze_loaded(loaded) else { return Outcome::Internal };
    match (analyzed.diagnostics.is_empty(), lower) {
        (false, _) => Outcome::Diagnostics,
        (true, false) => Outcome::Clean,
        (true, true) => match onsa_driver::lower_core(&analyzed) {
            Ok(_) => Outcome::Lowered,
            Err(onsa_driver::LowerError::Diagnostics(_)) => Outcome::LowerDiagnostics,
            Err(onsa_driver::LowerError::Internal(_)) => Outcome::Internal,
        },
    }
}

fn least(a: Times, b: Times) -> Times {
    let phases = a.phases.iter().zip(&b.phases).map(|(x, y)| (x.0, x.1.min(y.1), x.2)).collect();
    Times { phases, total: a.total.min(b.total) }
}

/// One line of JSON for an input: microseconds by phase and in all.
pub fn json(path: &str, outcome: Outcome, t: &Times) -> serde_json::Value {
    let us = |d: Duration| d.as_micros() as u64;
    let phases: serde_json::Map<String, serde_json::Value> =
        t.phases.iter().map(|(p, d, _)| (p.name().to_string(), us(*d).into())).collect();
    serde_json::json!({
        "path": path,
        "outcome": format!("{outcome:?}"),
        "total_us": us(t.total),
        "phases_us": phases,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use onsa_diag::timing::Phase;

    /// Every phase is entered by the check and the lowering of a package
    /// with a flow, and the phases add up to at most the whole.
    #[test]
    fn a_lowered_flow_enters_every_phase() {
        let src = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  let y = x + 0.5 * prev~(^y)\n  y\n}\n\n\
                   fn twice(x: I32) -> I32 {\n  x * 2\n}\n\ntest \"t\" {\n  assert twice(2) == 4\n}\n";
        let input = PackageInput::single_file("m.onsa", src);
        let (outcome, t) = measure(&input, true, 2).unwrap();
        assert_eq!(outcome, Outcome::Lowered);
        let missed: Vec<&str> = t.phases.iter().filter(|p| p.2 == 0).map(|p| p.0.name()).collect();
        assert!(missed.is_empty(), "not entered: {missed:?}");
        assert_eq!(t.phases.iter().map(|p| p.0).collect::<Vec<_>>(), Phase::ALL);
        assert!(t.phases.iter().map(|p| p.1).sum::<Duration>() <= t.total, "{t:?}");
    }
}
