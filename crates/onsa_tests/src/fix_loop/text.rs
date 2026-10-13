//! The reports of the walks as the lines a person reads.

use super::{How, Report, Stop, Walk};

/// The reports as the lines a person reads: a line per file, and a line per
/// step of the walks it keeps.
pub fn text(reports: &[Report]) -> String {
    let mut out = String::new();
    for r in reports {
        if let Some(e) = &r.unreadable {
            out += &format!("{}: cannot read it: {e}\n", r.file);
            continue;
        }
        if let Some(e) = &r.internal {
            out += &format!("{}: the check of the file ends in an internal error\n  {}\n", r.file, indent(e));
            continue;
        }
        let pick = r.pick.name();
        let late = if r.timed_out { "; out of time" } else { "" };
        if !r.branches && r.walks.len() == 1 {
            let w = &r.walks[0];
            out += &format!("{}: {}; {} errors at the start (--pick {pick}){late}\n", r.file, describe(w), r.errors);
            out += &steps_text(w, "  ");
            continue;
        }
        let stops: Vec<String> = r.stops.iter().map(|(k, v)| format!("{} {v}", k.name())).collect();
        // Truncated after the first round (which always ends), so with `discrepancies`.
        let truncated = match r.discrepancies {
            Some(n) if r.truncated => format!(", truncated (every walk with at most {n} other candidates walked)"),
            _ => String::new(),
        };
        out += &format!(
            "{}: walks: {}; {} texts checked, {} joined{truncated}{late}; {} errors at the start (--pick {pick}{})\n",
            r.file,
            if stops.is_empty() { "none".to_string() } else { stops.join(", ") },
            r.explored,
            r.joined,
            r.errors,
            if r.branches { " --branches" } else { "" },
        );
        for (i, w) in r.walks.iter().enumerate() {
            out += &format!("  walk {}: {}\n", i + 1, describe(w));
            out += &steps_text(w, "    ");
        }
    }
    out
}

/// How a walk stopped, in a few words.
fn describe(w: &Walk) -> String {
    let n = w.steps.len();
    let after = format!("after {n} step{}", if n == 1 { "" } else { "s" });
    let message = || w.message.as_deref().map_or(String::new(), |m| format!(": {}", indent(m)));
    match (w.stop, w.how, w.back_to) {
        (Stop::Cycle, Some(How::Undo), Some(j)) => format!("cycle (undoes step {j}) {after}"),
        (Stop::Cycle, _, Some(0)) => format!("cycle (back to the input) {after}"),
        (Stop::Cycle, _, Some(j)) => format!("cycle (back to the text after step {j}) {after}"),
        (Stop::Internal | Stop::CannotApply, ..) => format!("{} {after}{}", w.stop.name(), message()),
        (stop, ..) => format!("{} {after}", stop.name()),
    }
}

fn steps_text(w: &Walk, pad: &str) -> String {
    let mut out = String::new();
    for (i, s) in w.steps.iter().enumerate() {
        let errors =
            s.errors.map_or("not checked".to_string(), |e| format!("{e} error{}", if e == 1 { "" } else { "s" }));
        out += &format!(
            "{pad}{}. {} {}:{} candidate {}/{} `{}` -> {errors}\n",
            i + 1,
            s.code,
            s.line,
            s.col,
            s.candidate,
            s.of,
            s.title
        );
    }
    out
}

fn indent(s: &str) -> String {
    s.trim_end().replace('\n', "\n  ")
}
