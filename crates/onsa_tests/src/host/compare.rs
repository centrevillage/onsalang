//! The records of a run ([`super::driver`]) compared with the plan: the
//! status values exactly, the outputs and results by spec §13.4 (bit for
//! bit, NaNs equal; `0.0` and `-0.0` differ).
//!
//! A run that ends inside a step (a caught signal, the reset hook, the time
//! budget) fails that step; a step this version's C API cannot express fails
//! that step (the steps before it are compared). What the program could not
//! read or write, or records out of order, are errors of the harness.

use onsa_interp::Value;

use super::Outcome;
use super::driver::{END, PANIC_LINE, RESET_DONE, Unsupported};
use super::plan::{Before, Op, SeqPlan, SigOut, record_len};
use crate::c::{self, DriverKind, Finished};
use crate::scalar::{same, show};

/// The record of one step.
struct Record<'a> {
    status: Option<i32>,
    /// What follows the status: the outputs' bytes in the plan's order
    /// (channel by channel), the result, or the mark of `reset`.
    payload: &'a [u8],
}

/// How the run ended, when it did not end well: `Ok(reason)` for an end
/// inside a step (the step fails), `Err` for an error of the harness.
fn stop_reason(done: &Finished) -> Option<Result<String, String>> {
    let err = if done.stderr.is_empty() { String::new() } else { format!("\n{}", done.stderr) };
    let Some(status) = done.status else {
        return Some(Ok(format!("it ran longer than {}s{err}", c::RUN_TIMEOUT.as_secs())));
    };
    let meaning = |code: i32| c::exit_meaning(DriverKind::Host, code);
    match status.code() {
        Some(0) => None,
        Some(code @ (c::INPUT_EXIT | c::OUTPUT_EXIT | c::SETUP_EXIT | c::ARGS_EXIT)) => {
            Some(Err(format!("the program failed: {} (exit {code}){err}", meaning(code).unwrap_or("?"))))
        }
        Some(code) => {
            Some(Ok(meaning(code).map_or_else(|| format!("exit {code}"), |m| format!("{m} (exit {code})")) + &err))
        }
        None => Some(Ok(format!("it ended by a signal ({status}){err}"))),
    }
}

/// Compare the run `done` of the sequence `p`; `unsupported` is the step
/// the program does not make ([`super::driver::Program::seqs`]). `Err`: an
/// error of the harness.
pub fn outcome(p: &SeqPlan, done: &Finished, unsupported: Option<&Unsupported>) -> Result<Outcome, String> {
    let stop = match stop_reason(done) {
        Some(Err(e)) => return Err(e),
        Some(Ok(r)) => Some(r),
        None => None,
    };
    // The steps the program makes.
    let made = unsupported.map_or(p.steps.len(), |u| u.step.min(p.steps.len()));
    let bytes = &done.stdout;
    let mut at = 0usize;
    let mut records = Vec::new();
    // `Some(k)`: the program stopped inside step k (its index was written).
    let mut inside = None;
    let u32_at = |at: usize| bytes.get(at..at + 4).map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]));
    for (k, st) in p.steps[..made].iter().enumerate() {
        let Some(idx) = u32_at(at) else { break };
        if idx as usize != k {
            return Err(format!(
                "the program wrote the record of step {} where step {} was due",
                idx as u64 + 1,
                k + 1
            ));
        }
        at += 4;
        let Some(rec) = bytes.get(at..at + record_len(&st.op)) else {
            inside = Some(k);
            break;
        };
        at += rec.len();
        let record = if matches!(st.op, Op::Reset) {
            if u32::from_le_bytes([rec[0], rec[1], rec[2], rec[3]]) != RESET_DONE {
                return Err(format!("the program wrote no mark of a finished `reset` for step {}", k + 1));
            }
            Record { status: None, payload: &rec[4..] }
        } else {
            Record { status: Some(i32::from_le_bytes([rec[0], rec[1], rec[2], rec[3]])), payload: &rec[4..] }
        };
        records.push(record);
    }
    let complete = records.len() == made;
    let ended = complete && u32_at(at) == Some(END);
    if ended {
        at += 4;
    }
    if at != bytes.len() && inside.is_none() {
        return Err(format!("the program wrote {} bytes, more than its records ({at})", bytes.len()));
    }
    let mut lines = Vec::new();
    let mut compared = 0usize;
    for (k, rec) in records.iter().enumerate() {
        compared += step(p, k, rec, &mut lines);
    }
    let rest = |lines: &mut Vec<String>, k: usize| {
        let (first, last) = (k + 2, p.steps.len());
        if first == last {
            lines.push(format!("step {first} did not run"));
        } else if first < last {
            lines.push(format!("steps {first}..{last} did not run"));
        }
    };
    match (&stop, ended) {
        (None, true) => {
            if let Some(u) = unsupported {
                lines.push(format!(
                    "{}: this version's C API cannot express it: {}",
                    p.steps[u.step].label(u.step),
                    u.message
                ));
                rest(&mut lines, u.step);
            }
        }
        (None, false) => {
            return Err(format!(
                "the program exited with 0 but wrote the records of {} of {made} steps{}",
                records.len(),
                if complete { " and no end mark" } else { "" }
            ));
        }
        (Some(reason), _) => {
            let k = inside.unwrap_or(records.len());
            if k < made {
                let where_ = if inside.is_some() { "inside the call" } else { "before the call" };
                lines.push(format!("{}: the program ended {where_}: {reason}", p.steps[k].label(k)));
                rest(&mut lines, k);
            } else {
                lines.push(format!("the program ended after its last step: {reason}"));
            }
        }
    }
    if lines.is_empty() {
        if compared == 0 {
            return Err("the sequence compared no value".into());
        }
        return Ok(Outcome::Passed { compared });
    }
    // What panicked in the run, for the reader (the spec fixes no message, so it is not compared).
    let panics: Vec<&str> = done.stderr.lines().filter(|l| l.starts_with(PANIC_LINE)).collect();
    if stop.is_none() && !panics.is_empty() {
        lines.push(format!("the panics of the run:\n  {}", panics.join("\n  ")));
    }
    Ok(Outcome::Failed(lines.join("\n")))
}

/// Compare one step; the number of values compared.
fn step(p: &SeqPlan, k: usize, rec: &Record<'_>, lines: &mut Vec<String>) -> usize {
    let st = &p.steps[k];
    let label = st.label(k);
    let mut n = 0;
    let mut status = |want: i32, lines: &mut Vec<String>| {
        n += 1;
        if rec.status != Some(want) {
            lines.push(format!(
                "{label}: status: expected {want}, got {}",
                rec.status.map_or("nothing".into(), |s| s.to_string())
            ));
        }
    };
    match &st.op {
        Op::Init { status: want, .. } => status(*want, lines),
        Op::Process { status: want, frames, outputs, .. } => {
            status(*want, lines);
            let mut at = 0;
            for o in outputs.iter().flatten() {
                n += output(&label, o, *frames, rec.payload, &mut at, lines);
            }
        }
        Op::Reset => {}
        Op::Fn { status: want, ret, result, .. } => {
            status(*want, lines);
            if let (Some((s, _)), Some(want)) = (ret, result) {
                n += 1;
                match s.read(&rec.payload[..s.size()]) {
                    Ok(got) if same(&got, want) => {}
                    Ok(got) => lines.push(format!("{label}: result: expected {}, got {}", show(want), show(&got))),
                    Err(e) => lines.push(format!("{label}: result: expected {}, got {e}", show(want))),
                }
            }
        }
    }
    n
}

/// Compare the channels of one output; the number of values compared.
fn output(label: &str, o: &SigOut, frames: u32, payload: &[u8], at: &mut usize, lines: &mut Vec<String>) -> usize {
    let size = o.scalar.size();
    let mut n = 0;
    for (c, want) in o.expected.iter().enumerate() {
        let name = match o.planar {
            None => format!("output `{}`", o.name),
            Some(_) => format!("output `{}` channel {c}", o.name),
        };
        let mut first = None;
        let mut differ = 0usize;
        for (f, w) in want.iter().enumerate().take(frames as usize) {
            n += 1;
            let b = &payload[*at + f * size..*at + (f + 1) * size];
            let got = if matches!(o.before, Before::Pattern) && b.iter().all(|x| *x == super::PATTERN) {
                Err(format!("nothing written (the unwritten pattern {:#04x} in every byte)", super::PATTERN))
            } else {
                o.scalar.read(b).map_err(|e| format!("the bytes {b:02x?} ({e})"))
            };
            if !matches!(&got, Ok(g) if same(g, w)) {
                differ += 1;
                if first.is_none() {
                    first = Some((f, show(w), got.map_or_else(|e| e, |g: Value| show(&g))));
                }
            }
        }
        if let Some((f, w, g)) = first {
            let more = if differ > 1 { format!("; {} more frames differ", differ - 1) } else { String::new() };
            lines.push(format!("{label}: {name} frame {f}: expected {w}, got {g}{more}"));
        }
        *at += size * frames as usize;
    }
    n
}
