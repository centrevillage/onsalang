//! The host steps of a case (K-14, plan D-05): `[[test.host]]` in the
//! fragment's `[test]` table declares sequences of calls of an exported flow
//! or function at its C boundary, with the values each call must give (spec
//! §9.2 poison, §14.2 the status values, §15.3 `panic`).
//!
//! ```text
//! // [[test.host]]
//! // name = "boom poisons until reset"
//! // target = "host"
//! // flow = "poison.boom"
//! // steps = [
//! //   { call = "init", config = {}, sample_rate = 48000.0, status = 0 },
//! //   { call = "process", params = { k = 2.0 }, frames = 2, input = [1.0, 1.0], status = 0, output = [2.0, 2.0] },
//! //   { call = "reset" },
//! // ]
//! ```
//!
//! The layers, so that a change of the C API touches one place:
//!
//! - this module: the form of a sequence and the checks that need no build
//!   ([`check`]), and the run of the sequences of a target ([`run_target`]);
//! - [`plan`]: the values typed against the build (what is exported, the
//!   types of the inputs and outputs), the bytes the program reads, the
//!   errors of the case. It holds the C backend's records (the C names and
//!   types) and orders `config`, `params` and `args` as the C arguments, but
//!   not the form of the calls; the WASM of M6 needs it split there;
//! - [`driver`]: the C program, through [`crate::capi`] (the one place that
//!   knows this version's C API);
//! - [`compare`]: the records the program writes, compared with the plan by
//!   spec §13.4 (bit for bit, NaNs equal), and the report.
//!
//! Each sequence of a target runs in its own process (`argv[1]`), so one that
//! ends the process leaves the others' results. The values travel as bytes
//! on the standard input; the results come back as bytes on the standard
//! output.

pub mod compare;
pub mod driver;
pub mod plan;
#[cfg(test)]
mod tests;

use std::path::Path;

use serde::{Deserialize, Deserializer};

use onsa_backend_c::PanicMode;
use onsa_driver::BuildOutput;

use crate::c::{self, Check};
use crate::fragment::Mode;

/// The byte the harness fills an output with when the step gives no `fill`:
/// an output still holding it was not written.
pub const PATTERN: u8 = 0xA5;

/// A sequence: `[[test.host]]`.
#[derive(Debug, Clone, PartialEq)]
pub struct Seq {
    pub name: String,
    pub target: String,
    pub flow: Option<String>,
    pub fn_: Option<String>,
    pub steps: Vec<Step>,
    /// The line of the fragment that starts it (set by [`locate`]).
    pub line: usize,
    at: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSeq {
    name: String,
    target: String,
    #[serde(default)]
    flow: Option<String>,
    #[serde(default, rename = "fn")]
    fn_: Option<String>,
    steps: Vec<toml::Spanned<Step>>,
}

/// A step: a call and what it must give.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Step {
    pub call: Call,
    pub config: Option<toml::Table>,
    pub sample_rate: Option<toml::Value>,
    pub params: Option<toml::Table>,
    pub frames: Option<u32>,
    pub input: Option<toml::Value>,
    pub fill: Option<toml::Value>,
    pub inplace: Option<bool>,
    pub null: Option<Vec<NullArg>>,
    pub status: Option<i64>,
    pub output: Option<toml::Value>,
    pub args: Option<toml::Table>,
    pub result: Option<toml::Value>,
    /// The line of the fragment that holds it (set by [`locate`]).
    #[serde(skip)]
    pub line: usize,
    #[serde(skip)]
    at: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Call {
    Init,
    Process,
    Reset,
    Fn,
}

impl Call {
    pub fn name(self) -> &'static str {
        match self {
            Call::Init => "init",
            Call::Process => "process",
            Call::Reset => "reset",
            Call::Fn => "fn",
        }
    }
}

/// An argument passed as NULL (spec §14.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum NullArg {
    Bulk,
    Cfg,
    Input,
    Output,
}

impl NullArg {
    pub fn name(self) -> &'static str {
        match self {
            NullArg::Bulk => "bulk",
            NullArg::Cfg => "cfg",
            NullArg::Input => "input",
            NullArg::Output => "output",
        }
    }
}

impl Step {
    pub fn is_null(&self, a: NullArg) -> bool {
        self.null.as_ref().is_some_and(|n| n.contains(&a))
    }
}

/// `[test] host`, with the byte offset of each sequence and step in the
/// fragment's TOML (made lines by [`locate`]).
pub fn de_seqs<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<Seq>, D::Error> {
    let raw: Vec<toml::Spanned<RawSeq>> = Vec::deserialize(d)?;
    Ok(raw
        .into_iter()
        .map(|r| {
            let at = r.span().start;
            let r = r.into_inner();
            let steps = r
                .steps
                .into_iter()
                .map(|s| {
                    let at = s.span().start;
                    let mut s = s.into_inner();
                    s.at = at;
                    s
                })
                .collect();
            Seq { name: r.name, target: r.target, flow: r.flow, fn_: r.fn_, steps, line: 0, at }
        })
        .collect())
}

/// Turn the offsets of [`de_seqs`] into lines of `toml_text` (which keeps the
/// lines of the file).
pub fn locate(seqs: &mut [Seq], toml_text: &str) {
    let line = |at: usize| toml_text[..at.min(toml_text.len())].matches('\n').count() + 1;
    for s in seqs {
        s.line = line(s.at);
        for st in &mut s.steps {
            st.line = line(st.at);
        }
    }
}

impl Seq {
    /// What it calls, for messages: `flow m.f` / `fn m.g`.
    pub fn callee(&self) -> String {
        match (&self.flow, &self.fn_) {
            (Some(f), _) => format!("flow {f}"),
            (_, Some(f)) => format!("fn {f}"),
            _ => "nothing".into(),
        }
    }
}

/// The checks of the sequences that need no build (an error of the case):
/// the names, what a step may and must write for its call, the form of the
/// sequence. The values are checked against the build ([`plan`]).
pub fn check(seqs: &[Seq], mode: Mode) -> Result<(), String> {
    if let Some(s) = seqs.first()
        && matches!(mode, Mode::None | Mode::Parse)
    {
        return Err(format!(
            "line {}: [[test.host]] needs `mode = \"check\"` or `\"test\"` (not {mode:?}): the steps run on a build",
            s.line
        ));
    }
    for (i, s) in seqs.iter().enumerate() {
        let at = |m: String| format!("line {}: host \"{}\": {m}", s.line, s.name);
        if s.name.is_empty() || s.name.trim() != s.name || s.name.contains("::") || s.name.chars().any(char::is_control)
        {
            return Err(format!(
                "line {}: host `name = {:?}`: a name is not empty, has no space at its ends, no `::` and no control \
                 character (it names the sequence in tests/pending.toml as `<path>::<name>`)",
                s.line, s.name
            ));
        }
        if let Some(o) = seqs[..i].iter().find(|o| o.name == s.name) {
            return Err(at(format!("the name is used twice (also on line {})", o.line)));
        }
        let flow = match (&s.flow, &s.fn_) {
            (Some(_), None) => true,
            (None, Some(_)) => false,
            _ => return Err(at("write exactly one of `flow` and `fn`".into())),
        };
        if s.steps.is_empty() {
            return Err(at("`steps` is empty: a sequence has at least one step".into()));
        }
        if flow && s.steps[0].call != Call::Init {
            return Err(format!(
                "line {}: host \"{}\" step 1: the first step of a flow is `init` (the state's storage holds nothing \
                 before it)",
                s.steps[0].line, s.name
            ));
        }
        for (k, st) in s.steps.iter().enumerate() {
            check_step(st, flow).map_err(|m| format!("line {}: host \"{}\" step {}: {m}", st.line, s.name, k + 1))?;
        }
    }
    Ok(())
}

fn check_step(st: &Step, flow: bool) -> Result<(), String> {
    let c = st.call;
    match (flow, c) {
        (true, Call::Fn) => return Err("`call = \"fn\"` belongs to a sequence of `fn`".into()),
        (false, Call::Init | Call::Process | Call::Reset) => {
            return Err(format!("`call = \"{}\"` belongs to a sequence of `flow`", c.name()));
        }
        _ => {}
    }
    // (field, written, allowed for this call)
    let fields: [(&str, bool, &[Call]); 12] = [
        ("config", st.config.is_some(), &[Call::Init]),
        ("sample_rate", st.sample_rate.is_some(), &[Call::Init]),
        ("params", st.params.is_some(), &[Call::Process]),
        ("frames", st.frames.is_some(), &[Call::Process]),
        ("input", st.input.is_some(), &[Call::Process]),
        ("fill", st.fill.is_some(), &[Call::Process]),
        ("inplace", st.inplace.is_some(), &[Call::Process]),
        ("null", st.null.is_some(), &[Call::Init, Call::Process]),
        ("status", st.status.is_some(), &[Call::Init, Call::Process, Call::Fn]),
        ("output", st.output.is_some(), &[Call::Process]),
        ("args", st.args.is_some(), &[Call::Fn]),
        ("result", st.result.is_some(), &[Call::Fn]),
    ];
    for (name, written, calls) in fields {
        if written && !calls.contains(&c) {
            let why = if c == Call::Reset && name == "status" { " (`reset` returns nothing, S-198)" } else { "" };
            return Err(format!("`{name}` is not a field of `call = \"{}\"`{why}", c.name()));
        }
    }
    let need = |name: &str, written: bool| {
        if written { Ok(()) } else { Err(format!("`call = \"{}\"` needs `{name}`", c.name())) }
    };
    let nulls = st.null.as_deref().unwrap_or_default();
    for (i, n) in nulls.iter().enumerate() {
        if nulls[..i].contains(n) {
            return Err(format!("`null` names `{}` twice", n.name()));
        }
        let ok = match c {
            Call::Init => matches!(n, NullArg::Bulk | NullArg::Cfg),
            _ => matches!(n, NullArg::Input | NullArg::Output),
        };
        if !ok {
            return Err(format!("`null`: `{}` is not an argument of `{}`", n.name(), c.name()));
        }
    }
    let status = |allowed: &[i64]| match st.status {
        Some(v) if !allowed.contains(&v) => Err(format!(
            "`status = {v}`: `{}` returns {}",
            c.name(),
            allowed.iter().map(i64::to_string).collect::<Vec<_>>().join(", ")
        )),
        _ => Ok(()),
    };
    match c {
        Call::Init => {
            if st.is_null(NullArg::Cfg) {
                if st.config.is_some() {
                    return Err("`config` with `null = [\"cfg\"]`: the call passes no `Config`".into());
                }
            } else {
                need("config", st.config.is_some())?;
            }
            need("sample_rate", st.sample_rate.is_some())?;
            need("status", st.status.is_some())?;
            status(&[0, 1, 2])?;
        }
        Call::Process => {
            need("params", st.params.is_some())?;
            need("frames", st.frames.is_some())?;
            need("status", st.status.is_some())?;
            status(&[0, 1, 2])?;
            if !nulls.is_empty() && st.frames != Some(0) {
                return Err(
                    "`null` needs `frames = 0`: with frames, every pointer must point to them (spec §14.2)".into()
                );
            }
            if st.is_null(NullArg::Input) && st.input.is_some() {
                return Err("`input` with `null = [\"input\"]`: the call passes no input".into());
            }
            if st.is_null(NullArg::Output) {
                if st.output.is_some() || st.fill.is_some() {
                    return Err("`output` or `fill` with `null = [\"output\"]`: the call passes no output".into());
                }
            } else {
                need("output", st.output.is_some())?;
            }
            if st.inplace == Some(true) {
                if !nulls.is_empty() {
                    return Err("`inplace` with `null`: there is no buffer to share".into());
                }
                if st.fill.is_some() {
                    return Err("`fill` with `inplace`: the output buffer holds the input".into());
                }
            }
        }
        Call::Reset => {}
        Call::Fn => {
            need("args", st.args.is_some())?;
            need("status", st.status.is_some())?;
            status(&[0, 1])?;
        }
    }
    Ok(())
}

/// The outcome of one sequence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// Every step gave what it must; the values compared.
    Passed { compared: usize },
    /// A step did not give what it must, or the program ended inside a step,
    /// or this version's C API cannot express a step (the entry
    /// `<path>::<name>` of `tests/pending.toml` may hold it).
    Failed(String),
    /// The sequence did not run, for a reason of the whole case (it is not
    /// pending by its own entry).
    NotRun(String),
}

/// The result of one sequence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeqResult {
    pub name: String,
    pub target: String,
    pub outcome: Outcome,
}

/// What the run of the sequences of one target found.
#[derive(Debug, Default)]
pub struct TargetRun {
    pub results: Vec<SeqResult>,
    /// Errors of the case: never pending.
    pub case_errors: Vec<String>,
    /// Information for the reader (where `ONSA_C_KEEP` kept the files).
    pub notes: Vec<String>,
    /// Failures of the case as a whole (the program does not compile).
    pub failures: Vec<String>,
    /// The harness cannot run (no compiler, a file it cannot write, records it
    /// cannot read): never pending.
    pub harness: Vec<String>,
}

/// The C checks' item the case runner compiles the host programs with (plan:
/// W1-11 D-14): its compiler and flags.
pub const ITEM: &str = "c-clang";

/// Run the sequences `seqs` (all of `target`) on its build.
pub fn run_target(target: &str, seqs: &[&Seq], out: &BuildOutput) -> TargetRun {
    let mut r = TargetRun::default();
    let not_run = |r: &mut TargetRun, why: &str| {
        for s in seqs {
            r.results.push(SeqResult {
                name: s.name.clone(),
                target: target.into(),
                outcome: Outcome::NotRun(why.into()),
            });
        }
    };
    let settings = &out.settings;
    match settings.panic {
        PanicMode::Trap | PanicMode::Halt => {
            r.case_errors.push(format!(
                "[[test.host]] on target `{target}`: `panic = \"{}\"` never returns from a panic (a trap ends the \
                 process, which writes a crash report on macOS; halt spins); the steps need `\"poison\"` or `\"reset\"`",
                if settings.panic == PanicMode::Trap { "trap" } else { "halt" }
            ));
            return r;
        }
        PanicMode::Poison | PanicMode::Reset => {}
    }
    if !settings.platform.is_host() {
        r.case_errors.push(format!(
            "[[test.host]] on target `{target}`: the platform `{}` is not the host; the steps run here",
            settings.platform.triple
        ));
        return r;
    }
    let mut plans = Vec::new();
    for s in seqs {
        match plan::plan(s, out) {
            Ok(p) => plans.push(p),
            Err(plan::PlanError::Case(e)) => r.case_errors.push(e),
            Err(plan::PlanError::Harness(e)) => r.harness.push(e),
        }
    }
    if !r.case_errors.is_empty() || !r.harness.is_empty() {
        return r;
    }
    let Some(Check::Unit(tool)) = c::item(ITEM).map(|i| i.check) else {
        r.harness.push(format!("the C check `{ITEM}` is not a compile of units"));
        return r;
    };
    if let Err(e) = c::require(tool.cc) {
        r.harness.push(e);
        return r;
    }
    let dir = c::scratch_dir("onsa_host", "");
    let program = driver::program(out, &plans);
    let built = c::compile_driver(&tool, out, &dir, "host_driver.c", &program.source, driver::PANIC_HANDLER, &[]);
    if let Ok(exe) = &built {
        for (i, p) in plans.iter().enumerate() {
            let outcome = match run_seq(exe, i, p, tool.runner, program.seqs[i].as_ref()) {
                Ok(o) => o,
                Err(e) => {
                    r.harness.push(format!("host \"{}\": {e}", p.name));
                    continue;
                }
            };
            r.results.push(SeqResult { name: p.name.clone(), target: target.into(), outcome });
        }
    }
    let kept = c::keep_or_remove(&dir, "the host-steps files");
    if let Err(e) = built {
        let kept = kept.as_ref().map_or_else(String::new, |n| format!("\n({n})"));
        r.failures.push(format!("the host steps of target `{target}` do not compile: {e}{kept}"));
        not_run(&mut r, &format!("the program of target `{target}` does not compile"));
    }
    r.notes.extend(kept);
    r
}

/// Run sequence `i` of the program and compare it. `Err` is an error of the harness.
fn run_seq(
    exe: &Path,
    i: usize,
    p: &plan::SeqPlan,
    runner: c::Runner,
    unsupported: Option<&driver::Unsupported>,
) -> Result<Outcome, String> {
    let made = unsupported.map_or(p.steps.len(), |u| u.step);
    let done = c::run_program(exe, &[i.to_string()], runner, plan::input_bytes(p, made), c::RUN_TIMEOUT)?;
    compare::outcome(p, &done, unsupported)
}
