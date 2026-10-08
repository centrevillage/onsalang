//! The C program of the sequences of one target: a function per sequence
//! that makes its calls in order, `main` picks one by `argv[1]`. The calls
//! are written by [`crate::capi`]; the values are read from the standard
//! input in the order of [`super::plan::input_bytes`].
//!
//! What it writes to the standard output (unbuffered, so a run that ends
//! inside a call keeps what came before; [`super::compare`] reads it):
//!
//! ```text
//! per step:  u32 step index (before the call)
//!            i32 status                  (init, process, fn)
//!            the outputs, channel by channel, `frames` values each   (process, unless NULL)
//!            the returned value          (fn, when it returns one)
//!            u32 RESET_DONE              (reset: the call returned)
//! at the end: u32 0xFFFFFFFF
//! ```
//!
//! The sizes after the index are [`super::plan::record_len`]. A sequence is
//! the function `onsa_host_seq_<i>`: its name never reaches the C.

use std::fmt::Write as _;

use onsa_backend_c::{IoArg, PanicMode};
use onsa_driver::BuildOutput;

use super::plan::{Before, Callee, Op, SeqPlan};
use crate::c;
use crate::capi;

/// The function the program defines as `ONSA_PANIC_HANDLER`: it writes the
/// panic to stderr (for the report) and returns, so that the target's
/// `panic` setting acts.
pub const PANIC_HANDLER: &str = "onsa_host_panic";

/// The line of the panic handler.
pub const PANIC_LINE: &str = "onsa-host-panic:";

/// The end of the records.
pub const END: u32 = u32::MAX;

/// A step of a sequence that this version's C API cannot express: the
/// program makes the steps before it and stops there (the state does not go on).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported {
    /// 0-based.
    pub step: usize,
    pub message: String,
}

/// The mark a `reset` writes after the call: the call returned.
pub const RESET_DONE: u32 = 0x5245_5354;

/// A program: its source, and for each sequence the step this version's C
/// API cannot express, if any.
pub struct Program {
    pub source: String,
    pub seqs: Vec<Option<Unsupported>>,
}

/// The program of `plans` on the build `out`. A sequence is named by its
/// number only: its name never reaches the C (the report names it).
pub fn program(out: &BuildOutput, plans: &[SeqPlan]) -> Program {
    let headers: Vec<&str> = out.unit.headers.iter().map(|(n, _)| n.as_str()).collect();
    let mut d = c::driver_preamble(&headers);
    let _ = writeln!(
        d,
        "void {PANIC_HANDLER}(const char* msg, const char* file, uint32_t line) {{\n  \
         fprintf(stderr, \"{PANIC_LINE} %s (%s:%lu)\\n\", msg, file, (unsigned long)line);\n}}"
    );
    if out.settings.panic == PanicMode::Reset {
        let _ = writeln!(d, "_Noreturn void onsa_reset_hook(void) {{ _Exit({}); }}", c::RESET_HOOK_EXIT);
    }
    let _ = writeln!(d, "void onsa_host_step(uint32_t k) {{ onsa_driver_write(&k, sizeof k); }}\n");
    let mut seqs = Vec::new();
    let mut cases = String::new();
    for (i, p) in plans.iter().enumerate() {
        let (code, unsupported) = sequence(i, p);
        d.push_str(&code);
        let _ = writeln!(cases, "    case {i}: onsa_host_seq_{i}(); break;");
        seqs.push(unsupported);
    }
    let _ = writeln!(
        d,
        "int main(int argc, char** argv) {{\n  \
         setvbuf(stdout, NULL, _IONBF, 0);\n  \
         if (!onsa_driver_signals()) return {setup};\n  \
         if (argc != 2) return {args};\n  \
         switch (atoi(argv[1])) {{\n{cases}    default: return {args};\n  }}\n  \
         {{ uint32_t end = {END:#x}u; onsa_driver_write(&end, sizeof end); }}\n  \
         return 0;\n}}",
        setup = c::SETUP_EXIT,
        args = c::ARGS_EXIT,
    );
    Program { source: d, seqs }
}

/// The function of sequence `i`, up to the first step this version's C API
/// cannot express (that step and the ones after it are not in the program).
fn sequence(i: usize, p: &SeqPlan) -> (String, Option<Unsupported>) {
    let mut d = String::new();
    let mut body = String::new();
    let mem = format!("onsa_host_mem_{i}");
    let bulk = format!("onsa_host_bulk_{i}");
    if let Callee::Flow(api) = &p.callee {
        d.push_str(&capi::storage(api, &mem, &bulk));
        let state = capi::state_type(api);
        // The storage holds anything before `init` (spec §14.2: any storage of the size and alignment).
        let _ = writeln!(
            body,
            "  memset({mem}, {pat:#04x}, sizeof {mem});\n  memset({bulk}, {pat:#04x}, sizeof {bulk});\n  \
             {state}* s = ({state}*){mem};\n  (void)s;   /* the steps may stop before any call */",
            pat = super::PATTERN
        );
    }
    let mut unsupported = None;
    for (k, st) in p.steps.iter().enumerate() {
        match step(&mut body, k, &st.op, &p.callee, &bulk) {
            Ok(()) => {}
            Err(e) => {
                unsupported = Some(Unsupported { step: k, message: e });
                break;
            }
        }
    }
    let _ = writeln!(d, "static void onsa_host_seq_{i}(void) {{\n{body}}}\n");
    (d, unsupported)
}

/// The code of step `k`; `Err`: this version's C API cannot express it.
fn step(body: &mut String, k: usize, op: &Op, callee: &Callee, bulk: &str) -> Result<(), String> {
    let v = |j: usize| format!("v{k}_{j}");
    let mut b = String::new();
    let _ = writeln!(b, "  {{ /* step {} */", k + 1);
    match (op, callee) {
        (Op::Init { config, null_bulk, .. }, Callee::Flow(api)) => {
            for (j, x) in config.iter().flatten().enumerate() {
                let _ = writeln!(b, "    {} {}; onsa_driver_need(&{}, sizeof {});", x.field.c_type, v(j), v(j), v(j));
            }
            let _ = writeln!(b, "    {} sr; onsa_driver_need(&sr, sizeof sr);", capi::SAMPLE_RATE_C);
            let names: Vec<(String, String)> =
                config.iter().flatten().enumerate().map(|(j, x)| (x.field.name.clone(), v(j))).collect();
            let lookup = |f: &onsa_backend_c::ApiField| {
                names
                    .iter()
                    .find(|(n, _)| *n == f.name)
                    // An undeclared name: the program does not compile (never a silent value).
                    .map_or_else(|| format!("onsa_host_no_value_for_{}", f.c_name), |(_, e)| e.clone())
            };
            let cfg = match config {
                Some(_) => capi::Cfg::Values(&lookup),
                None => capi::Cfg::Null,
            };
            let bulk = if *null_bulk { "NULL" } else { bulk };
            let call = capi::init(api, "s", bulk, cfg, "sr").map_err(|e| e.0)?;
            let _ =
                writeln!(b, "    onsa_host_step({k}u);\n    int st = {call};\n    onsa_driver_write(&st, sizeof st);");
        }
        (Op::Process { params, frames, inputs, outputs, .. }, Callee::Flow(api)) => {
            let _ = writeln!(b, "    {} p; memset(&p, 0, sizeof p);", capi::params_type(api));
            for x in params {
                let f = &x.field.c_name;
                let _ = writeln!(b, "    onsa_driver_need(&p.{f}, sizeof p.{f});");
            }
            let n = (*frames).max(1);
            let buf = |kind: &str, j: usize, ch: u32| format!("{kind}{k}_{j}_{ch}");
            let mut in_expr: Vec<(String, String)> = Vec::new();
            for (j, s) in inputs.iter().flatten().enumerate() {
                let t = &s.c_type;
                for ch in 0..s.planar.unwrap_or(1) {
                    let x = buf("in", j, ch);
                    let _ = writeln!(b, "    static {t} {x}[{n}]; onsa_driver_need({x}, sizeof({t}) * {frames}u);");
                }
                let e = match s.planar {
                    None => buf("in", j, 0),
                    Some(c) => {
                        let list: Vec<String> = (0..c).map(|ch| buf("in", j, ch)).collect();
                        let _ = writeln!(b, "    const {t}* in{k}_{j}[{c}] = {{ {} }};", list.join(", "));
                        format!("in{k}_{j}")
                    }
                };
                in_expr.push((s.name.clone(), e));
            }
            // The outputs' buffers: filled before the call, or the input's (`inplace`).
            let mut out_expr: Vec<(String, String)> = Vec::new();
            let mut out_bufs: Vec<(String, String)> = Vec::new(); // (buffer, C type), in record order
            for (j, o) in outputs.iter().flatten().enumerate() {
                let t = &o.c_type;
                let chans = o.planar.unwrap_or(1);
                let names: Vec<String> = match o.before {
                    Before::Inplace(src) => (0..chans).map(|ch| buf("in", src, ch)).collect(),
                    _ => (0..chans)
                        .map(|ch| {
                            let x = buf("out", j, ch);
                            let _ =
                                writeln!(b, "    static {t} {x}[{n}]; onsa_driver_need({x}, sizeof({t}) * {frames}u);");
                            x
                        })
                        .collect(),
                };
                let e = match o.planar {
                    None => names[0].clone(),
                    Some(c) => {
                        let _ = writeln!(b, "    {t}* out{k}_{j}[{c}] = {{ {} }};", names.join(", "));
                        format!("out{k}_{j}")
                    }
                };
                out_bufs.extend(names.into_iter().map(|x| (x, t.clone())));
                out_expr.push((o.name.clone(), e));
            }
            let io = |a: &IoArg| {
                let list = if a.output { &out_expr } else { &in_expr };
                let null = if a.output { outputs.is_none() } else { inputs.is_none() };
                match list.iter().find(|(n, _)| *n == a.name) {
                    Some((_, e)) => e.clone(),
                    None if null => "NULL".into(),
                    // An undeclared name: the program does not compile (never a silent NULL).
                    None => format!("onsa_host_no_signal_{}", a.c_name),
                }
            };
            let call = capi::process(api, "s", "&p", &io, &format!("{frames}u"));
            let _ =
                writeln!(b, "    onsa_host_step({k}u);\n    int st = {call};\n    onsa_driver_write(&st, sizeof st);");
            for (x, t) in &out_bufs {
                let _ = writeln!(b, "    onsa_driver_write({x}, sizeof({t}) * {frames}u);");
            }
        }
        (Op::Reset, Callee::Flow(api)) => {
            let _ = writeln!(
                b,
                "    onsa_host_step({k}u);\n    {}\n    {{ uint32_t done = {RESET_DONE:#x}u; onsa_driver_write(&done, sizeof done); }}",
                capi::reset(api, "s")
            );
        }
        (Op::Fn { args, ret, .. }, Callee::Fn(api, take_panic)) => {
            let mut fargs = Vec::new();
            for (j, a) in args.iter().enumerate() {
                let t = &a.param.field.c_type;
                match a.param.kind {
                    onsa_backend_c::FnParamKind::Span { .. } => {
                        let len = a.values.len();
                        let _ = writeln!(
                            b,
                            "    static {t} {}[{}]; onsa_driver_need({}, sizeof({t}) * {len}u);",
                            v(j),
                            len.max(1),
                            v(j)
                        );
                        fargs.push(capi::FnArg::Span(v(j), format!("{len}u")));
                    }
                    _ => {
                        let _ = writeln!(b, "    {t} {}; onsa_driver_need(&{}, sizeof {});", v(j), v(j), v(j));
                        fargs.push(capi::FnArg::Scalar(v(j)));
                    }
                }
            }
            let _ = writeln!(b, "    int st;");
            if let Some((_, c)) = ret {
                let _ = writeln!(b, "    {c} r;");
            }
            let call =
                capi::call_fn(api, take_panic.as_deref(), &fargs, "st", ret.as_ref().map(|_| "r")).map_err(|e| e.0)?;
            let _ = writeln!(b, "    onsa_host_step({k}u);\n    {call}\n    onsa_driver_write(&st, sizeof st);");
            if ret.is_some() {
                let _ = writeln!(b, "    onsa_driver_write(&r, sizeof r);");
            }
        }
        _ => return Err("the call does not fit the sequence".into()),
    }
    let _ = writeln!(b, "  }}");
    body.push_str(&b);
    Ok(())
}
