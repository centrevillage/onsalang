//! Conformance (T4-7, spec §13.4) of one build: every exported flow is run
//! through the interpreter and through the generated C with the same stimuli
//! (impulse, silence, deterministic noise per `Sig` input channel; two
//! blocks of 2048 frames so `ctl` runs twice; `@param` defaults, fixed
//! `Init` values). Flows that reach a transcendental primitive are compared
//! within 2 ULP (S-14); the others must match bit for bit; NaNs compare
//! equal (§13.4). A panic is part of the result: both must panic, or
//! neither. The interpreter runs the same Core module the C was emitted
//! from (the build's, R-89 (3)).
//!
//! Every scalar type of the boundary (§11.6) is fed and read: `F32`, `F64`,
//! the integers, `Bool`, `Char`. A flow the harness cannot drive is not
//! dropped silently: it is counted in [`Outcome::skipped`] with the reason
//! (R-113 3).
//!
//! The C program reads the `Init` values, the `Ctl` values and the inputs
//! from its standard input as bytes, and writes the outputs to its standard
//! output; the stimuli are made once, here. It never ends by a signal
//! (`crate::c`): a panic exits with [`crate::c::PANIC_EXIT`].

use std::fmt::Write as _;
use std::path::Path;

use onsa_backend_c::{FlowApi, PanicMode};
use onsa_core::prim::Prim;
use onsa_core::walk::walk_block;
use onsa_core::{ExprKind, FlowMeta, FnId, Module, Ty, TypeDefKind, TypeId};
use onsa_driver::BuildOutput;
use onsa_interp::value::{int_value, zero_array};
use onsa_interp::{ArrayData, Interp, Proj, SpanRef, Value, slot};

use crate::c::{self, Toolchain};
use crate::capi;
use crate::scalar::{Scalar, distance, same};

const FRAMES: u32 = 4096;
const BLOCK: u32 = 2048;
const STIMULI: u32 = 3;
const SAMPLE_RATE: f32 = 48000.0;

/// The stimuli and the fixed values the harness feeds (the codec is [`crate::scalar`]).
impl Scalar {
    /// One: the value of an impulse.
    fn one(self) -> Value {
        match self {
            Scalar::F32 => Value::F32(1.0),
            Scalar::F64 => Value::F64(1.0),
            Scalar::Int(k) => int_value(k, 1),
            Scalar::Bool => Value::Bool(true),
            Scalar::Char => Value::Char('\u{1}'),
        }
    }

    /// A noise sample from the 32-bit state `x`: in [-0.5, 0.5) for the
    /// floats (exact in `f32`); a small range for the integers (-128..=127,
    /// 0..=255 unsigned) so that ordinary arithmetic does not overflow at
    /// once; ASCII for `Char`.
    fn noise(self, x: u32) -> Value {
        let f = ((x >> 8) as f32) / 16777216.0 - 0.5;
        match self {
            Scalar::F32 => Value::F32(f),
            Scalar::F64 => Value::F64(f as f64),
            Scalar::Int(k) => int_value(k, (x >> 24) as i128 - if k.signed() { 128 } else { 0 }),
            Scalar::Bool => Value::Bool(x >> 31 == 1),
            Scalar::Char => Value::Char(char::from((x >> 25) as u8)),
        }
    }

    /// The value the harness gives an `Init` input (no default exists): a
    /// fixed value other than zero.
    fn init_value(self) -> Value {
        match self {
            Scalar::F32 => Value::F32(0.25),
            Scalar::F64 => Value::F64(0.25),
            Scalar::Int(k) => int_value(k, 3),
            Scalar::Bool => Value::Bool(true),
            Scalar::Char => Value::Char('a'),
        }
    }

    /// The value of a `Ctl` input: its `@param` default (an integer input
    /// takes it when it is a whole number in range), else zero.
    fn param_value(self, default: Option<f64>) -> Value {
        match (self, default) {
            (Scalar::F32, Some(d)) => Value::F32(d as f32),
            (Scalar::F64, Some(d)) => Value::F64(d),
            (Scalar::Int(k), Some(d)) if d.fract() == 0.0 && k.range().0 as f64 <= d && d <= k.range().1 as f64 => {
                int_value(k, d as i128)
            }
            (s, _) => s.zero(),
        }
    }
}

fn reaches_transcendental(m: &Module, meta: &FlowMeta) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack: Vec<FnId> = vec![meta.fns.init, meta.fns.ctl, meta.fns.tick, meta.fns.process];
    let mut found = false;
    while let Some(f) = stack.pop() {
        if !seen.insert(f) {
            continue;
        }
        if let Some(b) = &m.fn_(f).body {
            walk_block(b, &mut |e| match &e.kind {
                ExprKind::Call { fn_, .. } => stack.push(*fn_),
                ExprKind::Prim { prim: Prim::Math(mf, _), .. } if !mf.is_exact() => found = true,
                _ => {}
            });
        }
    }
    found
}

/// A `Sig` input or an output: its scalar type and its channels (`None`:
/// one buffer; `Some(n)`: `[T; n]`, a buffer per channel).
#[derive(Debug, Clone)]
struct Signal {
    name: String,
    scalar: Scalar,
    planar: Option<u32>,
}

impl Signal {
    fn channels(&self) -> u32 {
        self.planar.unwrap_or(1)
    }
}

/// What the harness feeds and reads of one flow.
#[derive(Debug, Clone)]
struct Shape {
    config: Vec<(String, Scalar)>,
    params: Vec<(String, Scalar, Value)>,
    inputs: Vec<Signal>,
    outputs: Vec<Signal>,
}

fn struct_fields(m: &Module, id: TypeId) -> &[(String, Ty)] {
    match &m.ty(id).kind {
        TypeDefKind::Struct { fields } => fields,
        _ => &[],
    }
}

fn scalar_of(ty: &Ty, what: &str) -> Result<Scalar, String> {
    Scalar::of(ty).ok_or_else(|| format!("{what} of type {ty:?} is not a scalar"))
}

fn signal(name: &str, ty: &Ty, planar: Option<u32>, what: &str) -> Result<Signal, String> {
    let (elem, planar) = match (ty, planar) {
        (Ty::Array(e, n), None) => (&**e, Some(*n)),
        (t, p) => (t, p),
    };
    Ok(Signal { name: name.to_string(), scalar: scalar_of(elem, &format!("{what} `{name}`"))?, planar })
}

impl Shape {
    /// The shape of a flow, or why the harness cannot drive it.
    fn of(m: &Module, meta: &FlowMeta) -> Result<Shape, String> {
        let config = struct_fields(m, meta.fns.config)
            .iter()
            .map(|(n, t)| Ok((n.clone(), scalar_of(t, &format!("the `Init` input `{n}`"))?)))
            .collect::<Result<_, String>>()?;
        let pfields = struct_fields(m, meta.fns.params);
        if pfields.len() != meta.params.len() {
            return Err(format!("{} `Ctl` inputs but {} fields in its params", meta.params.len(), pfields.len()));
        }
        let params = pfields
            .iter()
            .zip(&meta.params)
            .map(|((n, t), (_, _, pm))| {
                let s = scalar_of(t, &format!("the `Ctl` input `{n}`"))?;
                Ok((n.clone(), s, s.param_value(pm.as_ref().and_then(|p| p.default))))
            })
            .collect::<Result<_, String>>()?;
        let inputs =
            meta.sig_inputs.iter().map(|(n, t)| signal(n, t, None, "the `Sig` input")).collect::<Result<_, _>>()?;
        let outputs = meta.outputs.iter().map(|(n, t, p)| signal(n, t, *p, "the output")).collect::<Result<_, _>>()?;
        Ok(Shape { config, params, inputs, outputs })
    }

    /// The stimulus `k` of every input channel, in order (inputs, then channels).
    fn stimuli(&self, k: u32) -> Vec<Vec<Value>> {
        let mut out = Vec::new();
        let mut j = 0u32;
        for s in &self.inputs {
            for _ in 0..s.channels() {
                let mut v = vec![s.scalar.zero(); FRAMES as usize];
                match k {
                    0 => v[0] = s.scalar.one(),
                    1 => {}
                    _ => {
                        let mut x: u32 = 12345 + j * 7919;
                        for e in v.iter_mut() {
                            x = x.wrapping_mul(1664525).wrapping_add(1013904223);
                            *e = s.scalar.noise(x);
                        }
                    }
                }
                out.push(v);
                j += 1;
            }
        }
        out
    }

    fn config_values(&self) -> Vec<Value> {
        self.config.iter().map(|(_, s)| s.init_value()).collect()
    }

    /// The standard input of the C program: `Init` values, `Ctl` values, inputs.
    fn stdin(&self, stimuli: &[Vec<Value>]) -> Vec<u8> {
        let mut b = Vec::new();
        for ((_, s), v) in self.config.iter().zip(self.config_values()) {
            s.bytes(&v, &mut b);
        }
        for (_, s, v) in &self.params {
            s.bytes(v, &mut b);
        }
        let scalars = self.inputs.iter().flat_map(|s| (0..s.channels()).map(move |_| s.scalar));
        for (s, ch) in scalars.zip(stimuli) {
            for v in ch {
                s.bytes(v, &mut b);
            }
        }
        b
    }
}

/// The result of one stimulus: the samples of every output channel (outputs,
/// then channels), or a panic.
#[derive(Debug)]
enum Run {
    Samples(Vec<Vec<Value>>),
    Panicked(Panic),
}

/// Where a panic happened: in `init`, or in the `process` call of a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum At {
    Init,
    Block(u32),
}

impl std::fmt::Display for At {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            At::Init => write!(f, "the `init` call"),
            At::Block(b) => write!(f, "the process of block {b}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Panic {
    at: At,
    message: String,
}

/// The check a panic message names. The spec fixes which check panics
/// (§3.4, §9.2), not the words of the message, so the comparison is of the
/// kind and of where it happened.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PanicKind {
    Overflow,
    DivisionByZero,
    Bounds,
    Conversion,
    Shift,
    SpanLengths,
    /// Another message (an Onsa `panic`, an `assert`): compared as written.
    Other(String),
    /// No message (a target with `panic_messages = false`): any kind.
    Unknown,
}

fn panic_kind(message: &str) -> PanicKind {
    let m = message.trim();
    if m.is_empty() {
        PanicKind::Unknown
    } else if m.contains("NaN") {
        PanicKind::Conversion
    } else if m.contains("division by zero") {
        PanicKind::DivisionByZero
    } else if m.contains("index") || m.contains("slice out of range") {
        PanicKind::Bounds
    } else if m.contains("out of range for") {
        PanicKind::Conversion
    } else if m.contains("overflow") || m.contains("negation") {
        PanicKind::Overflow
    } else if m.contains("shift amount") {
        PanicKind::Shift
    } else if m.contains("span lengths differ") {
        PanicKind::SpanLengths
    } else {
        PanicKind::Other(m.to_string())
    }
}

/// Whether two panics are the same: the same check, at the same place.
fn same_panic(a: &Panic, b: &Panic) -> bool {
    let (ka, kb) = (panic_kind(&a.message), panic_kind(&b.message));
    a.at == b.at && (ka == kb || ka == PanicKind::Unknown || kb == PanicKind::Unknown)
}

fn interp_run(module: &Module, meta: &FlowMeta, shape: &Shape, stimuli: Vec<Vec<Value>>) -> Result<Run, String> {
    // A case the interpreter cannot run is an error of the case (E0200,
    // S-224), found before any call, as `onsa test` and the vectors find it.
    let unsupported = onsa_interp::unsupported(module);
    if !unsupported.is_empty() {
        let found: Vec<String> = unsupported
            .iter()
            .map(|u| {
                let d = u.diagnostic();
                format!("{}: {}", d.code.as_str(), d.message)
            })
            .collect();
        return Err(format!("the interpreter of this version does not run the case: {}", found.join("; ")));
    }
    let interp = Interp::new(module);
    let fns = &meta.fns;
    let state = match interp.call(fns.init, vec![Value::Struct(shape.config_values()), Value::F32(SAMPLE_RATE)]) {
        Ok(s) => slot(s),
        Err(onsa_interp::Failure::Panic(p)) => return Ok(Run::Panicked(Panic { at: At::Init, message: p.message })),
        Err(onsa_interp::Failure::Unsupported(u)) => reached(&u),
    };
    let params = Value::Struct(shape.params.iter().map(|(_, _, v)| v.clone()).collect());
    let mut inputs = stimuli.into_iter();
    let ins: Vec<Vec<onsa_interp::Slot>> = shape
        .inputs
        .iter()
        .map(|s| {
            (0..s.channels())
                .map(|_| {
                    let data = ArrayData::from_values(&s.scalar.ty(), inputs.next().expect("a stimulus per channel"));
                    slot(Value::Array(data))
                })
                .collect()
        })
        .collect();
    let outs: Vec<Vec<onsa_interp::Slot>> = shape
        .outputs
        .iter()
        .map(|s| (0..s.channels()).map(|_| slot(Value::Array(zero_array(module, &s.scalar.ty(), FRAMES)))).collect())
        .collect();
    for b in 0..FRAMES / BLOCK {
        let span = |s: &onsa_interp::Slot| {
            Value::Span(SpanRef { root: s.clone(), projs: Vec::<Proj>::new(), start: b * BLOCK, len: BLOCK })
        };
        let arg = |sig: &Signal, slots: &[onsa_interp::Slot]| match sig.planar {
            None => span(&slots[0]),
            Some(_) => Value::Array(ArrayData::Any(slots.iter().map(span).collect())),
        };
        let mut args = vec![params.clone()];
        args.extend(shape.inputs.iter().zip(&ins).map(|(s, x)| arg(s, x)));
        args.extend(shape.outputs.iter().zip(&outs).map(|(s, x)| arg(s, x)));
        match interp.call_inout(fns.process, &state, args) {
            Ok(_) => {}
            Err(onsa_interp::Failure::Panic(p)) => {
                return Ok(Run::Panicked(Panic { at: At::Block(b), message: p.message }));
            }
            Err(onsa_interp::Failure::Unsupported(u)) => reached(&u),
        }
    }
    let mut all = Vec::new();
    for ch in outs.iter().flatten() {
        match &*ch.borrow() {
            Value::Array(data) => all.push((0..data.len()).map(|i| data.get(i)).collect()),
            other => return Err(format!("the harness read an interpreter output that is not an array: {other:?}")),
        }
    }
    Ok(Run::Samples(all))
}

/// A form the interpreter cannot run, reached by a run that the check before
/// it let through: an internal error (S-67), as in `onsa test`.
fn reached(u: &onsa_interp::Unsupported) -> ! {
    onsa_diag::internal::bug(
        Some(u.span),
        format!("the interpreter reached `{}`, which the check before the run did not find", u.std_fn),
    )
}

/// The line the C program's panic handler writes to stderr.
const PANIC_LINE: &str = "onsa-conformance-panic:";

/// The panic the C program reported on stderr (`PANIC_LINE at=<n> msg=<m>`;
/// `n` is -1 for `init`, the block otherwise).
fn c_panic(stderr: &str) -> Result<Panic, String> {
    let line = stderr
        .lines()
        .find_map(|l| l.strip_prefix(PANIC_LINE))
        .ok_or_else(|| format!("the program exited as panicking but wrote no `{PANIC_LINE}` line:\n{stderr}"))?;
    let rest = line.trim_start().strip_prefix("at=").ok_or("no `at=` in the panic line")?;
    let (at, msg) = rest.split_once(" msg=").ok_or("no ` msg=` in the panic line")?;
    let at = match at.parse::<i64>().map_err(|e| format!("bad `at={at}`: {e}"))? {
        -1 => At::Init,
        b => At::Block(u32::try_from(b).map_err(|_| format!("bad `at={b}`"))?),
    };
    Ok(Panic { at, message: msg.to_string() })
}

/// The C program: reads the `Init` values, the `Ctl` values and the inputs
/// from stdin, runs two blocks, writes the outputs to stdout. The names come
/// from the C backend (`FlowApi`); the form of the calls from
/// [`crate::capi`]; the start of the program is [`c::driver_preamble`].
fn c_driver(api: &FlowApi, shape: &Shape, bulk_size: u32, panic: PanicMode) -> String {
    let mut d = c::driver_preamble(&[&api.header]);
    // A panic exits with a code (the trap is never reached), and says which check and where.
    let _ = writeln!(d, "static volatile int onsa_conformance_at = -1;   /* -1: init; else the block */");
    let _ = writeln!(
        d,
        "void onsa_conformance_panic(const char* msg, const char* file, uint32_t line) {{\n  \
         fprintf(stderr, \"{PANIC_LINE} at=%d msg=%s\\n(%s:%lu)\\n\", onsa_conformance_at, msg, file, (unsigned long)line);\n  \
         _Exit({});\n}}",
        c::PANIC_EXIT
    );
    if panic == PanicMode::Reset {
        let _ = writeln!(d, "ONSA_NORETURN void onsa_reset_hook(void) {{ _Exit({}); }}", c::PANIC_EXIT);
    }
    // The C types are the backend's records (D-15); an undeclared name where
    // a record is missing: the program does not compile (never a silent type).
    let io_type = |name: &str, output: bool| {
        api.process_args.iter().find(|a| a.name == name && a.output == output).map_or_else(
            || format!("onsa_conformance_no_signal_{}", onsa_backend_c::c_ident(name)),
            |a| a.c_type.clone(),
        )
    };
    for (i, s) in shape.inputs.iter().enumerate() {
        let _ = writeln!(d, "static {} in{i}[{}][{FRAMES}];", io_type(&s.name, false), s.channels());
    }
    for (o, s) in shape.outputs.iter().enumerate() {
        let _ = writeln!(d, "static {} out{o}[{}][{FRAMES}];", io_type(&s.name, true), s.channels());
    }
    d.push_str(&capi::storage(api, "mem", "bulk"));
    let _ = writeln!(d, "int main(void) {{");
    let _ = writeln!(d, "  if (!onsa_driver_signals()) return {};", c::SETUP_EXIT);
    let _ = writeln!(d, "  {} p;\n  memset(&p, 0, sizeof p);", capi::params_type(api));
    for (i, (name, _)) in shape.config.iter().enumerate() {
        let t = api.init_args.iter().find(|f| &f.name == name).map_or_else(
            || format!("onsa_conformance_no_init_input_{}", onsa_backend_c::c_ident(name)),
            |f| f.c_type.clone(),
        );
        let _ = writeln!(d, "  {t} c{i};\n  onsa_driver_need(&c{i}, sizeof c{i});");
    }
    for (name, _, _) in &shape.params {
        // An undeclared field where the record is missing: the program does not compile.
        let f = api.params_fields.iter().find(|f| &f.name == name).map_or_else(
            || format!("onsa_conformance_no_param_{}", onsa_backend_c::c_ident(name)),
            |f| f.c_name.clone(),
        );
        let _ = writeln!(d, "  onsa_driver_need(&p.{f}, sizeof p.{f});");
    }
    for i in 0..shape.inputs.len() {
        let _ = writeln!(d, "  onsa_driver_need(in{i}, sizeof in{i});");
    }
    let state = capi::state_type(api);
    let _ = writeln!(d, "  {state}* s = ({state}*)mem;");
    // Without a bulk region the harness passes NULL (spec §14.2).
    let bulk = if bulk_size > 0 { "bulk" } else { "NULL" };
    if bulk_size == 0 {
        let _ = writeln!(d, "  (void)bulk;");
    }
    let cfg = |f: &onsa_backend_c::ApiField| match shape.config.iter().position(|(n, _)| *n == f.name) {
        Some(i) => format!("c{i}"),
        // An undeclared name: the program does not compile (never a silent value).
        None => format!("onsa_conformance_no_value_for_{}", f.c_name),
    };
    let init = capi::init(api, "s", bulk, capi::Cfg::Values(&cfg), &format!("{SAMPLE_RATE:.1}f"))
        .unwrap_or_else(|e| format!("/* {} */ -1", e.0));
    let _ = writeln!(d, "  if ({init} != 0) return {};", c::API_ERROR_EXIT);
    let _ = writeln!(d, "  for (uint32_t b = 0; b < {}; b++) {{", FRAMES / BLOCK);
    let _ = writeln!(d, "    onsa_conformance_at = (int)b;");
    for (i, s) in shape.inputs.iter().enumerate() {
        if let Some(n) = s.planar {
            let chans: Vec<String> = (0..n).map(|c| format!("in{i}[{c}] + b * {BLOCK}")).collect();
            let _ = writeln!(d, "    const {}* in{i}_ch[{n}] = {{ {} }};", io_type(&s.name, false), chans.join(", "));
        }
    }
    for (o, s) in shape.outputs.iter().enumerate() {
        if let Some(n) = s.planar {
            let chans: Vec<String> = (0..n).map(|c| format!("out{o}[{c}] + b * {BLOCK}")).collect();
            let _ = writeln!(d, "    {}* out{o}_ch[{n}] = {{ {} }};", io_type(&s.name, true), chans.join(", "));
        }
    }
    let io = |a: &onsa_backend_c::IoArg| {
        let (list, prefix) = if a.output { (&shape.outputs, "out") } else { (&shape.inputs, "in") };
        match list.iter().position(|s| s.name == a.name) {
            Some(i) if list[i].planar.is_some() => format!("{prefix}{i}_ch"),
            Some(i) => format!("{prefix}{i}[0] + b * {BLOCK}"),
            // An undeclared name: the program does not compile (never a silent NULL).
            None => format!("onsa_conformance_no_signal_{}", a.c_name),
        }
    };
    let process = capi::process(api, "s", "&p", &io, &BLOCK.to_string());
    let _ = writeln!(d, "    if ({process} != 0) return {};", c::API_ERROR_EXIT);
    let _ = writeln!(d, "  }}");
    for (o, s) in shape.outputs.iter().enumerate() {
        let _ = writeln!(
            d,
            "  for (uint32_t c = 0; c < {}; c++) fwrite(out{o}[c], sizeof out{o}[c][0], {FRAMES}, stdout);",
            s.channels()
        );
    }
    let _ = writeln!(d, "  return 0;\n}}");
    d
}

/// Compile the program of one flow; its path.
fn c_build(
    out: &BuildOutput,
    api: &FlowApi,
    meta: &FlowMeta,
    shape: &Shape,
    t: &Toolchain,
    dir: &Path,
) -> Result<std::path::PathBuf, String> {
    let dir = dir.join(&api.symbol);
    let driver = c_driver(api, shape, meta.layout.bulk_size, out.settings.panic);
    c::compile_driver(t, out, &dir, "driver.c", &driver, "onsa_conformance_panic", &[])
}

/// Run the program with `input` on stdin, within [`c::RUN_TIMEOUT`].
fn c_exec(exe: &Path, t: &Toolchain, input: Vec<u8>, shape: &Shape) -> Result<Run, String> {
    let done = c::run_program(exe, &[], t.runner, input, c::RUN_TIMEOUT)?;
    let Some(status) = done.status else {
        return Err(format!("the program ran longer than {}s", c::RUN_TIMEOUT.as_secs()));
    };
    let (bytes, err) = (done.stdout, done.stderr);
    match status.code() {
        Some(0) => {}
        Some(c::PANIC_EXIT) => return Ok(Run::Panicked(c_panic(&err)?)),
        Some(code) => {
            let what = c::exit_meaning(c::DriverKind::Conformance, code)
                .map_or_else(|| format!("exit {code}"), str::to_string);
            return Err(format!("the program failed: {what}\n{err}"));
        }
        None => return Err(format!("the program ended by a signal ({status})\n{err}")),
    }
    let mut chans = Vec::new();
    let mut at = 0;
    for s in &shape.outputs {
        let n = s.scalar.size();
        for _ in 0..s.channels() {
            let len = n * FRAMES as usize;
            let Some(b) = bytes.get(at..at + len) else {
                return Err(format!("the program wrote {} bytes, fewer than its outputs", bytes.len()));
            };
            chans.push(b.chunks_exact(n).map(|x| s.scalar.read(x)).collect::<Result<Vec<_>, _>>()?);
            at += len;
        }
    }
    if at != bytes.len() {
        return Err(format!("the program wrote {} bytes, more than its outputs ({at})", bytes.len()));
    }
    Ok(Run::Samples(chans))
}

/// The result of one build.
#[derive(Debug, Default)]
pub struct Outcome {
    /// A line per flow.
    pub report: Vec<String>,
    pub problems: Vec<String>,
    /// The flows compared.
    pub compared: usize,
    /// The flows not compared, with the reason: counted, never dropped (R-113 3).
    pub skipped: Vec<(String, String)>,
}

/// Run every flow the build exported in both, with the C of toolchain `t`.
/// `dir` is a scratch directory. The interpreter runs on the stack of a
/// command (R-05, `onsa_diag::stack`), under a guard on that thread: an
/// internal error of the interpreter is a problem of this build with its
/// position (S-67), not a panic of the caller's thread (P-2).
pub fn run(out: &BuildOutput, t: &Toolchain, dir: &Path) -> Outcome {
    onsa_driver::guard_on_stack(|| run_on_stack(out, t, dir)).unwrap_or_else(|e| Outcome {
        problems: vec![format!(
            "conformance: {}",
            e.render(&onsa_diag::SourceMap::default()).trim_end().replace('\n', "\n  ")
        )],
        ..Default::default()
    })
}

fn run_on_stack(out: &BuildOutput, t: &Toolchain, dir: &Path) -> Outcome {
    let module = &out.module;
    let mut outcome = Outcome::default();
    for api in &out.unit.flows {
        let Some(meta) = module.flows.iter().find(|m| m.name == api.flow) else {
            outcome.problems.push(format!("exported flow `{}` is not in the module", api.flow));
            continue;
        };
        let shape = match Shape::of(module, meta) {
            Ok(s) => s,
            Err(reason) => {
                outcome.report.push(format!("{}: skipped ({reason})", meta.name));
                outcome.skipped.push((meta.name.clone(), reason));
                continue;
            }
        };
        match compare_flow(out, api, meta, &shape, t, dir) {
            Ok(line) => {
                outcome.compared += 1;
                outcome.report.push(format!("{}: {line}", meta.name));
            }
            Err(e) => {
                outcome.compared += 1;
                outcome.problems.push(format!("{}: {e}", meta.name));
            }
        }
    }
    outcome
}

fn compare_flow(
    out: &BuildOutput,
    api: &FlowApi,
    meta: &FlowMeta,
    shape: &Shape,
    t: &Toolchain,
    dir: &Path,
) -> Result<String, String> {
    let exact = !reaches_transcendental(&out.module, meta);
    let exe = c_build(out, api, meta, shape, t, dir)?;
    let labels: Vec<String> = shape
        .outputs
        .iter()
        .flat_map(|s| {
            (0..s.channels()).map(move |c| match s.planar {
                None => format!("`{}`", s.name),
                Some(_) => format!("`{}` channel {c}", s.name),
            })
        })
        .collect();
    let (mut samples, mut differ, mut worst, mut panics) = (0usize, 0usize, 0u64, 0usize);
    for k in 0..STIMULI {
        let stimuli = shape.stimuli(k);
        let input = shape.stdin(&stimuli);
        let i = interp_run(&out.module, meta, shape, stimuli).map_err(|e| format!("stimulus {k}: {e}"))?;
        let c = c_exec(&exe, t, input, shape).map_err(|e| format!("stimulus {k}: {e}"))?;
        let (i, c) = match (i, c) {
            (Run::Panicked(a), Run::Panicked(b)) if same_panic(&a, &b) => {
                panics += 1;
                continue;
            }
            (Run::Panicked(a), Run::Panicked(b)) => {
                return Err(format!(
                    "stimulus {k}: both panic, but differently: the interpreter in {} ({}), the C in {} ({})",
                    a.at, a.message, b.at, b.message
                ));
            }
            (Run::Panicked(m), Run::Samples(_)) => {
                return Err(format!(
                    "stimulus {k}: the interpreter panics in {} ({}), the C does not",
                    m.at, m.message
                ));
            }
            (Run::Samples(_), Run::Panicked(m)) => {
                return Err(format!(
                    "stimulus {k}: the C panics in {} ({}), the interpreter does not",
                    m.at, m.message
                ));
            }
            (Run::Samples(i), Run::Samples(c)) => (i, c),
        };
        for (ch, (a, b)) in c.iter().zip(&i).enumerate() {
            for (n, (x, y)) in a.iter().zip(b).enumerate() {
                samples += 1;
                // The same sample by §13.4 ([`same`]); the ULP distance only within the tolerance.
                if same(x, y) {
                    continue;
                }
                match distance(x, y) {
                    Some(d) if !exact => {
                        differ += 1;
                        worst = worst.max(d);
                    }
                    _ => {
                        return Err(format!(
                            "stimulus {k}, output {}, sample {n} differs: C {x:?} vs interpreter {y:?}",
                            labels[ch]
                        ));
                    }
                }
            }
        }
    }
    if samples == 0 {
        return Err(format!(
            "compared no sample: every stimulus panics in both ({panics} of {STIMULI}); give the flow inputs that do not \
             always panic"
        ));
    }
    if worst > 2 {
        return Err(format!("worst difference {worst} ULP exceeds the precision target (2 ULP, S-14)"));
    }
    Ok(format!(
        "{samples} samples, {differ} differ, max {worst} ULP{} ({})",
        if panics > 0 { format!(", {panics} stimuli panic in both") } else { String::new() },
        if exact { "bit-exact required" } else { "2 ULP tolerance" }
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c::Runner;
    use onsa_core::{FloatKind, IntKind};

    /// The build of `src` (package `m`, every flow exported) for a host target.
    fn build(src: &str, flows: &[&str]) -> BuildOutput {
        let manifest = format!(
            "[package]\nname = \"m\"\nedition = \"2026\"\n\n[export]\nprefix = \"t_\"\nflows = [{}]\n\n\
             [targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\npanic = \"trap\"\nprovides = []\n",
            flows.iter().map(|f| format!("\"m.{f}\"")).collect::<Vec<_>>().join(", ")
        );
        let (manifest, _) = onsa_driver::Manifest::parse(&manifest, &[]).unwrap();
        let input = onsa_driver::PackageInput {
            manifest: Some(manifest),
            files: vec![onsa_driver::SourceFile { path: "m.onsa".into(), text: src.into() }],
            root: None,
        };
        let mut loaded = onsa_driver::Loaded::from_input(input);
        let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap();
        assert!(analyzed.diagnostics.is_empty(), "{:?}", analyzed.diagnostics);
        onsa_driver::build_analyzed(&loaded, &analyzed, "host").unwrap_or_else(|_| panic!("the build failed"))
    }

    const FLOWS: &str = "pub flow f(x: Sig[F32], n: Init[I32]) -> Sig[F32] {\n  x * n.round_f32()\n}\n";

    #[test]
    fn shapes_and_the_flows_that_are_skipped() {
        let mut out = build(FLOWS, &["f"]);
        let meta = out.module.flows[0].clone();
        let shape = Shape::of(&out.module, &meta).unwrap();
        assert_eq!(
            shape.config.iter().map(|(n, s)| (n.as_str(), *s)).collect::<Vec<_>>(),
            [("n", Scalar::Int(IntKind::I32))]
        );
        assert_eq!(shape.inputs.len(), 1);
        // A type the harness cannot feed: the flow is skipped with the reason, never dropped.
        let mut odd = meta.clone();
        odd.sig_inputs[0].1 = Ty::Tuple(Vec::new());
        let why = Shape::of(&out.module, &odd).unwrap_err();
        assert!(why.contains("the `Sig` input `x`") && why.contains("is not a scalar"), "{why}");
        let mut odd = meta.clone();
        odd.params.push(("k".into(), Ty::Float(FloatKind::F32), None));
        assert!(Shape::of(&out.module, &odd).unwrap_err().contains("1 `Ctl` inputs but 0 fields"));
        // Through `run`: counted in `skipped`, nothing compiled.
        out.module.flows[0].outputs[0].1 = Ty::Unit;
        let t = Toolchain { cc: "onsa-no-such-cc", flags: &[], off: &[], runner: Runner::Native };
        let o = run(&out, &t, Path::new("/nonexistent"));
        assert_eq!(o.compared, 0);
        assert!(o.problems.is_empty(), "{:?}", o.problems);
        assert_eq!(o.skipped.len(), 1);
        assert_eq!(o.skipped[0].0, "m.f");
        assert!(o.report[0].contains("skipped"), "{:?}", o.report);
    }

    #[test]
    fn panics_compare_by_check_and_place() {
        let p = |at, m: &str| Panic { at, message: m.into() };
        let pairs = [
            ("integer overflow in `127 * 2` (I8)", "integer overflow in `*`"),
            ("integer overflow in `-128`", "integer overflow in negation"),
            ("division by zero", "division by zero"),
            ("index 4 out of range for a sequence of length 4", "index out of range"),
            ("conversion of NaN to an integer", "conversion of NaN to an integer"),
            ("30000000000.0 is out of range for I32", "float out of range for the integer type"),
            ("shift amount 9 is not below the bit width 8", "shift amount exceeds the bit width"),
            ("span lengths differ: 3 and 4", "span lengths differ"),
        ];
        for (i, c) in pairs {
            assert!(same_panic(&p(At::Block(1), i), &p(At::Block(1), c)), "{i} / {c}");
            assert!(!same_panic(&p(At::Block(1), i), &p(At::Block(0), c)), "{i} / {c}: another block");
            assert!(!same_panic(&p(At::Init, i), &p(At::Block(0), c)), "{i} / {c}: init and process");
        }
        assert!(!same_panic(&p(At::Init, "division by zero"), &p(At::Init, "integer overflow in `/`")));
        assert!(!same_panic(
            &p(At::Init, "index 1 out of range"),
            &p(At::Init, "float out of range for the integer type")
        ));
        assert!(same_panic(&p(At::Init, "custom"), &p(At::Init, "custom")));
        assert!(!same_panic(&p(At::Init, "custom"), &p(At::Init, "other")));
        // a target without panic messages: any check
        assert!(same_panic(&p(At::Init, ""), &p(At::Init, "division by zero")));
    }

    #[test]
    fn the_panic_line_of_the_c_program() {
        let p = c_panic("x\nonsa-conformance-panic: at=1 msg=integer overflow in `*`\n(m.onsa:3)\n").unwrap();
        assert_eq!(p, Panic { at: At::Block(1), message: "integer overflow in `*`".into() });
        assert_eq!(c_panic("onsa-conformance-panic: at=-1 msg=\n").unwrap().at, At::Init);
        assert!(c_panic("panic: boom\n").is_err());
        assert!(c_panic("onsa-conformance-panic: at=x msg=a\n").is_err());
    }

    #[test]
    fn scalars_round_trip_through_bytes() {
        let kinds = [
            Scalar::F32,
            Scalar::F64,
            Scalar::Bool,
            Scalar::Char,
            Scalar::Int(IntKind::I8),
            Scalar::Int(IntKind::I16),
            Scalar::Int(IntKind::I32),
            Scalar::Int(IntKind::I64),
            Scalar::Int(IntKind::U8),
            Scalar::Int(IntKind::U16),
            Scalar::Int(IntKind::U32),
            Scalar::Int(IntKind::U64),
        ];
        for s in kinds {
            for v in [s.zero(), s.one(), s.noise(0xffff_ffff), s.noise(0x0000_0000), s.init_value()] {
                let mut b = Vec::new();
                s.bytes(&v, &mut b);
                assert_eq!(b.len(), s.size(), "{s:?}");
                assert_eq!(distance(&s.read(&b).unwrap(), &v), Some(0), "{s:?} {v:?}");
            }
        }
        // the extremes of the signed kinds
        let mut b = Vec::new();
        Scalar::Int(IntKind::I8).bytes(&Value::I8(-128), &mut b);
        assert_eq!(b, [0x80]);
        assert!(matches!(Scalar::Int(IntKind::I8).read(&b).unwrap(), Value::I8(-128)));
        assert!(Scalar::Bool.read(&[2]).is_err());
        assert!(Scalar::Char.read(&0xd800u32.to_le_bytes()).is_err());
    }

    #[test]
    fn distances() {
        assert_eq!(distance(&Value::F32(f32::NAN), &Value::F32(-f32::NAN)), Some(0));
        assert_eq!(distance(&Value::F64(f64::NAN), &Value::F64(f64::NAN)), Some(0));
        assert_eq!(distance(&Value::F32(1.0), &Value::F32(f32::from_bits(1.0f32.to_bits() + 2))), Some(2));
        assert_ne!(distance(&Value::F32(0.0), &Value::F32(-0.0)), Some(0));
        // A NaN is never within a tolerance of a value that is not a NaN, even
        // when the bits are next to each other (S-106).
        assert_eq!(distance(&Value::F32(f32::from_bits(0x7f80_0001)), &Value::F32(f32::INFINITY)), None);
        assert_eq!(distance(&Value::F32(f32::MAX), &Value::F32(f32::from_bits(0x7f80_0001))), None);
        assert_eq!(distance(&Value::F64(f64::from_bits(0x7ff0_0000_0000_0001)), &Value::F64(f64::INFINITY)), None);
        assert_eq!(distance(&Value::F64(f64::from_bits(0xfff8_0000_0000_0000)), &Value::F64(1.0)), None);
        assert_eq!(
            distance(&Value::F32(f32::from_bits(0x7fc0_0001)), &Value::F32(f32::from_bits(0xff80_0001))),
            Some(0)
        );
        assert_eq!(distance(&Value::I32(3), &Value::I32(3)), Some(0));
        assert_eq!(distance(&Value::I32(3), &Value::I32(4)), None);
        assert_eq!(distance(&Value::I32(3), &Value::U32(3)), None);
        assert_eq!(distance(&Value::Bool(true), &Value::Bool(false)), None);
    }

    #[test]
    fn noise_stays_small_for_integers() {
        for x in [0u32, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff] {
            for k in [IntKind::I8, IntKind::I64] {
                let n = Scalar::Int(k).noise(x).to_i128().unwrap();
                assert!((-128..=127).contains(&n), "{k:?} {n}");
            }
            let n = Scalar::Int(IntKind::U8).noise(x).to_i128().unwrap();
            assert!((0..=255).contains(&n));
        }
    }
}
