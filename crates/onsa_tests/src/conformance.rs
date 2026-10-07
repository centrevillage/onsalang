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
use std::io::{Read as _, Write as _};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use onsa_backend_c::{FlowApi, PanicMode};
use onsa_core::prim::Prim;
use onsa_core::walk::walk_block;
use onsa_core::{ExprKind, FloatKind, FlowMeta, FnId, IntKind, Module, Ty, TypeDefKind, TypeId};
use onsa_driver::BuildOutput;
use onsa_interp::value::{int_value, zero_array};
use onsa_interp::{ArrayData, Interp, Proj, SpanRef, Value, slot};

use crate::c::{self, Runner, Toolchain};

const FRAMES: u32 = 4096;
const BLOCK: u32 = 2048;
const STIMULI: u32 = 3;
const SAMPLE_RATE: f32 = 48000.0;
/// How long one run of the C program may take.
const TIMEOUT: Duration = Duration::from_secs(60);

/// A scalar type of the boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Scalar {
    F32,
    F64,
    Int(IntKind),
    Bool,
    Char,
}

impl Scalar {
    fn of(ty: &Ty) -> Option<Scalar> {
        Some(match ty {
            Ty::Float(FloatKind::F32) => Scalar::F32,
            Ty::Float(FloatKind::F64) => Scalar::F64,
            Ty::Int(k) => Scalar::Int(*k),
            Ty::Bool => Scalar::Bool,
            Ty::Char => Scalar::Char,
            _ => return None,
        })
    }

    fn ty(self) -> Ty {
        match self {
            Scalar::F32 => Ty::Float(FloatKind::F32),
            Scalar::F64 => Ty::Float(FloatKind::F64),
            Scalar::Int(k) => Ty::Int(k),
            Scalar::Bool => Ty::Bool,
            Scalar::Char => Ty::Char,
        }
    }

    /// The C spelling, as the backend writes it.
    fn c(self) -> &'static str {
        onsa_backend_c::scalar_c(&self.ty()).expect("a scalar has a C name")
    }

    fn size(self) -> usize {
        match self {
            Scalar::F32 | Scalar::Char => 4,
            Scalar::F64 => 8,
            Scalar::Int(k) => k.bits() as usize / 8,
            Scalar::Bool => 1,
        }
    }

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

    fn zero(self) -> Value {
        match self {
            Scalar::F32 => Value::F32(0.0),
            Scalar::F64 => Value::F64(0.0),
            Scalar::Int(k) => int_value(k, 0),
            Scalar::Bool => Value::Bool(false),
            Scalar::Char => Value::Char('\0'),
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

    /// The little-endian bytes of `v` (of this type), as C holds it.
    fn bytes(self, v: &Value, out: &mut Vec<u8>) {
        match (self, v) {
            (Scalar::F32, Value::F32(x)) => out.extend(x.to_le_bytes()),
            (Scalar::F64, Value::F64(x)) => out.extend(x.to_le_bytes()),
            (Scalar::Bool, Value::Bool(b)) => out.push(*b as u8),
            (Scalar::Char, Value::Char(c)) => out.extend((*c as u32).to_le_bytes()),
            (Scalar::Int(k), v) => {
                let n = v.to_i128().expect("an integer value");
                out.extend(&n.to_le_bytes()[..k.bits() as usize / 8]);
            }
            (s, v) => panic!("a {s:?} value expected, got {v:?}"),
        }
    }

    /// The value of `b` (`self.size()` bytes, little-endian).
    fn read(self, b: &[u8]) -> Result<Value, String> {
        let mut w = [0u8; 16];
        w[..b.len()].copy_from_slice(b);
        Ok(match self {
            Scalar::F32 => Value::F32(f32::from_le_bytes([b[0], b[1], b[2], b[3]])),
            Scalar::F64 => Value::F64(f64::from_le_bytes(w[..8].try_into().expect("8 bytes"))),
            Scalar::Bool => match b[0] {
                0 => Value::Bool(false),
                1 => Value::Bool(true),
                x => return Err(format!("a `bool` byte {x} (neither 0 nor 1)")),
            },
            Scalar::Char => {
                let u = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
                Value::Char(char::from_u32(u).ok_or_else(|| format!("a `Char` {u:#x} that is not a scalar value"))?)
            }
            Scalar::Int(k) => {
                let raw = u128::from_le_bytes(w) as i128;
                let bits = k.bits();
                // Sign-extend from the width of the kind.
                let n = if k.signed() && raw >> (bits - 1) & 1 == 1 { raw - (1i128 << bits) } else { raw };
                int_value(k, n)
            }
        })
    }
}

/// Whether two outputs are the same sample: bit for bit, NaNs equal
/// (§13.4); the ULP distance of two floats otherwise.
fn distance(a: &Value, b: &Value) -> Option<u64> {
    match (a, b) {
        (Value::F32(x), Value::F32(y)) if x.is_nan() && y.is_nan() => Some(0),
        (Value::F64(x), Value::F64(y)) if x.is_nan() && y.is_nan() => Some(0),
        (Value::F32(x), Value::F32(y)) => Some((x.to_bits() as i64 - y.to_bits() as i64).unsigned_abs()),
        (Value::F64(x), Value::F64(y)) => {
            Some(u64::try_from((x.to_bits() as i128 - y.to_bits() as i128).unsigned_abs()).unwrap_or(u64::MAX))
        }
        (a, b) => {
            let same = match (a, b) {
                (Value::Bool(x), Value::Bool(y)) => x == y,
                (Value::Char(x), Value::Char(y)) => x == y,
                _ => a.to_i128().is_some() && a.to_i128() == b.to_i128() && a.int_kind() == b.int_kind(),
            };
            if same { Some(0) } else { None }
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
    let interp = Interp::new(module);
    let fns = &meta.fns;
    let state = match interp.call(fns.init, vec![Value::Struct(shape.config_values()), Value::F32(SAMPLE_RATE)]) {
        Ok(s) => slot(s),
        Err(p) => return Ok(Run::Panicked(Panic { at: At::Init, message: p.message })),
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
        if let Err(p) = interp.call_inout(fns.process, &state, args) {
            return Ok(Run::Panicked(Panic { at: At::Block(b), message: p.message }));
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
/// from the C backend (`FlowApi`, `scalar_c`, `c_ident`); the suffixes are
/// the API of spec §11.6.
fn c_driver(api: &FlowApi, shape: &Shape, bulk_size: u32, panic: PanicMode) -> String {
    let (sym, upper) = (&api.symbol, &api.upper);
    let mut d = String::new();
    // sigaction and sigaltstack are POSIX (XSI), outside ISO C.
    let _ = writeln!(
        d,
        "#define _XOPEN_SOURCE 700\n#include \"{}\"\n#include <signal.h>\n#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n",
        api.header
    );
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
    // A fatal signal exits with a code, on its own stack (a stack overflow too).
    let _ = writeln!(
        d,
        "#ifndef ONSA_CONFORMANCE_SANITIZED\n\
         static void onsa_conformance_signal(int sig) {{ (void)sig; _Exit({}); }}\n\
         static char onsa_conformance_altstack[65536];\n\
         static int onsa_conformance_signals(void) {{\n  \
         stack_t ss;\n  memset(&ss, 0, sizeof ss);\n  ss.ss_sp = onsa_conformance_altstack;\n  \
         ss.ss_size = sizeof onsa_conformance_altstack;\n  if (sigaltstack(&ss, NULL) != 0) return 0;\n  \
         struct sigaction sa;\n  memset(&sa, 0, sizeof sa);\n  sa.sa_handler = onsa_conformance_signal;\n  \
         sigemptyset(&sa.sa_mask);\n  sa.sa_flags = SA_ONSTACK;\n  \
         const int sigs[] = {{ SIGSEGV, SIGILL, SIGFPE, SIGABRT, SIGBUS, SIGTRAP }};\n  \
         for (size_t i = 0; i < sizeof sigs / sizeof sigs[0]; i++)\n    \
         if (sigaction(sigs[i], &sa, NULL) != 0) return 0;\n  return 1;\n}}\n#endif",
        c::SIGNAL_EXIT
    );
    let _ = writeln!(d, "static int onsa_conformance_read(void* p, size_t n) {{ return fread(p, 1, n, stdin) == n; }}");
    for (i, s) in shape.inputs.iter().enumerate() {
        let _ = writeln!(d, "static {} in{i}[{}][{FRAMES}];", s.scalar.c(), s.channels());
    }
    for (o, s) in shape.outputs.iter().enumerate() {
        let _ = writeln!(d, "static {} out{o}[{}][{FRAMES}];", s.scalar.c(), s.channels());
    }
    let _ = writeln!(d, "static _Alignas({upper}_ALIGN) unsigned char mem[{upper}_SIZE];");
    if bulk_size > 0 {
        let _ = writeln!(d, "static _Alignas(16) unsigned char bulk[{upper}_BULK_SIZE];");
    }
    let _ = writeln!(d, "int main(void) {{");
    let _ = writeln!(
        d,
        "#ifndef ONSA_CONFORMANCE_SANITIZED\n  if (!onsa_conformance_signals()) return {};\n#endif",
        c::SETUP_EXIT
    );
    let _ = writeln!(d, "  {sym}_params p;\n  memset(&p, 0, sizeof p);");
    let mut cfg_args = String::new();
    for (i, (_, s)) in shape.config.iter().enumerate() {
        let _ = writeln!(
            d,
            "  {} c{i};\n  if (!onsa_conformance_read(&c{i}, sizeof c{i})) return {};",
            s.c(),
            c::INPUT_EXIT
        );
        let _ = write!(cfg_args, "c{i}, ");
    }
    for (name, _, _) in &shape.params {
        let f = onsa_backend_c::c_ident(name);
        let _ = writeln!(d, "  if (!onsa_conformance_read(&p.{f}, sizeof p.{f})) return {};", c::INPUT_EXIT);
    }
    for i in 0..shape.inputs.len() {
        let _ = writeln!(d, "  if (!onsa_conformance_read(in{i}, sizeof in{i})) return {};", c::INPUT_EXIT);
    }
    let _ = writeln!(d, "  {sym}* s = ({sym}*)mem;");
    let bulk = if bulk_size > 0 { "bulk" } else { "NULL" };
    let _ = writeln!(d, "  if ({sym}_init(s, {bulk}, {cfg_args}{SAMPLE_RATE:.1}f) != 0) return {};", c::API_ERROR_EXIT);
    let _ = writeln!(d, "  for (uint32_t b = 0; b < {}; b++) {{", FRAMES / BLOCK);
    let _ = writeln!(d, "    onsa_conformance_at = (int)b;");
    let mut args = vec!["s".to_string(), "&p".to_string()];
    for (i, s) in shape.inputs.iter().enumerate() {
        match s.planar {
            None => args.push(format!("in{i}[0] + b * {BLOCK}")),
            Some(n) => {
                let chans: Vec<String> = (0..n).map(|c| format!("in{i}[{c}] + b * {BLOCK}")).collect();
                let _ = writeln!(d, "    const {}* in{i}_ch[{n}] = {{ {} }};", s.scalar.c(), chans.join(", "));
                args.push(format!("in{i}_ch"));
            }
        }
    }
    for (o, s) in shape.outputs.iter().enumerate() {
        match s.planar {
            None => args.push(format!("out{o}[0] + b * {BLOCK}")),
            Some(n) => {
                let chans: Vec<String> = (0..n).map(|c| format!("out{o}[{c}] + b * {BLOCK}")).collect();
                let _ = writeln!(d, "    {}* out{o}_ch[{n}] = {{ {} }};", s.scalar.c(), chans.join(", "));
                args.push(format!("out{o}_ch"));
            }
        }
    }
    let _ = writeln!(d, "    if ({sym}_process({}, {BLOCK}) != 0) return {};", args.join(", "), c::API_ERROR_EXIT);
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
    c::write_files(&dir, &out.files)?;
    let source = &out.files.last().ok_or("the build wrote no file")?.0;
    let d = dir.join("driver.c");
    std::fs::write(&d, c_driver(api, shape, meta.layout.bulk_size, out.settings.panic)).map_err(|e| e.to_string())?;
    let exe = dir.join("run");
    let mut cmd = c::command(t, &out.settings.platform.cflags, &dir);
    cmd.arg("-DONSA_PANIC_HANDLER=onsa_conformance_panic");
    if t.runner == Runner::Sanitized {
        cmd.arg("-DONSA_CONFORMANCE_SANITIZED");
    }
    cmd.arg(dir.join(source)).arg(&d).arg("-o").arg(&exe).arg("-lm");
    c::compile(&mut cmd, &format!("{} (the conformance program)", t.cc))?;
    Ok(exe)
}

/// Run the program with `input` on stdin, within [`TIMEOUT`].
fn c_exec(exe: &Path, t: &Toolchain, input: Vec<u8>, shape: &Shape) -> Result<Run, String> {
    let mut cmd = match t.runner {
        Runner::Rosetta => {
            let mut c = Command::new("arch");
            c.arg("-x86_64").arg(exe);
            c
        }
        _ => Command::new(exe),
    };
    if t.runner == Runner::Sanitized {
        cmd.envs(c::sanitizer_env());
    }
    let mut child = cmd
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run {}: {e}", exe.display()))?;
    let mut stdin = child.stdin.take().expect("piped stdin");
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let mut stdout = child.stdout.take().expect("piped stdout");
    let reader = std::thread::spawn(move || {
        let mut b = Vec::new();
        stdout.read_to_end(&mut b).map(|_| b)
    });
    let mut stderr = child.stderr.take().expect("piped stderr");
    let err_reader = std::thread::spawn(move || {
        let mut b = Vec::new();
        let _ = stderr.read_to_end(&mut b);
        b
    });
    let start = Instant::now();
    let status = loop {
        if let Some(s) = child.try_wait().map_err(|e| e.to_string())? {
            break s;
        }
        if start.elapsed() > TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!("the program ran longer than {}s", TIMEOUT.as_secs()));
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let _ = writer.join();
    let bytes = reader.join().map_err(|_| "the reader of stdout failed")?.map_err(|e| e.to_string())?;
    let err = String::from_utf8_lossy(&err_reader.join().unwrap_or_default()).trim_end().to_string();
    match status.code() {
        Some(0) => {}
        Some(c::PANIC_EXIT) => return Ok(Run::Panicked(c_panic(&err)?)),
        Some(code) => {
            let what = match code {
                c::API_ERROR_EXIT => "`init` or `process` returned an error".to_string(),
                c::INPUT_EXIT => "the program could not read its input".to_string(),
                c::SETUP_EXIT => "the program could not install its signal handlers".to_string(),
                c::SIGNAL_EXIT => "a fatal signal (caught)".to_string(),
                c::SANITIZER_EXIT => "a sanitizer (ASan or UBSan) reported an error".to_string(),
                _ => format!("exit {code}"),
            };
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
/// `dir` is a scratch directory.
pub fn run(out: &BuildOutput, t: &Toolchain, dir: &Path) -> Outcome {
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
                match distance(x, y) {
                    Some(0) => {}
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
            ("3e10 is out of range for I32", "float out of range for the integer type"),
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
