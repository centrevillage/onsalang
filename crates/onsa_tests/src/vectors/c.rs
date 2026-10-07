//! The generated C against the vectors (gate item `vectors-c`).
//!
//! The fixture is built for its one target with `platform = "host"` and
//! `panic = "poison"` (`panic = "trap"` code never runs here). For each C
//! toolchain of the checks ([`toolchains`]: the compile-and-run rows of
//! [`crate::c::ITEMS`], once per distinct compile), one program makes the
//! calls of a row by the row's operation number: it reads `u32 operation,
//! the arguments` from the standard input and writes, per call (unbuffered,
//! so a run that ends keeps what came before),
//!
//! ```text
//! i32 status    (0 / 1: the boundary's report of a panic, through crate::capi)
//! u8  handler   (1: the panic handler ran during the call)
//! the result
//! ```
//!
//! one call for an operation of one function; for `Option`, `<fn>_some`, then
//! `<fn>_val` only when `_some` returned `true` with status 0 (FORMAT.md). It
//! writes `u32 0xFFFFFFFF` at the end. A call whose status and handler
//! disagree fails ([`Got::Boundary`]).
//!
//! The C is compiled with `-w` ([`crate::c::compile_driver`]): the warnings
//! are the C checks' (the fixture is one of their cases). A run that ends
//! inside a row (a fatal signal, which the driver turns into an exit code; a
//! sanitizer, which exits; the time budget, SIGKILL) fails that row; the
//! operation's later rows are not made (they count among its failing rows),
//! and the program starts again at the next operation.
//!
//! The form of a call is [`crate::capi::call_fn`]'s: when the API of an
//! exported function changes (W10-03), that is what changes.

use std::fmt::Write as _;
use std::path::Path;
use std::time::{Duration, Instant};

use onsa_backend_c::{FnApi, PanicMode};
use onsa_driver::{BuildError, BuildOutput, Loaded, TargetSettings};

use super::bind::{Bound, Callee, Shape, bind, plan};
use super::data::Data;
use super::item::{BuildFailure, VectorsRun, load_fixture, package_failure, package_path};
use super::judge::{Got, cases};
use crate::c::{self, Check, DriverKind, Finished, Item, Runner};
use crate::capi;
use crate::pending::Pending;
use crate::scalar::Scalar;

/// How long the runs of one toolchain over one package may take, restarts included.
pub const BUDGET: Duration = Duration::from_secs(300);
/// The panic handler the program defines (`ONSA_PANIC_HANDLER`): it only marks the call.
pub const PANIC_HANDLER: &str = "onsa_vec_panic";
/// The end of the records.
pub const END: u32 = u32::MAX;
/// The bytes of a record before the result.
const HEAD: usize = 5;

/// The toolchains: every compile-and-run row of the C checks, once per
/// distinct compile (with `-w`, the warnings a row switches off do not make
/// another program: `c-gcc-strict` is `c-gcc`'s).
pub fn toolchains() -> Vec<&'static Item> {
    let mut out: Vec<&'static Item> = Vec::new();
    for i in c::ITEMS {
        let Check::Unit(t) = i.check else { continue };
        let same =
            |o: &&Item| matches!(o.check, Check::Unit(u) if u.cc == t.cc && u.flags == t.flags && u.runner == t.runner);
        if !out.iter().any(same) {
            out.push(i);
        }
    }
    out
}

/// What one call of the program gave.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Raw {
    Returned {
        status: i32,
        handler: bool,
        bytes: Vec<u8>,
    },
    /// The program ended inside the call.
    Ended(String),
    /// Not made (an earlier row of the operation ended the program).
    NotRun,
}

/// The call as the vectors judge it.
pub fn got(raw: &Raw, ret: Scalar) -> Got {
    match raw {
        Raw::Returned { status: 0, handler: false, bytes } => match ret.read(bytes) {
            Ok(v) => Got::Value(v),
            Err(e) => Got::Boundary(format!("the result {bytes:02x?}: {e}")),
        },
        Raw::Returned { status: 1, handler: true, .. } => Got::Panic("status 1".into()),
        Raw::Returned { status, handler, .. } => Got::Boundary(format!(
            "status {status}, and the panic handler {}",
            if *handler { "ran" } else { "did not run" }
        )),
        Raw::Ended(m) => Got::Ended(m.clone()),
        Raw::NotRun => Got::NotRun,
    }
}

/// The records a row writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowRecords {
    /// One call: the size of its result.
    Plain(usize),
    /// `_some` (a `Bool`), then `_val` (the size of its result) when `_some`
    /// returned `true` with status 0.
    Opt(usize),
}

/// The target of the fixture the vectors run on.
pub fn host_target(loaded: &Loaded) -> Result<String, String> {
    let m = loaded.manifest.as_ref().ok_or("no onsa.toml")?;
    let mut names: Vec<&String> = m
        .targets
        .iter()
        .filter(|(n, t)| {
            TargetSettings::from_manifest(n, t).is_ok_and(|s| s.platform.is_host() && s.panic == PanicMode::Poison)
        })
        .map(|(n, _)| n)
        .collect();
    names.sort();
    match names.as_slice() {
        [one] => Ok((*one).clone()),
        _ => Err(format!(
            "{} targets with `platform = \"host\"` and `panic = \"poison\"`; the vectors need exactly one",
            names.len()
        )),
    }
}

/// Run every package of the data with every toolchain.
pub fn run(root: &Path, data: &Data, list: &Pending) -> VectorsRun {
    run_with(root, data, list, &toolchains())
}

/// [`run`] with the toolchains `tools` (rows of [`crate::c::ITEMS`] that compile and run).
pub fn run_with(root: &Path, data: &Data, list: &Pending, tools: &[&'static Item]) -> VectorsRun {
    let mut out = VectorsRun::default();
    out.run.errors.extend(tools.iter().flat_map(|t| t.cannot_run()));
    if tools.is_empty() {
        out.run.errors.push("the C checks have no compile-and-run row".into());
    }
    if !out.run.errors.is_empty() {
        return out;
    }
    let scratch = c::scratch_dir("onsa_vectors_c", "");
    let mut counts: Vec<(usize, usize, usize)> = vec![(0, 0, 0); tools.len()];
    for pkg in data.packages() {
        let fixture = match load_fixture(root, pkg) {
            Ok(f) => f,
            Err(f) => {
                package_failure(&mut out, data, list, pkg, f);
                continue;
            }
        };
        let target = match host_target(&fixture.loaded) {
            Ok(t) => t,
            Err(e) => {
                out.run.errors.push(format!("{}: {e}", package_path(pkg)));
                continue;
            }
        };
        let build = match onsa_driver::build_analyzed(&fixture.loaded, &fixture.analyzed, &target) {
            Ok(b) => b,
            Err(BuildError::Usage(m)) => {
                out.run.errors.push(format!("{}: build of `{target}`: {m}", package_path(pkg)));
                continue;
            }
            Err(BuildError::Diagnostics { sources, diagnostics }) => {
                let why = format!(
                    "the build of `{target}` reports {} diagnostics:\n{}",
                    diagnostics.len(),
                    c::head(&onsa_diag::to_text(&sources, &diagnostics))
                );
                package_failure(&mut out, data, list, pkg, BuildFailure::of(why));
                continue;
            }
            Err(BuildError::Internal { sources, error }) => {
                package_failure(&mut out, data, list, pkg, BuildFailure::internal(&sources, &error));
                continue;
            }
        };
        let prepared = bind(data, pkg, &build.module, &fixture.exported)
            .and_then(|b| Ok((plan(data, &b)?, b)))
            .and_then(|(plans, b)| Ok((program(&build, &b).map_err(|e| vec![format!("{pkg}: {e}")])?, plans, b)));
        let (source, plans, bound) = match prepared {
            Ok(x) => x,
            Err(e) => {
                out.run.errors.extend(e);
                continue;
            }
        };
        // The program's number of each operation: its place among the bound ones.
        let number = |op: usize| bound.ops.keys().position(|o| *o == op).expect("a bound operation") as u32;
        let inputs: Vec<Vec<u8>> = plans
            .iter()
            .map(|p| {
                let mut b = number(p.op).to_le_bytes().to_vec();
                let params = &bound.callees[first_callee(p.shape)].params;
                for (s, v) in params.iter().zip(&p.args) {
                    s.bytes(v, &mut b);
                }
                b
            })
            .collect();
        let ops: Vec<usize> = plans.iter().map(|p| p.op).collect();
        let records: Vec<RowRecords> = plans
            .iter()
            .map(|p| match p.shape {
                Shape::Plain(f) => RowRecords::Plain(bound.callees[f].ret.size()),
                Shape::Opt { val, .. } => RowRecords::Opt(bound.callees[val].ret.size()),
            })
            .collect();
        let runs: Vec<Result<Vec<Vec<Raw>>, String>> = std::thread::scope(|s| {
            let handles: Vec<_> = tools
                .iter()
                .map(|item| {
                    let dir = scratch.join(pkg).join(item.name);
                    let (source, inputs, ops, records, build) = (&source, &inputs, &ops, &records, &build);
                    s.spawn(move || {
                        let Check::Unit(t) = item.check else { unreachable!("toolchains() keeps the units") };
                        let exe =
                            c::compile_driver(&t, build, &dir, "vectors_driver.c", source, PANIC_HANDLER, &["-w"])?;
                        run_rows(&exe, t.runner, inputs, ops, records)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_else(|_| Err("the toolchain's thread panicked".into())))
                .collect()
        });
        for (ti, (item, raws)) in tools.iter().zip(runs).enumerate() {
            let raws = match raws {
                Ok(r) => r,
                Err(e) => {
                    out.run.errors.push(format!("{} [{}]: {e}", package_path(pkg), item.name));
                    continue;
                }
            };
            let gots: Vec<Vec<Got>> = plans
                .iter()
                .zip(&raws)
                .map(|(p, rs)| {
                    let rets: Vec<Scalar> = match p.shape {
                        Shape::Plain(f) => vec![bound.callees[f].ret],
                        Shape::Opt { some, val } => vec![bound.callees[some].ret, bound.callees[val].ret],
                    };
                    rs.iter().zip(rets).map(|(r, s)| got(r, s)).collect()
                })
                .collect();
            let id = |op: usize| format!("{}[{}]", data.ops[op].id, item.name);
            let (results, (o, r, h)) = cases(data, &plans, &gots, bound.ops.keys().copied(), &id);
            out.run.results.extend(results);
            counts[ti].0 += o;
            counts[ti].1 += r;
            counts[ti].2 += h;
        }
    }
    for (item, (ops, rows, held)) in tools.iter().zip(counts) {
        out.counts.push((item.name.to_string(), ops, rows, held));
    }
    out.run.notes.extend(c::keep_or_remove(&scratch, "the files"));
    out
}

fn first_callee(s: Shape) -> usize {
    match s {
        Shape::Plain(f) => f,
        Shape::Opt { some, .. } => some,
    }
}

/// The C API of `callee`, checked against its types.
fn api_of<'a>(out: &'a BuildOutput, callee: &Callee) -> Result<&'a FnApi, String> {
    let api = out
        .unit
        .fns
        .iter()
        .find(|a| a.fn_ == callee.name)
        .ok_or_else(|| format!("`{}` is not exported in the C (`CUnit::fns`)", callee.name))?;
    if api.params.len() != callee.params.len() {
        return Err(format!("`{}`: the C takes {} arguments", callee.name, api.params.len()));
    }
    let ret = api.ret.as_deref().ok_or_else(|| format!("`{}` returns nothing in the C", callee.name))?;
    if callee.ret.c_type() != Some(ret) {
        return Err(format!("the C backend records `{ret}` for the result of `{}`", callee.name));
    }
    for (p, s) in api.params.iter().zip(&callee.params) {
        if s.c_type() != Some(p.field.c_type.as_str()) {
            return Err(format!(
                "the C backend records `{}` for `{}` of `{}`, whose type is {}",
                p.field.c_type,
                p.field.name,
                callee.name,
                s.name()
            ));
        }
    }
    Ok(api)
}

/// The program that makes the calls of the operations of `b` (numbered as
/// `b.ops` in order).
pub fn program(out: &BuildOutput, b: &Bound) -> Result<String, String> {
    let take_panic =
        out.unit.take_panic.as_deref().ok_or("the build has no `take_panic`: the vectors need `panic = \"poison\"`")?;
    let headers: Vec<&str> = out.unit.headers.iter().map(|(n, _)| n.as_str()).collect();
    let mut d = c::driver_preamble(&headers);
    let _ = writeln!(
        d,
        "static int onsa_vec_panicked = 0;\n\
         void {PANIC_HANDLER}(const char* msg, const char* file, uint32_t line) {{\n  \
         (void)msg; (void)file; (void)line; onsa_vec_panicked = 1;\n}}\n\
         static void onsa_vec_op(uint32_t k) {{\n  switch (k) {{"
    );
    // One call: its status into `st`, its result into `r`, and the record.
    let call = |callee: &Callee, args: &[capi::FnArg]| -> Result<String, String> {
        let api = api_of(out, callee)?;
        let ret = api.ret.as_deref().expect("checked");
        let c = capi::call_fn(api, Some(take_panic), args, "st", Some("r")).map_err(|e| e.0)?;
        Ok(format!(
            "{{ int st; {ret} r;\n        onsa_vec_panicked = 0;\n        {c}\n        \
             int32_t s32 = (int32_t)st; unsigned char h = (unsigned char)onsa_vec_panicked;\n        \
             onsa_driver_write(&s32, sizeof s32); onsa_driver_write(&h, 1); onsa_driver_write(&r, sizeof r);"
        ))
    };
    for (k, (op, shape)) in b.ops.iter().enumerate() {
        let first = &b.callees[first_callee(*shape)];
        let mut body = String::new();
        let mut args = Vec::new();
        for (j, s) in first.params.iter().enumerate() {
            let t = s.c_type().ok_or_else(|| format!("no C type for {}", s.name()))?;
            let _ = writeln!(body, "      {t} a{j}; onsa_driver_need(&a{j}, sizeof a{j});");
            args.push(capi::FnArg::Scalar(format!("a{j}")));
        }
        match *shape {
            Shape::Plain(f) => {
                let _ = writeln!(body, "      {} }}", call(&b.callees[f], &args)?);
            }
            Shape::Opt { some, val } => {
                // `_val` only when `_some` returned `true` (FORMAT.md).
                let _ = writeln!(
                    body,
                    "      int more = 0;\n      {}\n        more = st == 0 && r; }}\n      if (more) {} }}",
                    call(&b.callees[some], &args)?,
                    call(&b.callees[val], &args)?
                );
            }
        }
        let _ = writeln!(d, "    case {k}: {{ /* operation {op} */\n{body}    }} break;");
    }
    let _ = writeln!(
        d,
        "    default: _Exit({args});\n  }}\n}}\n\
         int main(void) {{\n  setvbuf(stdout, NULL, _IONBF, 0);\n  if (!onsa_driver_signals()) return {setup};\n  \
         uint32_t k;\n  while (fread(&k, sizeof k, 1, stdin) == 1) onsa_vec_op(k);\n  \
         if (ferror(stdin)) return {input};\n  {{ uint32_t end = {END:#x}u; onsa_driver_write(&end, sizeof end); }}\n  \
         return 0;\n}}",
        args = c::ARGS_EXIT,
        setup = c::SETUP_EXIT,
        input = c::INPUT_EXIT,
    );
    Ok(d)
}

/// The next record of `b` from `at`, of a result of `size` bytes.
fn record(b: &[u8], at: &mut usize, size: usize) -> Result<Option<Raw>, String> {
    let Some(rec) = b.get(*at..*at + HEAD + size) else { return Ok(None) };
    *at += rec.len();
    let handler = match rec[4] {
        0 => false,
        1 => true,
        x => return Err(format!("a handler byte {x}")),
    };
    Ok(Some(Raw::Returned {
        status: i32::from_le_bytes([rec[0], rec[1], rec[2], rec[3]]),
        handler,
        bytes: rec[HEAD..].to_vec(),
    }))
}

/// Make the rows `inputs` (each `u32 operation, the arguments`; `ops[i]` is
/// the operation of row `i`, `records[i]` what it writes), starting the
/// program again after a row that ends it: the calls of each row. `Err`: the
/// harness.
pub fn run_rows(
    exe: &Path,
    runner: Runner,
    inputs: &[Vec<u8>],
    ops: &[usize],
    records: &[RowRecords],
) -> Result<Vec<Vec<Raw>>, String> {
    let n = inputs.len();
    let mut out: Vec<Vec<Raw>> = Vec::with_capacity(n);
    let start = Instant::now();
    while out.len() < n {
        if start.elapsed() > BUDGET {
            return Err(format!(
                "the runs took longer than the budget of {}s ({} of {n} rows made)",
                BUDGET.as_secs(),
                out.len()
            ));
        }
        let first = out.len();
        let done = c::run_program(exe, &[], runner, inputs[first..].concat(), c::RUN_TIMEOUT)?;
        let b = &done.stdout;
        let mut at = 0;
        // The row the program was in when it ended, with the calls it made.
        let mut partial: Vec<Raw> = Vec::new();
        while out.len() < n {
            let k = out.len();
            let mut calls = Vec::new();
            let complete = match records[k] {
                RowRecords::Plain(size) => match record(b, &mut at, size).map_err(|e| format!("row {k}: {e}"))? {
                    Some(r) => {
                        calls.push(r);
                        true
                    }
                    None => false,
                },
                RowRecords::Opt(size) => match record(b, &mut at, 1).map_err(|e| format!("row {k}: {e}"))? {
                    Some(r) => {
                        let more = matches!(&r, Raw::Returned { status: 0, bytes, .. } if bytes[0] != 0);
                        calls.push(r);
                        if more {
                            match record(b, &mut at, size).map_err(|e| format!("row {k}: {e}"))? {
                                Some(v) => {
                                    calls.push(v);
                                    true
                                }
                                None => false,
                            }
                        } else {
                            true
                        }
                    }
                    None => false,
                },
            };
            if !complete {
                partial = calls;
                break;
            }
            out.push(calls);
        }
        let rest = &b[at.min(b.len())..];
        if out.len() == n {
            let clean = done.status.is_some_and(|s| s.success());
            if !clean || rest != END.to_le_bytes() {
                return Err(format!(
                    "the program made every row but did not end well ({}; {} bytes after the records){}",
                    done.status.map_or_else(|| "killed".to_string(), |s| s.to_string()),
                    rest.len(),
                    stderr_line(&done)
                ));
            }
            break;
        }
        // The program ended inside row `k`: that row fails, the operation's later rows are not made.
        let k = out.len();
        partial.push(Raw::Ended(ended(&done)?));
        out.push(partial);
        while out.len() < n && ops[out.len()] == ops[k] {
            out.push(vec![Raw::NotRun]);
        }
    }
    Ok(out)
}

/// Why the program ended inside a row; `Err` when that is the harness's.
fn ended(done: &Finished) -> Result<String, String> {
    let err = stderr_line(done);
    let Some(status) = done.status else {
        return Ok(format!("the time budget: it ran longer than {}s and was killed{err}", c::RUN_TIMEOUT.as_secs()));
    };
    let meaning = |code: i32| c::exit_meaning(DriverKind::Vectors, code);
    match status.code() {
        Some(0) => Err(format!("the program ended well before its last row{err}")),
        Some(code @ (c::INPUT_EXIT | c::OUTPUT_EXIT | c::SETUP_EXIT | c::ARGS_EXIT)) => {
            Err(format!("the program failed: {} (exit {code}){err}", meaning(code).unwrap_or("?")))
        }
        Some(code) => Ok(meaning(code).map_or_else(|| format!("exit {code}"), |m| format!("{m} (exit {code})")) + &err),
        None => Ok(format!("it ended by a signal ({status}){err}")),
    }
}

/// The line of the program's standard error that says the most (a
/// sanitizer's report), for messages.
fn stderr_line(done: &Finished) -> String {
    let lines: Vec<&str> = done.stderr.lines().collect();
    let line = lines
        .iter()
        .find(|l| l.contains("runtime error") || l.contains("ERROR:"))
        .or_else(|| lines.first())
        .map(|l| l.trim());
    match line {
        Some(l) if !l.is_empty() => {
            let l: String = l.chars().take(300).collect();
            format!(": {l}")
        }
        _ => String::new(),
    }
}
