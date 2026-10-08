//! The interpreter against the vectors (gate item `vectors-interp`).
//!
//! The Core it runs is `lower_core`'s, `onsa test`'s path (independent of a
//! target). Each call is guarded ([`onsa_driver::guard`]): a failure of the
//! interpreter itself (its own report of a state it cannot be in, R-137, or
//! a panic of the host) is an internal error of the compiler (S-67), never
//! the program's panic ([`Failure::Panic`]). The whole run is on its own
//! thread with the stack of a command ([`onsa_diag::stack`]) and a time
//! budget ([`BUDGET`]).

use std::path::Path;
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use onsa_core::FnId;
use onsa_interp::{Failure, Interp, Value};

use super::bind::{Callee, Shape, bind, plan};
use super::data::Data;
use super::item::{VectorsRun, load_fixture, lower_fixture, package_failure};
use super::judge::{Got, cases};
use crate::ccheck::ItemRun;
use crate::pending::Pending;

/// How long the item may run.
pub const BUDGET: Duration = Duration::from_secs(120);

/// Run every package of the data in the interpreter.
pub fn run(root: &Path, data: &Data, list: &Pending) -> VectorsRun {
    let (tx, rx) = mpsc::channel();
    let at = Arc::new(Mutex::new(String::from("(loading)")));
    let (root2, data2, list2, at2) = (root.to_path_buf(), data.clone(), list.clone(), at.clone());
    let spawned = onsa_diag::stack::spawn("vectors-interp", move || {
        let _ = tx.send(run_all(&root2, &data2, &list2, &at2));
    });
    let error = |m: String| VectorsRun { run: ItemRun { errors: vec![m], ..Default::default() }, ..Default::default() };
    if let Err(e) = spawned {
        return error(format!("cannot start the interpreter's thread: {e}"));
    }
    let at = || at.lock().map_or_else(|_| "?".to_string(), |a| a.clone());
    match rx.recv_timeout(BUDGET) {
        Ok(v) => v,
        // The thread is left behind; the process ends with the item.
        Err(RecvTimeoutError::Timeout) => {
            error(format!("the interpreter ran longer than the budget of {}s (at `{}`)", BUDGET.as_secs(), at()))
        }
        Err(RecvTimeoutError::Disconnected) => {
            error(format!("the interpreter's thread ended without a result (at `{}`)", at()))
        }
    }
}

fn run_all(root: &Path, data: &Data, list: &Pending, at: &Mutex<String>) -> VectorsRun {
    let mut out = VectorsRun::default();
    let (mut ops, mut rows, mut held) = (0, 0, 0);
    for pkg in data.packages() {
        let (module, exported) = match load_fixture(root, pkg).and_then(|f| Ok((lower_fixture(&f)?, f.exported))) {
            Ok(m) => m,
            Err(f) => {
                package_failure(&mut out, data, list, pkg, f);
                continue;
            }
        };
        let bound = match bind(data, pkg, &module, &exported) {
            Ok(b) => b,
            Err(e) => {
                out.run.errors.extend(e);
                continue;
            }
        };
        let plans = match plan(data, &bound) {
            Ok(p) => p,
            Err(e) => {
                out.run.errors.extend(e);
                continue;
            }
        };
        // A fixture the interpreter cannot run is an error of the item (E0200,
        // S-224), found before any call, as `onsa test` finds it.
        let unsupported = onsa_interp::unsupported(&module);
        if !unsupported.is_empty() {
            out.run.errors.extend(unsupported.iter().map(|u| {
                let d = u.diagnostic();
                format!("{pkg}: {}: {}", d.code.as_str(), d.message)
            }));
            continue;
        }
        let interp = Interp::new(&module);
        let Some(ids) = bound.callees.iter().map(|c| interp.fn_by_name(&c.name)).collect::<Option<Vec<FnId>>>() else {
            out.run.errors.push(format!("{pkg}: the interpreter does not find an exported function"));
            continue;
        };
        let mut gots = Vec::with_capacity(plans.len());
        let mut current = usize::MAX;
        for p in &plans {
            if p.op != current {
                current = p.op;
                if let Ok(mut a) = at.lock() {
                    *a = data.ops[p.op].id.clone();
                }
            }
            let make = |k: usize| call(&interp, ids[k], &bound.callees[k], p.args.clone());
            gots.push(match p.shape {
                Shape::Plain(f) => vec![make(f)],
                // `_val` only when `_some` gives `true` (FORMAT.md).
                Shape::Opt { some, val } => match make(some) {
                    g @ Got::Value(onsa_interp::Value::Bool(true)) => vec![g, make(val)],
                    g => vec![g],
                },
            });
        }
        let (results, (o, r, h)) = cases(data, &plans, &gots, bound.ops.keys().copied(), &|op| data.ops[op].id.clone());
        out.run.results.extend(results);
        ops += o;
        rows += r;
        held += h;
    }
    out.counts.push(("interpreter".into(), ops, rows, held));
    out
}

/// One call, classified.
fn call(interp: &Interp<'_>, f: FnId, callee: &Callee, args: Vec<Value>) -> Got {
    match onsa_driver::guard(|| interp.call(f, args)) {
        Err(e) => Got::Internal(match &e.origin {
            onsa_driver::Origin::Panic { location: Some(l) } => format!("{} (at {l})", e.message),
            _ => e.message,
        }),
        Ok(Err(Failure::Panic(p))) => Got::Panic(p.message),
        // `run_all` found every one before the calls.
        Ok(Err(Failure::Unsupported(u))) => Got::Internal(format!(
            "the interpreter reached `{}`, which the check before the calls did not find",
            u.std_fn
        )),
        Ok(Ok(v)) if callee.ret.holds(&v) => Got::Value(v),
        Ok(Ok(v)) => Got::Internal(format!("`{}` returned {v:?}, not a {}", callee.name, callee.ret.name())),
    }
}
