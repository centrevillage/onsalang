//! Each row judged by what its calls gave ([`judge`], spec §13.4 through
//! [`crate::scalar::same`]), and the rows of an operation made one case of
//! the item ([`op_result`]).

use std::collections::BTreeMap;
use std::fmt::Write as _;

use onsa_interp::Value;

use super::bind::{RowPlan, Shape};
use super::data::{Data, Row, Want};
use crate::ccheck::{CaseResult, FailureKind};
use crate::scalar::{same, show};

/// The failing rows the report shows per case.
const SHOWN: usize = 3;

/// What one call gave.
#[derive(Debug, Clone)]
pub enum Got {
    Value(Value),
    /// It panicked (spec §9.2): the message, or the status of the C boundary.
    Panic(String),
    /// An internal error of the compiler (S-67).
    Internal(String),
    /// The C program ended inside the call (a signal, a sanitizer, the time budget).
    Ended(String),
    /// The C boundary contradicts itself (the panic handler and the status).
    Boundary(String),
    /// Not made: an earlier row of the same operation ended the program.
    NotRun,
}

impl Got {
    fn show(&self) -> String {
        match self {
            Got::Value(v) => show(v),
            Got::Panic(m) => format!("panic ({m})"),
            Got::Internal(m) => format!("internal error: {m}"),
            Got::Ended(m) => format!("the program ended: {m}"),
            Got::Boundary(m) => format!("the boundary: {m}"),
            Got::NotRun => "not run".into(),
        }
    }
}

/// The verdict of a row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    Pass,
    /// What it got; whether that is an internal error.
    Fail {
        got: String,
        internal: bool,
    },
    /// The row was not made (the program ended in an earlier row of its operation).
    NotRun,
}

/// Judge a row by what its calls gave: one call for [`Shape::Plain`]; for
/// [`Shape::Opt`], `<fn>_some`, then `<fn>_val` only when it gave `true`.
pub fn judge(p: &RowPlan, gots: &[Got]) -> Verdict {
    let fail = |got: String| Verdict::Fail { got, internal: false };
    if let Some(Got::Internal(m)) = gots.iter().find(|g| matches!(g, Got::Internal(_))) {
        return Verdict::Fail { got: format!("internal error: {m}"), internal: true };
    }
    // Before a call not made: the row whose call ended the program fails.
    if let Some(g) = gots.iter().find(|g| matches!(g, Got::Ended(_) | Got::Boundary(_))) {
        return fail(g.show());
    }
    if gots.iter().any(|g| matches!(g, Got::NotRun)) {
        return Verdict::NotRun;
    }
    if matches!(p.want, Want::Held) {
        return Verdict::Pass;
    }
    let panicked = gots.iter().find(|g| matches!(g, Got::Panic(_)));
    match (&p.want, panicked) {
        (Want::Panic, Some(_)) => return Verdict::Pass,
        (Want::Panic, None) => return fail(gots.last().map_or_else(String::new, Got::show)),
        (_, Some(g)) => return fail(g.show()),
        _ => {}
    }
    match (&p.want, p.shape, gots) {
        (Want::Value(w), Shape::Plain(_), [Got::Value(v)]) => {
            if same(v, w) {
                Verdict::Pass
            } else {
                fail(show(v))
            }
        }
        (Want::None, Shape::Opt { .. }, [Got::Value(Value::Bool(false))]) => Verdict::Pass,
        (Want::None, Shape::Opt { .. }, [Got::Value(Value::Bool(true)), Got::Value(v)]) => {
            fail(format!("some:{}", show(v)))
        }
        (Want::Some(_), Shape::Opt { .. }, [Got::Value(Value::Bool(false))]) => fail("none".into()),
        (Want::Some(w), Shape::Opt { .. }, [Got::Value(Value::Bool(true)), Got::Value(v)]) => {
            if same(v, w) {
                Verdict::Pass
            } else {
                fail(format!("some:{}", show(v)))
            }
        }
        _ => fail(format!("the calls gave {}", gots.iter().map(Got::show).collect::<Vec<_>>().join(", "))),
    }
}

/// The run of one operation by one implementation (and toolchain).
#[derive(Debug, Clone, Default)]
pub struct OpRun {
    /// Rows compared (not `held-*`).
    pub compared: usize,
    /// `held-*` rows run.
    pub held: usize,
    /// Rows not made (their indices): the program ended in an earlier row.
    pub not_run: Vec<usize>,
    /// Why the program ended (the first time), when rows were not made.
    pub ended: Option<String>,
    /// The failing rows: `(row index, what it got)`.
    pub failed: Vec<(usize, String)>,
    pub internal: usize,
}

/// Judge the rows `plans` (`gots[i]`: what the calls of `plans[i]` gave)
/// into one [`OpRun`] per operation.
pub fn op_runs(plans: &[RowPlan], gots: &[Vec<Got>]) -> BTreeMap<usize, OpRun> {
    let mut out: BTreeMap<usize, OpRun> = BTreeMap::new();
    for (p, g) in plans.iter().zip(gots) {
        let r = out.entry(p.op).or_default();
        let ended = g.iter().find_map(|x| if let Got::Ended(m) = x { Some(m.clone()) } else { None });
        if r.ended.is_none() {
            r.ended = ended;
        }
        match judge(p, g) {
            Verdict::NotRun => r.not_run.push(p.row),
            v => {
                if matches!(p.want, Want::Held) {
                    r.held += 1;
                } else {
                    r.compared += 1;
                }
                if let Verdict::Fail { got, internal } = v {
                    r.internal += usize::from(internal);
                    r.failed.push((p.row, got));
                }
            }
        }
    }
    out
}

/// The case of an operation's run: `id` is `<op>` or `<op>[<toolchain>]`.
/// Its count of failing rows ([`CaseResult::rows`]) takes the rows not made
/// too: an entry holds exactly that many.
pub fn op_result(data: &Data, id: String, run: &OpRun, args_of: &dyn Fn(usize) -> String) -> CaseResult {
    let mut r = CaseResult { id, ..Default::default() };
    if run.compared + run.held + run.not_run.len() == 0 {
        r.problems.push("no row ran (nothing compared)".into());
        return r;
    }
    let failing = run.failed.len() + run.not_run.len();
    let mut ids: Vec<String> = run
        .failed
        .iter()
        .map(|(row, _)| *row)
        .chain(run.not_run.iter().copied())
        .map(|row| data.rows[row].id(&data.ops))
        .collect();
    ids.sort();
    r.rows = Some(failing);
    r.digest = Some(digest(&ids));
    r.failing = ids;
    if failing == 0 {
        return r;
    }
    r.failure = match (run.internal, failing - run.internal) {
        (0, _) => FailureKind::Ordinary,
        (_, 0) => FailureKind::Internal,
        _ => FailureKind::Mixed,
    };
    let mut s = format!("{failing} rows fail of {}", run.compared + run.held + run.not_run.len());
    if run.held > 0 {
        let _ = write!(s, " ({} held rows run)", run.held);
    }
    if !run.not_run.is_empty() {
        let why = run.ended.as_deref().unwrap_or("?");
        let _ = write!(s, "; {} of them not run: the program ended in an earlier row ({why})", run.not_run.len());
    }
    for (row, got) in run.failed.iter().take(SHOWN) {
        let w: &Row = &data.rows[*row];
        let op = &data.ops[w.op];
        let _ = write!(s, "\n{}  {}({})  expected {}  got {got}", w.at(), op.id, args_of(*row), w.expect.text());
    }
    if run.failed.len() > SHOWN {
        let _ = write!(s, "\n... {} more rows", run.failed.len() - SHOWN);
    }
    if let Some((row, _)) = run.failed.first() {
        let _ =
            write!(s, "\nexplain: python3 -B tools/vectors/gen.py --explain {}/{}", super::DIR, data.rows[*row].at());
    }
    r.problems.push(s);
    r
}

/// The digest of the failing rows `ids` (sorted [`Row::id`]s): which rows
/// fail, so that an entry holds those rows and no others (W2-02/b). FNV-1a
/// over the ids joined by `\n`, 64 bits in 16 lowercase hex digits.
pub fn digest(ids: &[String]) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for (i, id) in ids.iter().enumerate() {
        if i > 0 {
            h = (h ^ u64::from(b'\n')).wrapping_mul(0x0000_0100_0000_01b3);
        }
        for b in id.bytes() {
            h = (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    format!("{h:016x}")
}

/// The arguments of a row for messages: the data's text, and the value of a float.
pub fn show_args(p: &RowPlan, row: &Row) -> String {
    p.args
        .iter()
        .zip(&row.args)
        .map(|(v, t)| match v {
            Value::F32(_) | Value::F64(_) => show(v),
            _ => t.clone(),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// The cases of the bound operations `ops` from their runs, `id` naming each.
pub fn cases(
    data: &Data,
    plans: &[RowPlan],
    gots: &[Vec<Got>],
    ops: impl Iterator<Item = usize>,
    id: &dyn Fn(usize) -> String,
) -> (Vec<CaseResult>, (usize, usize, usize)) {
    let runs = op_runs(plans, gots);
    let by_row: BTreeMap<usize, &RowPlan> = plans.iter().map(|p| (p.row, p)).collect();
    let args = |row: usize| by_row.get(&row).map_or_else(String::new, |p| show_args(p, &data.rows[row]));
    let mut counts = (0, 0, 0);
    let mut out = Vec::new();
    for op in ops {
        let r = runs.get(&op).cloned().unwrap_or_default();
        counts.0 += 1;
        counts.1 += r.compared;
        counts.2 += r.held;
        out.push(op_result(data, id(op), &r, &args));
    }
    (out, counts)
}
