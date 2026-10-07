//! The operations of a package bound to the functions its build exports
//! ([`bind`]), and its rows made calls ([`plan`]).

use std::collections::{BTreeMap, BTreeSet};

use onsa_core::Module;
use onsa_interp::Value;

use super::data::{Data, Want, typed};
use super::{REGISTRY, SOME, VAL};
use crate::scalar::Scalar;

/// A function of the fixture an operation calls.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Callee {
    /// The exported name (`ops.i32_add`).
    pub name: String,
    pub params: Vec<Scalar>,
    pub ret: Scalar,
}

/// How an operation is called.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    /// One function: its index in [`Bound::callees`].
    Plain(usize),
    /// `Option`: `<fn>_some` (`Bool`), and `<fn>_val` only when it gives `true` (FORMAT.md).
    Opt { some: usize, val: usize },
}

/// The operations of a package bound to the functions of its build.
#[derive(Debug, Clone, Default)]
pub struct Bound {
    pub callees: Vec<Callee>,
    /// By the operation's index in [`Data::ops`].
    pub ops: BTreeMap<usize, Shape>,
}

/// Bind the operations of package `pkg` to the functions `exported` (the
/// manifest's `[export] fns`) of `module`, checked against the types of
/// `OPS.tsv`. The errors are of the data or the fixture (they disagree):
/// never pending.
pub fn bind(data: &Data, pkg: &str, module: &Module, exported: &[String]) -> Result<Bound, Vec<String>> {
    let mut errors = Vec::new();
    let mut by_short: BTreeMap<&str, &str> = BTreeMap::new();
    for q in exported {
        let short = q.rsplit_once('.').map_or(q.as_str(), |(_, s)| s);
        if by_short.insert(short, q).is_some() {
            errors.push(format!("{pkg}: two exported functions are named `{short}`"));
        }
    }
    let mut b = Bound::default();
    let mut used = BTreeSet::new();
    let mut callee = |b: &mut Bound, short: &str, errors: &mut Vec<String>| -> Option<usize> {
        let q = *by_short.get(short)?;
        used.insert(short.to_string());
        if let Some(i) = b.callees.iter().position(|c| c.name == q) {
            return Some(i);
        }
        let Some(f) = module.fns.iter().find(|f| f.name == q) else {
            errors.push(format!("{pkg}: `{q}` is exported but not in the build"));
            return None;
        };
        let ty = |t: &onsa_core::Ty| {
            Scalar::of(t).ok_or_else(|| format!("{pkg}: `{q}` has a type that is not a scalar of the boundary"))
        };
        let params: Result<Vec<Scalar>, String> = f.params.iter().map(|p| ty(&p.ty)).collect();
        match (params, ty(&f.ret)) {
            (Ok(params), Ok(ret)) => {
                b.callees.push(Callee { name: q.to_string(), params, ret });
                Some(b.callees.len() - 1)
            }
            (Err(e), _) | (_, Err(e)) => {
                errors.push(e);
                None
            }
        }
    };
    for (i, o) in data.ops.iter().enumerate().filter(|(_, o)| o.pkg == pkg) {
        let t = data.types_of(i);
        let (some, val) = (format!("{}{SOME}", o.fn_), format!("{}{VAL}", o.fn_));
        let shape = if t.option {
            match (callee(&mut b, &some, &mut errors), callee(&mut b, &val, &mut errors)) {
                (Some(some), Some(val)) => Shape::Opt { some, val },
                _ => {
                    errors.push(format!(
                        "{pkg}: `{}` returns {}: the fixture exports no `{some}` and `{val}`",
                        o.id, o.ret
                    ));
                    continue;
                }
            }
        } else {
            match callee(&mut b, &o.fn_, &mut errors) {
                Some(f) => Shape::Plain(f),
                None => {
                    errors.push(format!("{pkg}: `{}`: the fixture exports no `{}`", o.id, o.fn_));
                    continue;
                }
            }
        };
        let (params, ret) = match shape {
            Shape::Plain(f) => (b.callees[f].params.clone(), b.callees[f].ret),
            Shape::Opt { some, val } => {
                let (s, v) = (&b.callees[some], &b.callees[val]);
                if s.ret != Scalar::Bool || s.params != v.params {
                    errors.push(format!("{pkg}: `{}`: `{}` is not the `Bool` of `{}`", o.id, s.name, v.name));
                }
                (v.params.clone(), v.ret)
            }
        };
        if params != t.args || ret != t.ret {
            let names = |ps: &[Scalar]| ps.iter().map(|s| s.name()).collect::<Vec<_>>().join(", ");
            errors.push(format!(
                "{pkg}: `{}` is ({}) -> {} in the build, ({}) -> {} in {REGISTRY}",
                o.id,
                names(&params),
                ret.name(),
                names(t.args),
                o.ret
            ));
        }
        b.ops.insert(i, shape);
    }
    for short in by_short.keys() {
        if !used.contains(*short) {
            errors.push(format!("{pkg}: the exported function `{short}` is no operation's ({REGISTRY})"));
        }
    }
    if errors.is_empty() { Ok(b) } else { Err(errors) }
}

/// A row ready to call: the arguments and what it wants.
#[derive(Debug, Clone)]
pub struct RowPlan {
    /// Index into [`Data::rows`].
    pub row: usize,
    pub op: usize,
    pub shape: Shape,
    pub args: Vec<Value>,
    pub want: Want,
}

/// The rows of the bound operations, grouped by operation (in the order of
/// the registry, then of the rows).
pub fn plan(data: &Data, b: &Bound) -> Result<Vec<RowPlan>, Vec<String>> {
    let mut errors = Vec::new();
    let mut plans = Vec::new();
    let mut rows: Vec<(usize, &super::data::Row)> =
        data.rows.iter().enumerate().filter(|(_, r)| b.ops.contains_key(&r.op)).collect();
    rows.sort_by_key(|(i, r)| (r.op, *i));
    for (i, r) in rows {
        // Checked when the data was read ([`Data::parse`]); the same function.
        match typed(&data.ops[r.op], data.types_of(r.op), r) {
            Ok((args, want)) => plans.push(RowPlan { row: i, op: r.op, shape: b.ops[&r.op], args, want }),
            Err(e) => errors.push(format!("{}/{}: {e}", super::DIR, r.at())),
        }
    }
    if errors.is_empty() { Ok(plans) } else { Err(errors) }
}
