//! The reader of the data (`tests/vectors/FORMAT.md`): the registry
//! `OPS.tsv` and the rows of its data files, read strictly. Every row is
//! typed here ([`typed`]), whether its operation runs or not: the arguments
//! and the expectation by the types `OPS.tsv` writes ([`OpTypes`], through
//! [`Scalar::from_name`]). Rust holds no table of the operations (D-15).

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use onsa_interp::Value;
use onsa_interp::value::int_value;

use super::{DIR, FORMAT, MANIFEST, NO_ARGS, REGISTRY};
use crate::scalar::Scalar;

/// The columns of `OPS.tsv` (`FORMAT.md`).
const REGISTRY_COLUMNS: usize = 9;

/// An operation of the registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Op {
    /// `i32.add`.
    pub id: String,
    /// The fixture's function (`i32_add`; `<fn>_some` / `<fn>_val` for `Option`).
    pub fn_: String,
    /// The data file (`int-i32.tsv`).
    pub file: String,
    /// The fixture package (`scalar`).
    pub pkg: String,
    /// The Onsa types of the arguments, as written.
    pub args: Vec<String>,
    /// The Onsa type of the result, as written.
    pub ret: String,
}

/// The types of an operation, as `OPS.tsv` writes them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpTypes<'a> {
    pub args: &'a [Scalar],
    /// The value (of `Option` when `option`).
    pub ret: Scalar,
    /// The result is `<X>[<ret>]` (`Option`, `FORMAT.md`): the pair `<fn>_some` / `<fn>_val`.
    pub option: bool,
}

/// The types of `op`: the arguments, and the result (`T` or `<X>[T]`).
pub fn op_types(op: &Op) -> Result<(Vec<Scalar>, Scalar, bool), String> {
    let ty = |t: &str| Scalar::from_name(t).ok_or_else(|| format!("`{}`: `{t}` is not a scalar type", op.id));
    let args = op.args.iter().map(|a| ty(a)).collect::<Result<Vec<_>, _>>()?;
    match op.ret.strip_suffix(']').and_then(|r| r.split_once('[')) {
        Some((outer, inner)) if !outer.is_empty() && !outer.contains(['[', ']']) => Ok((args, ty(inner)?, true)),
        _ => Ok((args, ty(&op.ret)?, false)),
    }
}

/// What a row expects (`FORMAT.md`), as written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expect {
    Value(String),
    /// Any NaN.
    Nan,
    /// The call panics (the kind is for the reader).
    Panic(String),
    Some(String),
    None,
    /// A row of a `held-*` section: no expectation.
    Held,
}

impl Expect {
    fn parse(s: &str) -> Result<Expect, String> {
        Ok(match s {
            "?" => Expect::Held,
            "nan" => Expect::Nan,
            "none" => Expect::None,
            _ => {
                if let Some(k) = s.strip_prefix("panic:") {
                    if k.is_empty() || k.contains(char::is_whitespace) {
                        return Err(format!("a panic without its kind: `{s}`"));
                    }
                    Expect::Panic(k.to_string())
                } else if let Some(v) = s.strip_prefix("some:") {
                    Expect::Some(v.to_string())
                } else if s.is_empty() || s.contains(char::is_whitespace) {
                    return Err(format!("an expectation `{s}` of no form"));
                } else {
                    Expect::Value(s.to_string())
                }
            }
        })
    }

    /// As the data writes it.
    pub fn text(&self) -> String {
        match self {
            Expect::Value(v) => v.clone(),
            Expect::Nan => "nan".into(),
            Expect::Panic(k) => format!("panic:{k}"),
            Expect::Some(v) => format!("some:{v}"),
            Expect::None => "none".into(),
            Expect::Held => "?".into(),
        }
    }
}

/// A row of a data file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    /// Index into [`Data::ops`].
    pub op: usize,
    pub file: String,
    /// 1-based.
    pub line: usize,
    /// The stage of its section (`edge`, `rand`, `held-S207`).
    pub stage: String,
    pub args: Vec<String>,
    pub expect: Expect,
}

impl Row {
    /// `int-i32.tsv:300`.
    pub fn at(&self) -> String {
        format!("{}:{}", self.file, self.line)
    }

    /// What names the row in the list (`digest`, [`super::judge::digest`]):
    /// its file, its section and its arguments as written. Not its line,
    /// which moves when the data is made again.
    pub fn id(&self, ops: &[Op]) -> String {
        let args = if self.args.is_empty() { NO_ARGS.to_string() } else { self.args.join(" ") };
        format!("{} @ {} {} : {args}", self.file, ops[self.op].id, self.stage)
    }
}

/// What a row wants of its calls.
#[derive(Debug, Clone)]
pub enum Want {
    /// The value (an expected `nan` is a NaN: [`crate::scalar::same`] takes any NaN for it).
    Value(Value),
    Panic,
    Some(Value),
    None,
    Held,
}

/// The registry and every row of its data files.
#[derive(Debug, Clone, Default)]
pub struct Data {
    pub ops: Vec<Op>,
    /// The types of each operation ([`op_types`]), by its index.
    pub types: Vec<(Vec<Scalar>, Scalar, bool)>,
    pub rows: Vec<Row>,
}

impl Data {
    /// Read `root/tests/vectors`. The errors are of the data (never pending).
    pub fn load(root: &Path) -> Result<Data, Vec<String>> {
        let dir = root.join(DIR);
        let read = |name: &str| {
            std::fs::read_to_string(dir.join(name)).map_err(|e| vec![format!("{DIR}/{name}: cannot read: {e}")])
        };
        let manifest = read(MANIFEST)?;
        let registry = read(REGISTRY)?;
        let ops = parse_registry(&registry)?;
        let names: BTreeSet<&str> = ops.iter().map(|o| o.file.as_str()).collect();
        let mut files = Vec::new();
        for n in names {
            files.push((n.to_string(), read(n)?));
        }
        Data::parse(&manifest, ops, &files)
    }

    /// The data from the texts of `MANIFEST` and of the data files `(name, text)`.
    pub fn parse(manifest: &str, ops: Vec<Op>, files: &[(String, String)]) -> Result<Data, Vec<String>> {
        let mut errors = Vec::new();
        if manifest.lines().next() != Some(FORMAT) {
            errors.push(format!(
                "{DIR}/{MANIFEST}: the first line is `{}`, not `{FORMAT}` (this reader knows FORMAT.md's {FORMAT})",
                manifest.lines().next().unwrap_or("")
            ));
            return Err(errors);
        }
        let mut types = Vec::new();
        for o in &ops {
            match op_types(o) {
                Ok(t) => types.push(t),
                Err(e) => {
                    errors.push(format!("{DIR}/{REGISTRY}: {e}"));
                    types.push((Vec::new(), Scalar::Bool, false));
                }
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        let index: BTreeMap<&str, usize> = ops.iter().enumerate().map(|(i, o)| (o.id.as_str(), i)).collect();
        let mut rows = Vec::new();
        for (name, text) in files {
            let at = |line: usize, m: String| format!("{DIR}/{name}:{line}: {m}");
            let mut section: Option<(usize, bool, String)> = None;
            let lines: Vec<&str> = text.split('\n').collect();
            for (i, l) in lines.iter().copied().enumerate() {
                let line = i + 1;
                if l.is_empty() && line == lines.len() {
                    break; // the end of the last line
                }
                if l.starts_with('#') {
                    continue;
                }
                if let Some(h) = l.strip_prefix("@ ") {
                    section = section_of(h, &index, &ops, name).map_err(|e| errors.push(at(line, e))).ok();
                    continue;
                }
                let Some((op, held, stage)) = section.clone() else {
                    errors.push(at(line, "a row outside a section (`@ <op> <stage>`)".into()));
                    continue;
                };
                let cols: Vec<&str> = l.split('\t').collect();
                if !(2..=3).contains(&cols.len()) {
                    errors.push(at(line, format!("{} columns (arguments, expectation, note)", cols.len())));
                    continue;
                }
                let args: Vec<String> =
                    if cols[0] == NO_ARGS { Vec::new() } else { cols[0].split(' ').map(str::to_string).collect() };
                let expect = match Expect::parse(cols[1]) {
                    Ok(e) => e,
                    Err(e) => {
                        errors.push(at(line, e));
                        continue;
                    }
                };
                if held != (expect == Expect::Held) {
                    errors.push(at(line, "`?` is the expectation of a `held-*` section, and only of it".into()));
                    continue;
                }
                let row = Row { op, file: name.clone(), line, stage, args, expect };
                let (a, r, o) = &types[op];
                match typed(&ops[op], OpTypes { args: a, ret: *r, option: *o }, &row) {
                    Ok(_) => rows.push(row),
                    Err(e) => errors.push(at(line, e)),
                }
            }
        }
        let with_rows: BTreeSet<usize> = rows.iter().map(|r| r.op).collect();
        for (i, o) in ops.iter().enumerate() {
            if !with_rows.contains(&i) {
                errors.push(format!("{DIR}/{}: no row of `{}`", o.file, o.id));
            }
        }
        if ops.is_empty() {
            errors.push(format!("{DIR}/{REGISTRY}: no operation"));
        }
        if errors.is_empty() { Ok(Data { ops, types, rows }) } else { Err(errors) }
    }

    /// The types of operation `op`.
    pub fn types_of(&self, op: usize) -> OpTypes<'_> {
        let (a, r, o) = &self.types[op];
        OpTypes { args: a, ret: *r, option: *o }
    }

    /// The packages of the operations, sorted.
    pub fn packages(&self) -> Vec<&str> {
        self.ops.iter().map(|o| o.pkg.as_str()).collect::<BTreeSet<_>>().into_iter().collect()
    }
}

/// The operation and whether its rows are held, of a section line `@ <op> <stage>` (without `@ `).
fn section_of(h: &str, index: &BTreeMap<&str, usize>, ops: &[Op], file: &str) -> Result<(usize, bool, String), String> {
    let (op, stage) = h.split_once(' ').ok_or_else(|| format!("a section `@ {h}` without its stage"))?;
    let k = *index.get(op).ok_or_else(|| format!("the operation `{op}` is not in {REGISTRY}"))?;
    if ops[k].file != file {
        return Err(format!("`{op}` belongs to {} ({REGISTRY})", ops[k].file));
    }
    let held = match stage {
        "edge" | "rand" => false,
        s if s.strip_prefix("held-S").is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit())) => true,
        s => return Err(format!("the stage `{s}` (edge, rand or held-S<n>)")),
    };
    Ok((k, held, stage.to_string()))
}

/// Read the registry `OPS.tsv`.
pub fn parse_registry(text: &str) -> Result<Vec<Op>, Vec<String>> {
    let mut ops = Vec::new();
    let mut errors = Vec::new();
    let mut seen = BTreeSet::new();
    for (i, l) in text.lines().enumerate() {
        if l.starts_with('#') {
            continue;
        }
        let at = |m: String| format!("{DIR}/{REGISTRY}:{}: {m}", i + 1);
        let c: Vec<&str> = l.split('\t').collect();
        if c.len() != REGISTRY_COLUMNS || c[..6].iter().any(|x| x.is_empty()) {
            errors.push(at(format!("{} columns, or an empty one (FORMAT.md: {REGISTRY_COLUMNS})", c.len())));
            continue;
        }
        if !seen.insert(c[0].to_string()) {
            errors.push(at(format!("`{}` twice", c[0])));
            continue;
        }
        let args = if c[4] == NO_ARGS { Vec::new() } else { c[4].split(' ').map(str::to_string).collect() };
        ops.push(Op { id: c[0].into(), fn_: c[1].into(), file: c[2].into(), pkg: c[3].into(), args, ret: c[5].into() });
    }
    if errors.is_empty() { Ok(ops) } else { Err(errors) }
}

/// A value of `s` as the data writes it (`FORMAT.md`), strictly.
pub fn parse_value(s: Scalar, t: &str) -> Result<Value, String> {
    let bad = || format!("`{t}` is not a {} as FORMAT.md writes it", s.name());
    let hex = |digits: usize| -> Result<u64, String> {
        let h = t.strip_prefix("0x").ok_or_else(bad)?;
        if h.len() != digits || !h.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
            return Err(bad());
        }
        u64::from_str_radix(h, 16).map_err(|_| bad())
    };
    Ok(match s {
        Scalar::F32 => Value::F32(f32::from_bits(hex(8)? as u32)),
        Scalar::F64 => Value::F64(f64::from_bits(hex(16)?)),
        Scalar::Bool => match t {
            "true" => Value::Bool(true),
            "false" => Value::Bool(false),
            _ => return Err(bad()),
        },
        Scalar::Int(k) => {
            let digits = t.strip_prefix('-').unwrap_or(t);
            let canonical = !digits.is_empty()
                && digits.bytes().all(|b| b.is_ascii_digit())
                && (digits == "0" || !digits.starts_with('0'))
                && t != "-0";
            let n: i128 = if canonical { t.parse().map_err(|_| bad())? } else { return Err(bad()) };
            let (lo, hi) = k.range();
            if n < lo || n > hi {
                return Err(format!("`{t}` is out of the range of {}", s.name()));
            }
            int_value(k, n)
        }
        Scalar::Char => return Err(format!("`{t}`: the data has no {} values", s.name())),
    })
}

/// An expected result of `s`: a value, never the bits of a NaN (FORMAT.md
/// writes a NaN result `nan`: its sign and payload are not compared, §3.4).
fn result_value(s: Scalar, t: &str) -> Result<Value, String> {
    let v = parse_value(s, t)?;
    match v {
        Value::F32(x) if x.is_nan() => Err(format!("the NaN `{t}` as a result: FORMAT.md writes it `nan`")),
        Value::F64(x) if x.is_nan() => Err(format!("the NaN `{t}` as a result: FORMAT.md writes it `nan`")),
        v => Ok(v),
    }
}

/// The arguments and the expectation of `row` by the types `t` of its
/// operation: the one check of a row's values (FORMAT.md), for every row.
pub fn typed(op: &Op, t: OpTypes<'_>, row: &Row) -> Result<(Vec<Value>, Want), String> {
    if row.args.len() != t.args.len() || row.args.iter().any(String::is_empty) {
        return Err(format!("the arguments `{}` for the {} of `{}`", row.args.join(" "), t.args.len(), op.id));
    }
    let args = t.args.iter().zip(&row.args).map(|(s, a)| parse_value(*s, a)).collect::<Result<Vec<_>, _>>()?;
    let nan = match t.ret {
        Scalar::F32 => Some(Value::F32(f32::NAN)),
        Scalar::F64 => Some(Value::F64(f64::NAN)),
        _ => None,
    };
    let want = match (&row.expect, t.option) {
        (Expect::Held, _) => Want::Held,
        (Expect::Panic(_), _) => Want::Panic,
        (Expect::Value(v), false) => Want::Value(result_value(t.ret, v)?),
        (Expect::Nan, false) => Want::Value(nan.ok_or_else(|| format!("`nan` for a {}", t.ret.name()))?),
        (Expect::Some(v), true) => Want::Some(result_value(t.ret, v)?),
        (Expect::None, true) => Want::None,
        (e, _) => return Err(format!("`{}` for `{}`, which returns {}", e.text(), op.id, op.ret)),
    };
    Ok((args, want))
}
