//! A sequence typed against the build: what it calls (the API the C backend
//! recorded, D-15), every value checked against the type of its input or
//! output and turned into the value the program reads or must write.
//!
//! The plan holds the C backend's records ([`FlowApi`], [`FnApi`],
//! [`ApiField`]: the C names and types the driver writes), and the values of
//! `config`, `params` and `args` are in the order of the C arguments and
//! fields. It does not hold the form of the calls ([`crate::capi`]). The
//! values, the shapes of the signals and the comparison do not depend on C;
//! the WASM of M6 needs the plan split there (the records out of it).
//!
//! An error here is an error of the case, with the line of the step
//! ([`PlanError::Case`]), or a record of the backend that does not match the
//! build ([`PlanError::Harness`]).

use onsa_backend_c::{ApiField, FlowApi, FnApi, FnParam, FnParamKind};
use onsa_core::{FlowMeta, Module, Ty, TypeDefKind, TypeId};
use onsa_driver::BuildOutput;
use onsa_interp::Value;
use onsa_interp::value::int_value;

use super::{Call, NullArg, PATTERN, Seq, Step};
use crate::scalar::Scalar;

/// Why a sequence has no plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanError {
    /// An error of the case: never pending.
    Case(String),
    /// A record of the C backend does not match the build: the harness cannot run it.
    Harness(String),
}

impl From<String> for PlanError {
    fn from(m: String) -> PlanError {
        PlanError::Case(m)
    }
}

impl From<&str> for PlanError {
    fn from(m: &str) -> PlanError {
        PlanError::Case(m.into())
    }
}

impl PlanError {
    fn map(self, f: impl Fn(String) -> String) -> PlanError {
        match self {
            PlanError::Case(m) => PlanError::Case(f(m)),
            PlanError::Harness(m) => PlanError::Harness(f(m)),
        }
    }
}

/// The C type the backend recorded for a value of `s`, checked against the
/// backend's spelling of `s` (the codec of the bytes is `s`).
fn recorded(c_type: &str, s: Scalar, what: &str) -> Result<String, PlanError> {
    if s.c_type() == Some(c_type) {
        Ok(c_type.to_string())
    } else {
        Err(PlanError::Harness(format!("the C backend records `{c_type}` for {what}, but its type is {}", s.name())))
    }
}

/// A sequence ready to run.
#[derive(Debug, Clone)]
pub struct SeqPlan {
    pub name: String,
    pub line: usize,
    pub callee: Callee,
    pub steps: Vec<StepPlan>,
}

#[derive(Debug, Clone)]
pub enum Callee {
    Flow(FlowApi),
    /// The function, and how this version reports its panic ([`onsa_backend_c::CUnit::take_panic`]).
    Fn(FnApi, Option<String>),
}

#[derive(Debug, Clone)]
pub struct StepPlan {
    pub line: usize,
    pub call: Call,
    pub op: Op,
}

impl StepPlan {
    /// `step 3 (process, line 30)`, 0-based `k`.
    pub fn label(&self, k: usize) -> String {
        format!("step {} ({}, line {})", k + 1, self.call.name(), self.line)
    }
}

#[derive(Debug, Clone)]
pub enum Op {
    Init {
        /// In [`FlowApi::init_args`] order; `None`: a NULL `cfg`.
        config: Option<Vec<Val>>,
        null_bulk: bool,
        sample_rate: f32,
        status: i32,
    },
    Process {
        /// In [`FlowApi::params_fields`] order.
        params: Vec<Val>,
        frames: u32,
        /// `None`: NULL.
        inputs: Option<Vec<SigIn>>,
        /// `None`: NULL.
        outputs: Option<Vec<SigOut>>,
        status: i32,
    },
    Reset,
    Fn {
        /// In [`FnApi::params`] order.
        args: Vec<Arg>,
        status: i32,
        /// The type of the returned value, and its C type ([`FnApi::ret`]).
        ret: Option<(Scalar, String)>,
        /// The result compared (status 0).
        result: Option<Value>,
    },
}

/// A scalar of the API with its value.
#[derive(Debug, Clone)]
pub struct Val {
    pub field: ApiField,
    pub scalar: Scalar,
    pub value: Value,
}

/// A `sample` input: its channels (one, or `n` for `[T; n]`).
#[derive(Debug, Clone)]
pub struct SigIn {
    pub name: String,
    pub scalar: Scalar,
    /// The C type of an element ([`onsa_backend_c::IoArg::c_type`]).
    pub c_type: String,
    pub planar: Option<u32>,
    pub data: Vec<Vec<Value>>,
    /// `place`: the byte offset of each channel in the shared region.
    pub place: Option<Vec<usize>>,
}

/// An output: what its buffer holds before the call, and what it must hold after.
#[derive(Debug, Clone)]
pub struct SigOut {
    pub name: String,
    pub scalar: Scalar,
    /// The C type of an element ([`onsa_backend_c::IoArg::c_type`]).
    pub c_type: String,
    pub planar: Option<u32>,
    pub before: Before,
    pub expected: Vec<Vec<Value>>,
    /// `place`: the byte offset of each channel in the shared region.
    pub place: Option<Vec<usize>>,
}

impl SigOut {
    /// The bytes of its buffer: every channel, `frames` values each.
    pub fn byte_len(&self, frames: u32) -> usize {
        self.scalar.size() * frames as usize * self.planar.unwrap_or(1) as usize
    }
}

/// The bytes of the shared region of `place` (0: no buffer is placed): up to
/// the end of the last placed channel, and at least 1 (a call of 0 frames
/// still places its buffers).
pub fn region_len(inputs: &[SigIn], outputs: &[SigOut], frames: u32) -> usize {
    let ins = inputs.iter().map(|i| (&i.place, i.scalar));
    let outs = outputs.iter().map(|o| (&o.place, o.scalar));
    ins.chain(outs)
        .flat_map(|(p, s)| p.iter().flatten().map(move |o| (o + s.size() * frames as usize).max(1)))
        .max()
        .unwrap_or(0)
}

/// The number of bytes the program writes after the index of a step
/// ([`super::driver`]): the status, then the outputs or the result; the mark
/// of a finished `reset`.
pub fn record_len(op: &Op) -> usize {
    match op {
        Op::Init { .. } => 4,
        Op::Process { frames, outputs, .. } => 4 + outputs.iter().flatten().map(|o| o.byte_len(*frames)).sum::<usize>(),
        Op::Reset => 4,
        Op::Fn { ret, .. } => 4 + ret.as_ref().map_or(0, |(s, _)| s.size()),
    }
}

#[derive(Debug, Clone)]
pub enum Before {
    /// `fill`.
    Fill(Vec<Vec<Value>>),
    /// No `fill`: [`PATTERN`] in every byte.
    Pattern,
    /// `inplace`: the buffer of this input (index into the inputs).
    Inplace(usize),
}

/// An argument of an exported function.
#[derive(Debug, Clone)]
pub struct Arg {
    pub param: FnParam,
    pub scalar: Scalar,
    /// One value for a scalar; the elements for a span.
    pub values: Vec<Value>,
}

/// The type of each `init` input, `block` input, `sample` input and output of a flow.
struct FlowTypes {
    config: Vec<(String, Scalar)>,
    params: Vec<(String, Scalar)>,
    inputs: Vec<(String, Scalar, Option<u32>)>,
    outputs: Vec<(String, Scalar, Option<u32>)>,
    /// The output is a struct (spec §11.6: `Out`, written as a table by field).
    out_struct: bool,
}

fn struct_fields(m: &Module, id: TypeId) -> &[(String, Ty)] {
    match &m.ty(id).kind {
        TypeDefKind::Struct { fields } => fields,
        _ => &[],
    }
}

fn scalar_of(m: &Module, ty: &Ty, what: &str) -> Result<Scalar, String> {
    Scalar::of(ty).ok_or_else(|| {
        let name = onsa_core::dump::type_name(m, ty);
        format!("{what} has the type {name}, which the host steps cannot drive (not a scalar)")
    })
}

fn flow_types(m: &Module, meta: &FlowMeta) -> Result<FlowTypes, String> {
    let named = |fields: &[(String, Ty)], what: &str| -> Result<Vec<(String, Scalar)>, String> {
        fields.iter().map(|(n, t)| Ok((n.clone(), scalar_of(m, t, &format!("the {what} `{n}`"))?))).collect()
    };
    let config = named(struct_fields(m, meta.fns.config), "`init` input")?;
    let params = named(struct_fields(m, meta.fns.params), "`block` input")?;
    let inputs = meta
        .sig_inputs
        .iter()
        .map(|(n, t)| {
            let (e, planar) = match t {
                Ty::Array(e, k) => (&**e, Some(*k)),
                t => (t, None),
            };
            Ok((n.clone(), scalar_of(m, e, &format!("the `sample` input `{n}`"))?, planar))
        })
        .collect::<Result<_, String>>()?;
    let outputs = meta
        .outputs
        .iter()
        .map(|(n, t, p)| Ok((n.clone(), scalar_of(m, t, &format!("the output `{n}`"))?, *p)))
        .collect::<Result<_, String>>()?;
    let out_struct = matches!(m.fn_(meta.fns.tick).ret, Ty::Struct(_));
    Ok(FlowTypes { config, params, inputs, outputs, out_struct })
}

/// Type the sequence `s` against the build `out`.
pub fn plan(s: &Seq, out: &BuildOutput) -> Result<SeqPlan, PlanError> {
    let m = &out.module;
    let head = |line: usize, m: String| format!("line {line}: host \"{}\": {m}", s.name);
    let (callee, flow) = match (&s.flow, &s.fn_) {
        (Some(f), _) => {
            let api = out.unit.flows.iter().find(|a| &a.flow == f).ok_or_else(|| {
                head(s.line, format!("the flow `{f}` is not exported for target `{}` (`[export] flows`)", s.target))
            })?;
            let meta = m
                .flows
                .iter()
                .find(|x| &x.name == f)
                .ok_or_else(|| head(s.line, format!("the build has no flow `{f}`")))?;
            let types = flow_types(m, meta).map_err(|e| head(s.line, e))?;
            (Callee::Flow(api.clone()), Some(types))
        }
        (_, Some(f)) => {
            let api = out.unit.fns.iter().find(|a| &a.fn_ == f).ok_or_else(|| {
                head(s.line, format!("the function `{f}` is not exported for target `{}` (`[export] fns`)", s.target))
            })?;
            (Callee::Fn(api.clone(), out.unit.take_panic.clone()), None)
        }
        _ => return Err(head(s.line, "write exactly one of `flow` and `fn`".into()).into()),
    };
    let mut steps = Vec::new();
    for (k, st) in s.steps.iter().enumerate() {
        let at = |m: String| format!("line {}: host \"{}\" step {}: {m}", st.line, s.name, k + 1);
        let op = match (&callee, &flow) {
            (Callee::Flow(api), Some(t)) => flow_step(st, api, t),
            (Callee::Fn(api, _), _) => fn_step(st, api, m),
            _ => Err("a flow without its types".into()),
        }
        .map_err(|e| e.map(at))?;
        steps.push(StepPlan { line: st.line, call: st.call, op });
    }
    Ok(SeqPlan { name: s.name.clone(), line: s.line, callee, steps })
}

fn status(st: &Step) -> Result<i32, PlanError> {
    let v = st.status.ok_or("no `status`")?;
    Ok(i32::try_from(v).map_err(|_| format!("`status = {v}` is not a status"))?)
}

/// The values of a table that must name exactly `fields`, in the order of `order`.
fn table_values(
    t: &toml::Table,
    what: &str,
    fields: &[(String, Scalar)],
    order: &[ApiField],
) -> Result<Vec<Val>, PlanError> {
    for k in t.keys() {
        if !fields.iter().any(|(n, _)| n == k) {
            let names: Vec<String> = fields.iter().map(|(n, _)| format!("`{n}`")).collect();
            return Err(format!(
                "`{what}` has `{k}`, which is not one of its fields ({})",
                if names.is_empty() { "none".into() } else { names.join(", ") }
            )
            .into());
        }
    }
    for (n, _) in fields {
        if !t.contains_key(n) {
            return Err(format!("`{what}` has no `{n}` (write every field)").into());
        }
    }
    let mut out = Vec::new();
    for f in order {
        let (_, s) = fields
            .iter()
            .find(|(n, _)| *n == f.name)
            .ok_or_else(|| PlanError::Harness(format!("the C API has `{}`, which `{what}` does not know", f.name)))?;
        let v = scalar_value(&t[&f.name], *s).map_err(|e| format!("`{what}.{}`: {e}", f.name))?;
        recorded(&f.c_type, *s, &format!("`{what}.{}`", f.name))?;
        out.push(Val { field: f.clone(), scalar: *s, value: v });
    }
    if order.len() != fields.len() {
        return Err(PlanError::Harness(format!(
            "`{what}`: the C API passes {} of its {} fields",
            order.len(),
            fields.len()
        )));
    }
    Ok(out)
}

fn flow_step(st: &Step, api: &FlowApi, t: &FlowTypes) -> Result<Op, PlanError> {
    Ok(match st.call {
        Call::Init => {
            let config = match &st.config {
                Some(c) => Some(table_values(c, "config", &t.config, &api.init_args)?),
                None => None,
            };
            let sr = st.sample_rate.as_ref().ok_or("no `sample_rate`")?;
            let sample_rate = match scalar_value(sr, Scalar::F32).map_err(|e| format!("`sample_rate`: {e}"))? {
                Value::F32(x) => x,
                v => return Err(format!("`sample_rate`: {v:?}").into()),
            };
            Op::Init { config, null_bulk: st.is_null(NullArg::Bulk), sample_rate, status: status(st)? }
        }
        Call::Process => {
            let params =
                table_values(st.params.as_ref().ok_or("no `params`")?, "params", &t.params, &api.params_fields)?;
            let frames = st.frames.ok_or("no `frames`")?;
            let (in_place, out_place) = placement(st, t)?;
            let inputs = if st.is_null(NullArg::Input) {
                if t.inputs.is_empty() {
                    return Err("`null = [\"input\"]`, but the flow has no `sample` input".into());
                }
                None
            } else {
                let mut ins = inputs(st, api, t, frames)?;
                for (i, p) in ins.iter_mut().zip(in_place) {
                    i.place = p;
                }
                Some(ins)
            };
            let outputs = if st.is_null(NullArg::Output) {
                None
            } else {
                let mut outs = outputs(st, api, t, frames, inputs.as_deref())?;
                for (o, p) in outs.iter_mut().zip(out_place) {
                    o.place = p;
                }
                Some(outs)
            };
            Op::Process { params, frames, inputs, outputs, status: status(st)? }
        }
        Call::Reset => Op::Reset,
        Call::Fn => return Err("`call = \"fn\"` in a sequence of `flow`".into()),
    })
}

/// The C type the backend recorded for the input or output `name`.
fn io_type(api: &FlowApi, name: &str, output: bool, s: Scalar) -> Result<String, PlanError> {
    let what = if output { "output" } else { "`sample` input" };
    let a = api.process_args.iter().find(|a| a.name == name && a.output == output).ok_or_else(|| {
        PlanError::Harness(format!("the C backend records no {what} `{name}` of `{}_process`", api.symbol))
    })?;
    recorded(&a.c_type, s, &format!("the {what} `{name}`"))
}

fn inputs(st: &Step, api: &FlowApi, t: &FlowTypes, frames: u32) -> Result<Vec<SigIn>, PlanError> {
    let sig = |(n, s, p): &(String, Scalar, Option<u32>), v: &toml::Value, what: &str| -> Result<SigIn, PlanError> {
        let data = channels(v, *s, *p, frames, what)?;
        Ok(SigIn { name: n.clone(), scalar: *s, c_type: io_type(api, n, false, *s)?, planar: *p, data, place: None })
    };
    match (t.inputs.as_slice(), &st.input) {
        ([], None) => Ok(Vec::new()),
        ([], Some(_)) => Err("`input`, but the flow has no `sample` input".into()),
        (_, None) => Err("`call = \"process\"` needs `input` (the flow has `sample` inputs)".into()),
        ([one], Some(v)) => Ok(vec![sig(one, v, "input")?]),
        (many, Some(v)) => {
            let names: Vec<&str> = many.iter().map(|(n, _, _)| n.as_str()).collect();
            let table = keyed(v, "input", &names)?;
            many.iter().map(|i| sig(i, &table[&i.0], &format!("input.{}", i.0))).collect()
        }
    }
}

fn outputs(
    st: &Step,
    api: &FlowApi,
    t: &FlowTypes,
    frames: u32,
    inputs: Option<&[SigIn]>,
) -> Result<Vec<SigOut>, PlanError> {
    let per = |v: &toml::Value, what: &str| -> Result<Vec<Vec<Vec<Value>>>, String> {
        if t.out_struct {
            let names: Vec<&str> = t.outputs.iter().map(|(n, _, _)| n.as_str()).collect();
            let table = keyed(v, what, &names)?;
            t.outputs.iter().map(|(n, s, p)| channels(&table[n], *s, *p, frames, &format!("{what}.{n}"))).collect()
        } else {
            match t.outputs.as_slice() {
                [(_, s, p)] => Ok(vec![channels(v, *s, *p, frames, what)?]),
                _ => Err(format!("the flow has {} outputs and no struct output", t.outputs.len())),
            }
        }
    };
    let expected = per(st.output.as_ref().ok_or("no `output`")?, "output")?;
    let inplace = st.inplace == Some(true);
    if inplace {
        let ins = inputs.unwrap_or_default();
        let fits = ins.len() == t.outputs.len()
            && ins.iter().zip(&t.outputs).all(|(i, (_, s, p))| i.scalar == *s && i.planar == *p);
        if !fits {
            return Err("`inplace`: the `sample` inputs and the outputs do not pair by position with the same types \
                        and channels (spec §11.6 `process_inplace`)"
                .into());
        }
    }
    let fill = match &st.fill {
        Some(v) => Some(per(v, "fill")?),
        None => None,
    };
    let mut out = Vec::new();
    for (j, ((n, s, p), exp)) in t.outputs.iter().zip(expected).enumerate() {
        let before = if inplace {
            Before::Inplace(j)
        } else if let Some(f) = &fill {
            Before::Fill(f[j].clone())
        } else {
            let mut b = Vec::new();
            for v in exp.iter().flatten() {
                b.clear();
                s.bytes(v, &mut b);
                if b.iter().all(|x| *x == PATTERN) {
                    return Err(format!(
                        "`output`: a value of `{n}` has the bits of the unwritten pattern ({PATTERN:#04x} in every \
                         byte); write `fill` so that a call that does not write is seen"
                    )
                    .into());
                }
            }
            Before::Pattern
        };
        let c_type = io_type(api, n, true, *s)?;
        out.push(SigOut { name: n.clone(), scalar: *s, c_type, planar: *p, before, expected: exp, place: None });
    }
    Ok(out)
}

/// The most a placed buffer may reach into the shared region, in bytes.
const REGION_MAX: usize = 1 << 20;

/// The offsets of `place`, by input and by output (in the order of the
/// flow's types): `None` for a buffer it does not name.
type Places = Vec<Option<Vec<usize>>>;

/// `place` (spec §14.2, W2-08): the byte offset of each channel it names, a
/// multiple of the element's size. Like `input` and `output`, a group of one
/// signal (one input, an output that is not a struct) is written directly,
/// otherwise by name; `[T; N]` takes one offset per channel.
fn placement(st: &Step, t: &FlowTypes) -> Result<(Places, Places), String> {
    let mut ins: Places = vec![None; t.inputs.len()];
    let mut outs: Places = vec![None; t.outputs.len()];
    let Some(place) = &st.place else { return Ok((ins, outs)) };
    for (k, v) in place {
        let (sigs, slots, by_name) = match k.as_str() {
            "input" => (&t.inputs, &mut ins, t.inputs.len() != 1),
            "output" => (&t.outputs, &mut outs, t.out_struct),
            _ => return Err(format!("`place` has `{k}`, which is not `input` or `output`")),
        };
        if sigs.is_empty() {
            return Err(format!("`place.{k}`, but the flow has no `sample` {k}"));
        }
        if !by_name {
            let (_, s, p) = &sigs[0];
            slots[0] = Some(offsets(v, *s, *p, &format!("place.{k}"))?);
            continue;
        }
        let table = v.as_table().ok_or_else(|| format!("`place.{k}` is a table by name"))?;
        for (n, x) in table {
            let j = sigs.iter().position(|(m, _, _)| m == n).ok_or_else(|| {
                let names: Vec<&str> = sigs.iter().map(|(m, _, _)| m.as_str()).collect();
                format!("`place.{k}` has `{n}`, which is not one of {}", names.join(", "))
            })?;
            let (_, s, p) = &sigs[j];
            slots[j] = Some(offsets(x, *s, *p, &format!("place.{k}.{n}"))?);
        }
    }
    Ok((ins, outs))
}

/// The byte offsets of the channels of one signal in `place`.
fn offsets(v: &toml::Value, s: Scalar, planar: Option<u32>, what: &str) -> Result<Vec<usize>, String> {
    let one = |x: &toml::Value, what: &str| -> Result<usize, String> {
        let o = x
            .as_integer()
            .and_then(|o| usize::try_from(o).ok())
            .filter(|o| *o <= REGION_MAX)
            .ok_or_else(|| format!("`{what}` is a byte offset (an integer from 0 to {REGION_MAX})"))?;
        if o % s.size() != 0 {
            return Err(format!("`{what} = {o}` is not a multiple of {}, the size of {}", s.size(), s.name()));
        }
        Ok(o)
    };
    match planar {
        None => Ok(vec![one(v, what)?]),
        Some(n) => {
            let a = v.as_array().ok_or_else(|| format!("`{what}` is an array of {n} offsets (`[T; {n}]`)"))?;
            if a.len() != n as usize {
                return Err(format!("`{what}` has {} offsets, but the type has {n} channels", a.len()));
            }
            a.iter().enumerate().map(|(c, x)| one(x, &format!("{what}[{c}]"))).collect()
        }
    }
}

/// A table with exactly the keys `names`.
fn keyed<'v>(v: &'v toml::Value, what: &str, names: &[&str]) -> Result<&'v toml::Table, String> {
    let t = v.as_table().ok_or_else(|| {
        format!(
            "`{what}` is a table by name ({})",
            names.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")
        )
    })?;
    for k in t.keys() {
        if !names.contains(&k.as_str()) {
            return Err(format!("`{what}` has `{k}`, which is not one of {}", names.join(", ")));
        }
    }
    for n in names {
        if !t.contains_key(*n) {
            return Err(format!("`{what}` has no `{n}`"));
        }
    }
    Ok(t)
}

/// The channels of one signal: `[v, ...]` (`frames` values), or `[[...], ...]`
/// (`n` channels) for `[T; n]`.
fn channels(
    v: &toml::Value,
    s: Scalar,
    planar: Option<u32>,
    frames: u32,
    what: &str,
) -> Result<Vec<Vec<Value>>, String> {
    let one = |v: &toml::Value, what: &str| -> Result<Vec<Value>, String> {
        let a = v.as_array().ok_or_else(|| format!("`{what}` is an array of {frames} values"))?;
        if a.len() != frames as usize {
            return Err(format!("`{what}` has {} values, but `frames = {frames}`", a.len()));
        }
        a.iter().enumerate().map(|(i, x)| scalar_value(x, s).map_err(|e| format!("`{what}[{i}]`: {e}"))).collect()
    };
    match planar {
        None => Ok(vec![one(v, what)?]),
        Some(n) => {
            let a = v.as_array().ok_or_else(|| format!("`{what}` is an array of {n} channels (`[T; {n}]`)"))?;
            if a.len() != n as usize {
                return Err(format!("`{what}` has {} channels, but the type has {n}", a.len()));
            }
            a.iter().enumerate().map(|(c, ch)| one(ch, &format!("{what}[{c}]"))).collect()
        }
    }
}

fn fn_step(st: &Step, api: &FnApi, m: &Module) -> Result<Op, PlanError> {
    let def =
        m.fns.iter().find(|f| f.name == api.fn_).ok_or_else(|| format!("the build has no function `{}`", api.fn_))?;
    if def.params.len() != api.params.len() {
        return Err(PlanError::Harness(format!(
            "`{}` has {} parameters, its C API {}",
            api.fn_,
            def.params.len(),
            api.params.len()
        )));
    }
    let table = st.args.as_ref().ok_or("no `args`")?;
    for k in table.keys() {
        if !api.params.iter().any(|p| &p.field.name == k) {
            return Err(format!("`args` has `{k}`, which is not a parameter of `{}`", api.fn_).into());
        }
    }
    let mut args = Vec::new();
    for (p, cp) in api.params.iter().zip(&def.params) {
        let name = &p.field.name;
        let v = table.get(name).ok_or_else(|| format!("`args` has no `{name}` (write every parameter)"))?;
        let what = format!("`args.{name}`");
        let (scalar, values) = match (p.kind, &cp.ty) {
            (FnParamKind::Scalar, t) => {
                let s = scalar_of(m, t, &what)?;
                (s, vec![scalar_value(v, s).map_err(|e| format!("{what}: {e}"))?])
            }
            (FnParamKind::Span { inout: false }, Ty::Span(e)) => {
                let s = scalar_of(m, e, &what)?;
                let a = v.as_array().ok_or_else(|| format!("{what} is an array (a `Span`)"))?;
                let vals = a
                    .iter()
                    .enumerate()
                    .map(|(i, x)| scalar_value(x, s).map_err(|e| format!("{what}[{i}]: {e}")))
                    .collect::<Result<_, _>>()?;
                (s, vals)
            }
            (FnParamKind::InoutScalar | FnParamKind::Span { inout: true }, _) => {
                return Err(format!(
                    "the parameter `{name}` is `inout`: the host steps have no field for its value after the call yet"
                )
                .into());
            }
            (_, t) => {
                return Err(PlanError::Harness(format!(
                    "the parameter `{name}` of type {t:?}: its C API does not match"
                )));
            }
        };
        recorded(&p.field.c_type, scalar, &format!("the parameter `{name}`"))?;
        args.push(Arg { param: p.clone(), scalar, values });
    }
    let status = status(st)?;
    let ret = match (&def.ret, &api.ret) {
        (Ty::Unit, None) => None,
        (t, Some(c)) if *t != Ty::Unit => {
            let s = scalar_of(m, t, "the returned value")?;
            Some((s, recorded(c, s, "the returned value")?))
        }
        _ => {
            return Err(PlanError::Harness(format!("`{}` returns {:?}, its C API does not match", api.fn_, def.ret)));
        }
    };
    let result = match (ret.as_ref().map(|r| r.0), status, &st.result) {
        (Some(s), 0, Some(v)) => Some(scalar_value(v, s).map_err(|e| format!("`result`: {e}"))?),
        (Some(_), 0, None) => return Err("`status = 0` needs `result` (the function returns a value)".into()),
        (None, _, Some(_)) => return Err("`result`, but the function returns nothing".into()),
        (Some(_), _, Some(_)) => {
            return Err("`result` with `status = 1`: a panicked call writes no result (spec §9.2, §14.2)".into());
        }
        (_, _, None) => None,
    };
    Ok(Op::Fn { args, status, ret, result })
}

/// A TOML value as a value of `s`, exact (an error otherwise).
pub fn scalar_value(v: &toml::Value, s: Scalar) -> Result<Value, String> {
    let ty = s.name();
    match (s, v) {
        (Scalar::F32, toml::Value::Float(x)) => {
            let f = *x as f32;
            if x.is_nan() || f as f64 == *x {
                Ok(Value::F32(f))
            } else {
                Err(format!(
                    "{x} is not exact in F32 (the nearest F32 is {}); write a value F32 holds exactly",
                    f as f64
                ))
            }
        }
        (Scalar::F64, toml::Value::Float(x)) => Ok(Value::F64(*x)),
        (Scalar::F32 | Scalar::F64, toml::Value::Integer(n)) => Err(format!(
            "the integer {n} for a value of {ty}: write a float (`{n}.0`); there is no implicit conversion"
        )),
        (Scalar::Int(k), toml::Value::Integer(n)) => {
            let (lo, hi) = k.range();
            if (lo..=hi).contains(&(*n as i128)) {
                Ok(int_value(k, *n as i128))
            } else {
                Err(format!("{n} is outside {ty} ({lo}..={hi})"))
            }
        }
        (Scalar::Bool, toml::Value::Boolean(b)) => Ok(Value::Bool(*b)),
        (Scalar::Char, toml::Value::String(t)) => {
            let mut cs = t.chars();
            match (cs.next(), cs.next()) {
                (Some(c), None) => Ok(Value::Char(c)),
                _ => Err(format!("{t:?} is not one character (a `Char` is one Unicode scalar value)")),
            }
        }
        (_, v) => Err(format!("{} for a value of {ty}", describe(v))),
    }
}

fn describe(v: &toml::Value) -> String {
    match v {
        toml::Value::String(s) => format!("the string {s:?}"),
        toml::Value::Integer(n) => format!("the integer {n}"),
        toml::Value::Float(x) => format!("the float {x}"),
        toml::Value::Boolean(b) => format!("the boolean {b}"),
        toml::Value::Datetime(d) => format!("the date {d}"),
        toml::Value::Array(_) => "an array".into(),
        toml::Value::Table(_) => "a table".into(),
    }
}

/// The bytes the program reads for the first `steps` steps (the ones it
/// makes), in the order it reads them ([`super::driver`]).
pub fn input_bytes(p: &SeqPlan, steps: usize) -> Vec<u8> {
    let mut b = Vec::new();
    for st in p.steps.iter().take(steps) {
        match &st.op {
            Op::Init { config, sample_rate, .. } => {
                for v in config.iter().flatten() {
                    v.scalar.bytes(&v.value, &mut b);
                }
                b.extend(sample_rate.to_le_bytes());
            }
            Op::Process { params, frames, inputs, outputs, .. } => {
                for v in params {
                    v.scalar.bytes(&v.value, &mut b);
                }
                // The outputs' contents, then the inputs: where `place` overlaps them, the input holds its values.
                for o in outputs.iter().flatten() {
                    match &o.before {
                        Before::Fill(f) => {
                            for v in f.iter().flatten() {
                                o.scalar.bytes(v, &mut b);
                            }
                        }
                        Before::Pattern => b.extend(std::iter::repeat_n(PATTERN, o.byte_len(*frames))),
                        Before::Inplace(_) => {}
                    }
                }
                for i in inputs.iter().flatten() {
                    for v in i.data.iter().flatten() {
                        i.scalar.bytes(v, &mut b);
                    }
                }
            }
            Op::Reset => {}
            Op::Fn { args, .. } => {
                for a in args {
                    for v in &a.values {
                        a.scalar.bytes(v, &mut b);
                    }
                }
            }
        }
    }
    b
}
