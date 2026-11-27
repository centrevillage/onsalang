//! The interpreter behind the door of the evaluator (W7-19 U1a): the functions of the user's package that the evaluator
//! does not evaluate itself (a statement, a `for`, a generic or an `inout` in the body) are run by `onsa_interp` in the
//! Core of the case, found by the declaration the checker named ([`FnDef::decl`]), so that the two sources meet on the
//! functions they share (K-04). The std functions are called through a wrapper package ([`wrap`]), the case having a Core
//! or not; a function of the user's package that Core has no instance of is `Unavailable`, as is every call of one when
//! the case has no Core (a lowering that stops, a work not done yet).
//!
//! A declaration may have several instances in Core (a generic one): the one whose parameters the arguments fit by
//! their types is called; when several fit (a `None`, a `[]`), the one the type arguments of the call name, if they
//! are scalars (`z__F32`); none or two that fit is `Unavailable`. The arguments are values of the evaluator, made
//! into the interpreter's by the type of the parameter in Core; the value back is made from itself alone, and the frame
//! that called checks it against the type the checker holds. A view, a buffer and a function value have no form in the
//! evaluator: they are `Unavailable`. An `inout` argument is a value here, as at every door of the evaluator: it does
//! not write back.
//!
//! `onsa_interp::Value` is not `Send`: make the host and use it in the thread of the evaluation (`onsa_diag::stack`).

use std::collections::HashMap;

use onsa_core::{CTy, FloatKind, FnDef, FnId, Module, TyKind, TypeDefKind, TypeId};
use onsa_interp::value::int_value;
use onsa_interp::{ArrayData, Failure, Interp, Value as IValue};
use onsa_sema::DefId;

pub use self::wrap::Wrappers;
use super::host::{FnHost, HostCall};
use super::scalar::{Fault, PanicKind};
use super::value::Value;

mod wrap;

pub struct InterpHost<'m> {
    module: Option<&'m Module>,
    /// The wrappers of the std functions, kept by the run of the tests and lent to the host of each case.
    wrappers: &'m Wrappers,
    /// The instances in Core of each declaration the checker names (those that have a body).
    by_decl: HashMap<DefId, Vec<FnId>>,
    /// The interpreter over the Core of the case, kept for the calls of the host (its constants are evaluated once).
    /// It does not call the evaluator back, so no call is inside another; made again after an internal error.
    interp: Option<Interp<'m>>,
}

impl<'m> InterpHost<'m> {
    /// A host for the Core of the case (`None` is a case that has none) and the wrappers of the run.
    pub fn new(module: Option<&'m Module>, wrappers: &'m Wrappers) -> InterpHost<'m> {
        let mut by_decl: HashMap<DefId, Vec<FnId>> = HashMap::new();
        for (i, f) in module.into_iter().flat_map(|m| m.fns.iter()).enumerate() {
            if let (Some(decl), Some(_)) = (f.decl, &f.body) {
                by_decl.entry(decl).or_default().push(FnId(i as u32));
            }
        }
        InterpHost { module, wrappers, by_decl, interp: module.map(Interp::new) }
    }

    /// The instance of `decl` the arguments fit, with them made into the interpreter's.
    fn choose(&self, m: &Module, call: &HostCall) -> Result<(FnId, Vec<IValue>), Fault> {
        let (mut fit, mut first_bad) = (Vec::new(), None);
        for &id in self.by_decl.get(&call.callee.def).map_or(&[][..], Vec::as_slice) {
            match to_interp_args(m, &m.fns[id.0 as usize], &call.args) {
                Ok(vs) => fit.push((id, vs)),
                Err(e) => _ = first_bad.get_or_insert(e),
            }
        }
        // Values that do not tell the instance (`None`, `[]`, `S {}`): the one named by the type arguments the checker
        // gave the call (`z__F32`), when they are scalars and one is.
        let suffix: String =
            call.callee.type_args.iter().map(|t| format!("__{}", call.view.display_type(*t))).collect();
        let named =
            |i: &usize| m.fns[fit[*i].0.0 as usize].name.strip_suffix(&suffix).is_some_and(|base| !base.contains("__"));
        if let (true, [at]) = (fit.len() > 1, &(0..fit.len()).filter(named).collect::<Vec<_>>()[..]) {
            return Ok(fit.swap_remove(*at));
        }
        match (fit.len(), first_bad) {
            (1, _) => Ok(fit.remove(0)),
            (0, bad) => Err(bad.unwrap_or(Fault::Unavailable("a function Core has no instance of"))),
            _ => Err(Fault::Unavailable("two instances of one declaration fit the arguments")),
        }
    }
}

/// The reason of a call of a function a flow generated (`render` in a helper): it is no function of Core to call.
pub const GENERATED: &str = "a function a flow generated";

impl FnHost for InterpHost<'_> {
    fn call(&mut self, call: HostCall) -> Result<Value, Fault> {
        if call.view.flow_fn(call.callee.def).is_some() {
            return Err(Fault::Unavailable(GENERATED));
        }
        if call.view.in_std(call.callee.def) {
            let built = self.wrappers.get(&call)?;
            let w = built.as_ref().as_ref().map_err(|e| *e)?;
            let args = to_interp_args(&w.module, &w.module.fns[w.f.0 as usize], &call.args)?;
            return run(&Interp::new(&w.module), w.f, args).0;
        }
        let Some(m) = self.module else { return Err(Fault::Unavailable("a case with no Core")) };
        let (f, args) = self.choose(m, &call)?;
        let (got, stopped) = run(self.interp.get_or_insert_with(|| Interp::new(m)), f, args);
        if stopped {
            self.interp = None;
        }
        got
    }
}

/// `f` on `args` in `interp`, guarded: what it does is a value, a host panic or `Unavailable`; `true` when it stopped on
/// an internal error (its state is not to be trusted).
fn run(interp: &Interp, f: FnId, args: Vec<IValue>) -> (Result<Value, Fault>, bool) {
    match onsa_driver::guard(|| interp.call(f, args)) {
        Err(_) => (Err(Fault::Internal("the interpreter stopped on an internal error")), true),
        Ok(Err(Failure::Panic(_))) => (Err(Fault::Panic(PanicKind::Host)), false),
        Ok(Err(Failure::Unsupported(_))) => (Err(Fault::Unavailable("a std function the interpreter has not")), false),
        Ok(Ok(v)) => (from_interp(&v), false),
    }
}

fn to_interp_args(m: &Module, f: &FnDef, args: &[Value]) -> Result<Vec<IValue>, Fault> {
    each(m, f.params.iter().map(|p| p.ty), args)
}

fn each(m: &Module, tys: impl ExactSizeIterator<Item = CTy>, vs: &[Value]) -> Result<Vec<IValue>, Fault> {
    if tys.len() != vs.len() {
        return Err(Fault::Internal("values that are not as many as the types"));
    }
    tys.zip(vs).map(|(t, v)| to_interp(m, t, v)).collect()
}

/// The value of the evaluator as the interpreter holds a value of the type `ty` of Core.
fn to_interp(m: &Module, ty: CTy, v: &Value) -> Result<IValue, Fault> {
    let bad = Fault::Internal("a value that is not of the type of its place");
    Ok(match (m.tys.kind(ty), v) {
        (TyKind::Int(k), Value::Int(j, n, _)) if k == j => int_value(*k, *n),
        (TyKind::Float(FloatKind::F32), Value::F32(x)) => IValue::F32(*x),
        (TyKind::Float(FloatKind::F64), Value::F64(x)) => IValue::F64(*x),
        (TyKind::Bool, Value::Bool(b)) => IValue::Bool(*b),
        (TyKind::Char, Value::Char(c)) => IValue::Char(*c),
        (TyKind::Unit, Value::Unit) => IValue::Unit,
        (TyKind::Array(e, n), Value::Array(vs)) if *n as usize == vs.len() => {
            let es = each(m, std::iter::repeat_n(*e, vs.len()), vs)?;
            IValue::Array(ArrayData::from_values(*e, es))
        }
        (TyKind::Tuple(ts), Value::Tuple(vs, _)) => IValue::Tuple(each(m, ts.iter().copied(), vs)?),
        (TyKind::Struct(id), Value::Struct(vs)) => match kind(m, *id) {
            TypeDefKind::Struct { fields } => IValue::Struct(each(m, fields.iter().map(|(_, t)| *t), vs)?),
            _ => return Err(bad),
        },
        (TyKind::Enum(id), Value::Enum { tag, fields }) => match kind(m, *id) {
            TypeDefKind::Enum { variants } => {
                let (_, ts) = variants.get(*tag as usize).ok_or(bad)?;
                IValue::Enum { tag: *tag, fields: each(m, ts.iter().copied(), fields)? }
            }
            _ => return Err(bad),
        },
        (TyKind::Span(_) | TyKind::Buf(_) | TyKind::FnPtr(_), _) => {
            return Err(Fault::Unavailable("a view, a buffer or a function value"));
        }
        _ => return Err(bad),
    })
}

fn kind(m: &Module, id: TypeId) -> &TypeDefKind {
    &m.types[id.0 as usize].kind
}

/// The value the interpreter gives, from itself alone (the caller checks it against the type of the call).
fn from_interp(v: &IValue) -> Result<Value, Fault> {
    let all = |vs: &[IValue]| vs.iter().map(from_interp).collect::<Result<Vec<_>, _>>();
    if let (Some(k), Some(n)) = (v.int_kind(), v.to_i128()) {
        return Ok(Value::int(k, n));
    }
    Ok(match v {
        IValue::F32(x) => Value::F32(*x),
        IValue::F64(x) => Value::F64(*x),
        IValue::Bool(b) => Value::Bool(*b),
        IValue::Char(c) => Value::Char(*c),
        IValue::Unit => Value::Unit,
        IValue::Array(a) => Value::Array((0..a.len()).map(|i| from_interp(&a.get(i))).collect::<Result<_, _>>()?),
        IValue::Tuple(vs) => Value::tuple(all(vs)?),
        IValue::Struct(vs) => Value::Struct(all(vs)?),
        IValue::Enum { tag, fields } => Value::Enum { tag: *tag, fields: all(fields)? },
        _ => return Err(Fault::Unavailable("a view, a buffer or a function value")),
    })
}

#[cfg(test)]
mod pairs_tests;
#[cfg(test)]
mod std_tests;
#[cfg(test)]
mod tests;
