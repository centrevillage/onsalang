//! An exported flow as the C API has it (§9.2, §11.6, §14.2): one instance with the status of each call. A panic of a
//! `process` is not an error: the call gives all its outputs as 0 (the frames done before the panic too), the status 1,
//! and the instance is poisoned, which later calls of `process` do not evaluate (0 for each frame, 1) and `reset`
//! frees. A panic of `init` leaves it uninitialized (as the state of the C `_init` that gave 1: zeros, and `process` is
//! the same, 1 and zeros, `reset` does nothing), and only an `init` again frees it. The lengths of the columns are compared
//! at the start of a `process` ([`PanicAt::Start`], `Fault::Panic(Length)`): a mismatch is a panic of the call, before
//! any state moves. A fault that is no panic (`Unavailable`, `Internal`) is the evaluator's, not the program's: `Err`.

use super::expr::{LIMITS, Stop};
use super::flow::{Ctx, Instance, Outcome, PanicAt};
use super::host::FnHost;
use super::scalar::Fault;
use super::sema_view::View;
use super::value::{Scalar, Value};
use onsa_sema::ty::Len;
use onsa_sema::{DefId, Ty};

/// What a call of the C API returns (the `int` of `_init` and `_process`): 0, or 1 for a panic and for a call on an instance
/// that is poisoned or not initialized.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Ok,
    Poisoned,
}

/// An exported flow: not initialized until its `init` has run and not panicked, poisoned from the panic of a `process` to
/// the next `reset`.
pub struct Boundary<'a> {
    view: View<'a>,
    def: DefId,
    sample_rate: f32,
    inst: Option<Instance<'a>>,
    poisoned: bool,
    last: Option<(PanicAt, Stop)>,
}

/// The zero of a type of an output (§9.2: all of it is 0, and a field's declared value is not read): each scalar leaf, a
/// `Bool` `false`, an array of its length and a struct of its fields.
fn zero(view: View, ty: &Ty) -> Result<Value, Fault> {
    if let Some(s) = Scalar::of(ty) {
        return Ok(s.default_value().unwrap_or(Value::Char('\0')));
    }
    Ok(match ty {
        Ty::Array(t, Len::Const(n)) if LIMITS.holds(*n as usize) => {
            Value::Array(vec![zero(view, view.ty(*t))?; *n as usize])
        }
        Ty::Named(def, _) => Value::Struct(
            view.struct_fields(*def)?.iter().map(|f| zero(view, view.ty(f.ty))).collect::<Result<_, _>>()?,
        ),
        _ => return Err(Fault::Unavailable("an output of a type the boundary has not")),
    })
}

impl<'a> Boundary<'a> {
    /// An instance of the flow `def` that has not run its `init`.
    pub fn new(view: View<'a>, def: DefId, sample_rate: f32) -> Boundary<'a> {
        Boundary { view, def, sample_rate, inst: None, poisoned: false, last: None }
    }

    /// `_init`: the instance as `init` makes it, `Ok` (a call that is made again starts the state from the beginning, and a
    /// poisoned instance is a new one), or `Poisoned` with the instance uninitialized when `init` panics.
    // SPEC-GAP(S-1132): an `init` called on an instance that is poisoned (not one that `init` left uninitialized) is read as a fresh
    // instance, not poisoned; the spec says that `init` again frees the uninitialized one and that `reset` frees the poisoned.
    pub fn init<'h>(&mut self, config: &[(&str, Value)], host: Option<&'h mut dyn FnHost>) -> Result<Status, Stop>
    where
        'a: 'h,
    {
        (self.inst, self.poisoned, self.last) = (None, false, None);
        match Instance::init(self.view, self.def, self.sample_rate, config, host) {
            Ok(inst) => {
                self.inst = Some(inst);
                Ok(Status::Ok)
            }
            Err(stop) if matches!(stop.fault, Fault::Panic(_)) => {
                self.last = Some((PanicAt::Init, stop));
                Ok(Status::Poisoned)
            }
            Err(stop) => Err(stop),
        }
    }

    /// `_process`: the status and the outputs, one for each of `frames`; a panic (or an instance that is poisoned or not
    /// initialized) is `Poisoned` and `frames` outputs that are all 0.
    pub fn process<'h>(
        &mut self,
        params: &[(&str, Value)],
        inputs: &[(&str, &[Value])],
        frames: usize,
        host: Option<&'h mut dyn FnHost>,
    ) -> Result<(Status, Vec<Value>), Stop>
    where
        'a: 'h,
    {
        let live = self.inst.as_mut().filter(|_| !self.poisoned);
        let panic = match live {
            Some(inst) => match inst.process_outcome(params, inputs, frames, host)? {
                Outcome::Ok(outs) => return Ok((Status::Ok, outs)),
                Outcome::Panic { at, stop } => Some((at, stop)),
            },
            None => None,
        };
        if panic.is_some() {
            (self.poisoned, self.last) = (true, panic);
        }
        let (decl, here) = (self.view.flow(self.def), self.view.name_span(self.def));
        let ty = decl.and_then(|d| self.view.body(self.def)?.ty(d.body)).map_err(|fault| Stop { fault, at: here })?;
        let zero = zero(self.view, ty).map_err(|fault| Stop { fault, at: here })?;
        Ok((Status::Poisoned, vec![zero; frames]))
    }

    /// `_reset`: the state as `init` made it, and the instance not poisoned; an instance that is not initialized stays so.
    pub fn reset(&mut self) {
        if let Some(inst) = self.inst.as_mut() {
            inst.reset();
            (self.poisoned, self.last) = (false, None);
        }
    }

    /// The panic that the instance is poisoned by, or that `init` stopped at: its stage and the stop.
    pub fn last_panic(&self) -> Option<&(PanicAt, Stop)> {
        self.last.as_ref()
    }

    /// The time of the instance; none while it is not initialized.
    pub fn ctx(&self) -> Option<Ctx> {
        self.inst.as_ref().map(|i| i.ctx)
    }
}
