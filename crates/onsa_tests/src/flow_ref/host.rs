//! The door of the functions the evaluator does not evaluate itself (the memo's way (b)): a call it hands over with
//! the function the checker named and the values of the arguments (the receiver first for a method), and the value
//! back or a [`Fault`]. W7-19 puts the interpreter behind it; here are the two the evaluator has of its own.

use std::collections::HashMap;

use super::scalar::Fault;
use super::sema_view::{Callee, View};
use super::value::Value;
use onsa_sema::TyId;

/// One call: the function (with its type arguments and the signature the checker holds), the table it was named in
/// (a host tells functions apart by `callee.def`, one for each; `View::qualified_name` is the name of a table of
/// rows) and the arguments, which are values: the host gets no place to write to. `types` are the types of the
/// arguments' expressions (the receiver first) and `ret` that of the call, as the checker holds them: what a host that
/// writes the call in source needs.
pub struct HostCall<'a> {
    pub view: View<'a>,
    pub callee: &'a Callee<'a>,
    pub args: Vec<Value>,
    pub types: Vec<TyId>,
    pub ret: TyId,
}

/// A host that runs a function (`InterpHost`) counts the calls inside the function from 0, whatever the depth of the call
/// that handed it over: §12.5's 128 of calls are not shared between the two, as a host has no door to take the depth in.
pub trait FnHost {
    fn call(&mut self, call: HostCall) -> Result<Value, Fault>;
}

/// No host: every call it is given is `Unavailable`.
pub struct NoHost;

impl FnHost for NoHost {
    fn call(&mut self, _: HostCall) -> Result<Value, Fault> {
        Err(Fault::Unavailable("a call"))
    }
}

/// What a test writes for a function: the arguments (the receiver first), the value or the fault.
pub type Row = fn(&[Value]) -> Result<Value, Fault>;

/// A closed table of Rust functions by the qualified name of the function (`t.loopy`, `t.P.lp`): what a test writes by hand
/// for the functions the evaluator does not evaluate. A name that is not in the table is `Unavailable`.
#[derive(Default)]
pub struct TableHost {
    rows: HashMap<&'static str, Row>,
}

impl TableHost {
    pub fn with(mut self, name: &'static str, row: Row) -> TableHost {
        self.rows.insert(name, row);
        self
    }
}

impl FnHost for TableHost {
    fn call(&mut self, call: HostCall) -> Result<Value, Fault> {
        let row = self.rows.get(call.view.qualified_name(call.callee.def).as_str());
        row.map_or(Err(Fault::Unavailable("a function the table has no row for")), |row| row(&call.args))
    }
}
