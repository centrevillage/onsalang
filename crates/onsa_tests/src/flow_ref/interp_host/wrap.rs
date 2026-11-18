//! The std functions of the interpreter host (W7-19 U1b). A std function is not in the Core of the case when it is a
//! `target` one (`floor`, `F32.round_from`), and the instance of a generic one is made for the interpreter's callers
//! only: so each is called through a wrapper, a package of one file that has the one function `w` whose body is the
//! call, written in the types of the call as the checker holds them (the receiver first). The package is analyzed and
//! lowered once for each text and kept (a test run keeps one [`Wrappers`]), and `w` is called like a function of the
//! case. A call whose types name a type of the user's package is not one a wrapper can write: it has diagnostics, and
//! is `Unavailable`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use onsa_core::{FnId, Module};
use onsa_diag::Code;
use onsa_driver::{Loaded, LowerError, PackageInput, analyze_loaded, lower_core};

use crate::flow_ref::host::HostCall;
use crate::flow_ref::scalar::Fault;

/// A wrapper made: its Core and the function `w` in it.
pub struct Wrapped {
    pub module: Module,
    pub f: FnId,
}

/// The wrappers made so far, by their text (the key holds the callee, its module and its types, so two calls share a
/// wrapper only when the same text calls the same function).
#[derive(Default)]
pub struct Wrappers {
    built: RefCell<HashMap<String, Rc<Result<Wrapped, Fault>>>>,
}

impl Wrappers {
    /// The wrapper of the call: made at the first, then the same one. The `Err` of the outside is a call that cannot be
    /// written; the one inside is a wrapper that could not be made, kept as well.
    pub fn get(&self, call: &HostCall) -> Result<Rc<Result<Wrapped, Fault>>, Fault> {
        let text = source(call)?;
        let mut built = self.built.borrow_mut();
        Ok(built.entry(text).or_insert_with_key(|t| Rc::new(build(t))).clone())
    }
}

#[cfg(test)]
impl Wrappers {
    pub(super) fn len(&self) -> usize {
        self.built.borrow().len()
    }
}

/// The package: the `use` of a function of a module (a member of a type and a method need none), and `w`.
fn source(call: &HostCall) -> Result<String, Fault> {
    let (view, def) = (call.view, call.callee.def);
    if call.types.len() != call.args.len() {
        return Err(Fault::Internal("the types of a call are not as many as its arguments"));
    }
    let names: Vec<String> = (0..call.types.len()).map(|i| format!("a{i}")).collect();
    let params: Vec<String> =
        names.iter().zip(&call.types).map(|(n, t)| format!("{n}: {}", view.display_type(*t))).collect();
    let shown = view.shown_name(def);
    let (callee, import) = if call.callee.method {
        let bare = shown.rsplit('.').next().unwrap_or(&shown);
        (format!("a0.{bare}({})", names[1..].join(", ")), String::new())
    } else if shown.contains('.') {
        (format!("{shown}({})", names.join(", ")), String::new())
    } else {
        let path = [onsa_sema::STD_PACKAGE, view.module_path(def), &shown]
            .iter()
            .filter(|s| !s.is_empty())
            .copied()
            .collect::<Vec<_>>();
        (format!("{shown}({})", names.join(", ")), format!("use {}\n", path.join(".")))
    };
    Ok(format!("{import}rt fn w({}) -> {} {{ {callee} }}\n", params.join(", "), view.display_type(call.ret)))
}

pub(super) fn build(text: &str) -> Result<Wrapped, Fault> {
    let internal = Fault::Internal("a wrapper package that does not load or analyze");
    let mut loaded = Loaded::from_input(PackageInput::single_file("w.onsa", text)).map_err(|_| internal)?;
    let analyzed = analyze_loaded(&mut loaded).map_err(|_| internal)?;
    // E0302 (`cannot find P`) is a type of the user's package, which the package of the wrapper does not have; any other
    // first diagnostic is a wrapper text the checker refuses, a mistake of `source`.
    match analyzed.diagnostics.first().map(|d| d.code) {
        Some(Code::E0302) => return Err(Fault::Unavailable("a std function whose types name a type of the package")),
        Some(_) => {
            return Err(Fault::Unavailable("a wrapper package the checker refuses (not for a type of the user)"));
        }
        None => {}
    }
    let module = lower_core(&analyzed).map_err(|e| match e {
        LowerError::Internal(_) => Fault::Internal("a wrapper that stops the lowering on an internal error"),
        LowerError::Diagnostics(_) => Fault::Unavailable("a wrapper that does not lower"),
    })?;
    let at = module.fns.iter().position(|f| f.name == "w.w").ok_or(internal)?;
    Ok(Wrapped { f: FnId(at as u32), module })
}
