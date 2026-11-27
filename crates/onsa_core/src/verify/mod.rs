//! Verifier (T3-2): type and structure invariants of a Core module. The
//! driver runs it at every stage boundary (`onsa_driver::verify_core`, R-82).

use std::fmt;

use onsa_diag::Span;

use crate::ir::*;

mod ids;
mod types;

/// A rule of the verifier: its number in the list of `design/04-core.md`,
/// shown as `V-04`: the numbers that list has a row of (a work adds a
/// number with its row).
#[rustfmt::skip]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    V01 = 1, V02, V03, V04, V05, V06, V07, V08, V09, V10,
    V11, V12, V13, V14, V15, V16, V17, V18, V19, V20,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "V-{:02}", *self as u8)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifyError {
    pub rule: Rule,
    /// The `const` or the function the rule is broken in (for a table of
    /// the module, the part of it).
    pub fn_name: String,
    /// The node that breaks the rule, else its item; `None` for a table.
    pub span: Option<Span>,
    pub message: String,
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "core verify: {}: in `{}`: {}", self.rule, self.fn_name, self.message)
    }
}

impl std::error::Error for VerifyError {}

pub fn verify(m: &Module) -> Result<(), VerifyError> {
    ids::table(m)?;
    for c in &m.consts {
        let mut v = V {
            m,
            f: None,
            defined: Vec::new(),
            lets: Vec::new(),
            loops: 0,
            process: false,
            known: false,
            name: c.name.clone(),
            at: Some(c.init.span),
        };
        let t = v.expr(&c.init)?;
        v.same(t, c.ty, "const initializer")?;
    }
    // The generated `process` of each flow, marked once (V-19).
    let mut process = vec![false; m.fns.len()];
    for fl in &m.flows {
        if let Some(p) = fl.fns.process.and_then(|f| process.get_mut(f.0 as usize)) {
            *p = true;
        }
    }
    for (f, &process) in m.fns.iter().zip(&process) {
        let Some(body) = &f.body else { continue };
        let mut v = V {
            m,
            f: Some(f),
            defined: vec![false; f.locals.len()],
            lets: vec![false; f.locals.len()],
            loops: 0,
            process,
            known: false,
            name: f.name.clone(),
            at: Some(f.span),
        };
        for p in &f.params {
            v.same(v.local_ty(p.local)?, p.ty, "parameter")?;
            v.define(p.local)?;
        }
        if f.sret != v.tys_of(f.ret)?.is_aggregate(f.ret) {
            return Err(v.err(Rule::V14, "sret flag does not match the return type"));
        }
        // `onsa test` calls a test with nothing and keeps no value (§11.8).
        if f.test.is_some() && (!f.params.is_empty() || f.ret != Types::UNIT) {
            return Err(v.err(Rule::V01, "a test function with parameters or a value"));
        }
        let t = v.block(body)?;
        // V-18 (R-481): stored at the function's level, a local with a `let` below the top of the body.
        for &h in &f.hoisted {
            let top = body.stmts.iter().any(|s| matches!(s.kind, StmtKind::Let(l, _) if l == h));
            if top || !v.lets.get(h.0 as usize).is_some_and(|&b| b) {
                return Err(v.err(Rule::V18, format!("hoisted local {} has no `let` below the top of the body", h.0)));
            }
        }
        if !body.diverges() {
            match t {
                Some(t) => v.same(t, f.ret, "body value")?,
                None => v.same(Types::UNIT, f.ret, "body without a value")?,
            }
        }
    }
    Ok(())
}

struct V<'a> {
    m: &'a Module,
    f: Option<&'a FnDef>,
    defined: Vec<bool>,
    /// The locals a `let` defines.
    lets: Vec<bool>,
    loops: u32,
    /// The function is the `process` generated for a flow (`FlowFns::process`).
    process: bool,
    /// V-19 (S-196): an index `Bounds::Known` may be here, in the sample loop of a `process`.
    known: bool,
    name: String,
    /// The node being checked, the position of an error.
    at: Option<Span>,
}

type R<T> = Result<T, VerifyError>;

impl<'a> V<'a> {
    fn err(&self, rule: Rule, msg: impl Into<String>) -> VerifyError {
        VerifyError { rule, fn_name: self.name.clone(), span: self.at, message: msg.into() }
    }

    fn read_local(&self, l: LocalId) -> R<CTy> {
        let t = self.local_ty(l)?;
        if !self.defined[l.0 as usize] {
            let name = &self.f.unwrap().locals[l.0 as usize].name;
            return Err(self.err(Rule::V04, format!("local `{name}` read before definition")));
        }
        Ok(t)
    }

    fn define(&mut self, l: LocalId) -> R<()> {
        self.local_ty(l)?;
        self.defined[l.0 as usize] = true;
        Ok(())
    }

    /// V-19 (S-196): an index known in range is in the sample loop of a `process` only.
    fn bounds(&self, b: Bounds) -> R<()> {
        if b == Bounds::Known && !self.known {
            return Err(self.err(Rule::V19, "an index known in range outside the sample loop of `process`"));
        }
        Ok(())
    }
}
