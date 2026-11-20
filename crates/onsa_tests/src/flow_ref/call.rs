//! The calls of the evaluator (§6.1, §6.2, §11.5): `f(x)`, `T.f(x)` and `x.m(y)`, and the construction of a variant
//! (`Some(x)`, which is a call to the syntax). The receiver and then the arguments are evaluated from the left (§3.5),
//! and the call is made after all of them. A function whose body is only expressions (`let`s and a value made of
//! names, literals, operators, `if`, `match`, calls and aggregates: way (a') of the memo) is evaluated here, with its
//! parameters bound; any other (a statement of a loop or a `var`, an `inout` or `move` parameter, a generic or a
//! `target` function) goes to the [`FnHost`] of the frame. A panic inside a function is at the
//! expression of its body that panics (§9.2: the calls it was in are `calls`, which a [`Stop`] does not keep), and a
//! call nested deeper than [`DEPTH`] panics at the call (§12.5).

use onsa_diag::Span;
use onsa_sema::{Target, TyId};
use onsa_syntax::ast::{Arg, ExprId, ExprKind, Mode};

use super::expr::{Eval, Frame, Stop, evaluates};
use super::host::{FnHost, HostCall, NoHost};
use super::scalar::{Fault, PanicKind};
use super::sema_view::{Body, Callee};
use super::value::Value;

/// §12.5: the calls one inside the other that an evaluation holds, the entry (a flow, a `const`) being 0. A `target`
/// function (`floor`) is a primitive, not a call, and is not counted.
pub const DEPTH: u32 = 128;

impl<'a> Frame<'a> {
    #[inline(never)]
    pub(super) fn call(&mut self, e: ExprId, callee: ExprId, args: &[Arg], at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        if self.body.time_call(e) {
            return self.stateful(e, at);
        }
        match self.body.target(e).map_err(here)? {
            Target::Variant { index, .. } => {
                let fields = args.iter().map(|a| self.eval(a.expr)).collect::<Result<_, _>>()?;
                return Ok(Value::Enum { tag: *index, fields });
            }
            // §9.2: at the call, and the text of the message (a literal, which is not evaluated) is not kept.
            Target::Panic => return Err(here(Fault::Panic(PanicKind::Explicit))),
            _ => {}
        }
        let func = self.body.callee(e).map_err(here)?;
        let mut vals = Vec::with_capacity(args.len() + 1);
        if func.method {
            let receiver = onsa_sema::receiver(self.body.ast, callee);
            vals.push(self.eval(receiver.ok_or(here(Fault::Internal("a method with no receiver")))?)?);
        }
        for a in args {
            vals.push(self.eval(a.expr)?);
        }
        self.invoke(&func, vals, e, at)
    }

    /// The value of `func` on `args`: the body evaluated here when it is plain, else what the host gives.
    #[inline(never)]
    pub(super) fn invoke(&mut self, func: &Callee<'a>, args: Vec<Value>, call: ExprId, at: Span) -> Eval {
        self.invoke_with(func, args, at, |f| {
            let types = parts(&f.body, call).into_iter().map(|x| f.body.ty_id(x)).collect::<Result<_, _>>()?;
            Ok((types, f.body.ty_id(call)?))
        })
    }

    /// `invoke` of a call that is no expression of the body (`T.default()` of a type that has it written by hand): `signature` is
    /// the types of the arguments and of the result that a host is given, asked for only when the host is.
    #[inline(never)]
    pub(super) fn invoke_with(
        &mut self,
        func: &Callee<'a>,
        args: Vec<Value>,
        at: Span,
        signature: impl FnOnce(&Self) -> Result<(Vec<TyId>, TyId), Fault>,
    ) -> Eval {
        let here = |fault| Stop { fault, at };
        if self.depth() >= DEPTH && !func.primitive() {
            return Err(here(Fault::Panic(PanicKind::Depth)));
        }
        let Some((body, expr)) = self.plain(func).map_err(here)? else {
            let (types, ret) = signature(self).map_err(here)?;
            let call = HostCall { view: self.body.view, callee: func, args, types, ret };
            return match self.host.as_deref_mut() {
                Some(host) => host.call(call),
                None => NoHost.call(call),
            }
            .map_err(here);
        };
        let params = body.params(func.func).map_err(here)?;
        if params.len() != args.len() {
            return Err(here(Fault::Internal("arguments that are not the parameters of the function")));
        }
        let locals = params.into_iter().zip(args).filter_map(|(local, v)| Some((local?, v))).collect();
        self.run_callee(body, locals, expr)
    }

    /// The body of `func` and its value expression when the evaluator evaluates it itself.
    fn plain(&self, func: &Callee<'a>) -> Result<Option<(Body<'a>, ExprId)>, Fault> {
        let f = func.func;
        // A std function is the host's whole (its body calls `target` functions that are private to its module).
        let mine = !func.primitive() && f.generics.is_empty() && !self.body.view.in_std(func.def);
        let by_value = f.self_mode.is_none_or(|m| m == Mode::Borrow) && f.params.iter().all(|p| p.mode == Mode::Borrow);
        let Some(expr) = f.body.filter(|_| mine && by_value) else { return Ok(None) };
        let body = self.body.view.body(func.def)?;
        let known = self.plain.borrow().get(&func.def).copied();
        let ok = known.unwrap_or_else(|| {
            let ok = evaluated(&body, expr);
            self.plain.borrow_mut().insert(func.def, ok);
            ok
        });
        Ok(ok.then_some((body, expr)))
    }
}

/// What the evaluator evaluates in `e` (not `e` itself): a call evaluates its receiver and arguments and not its callee, a
/// `panic` not even its message, and a name that is a path (`F32.PI`) not its base.
pub(super) fn parts(body: &Body, e: ExprId) -> Vec<ExprId> {
    let ast = body.ast;
    match (&ast.expr(e).kind, body.target(e)) {
        (ExprKind::Call { .. }, Ok(Target::Panic)) => vec![],
        (ExprKind::Call { callee, args, .. }, target) => {
            let receiver = onsa_sema::receiver(ast, *callee).filter(|_| matches!(target, Ok(Target::Method { .. })));
            receiver.into_iter().chain(args.iter().map(|a| a.expr)).collect()
        }
        (ExprKind::Field { .. }, _) if body.names(e) => vec![],
        _ => ast.sub_exprs(e),
    }
}

/// Does the evaluator evaluate `e` and what it evaluates in it ([`evaluates`] of each, [`parts`])?
pub(super) fn evaluated(body: &Body, e: ExprId) -> bool {
    evaluates(body, e) && parts(body, e).into_iter().all(|x| evaluated(body, x))
}

impl<'a> Frame<'a> {
    /// `T.default()` of a type whose `Default` is written by hand (§6.4): its `default` function, called with no argument (evaluated here
    /// when its body is plain, else handed to the host).
    pub(super) fn hand_default(&mut self, def: onsa_sema::DefId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let view = self.body.view;
        let (f, ret) = view.hand_default(def).map_err(here)?;
        let func = view.fn_callee(f).map_err(here)?;
        self.invoke_with(&func, Vec::new(), at, |_| Ok((Vec::new(), ret)))
    }
}
