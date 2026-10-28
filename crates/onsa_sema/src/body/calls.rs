//! The calls of functions, methods and builtin associated functions, and
//! their arguments.

use super::*;
use crate::names::body::PathRes;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ calls

    pub(super) fn check_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        kind: CallKind,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        if self.flow.is_some()
            && let Some(t) = self.check_flow_call(e, callee, kind, args, expected)?
        {
            return Ok(t);
        }
        if kind == CallKind::Flow {
            // The `~` comes right after the callee (`f~(`, §2.6).
            let at = self.expr(callee).span.end;
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Types,
                    Code::E0812,
                    span,
                    "`~(` creates a flow instance and is only written inside a flow body (§11.5)",
                )
                .with_found(self.src(span))
                .with_fix(Fix::delete("remove `~`", Span::new(span.file, at, at + 1))),
            ));
        }
        // `v.(x)` (§6.1, S-191): the callee is a value, whatever its form;
        // the names stage tells `inc.(1)` of an item from it (W4-12).
        if !matches!(kind, CallKind::Value { .. }) {
            // 1. A function, a variant or a constructor of the prelude, or
            // an associated function of a builtin type, as the names stage
            // resolved the callee.
            let cspan = self.expr(callee).span;
            match self.names.paths.get(&callee).cloned() {
                Some(PathRes::Item { entity, owner }) => {
                    let name = self.last_name(callee);
                    return match entity {
                        Entity::Builtin(Builtin::Panic) => Err(self.unsupported(name.span, Feature::Panic, &[])),
                        // `None`, which takes no value (what is neither a value
                        // nor a flow is the names stage's E0308).
                        Entity::Builtin(Builtin::None) => {
                            let shown = self.src(cspan);
                            Err(self.err(Code::E0401, cspan, format!("`{shown}` is not a function")))
                        }
                        _ => self.check_fn_call(e, callee, (entity, owner), &name, args, expected, kind),
                    };
                }
                Some(PathRes::BuiltinAssoc { ty, owner, .. }) => {
                    let name = self.last_name(callee);
                    return self.check_builtin_assoc_call(e, callee, (ty, owner), &name, args, expected);
                }
                _ => {}
            }
            // 2. A method `recv.name(...)` of the value before it.
            if let ExprKind::Field { base, name } = &self.expr(callee).kind {
                let (base, name) = (*base, name.clone());
                // After a constructor of the prelude (`Some.x()`): an
                // associated function that is none, in the words of
                // `check_builtin_assoc_call` (`panic.x()` is E0200, S-713).
                if let Some(PathRes::Item { entity: Entity::Builtin(b), .. }) = self.names.paths.get(&base)
                    && *b != Builtin::Panic
                {
                    return Err(self.err(Code::E0413, name.span, format!("`{}` does not exist", self.src(cspan))));
                }
                let recv = self.check_expr(base, None)?;
                let recv = self.known(recv, self.expr(base).span, "receiver")?;
                return self.check_method_call(e, callee, recv, &name, args, expected, kind);
            }
        }
        // 3. A function value.
        let ft = self.check_expr(callee, None)?;
        let ft = self.known(ft, self.expr(callee).span, "callee")?;
        // A value of the error type: an unknown callee (§18.1, R-271).
        if matches!(self.ty(ft), Ty::Error) {
            return self.args_of_unknown_callee(args);
        }
        let Ty::Fn(f) = self.ty(ft) else {
            let shown = self.display(ft);
            return Err(self.err(
                Code::E0401,
                self.expr(callee).span,
                format!("`{shown}` is not a function and cannot be called"),
            ));
        };
        if kind == CallKind::Bang {
            // The `!` comes right after the callee (`f!(`, §2.6).
            let at = self.expr(callee).span.end;
            return Err(self.diag(
                Diagnostic::new(Stage::Types, Code::E0714, span, "`!` marks `inout self` method calls only (§5.2)")
                    .with_found(self.src(span))
                    .with_fix(Fix::delete("remove `!`", Span::new(span.file, at, at + 1))),
            ));
        }
        self.info.targets.insert(e, Target::Value);
        self.check_args(args, &f.params, span)?;
        Ok(f.ret)
    }

    #[allow(clippy::too_many_arguments)]
    fn check_fn_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        (entity, owner): (Entity, Option<TyId>),
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        match entity {
            Entity::Def(d) | Entity::Member(d) => {
                let def = self.a.def(d).clone();
                if self.a.heading_failed(d) || crate::names::self_outside_impl(self.a, entity) {
                    return self.args_of_unknown_callee(args);
                }
                let DefKind::Fn(f) = &def.kind else {
                    if matches!(def.kind, DefKind::Unsupported(_)) {
                        return Ok(self.a.types.error());
                    }
                    return Err(self.err(Code::E0401, name.span, format!("`{}` is not a function", def.name)));
                };
                if f.self_mode.is_some() {
                    onsa_diag::internal::bug(Some(name.span), "a method in the function form the names stage took");
                }
                if kind == CallKind::Bang {
                    let at = self.expr(callee).span.end;
                    return Err(self.diag(
                        Diagnostic::new(
                            Stage::Types,
                            Code::E0714,
                            span,
                            "`!` marks `inout self` method calls only (§5.2)",
                        )
                        .with_found(self.src(span))
                        .with_fix(Fix::delete("remove `!`", Span::new(span.file, at, at + 1))),
                    ));
                }
                let targs = self.fresh_args(d);
                self.of_owner(d, &targs, owner, span)?;
                let params: Vec<(Mode, TyId)> = f.params.iter().map(|p| (p.mode, self.subst(p.ty, &targs))).collect();
                let ret = self.subst(f.ret, &targs);
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                let inst = self.finish_instance(d, targs, span)?;
                self.info.targets.insert(e, Target::Fn { def: d, inst });
                let fty = self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects.clone() }));
                self.record(callee, fty);
                Ok(ret)
            }
            Entity::Variant(d, i) => {
                let targs = self.fresh_args(d);
                self.of_owner(d, &targs, owner, span)?;
                let variant = self.a.def(d).as_enum().unwrap().variants[i as usize].clone();
                if variant.fields.is_empty() {
                    return Err(self.err(
                        Code::E0412,
                        span,
                        format!("`{}` is a unit variant and takes no arguments", variant.name),
                    ));
                }
                let params: Vec<(Mode, TyId)> =
                    variant.fields.iter().map(|&f| (Mode::Borrow, self.subst(f, &targs))).collect();
                let ret = self.a.types.intern(Ty::Named(d, targs.clone()));
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                self.finish_instance(d, targs, span)?;
                self.info.targets.insert(e, Target::Variant { def: d, index: i });
                Ok(ret)
            }
            Entity::Builtin(b) => {
                let ret = self.prelude_ctor(b, span);
                let t = match self.ty(ret) {
                    Ty::Builtin(BuiltinTy::Result, a) if b == Builtin::Err => a[1],
                    Ty::Builtin(_, a) => a[0],
                    _ => unreachable!("a prelude constructor makes an `Option` or a `Result`"),
                };
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &[(Mode::Borrow, t)], span)?;
                self.info.targets.insert(e, Target::Prelude(b));
                Ok(ret)
            }
            Entity::Module(_) => unreachable!(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_method_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        recv: TyId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let _ = callee;
        if let Ty::Named(d, targs_recv) = self.ty(recv) {
            let assoc = self.a.modules.assoc.get(&d).and_then(|m| m.get(&name.name)).copied();
            if let Some(md) = assoc {
                if self.a.heading_failed(md) {
                    return self.args_of_unknown_callee(args);
                }
                let mdef = self.a.def(md).clone();
                if let Err(err) = self.a.modules.member_reach(self.a.def(d), &mdef, name, self.m) {
                    return Err(self.diag(err.into_diagnostic()));
                }
                let DefKind::Fn(f) = &mdef.kind else {
                    return Err(self.err(Code::E0413, name.span, format!("`{}` is not a method", name.name)));
                };
                if f.self_mode.is_none() {
                    let tname = self.a.def(d).name.clone();
                    return Err(self.err(
                        Code::E0413,
                        name.span,
                        format!(
                            "`{}` is an associated function; call it as `{tname}.{}(...)` (§6.2)",
                            name.name, name.name
                        ),
                    ));
                }
                let targs = self.fresh_args(md);
                // The impl's own generic arguments come from the receiver.
                let impl_self = mdef.owner.and_then(|o| match &self.a.def(o).kind {
                    DefKind::Impl(i) => Some(i.self_ty),
                    _ => None,
                });
                if let Some(st) = impl_self {
                    let st2 = self.subst(st, &targs);
                    self.unify_at(name.span, recv, st2)?;
                }
                let _ = targs_recv;
                let params: Vec<(Mode, TyId)> = f.params.iter().map(|p| (p.mode, self.subst(p.ty, &targs))).collect();
                let ret = self.subst(f.ret, &targs);
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                let inst = self.finish_instance(md, targs, span)?;
                self.a.note_use(self.a.def(md).name_span, name.span);
                self.info.targets.insert(e, Target::Method { def: md, inst });
                let _ = kind;
                return Ok(ret);
            }
            if !matches!(self.a.def(d).kind, DefKind::Struct(_) | DefKind::Enum(_)) {
                return Ok(self.a.types.error());
            }
        }
        let Some(sig) = builtin::method(&mut self.a.types, recv, &name.name) else {
            // A receiver of the error type, or of a type parameter with an
            // unknown bound (§18.1, S-689, R-271): an unknown method.
            if self.traits_unknown(recv) {
                return self.args_of_unknown_callee(args);
            }
            let shown = self.display(recv);
            return Err(self.err(Code::E0413, name.span, format!("`{shown}` has no method `{}`", name.name)));
        };
        let params: Vec<(Mode, TyId)> = sig.params.iter().map(|&t| (Mode::Borrow, t)).collect();
        if let Some(exp) = expected {
            self.unify_at(span, sig.ret, exp)?;
        }
        self.check_args(args, &params, span)?;
        self.info.targets.insert(
            e,
            Target::BuiltinMethod { recv, name: name.name.clone(), bang: sig.bang, lazy_args: sig.lazy_args },
        );
        Ok(sig.ret)
    }

    /// `Buf.zeroed(4)`, `F32.from_bits(b)`: an associated function of the
    /// builtin type `ty` (a generic one by its key, `Analysis::builtin_key`),
    /// whose type argument the type an alias names it by decides (`owner`,
    /// `Samples.zeroed(n)` of `type Samples = Buf[F32]`, §4.4).
    fn check_builtin_assoc_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        (ty, owner): (TyId, Option<TyId>),
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let (scalar, generic) = match self.ty(ty) {
            Ty::Builtin(g, _) => (None, Some(g)),
            _ => (Some(ty), None),
        };
        let targ = self.fresh();
        let Some((params, ret)) = builtin::assoc_fn(&mut self.a.types, scalar, generic, &name.name, targ) else {
            let shown = self.src(self.expr(callee).span);
            return Err(self.err(Code::E0413, name.span, format!("`{shown}` does not exist")));
        };
        if let Some(o) = owner
            && let Ty::Builtin(_, of) = self.ty(o)
            && let Some(&arg) = of.first()
        {
            self.unify_at(span, targ, arg)?;
        }
        if let Some(g) = generic {
            // `Buf.zeroed(4)`: the element type may be decided later (§4.7, S-226), and
            // it must be Copy (§4.5), a kind constraint checked when it is (S-235).
            let what = format!("the element type of `{}`", self.src(self.expr(callee).span));
            self.defer(span, targ, DeferredKind::Origin { what });
            if matches!(g, BuiltinTy::Buf | BuiltinTy::Span) {
                self.defer(span, targ, DeferredKind::Require { bound: Bound::Copy, what: Required::BufElement });
            }
        }
        if let Some(exp) = expected {
            self.unify_at(span, ret, exp)?;
        }
        let params: Vec<(Mode, TyId)> = params.into_iter().map(|t| (Mode::Borrow, t)).collect();
        self.check_args(args, &params, span)?;
        self.info
            .targets
            .insert(e, Target::BuiltinMethod { recv: ty, name: name.name.clone(), bang: false, lazy_args: false });
        Ok(ret)
    }

    /// Arity and argument types. `Span[T]` parameters accept `[T; N]`,
    /// `Buf[T]` and `Span[T]` (§5.3); `[Span[T]; N]` accepts the planar forms.
    /// The arguments of a call of a function whose heading a syntax error
    /// cut (S-59): each is checked on its own (its errors are the caller's),
    /// and the call is an error, with no diagnostic of its own (R-71).
    pub(crate) fn args_of_unknown_callee(&mut self, args: &[Arg]) -> R<TyId> {
        let error = self.a.types.error();
        for arg in args {
            self.check_expr(arg.expr, Some(error))?;
        }
        Ok(error)
    }

    pub(crate) fn check_args(&mut self, args: &[Arg], params: &[(Mode, TyId)], span: Span) -> R<()> {
        if args.len() != params.len() {
            return Err(self.err(
                Code::E0412,
                span,
                format!("this call takes {} argument(s) but {} were given", params.len(), args.len()),
            ));
        }
        for (arg, (_, pt)) in args.iter().zip(params) {
            let pt = *pt;
            let ps = self.shallow(pt);
            let coerce = match self.ty(ps) {
                Ty::Builtin(BuiltinTy::Span, a) => Some((a[0], None)),
                Ty::Array(inner, len) => match self.ty(self.shallow(inner)) {
                    Ty::Builtin(BuiltinTy::Span, a) => Some((a[0], Some(len))),
                    _ => None,
                },
                _ => None,
            };
            match coerce {
                None => {
                    let callee = self.src(span);
                    let callee = callee.split('(').next().unwrap_or("").trim().to_string();
                    self.with_why(format!("an argument of `{callee}`"), pt, |ck| ck.check_expr(arg.expr, Some(pt)))?;
                }
                Some((elem, planar)) => {
                    let at = self.check_expr(arg.expr, None)?;
                    let at_s = self.known(at, self.expr(arg.expr).span, "argument")?;
                    let aspan = self.expr(arg.expr).span;
                    let cause = self.cause(aspan, None);
                    let ok = match (planar, self.ty(at_s)) {
                        (None, Ty::Array(el, _)) => self.infer.unify(&mut self.a.types, el, elem, &cause).is_ok(),
                        (None, Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a)) => {
                            self.infer.unify(&mut self.a.types, a[0], elem, &cause).is_ok()
                        }
                        (Some(n), Ty::Array(ch, m)) => {
                            let lens_ok =
                                self.infer.shallow_len(&self.a.types, n) == self.infer.shallow_len(&self.a.types, m);
                            lens_ok
                                && match self.ty(self.shallow(ch)) {
                                    Ty::Array(el, _) => self.infer.unify(&mut self.a.types, el, elem, &cause).is_ok(),
                                    Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a) => {
                                        self.infer.unify(&mut self.a.types, a[0], elem, &cause).is_ok()
                                    }
                                    _ => false,
                                }
                        }
                        (_, Ty::Error) => true,
                        _ => false,
                    };
                    if !ok {
                        let (ps_s, as_s) = (self.display(pt), self.display(at));
                        return Err(self.err(
                            Code::E0401,
                            aspan,
                            format!(
                                "expected `{ps_s}` (or an array / `Buf` of the same element), found `{as_s}` (§5.3)"
                            ),
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}
