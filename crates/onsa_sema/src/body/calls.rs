//! The calls of functions, methods and builtin associated functions, and
//! their arguments.

use super::*;

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
        if let ExprKind::TypeArgs { args, .. } = &self.expr(callee).kind {
            return Err(self.type_args_unsupported(args.span));
        }
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
        let value = matches!(kind, CallKind::Value { .. });
        // 1. Method call `recv.name(...)` when the base is a value.
        if !value && let ExprKind::Field { base, name } = &self.expr(callee).kind {
            let base = *base;
            let name = name.clone();
            let chain = self.name_chain(callee);
            let head_is_local = chain.as_ref().is_some_and(|c| self.is_local_head(&c[0].1.name));
            let resolved_fn = if head_is_local {
                None
            } else if let Some(c) = &chain {
                let path = Path { segments: c.iter().map(|(_, i)| i.clone()).collect(), span: self.expr(callee).span };
                match self.a.resolve_path(self.m, &path) {
                    Ok(en) => Some(en),
                    // A variant or an associated function of a struct or enum a
                    // syntax error cut (S-260): not known, no diagnostic.
                    Err(_) if self.a.through_partly_read(self.m, &path) => {
                        self.failed = true;
                        return Err(Stop);
                    }
                    // `util.f()` with no `use util` (R-39): the error of the
                    // whole path, with its candidate.
                    // A name held as an error (§18.1): no diagnostic.
                    Err(err @ (ResolveError::NeedsUse { .. } | ResolveError::Failed)) => {
                        return Err(self.resolve_error(&path, err));
                    }
                    Err(_) => {
                        // `Buf.zeroed`, `F32.from_bits`: builtin associated functions.
                        let prefix = Path {
                            segments: c[..c.len() - 1].iter().map(|(_, i)| i.clone()).collect(),
                            span: path.span,
                        };
                        if let Ok(Entity::Builtin(b)) = self.a.resolve_path(self.m, &prefix) {
                            return self.check_builtin_assoc_call(e, callee, b, &name, args, expected);
                        }
                        None
                    }
                }
            } else {
                None
            };
            match resolved_fn {
                Some(entity)
                    if matches!(
                        entity,
                        Entity::Def(_)
                            | Entity::Member(_)
                            | Entity::Variant(..)
                            | Entity::Builtin(Builtin::Some | Builtin::Ok | Builtin::Err)
                    ) =>
                {
                    return self.check_fn_call(e, callee, entity, &name, args, expected, kind);
                }
                Some(Entity::Module(_)) | Some(Entity::Builtin(_)) => {
                    let shown = self.src(self.expr(callee).span);
                    return Err(self.err(Code::E0401, self.expr(callee).span, format!("`{shown}` is not a function")));
                }
                _ => {}
            }
            let recv = self.check_expr(base, None)?;
            let recv = self.known(recv, self.expr(base).span, "receiver")?;
            return self.check_method_call(e, callee, recv, &name, args, expected, kind);
        }
        // 2. Named function, variant constructor, or prelude constructor.
        if !value
            && let ExprKind::Path(p) = &self.expr(callee).kind
            && p.segments.len() == 1
        {
            let name = p.segments[0].clone();
            if self.lookup_local(&name.name).is_none() && name.name != "self" {
                let path = Path { segments: vec![name.clone()], span: name.span };
                match self.a.resolve_path(self.m, &path) {
                    Ok(
                        entity @ (Entity::Def(_)
                        | Entity::Member(_)
                        | Entity::Variant(..)
                        | Entity::Builtin(Builtin::Some | Builtin::Ok | Builtin::Err)),
                    ) => {
                        return self.check_fn_call(e, callee, entity, &name, args, expected, kind);
                    }
                    Ok(_) => {
                        return Err(self.err(Code::E0401, name.span, format!("`{}` is not a function", name.name)));
                    }
                    Err(ResolveError::NotFound { .. }) => {
                        return Err(self.name_err(
                            Code::E0302,
                            name.span,
                            format!("cannot find `{}` in this scope", name.name),
                        ));
                    }
                    Err(err) => return Err(self.resolve_error(&path, err)),
                }
            }
        }
        // 3. A function value.
        let ft = self.check_expr(callee, None)?;
        let ft = self.known(ft, self.expr(callee).span, "callee")?;
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
        entity: Entity,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        match entity {
            Entity::Def(d) | Entity::Member(d) => {
                let def = self.a.def(d).clone();
                if self.a.heading_failed(d) {
                    return self.args_of_unknown_callee(args);
                }
                let DefKind::Fn(f) = &def.kind else {
                    if matches!(def.kind, DefKind::Unsupported) {
                        return Ok(self.a.types.error());
                    }
                    return Err(self.err(Code::E0401, name.span, format!("`{}` is not a function", def.name)));
                };
                if f.self_mode.is_some() {
                    return Err(self.err(
                        Code::E0401,
                        name.span,
                        format!("`{}` is a method; call it as `value.{}(...)` (§6.2)", def.name, def.name),
                    ));
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
                self.info.targets.insert(e, Target::Method { def: md, inst });
                let _ = kind;
                return Ok(ret);
            }
            if !matches!(self.a.def(d).kind, DefKind::Struct(_) | DefKind::Enum(_)) {
                return Ok(self.a.types.error());
            }
        }
        let Some(sig) = builtin::method(&mut self.a.types, recv, &name.name) else {
            if matches!(self.ty(recv), Ty::Error) {
                return Ok(recv);
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

    fn check_builtin_assoc_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        b: Builtin,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let _ = callee;
        let (scalar, generic) = match b {
            Builtin::Scalar(t) => (Some(t), None),
            Builtin::Generic(g) => (None, Some(g)),
            _ => (None, None),
        };
        let targ = self.fresh();
        let Some((params, ret)) = builtin::assoc_fn(&mut self.a.types, scalar, generic, &name.name, targ) else {
            let shown = self.src(self.expr(callee).span);
            return Err(self.err(Code::E0413, name.span, format!("`{shown}` does not exist")));
        };
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
        let recv = scalar.unwrap_or_else(|| self.a.builtin_key[&generic.unwrap()]);
        self.info
            .targets
            .insert(e, Target::BuiltinMethod { recv, name: name.name.clone(), bang: false, lazy_args: false });
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
