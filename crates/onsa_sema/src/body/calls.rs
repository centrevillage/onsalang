//! The calls of functions and methods, and their arguments.

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
        // Outside a flow body a `~(` is the names stage's E0821 (§11.1).
        if kind == CallKind::Flow {
            onsa_diag::internal::bug(Some(span), "a `~(` the names stage did not stop at");
        }
        // `v.(x)` (§6.1, S-191): the callee is a value, whatever its form;
        // the names stage tells `inc.(1)` of an item from it (E0020).
        if !matches!(kind, CallKind::Value { .. }) {
            // 1. A function (an associated one of a builtin type is std's,
            // `Buf.zeroed`), a variant or a constructor of the prelude, as
            // the names stage resolved the callee.
            let cspan = self.expr(callee).span;
            if let Some(PathRes::Item { entity, owner }) = self.names.paths.get(&callee).cloned() {
                let name = self.last_name(callee);
                return match entity {
                    Entity::Builtin(Builtin::Panic) => Err(self.unsupported(name.span, Feature::Panic, &[])),
                    // `None`, which takes no value (what is neither a value
                    // nor a flow is the names stage's E0308): the branch
                    // of the builtin `None` until W5-03 makes it a variant.
                    Entity::Builtin(Builtin::None) => Err(self.unit_variant_called(e, callee, kind, args)),
                    _ => self.check_fn_call(e, callee, (entity, owner), &name, args, expected, kind),
                };
            }
            // 2. A method `recv.name(...)` of the value before it.
            if let ExprKind::Field { base, name } = &self.expr(callee).kind {
                let (base, name) = (*base, name.clone());
                // After a constructor of the prelude (`Some.x()`): an
                // associated function that is none (`panic.x()` is E0200,
                // S-713).
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
        let ft = self.known_shape(ft, self.expr(callee).span, "callee")?;
        // A value of the error type: an unknown callee (§18.1, R-271).
        if matches!(self.ty(ft), Ty::Error) {
            return self.args_of_unknown_callee(args);
        }
        let Ty::Fn(f) = self.ty(ft) else {
            let shown = self.described(ft);
            return Err(self.err(
                Code::E0401,
                self.expr(callee).span,
                format!("{shown} is not a function and cannot be called"),
            ));
        };
        if kind == CallKind::Bang {
            // The `!` comes right after the callee (`h!(`, §2.6), and a
            // function value is called with `.(` (§5.2, S-812).
            let at = self.expr(callee).span.end;
            let dot = onsa_diag::Edit::replace(Span::new(span.file, at, at + 1), ".");
            return Err(self.diag(
                Diagnostic::new(Stage::Types, Code::E0714, span, BANG_ON_NO_INOUT_SELF)
                    .with_found(self.src(span))
                    .with_fix(Fix::new("call the function value with `.(`", vec![dot])),
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
                        Diagnostic::new(Stage::Types, Code::E0714, span, BANG_ON_NO_INOUT_SELF)
                            .with_found(self.src(span))
                            .with_fix(Fix::delete("remove `!`", Span::new(span.file, at, at + 1))),
                    ));
                }
                let targs = self.fresh_args(d);
                self.of_owner(d, &targs, owner, span)?;
                let params: Vec<(Mode, TyId)> =
                    f.params.iter().map(|p| (p.mode, self.a.types.subst(p.ty, &targs))).collect();
                let ret = self.a.types.subst(f.ret, &targs);
                // A conversion is judged by its source, which is not in its
                // result, before the result meets `expected` (§3.3, S-231).
                let conversion = crate::prim::conversion_target(self.a, d);
                if let (Some(exp), None) = (expected, conversion) {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                if let Some(to) = conversion {
                    self.conversion_use(name.span, targs[0], to)?;
                    if let Some(exp) = expected {
                        self.unify_at(span, ret, exp)?;
                    }
                }
                // Of std's `impl` of `Buf` (`Buf.zeroed`), the requirements
                // are its element's (§4.5), as of a `Buf` written (R-351).
                let element = self.a.self_ty_of(d).filter(|&t| matches!(self.ty(t), Ty::Builtin(BuiltinTy::Buf, _)));
                let element = element.map(|_| Required::BufElement(BuiltinTy::Buf));
                let inst = self.instance(d, targs, span, element)?;
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
                    return Err(self.unit_variant_called(e, callee, kind, args));
                }
                let params: Vec<(Mode, TyId)> =
                    variant.fields.iter().map(|&f| (Mode::Borrow, self.a.types.subst(f, &targs))).collect();
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
        let (key, owner, this) = self.method_key(recv, &name.name);
        let table = match owner {
            Some(d) => self.a.modules.assoc.get(&d),
            None => key.and_then(|k| self.a.modules.assoc_builtin.get(&k)),
        };
        if table.is_some() || owner.is_some() {
            // Of an E0304, an unknown callee too (§18.1, S-737).
            let Ok(assoc) = self.a.modules.assoc_member(table, &name.name) else {
                return self.args_of_unknown_callee(args);
            };
            if let Some(md) = assoc {
                if self.a.heading_failed(md) {
                    return self.args_of_unknown_callee(args);
                }
                let mdef = self.a.def(md).clone();
                let reach = match owner {
                    Some(d) => self.a.modules.member_reach(self.a.def(d), &mdef, name, self.m),
                    None => self.a.modules.builtin_reach(&mdef, name, self.m),
                };
                if let Err(err) = reach {
                    return Err(self.diag(err.into_diagnostic()));
                }
                let DefKind::Fn(f) = &mdef.kind else {
                    return Err(self.err(Code::E0413, name.span, format!("`{}` is not a method", name.name)));
                };
                if f.self_mode.is_none() {
                    let tname = self.type_head(recv);
                    return Err(self.err(
                        Code::E0413,
                        name.span,
                        format!(
                            "`{}` is an associated function; call it as `{tname}.{}(...)` (§6.2)",
                            name.name, name.name
                        ),
                    ));
                }
                if f.self_mode == Some(Mode::Inout) {
                    self.inout_receiver(callee)?;
                }
                let targs = self.fresh_args(md);
                // The impl's own generic arguments come from the receiver; of
                // std's `impl` of a sequence, its element (S-853).
                let mut element = None;
                if let Some(st) = self.a.self_ty_of(md) {
                    if matches!(self.ty(st), Ty::Array(..) | Ty::Builtin(BuiltinTy::Span, _)) {
                        element = Some(Required::SeqElement { recv: self.display(recv), method: name.name.clone() });
                    }
                    let st2 = self.a.types.subst(st, &targs);
                    self.unify_at(name.span, this, st2)?;
                }
                let params: Vec<(Mode, TyId)> =
                    f.params.iter().map(|p| (p.mode, self.a.types.subst(p.ty, &targs))).collect();
                let ret = self.a.types.subst(f.ret, &targs);
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                let inst = self.instance(md, targs, span, element)?;
                self.a.note_use(self.a.def(md).name_span, name.span);
                self.info.targets.insert(e, Target::Method { def: md, inst });
                let _ = kind;
                return Ok(ret);
            }
            if owner.is_some_and(|d| !matches!(self.a.def(d).kind, DefKind::Struct(_) | DefKind::Enum(_))) {
                return Ok(self.a.types.error());
            }
        }
        let Some(sig) = builtin::method(&mut self.a.types, recv, &name.name) else {
            // A receiver of the error type, or of a type parameter with an
            // unknown bound (§18.1, S-689, R-271): an unknown method.
            if self.traits_unknown(recv) {
                return self.args_of_unknown_callee(args);
            }
            return Err(self.removed_method(e, recv, name, args, expected, kind));
        };
        let params: Vec<(Mode, TyId)> = sig.params.iter().map(|&t| (Mode::Borrow, t)).collect();
        if let Some(exp) = expected {
            self.unify_at(span, sig.ret, exp)?;
        }
        self.check_args(args, &params, span)?;
        let (self_mode, lazy_args) = (sig.self_mode, sig.lazy_args);
        self.info.targets.insert(e, Target::BuiltinMethod { name: name.name.clone(), self_mode, lazy_args });
        Ok(sig.ret)
    }

    /// Where the method `name` of a receiver of the type `recv` is looked
    /// up: the key of the `impl`s of a builtin type, the owner of a user
    /// type, and the type its `self` stands for. The one lookup of the
    /// method calls and of the candidates of their E0413 (`removed.rs`).
    pub(super) fn method_key(&mut self, recv: TyId, name: &str) -> (Option<TyId>, Option<DefId>, TyId) {
        // The members of the `impl`s of the head of the receiver's type: of a
        // user type, of a scalar (std's, §3.3, §3.4) the same way (§6.2), of
        // an array and of a generic builtin type (std's, §4.2, §5.3, §9.1).
        let span_key = self.a.builtin_key.get(&BuiltinTy::Span).copied();
        let (mut key, owner) = match self.ty(recv) {
            Ty::Named(d, _) => (None, Some(d)),
            Ty::Int(k) => (Some(self.a.types.int(k)), None),
            Ty::Float(k) => (Some(self.a.types.float(k)), None),
            Ty::Array(..) => (self.a.array_key, None),
            Ty::Builtin(b, _) => (self.a.builtin_key.get(&b).copied(), None),
            _ => (None, None),
        };
        // §5.3: an array and a `Buf` take from `Span[T]` the methods their
        // own `impl`s (and the `len` of an array) have not, as a `Span` of
        // their element `T`: one step, `Span` takes from none.
        let mut this = recv;
        if let Some(elem) = self.viewed_element(recv)
            && !key.and_then(|k| self.a.modules.assoc_builtin.get(&k)).is_some_and(|t| t.contains_key(name))
            && builtin::method_self(&self.a.types, recv, name).is_none()
        {
            key = span_key;
            this = self.a.types.intern(Ty::Builtin(BuiltinTy::Span, vec![elem]));
        }
        (key, owner, this)
    }

    /// The element of an array or a `Buf` of the type `t`, which takes the
    /// members of `Span` (§5.3, [`builtin::takes_span_members`]).
    fn viewed_element(&self, t: TyId) -> Option<TyId> {
        match self.ty(t) {
            Ty::Array(elem, _) => Some(elem),
            Ty::Builtin(b, args) if builtin::takes_span_members(b) => args.first().copied(),
            _ => None,
        }
    }

    /// E0412 for the unit variant called by `e` (§4.4, S-514). With no
    /// argument and nothing but blanks between its parentheses (a comment
    /// stays, §18.1), the candidate takes them out; else a note says that it
    /// is written as a value.
    fn unit_variant_called(&mut self, e: ExprId, callee: ExprId, kind: CallKind, args: &[Arg]) -> Stop {
        let (span, cspan) = (self.expr(e).span, self.expr(callee).span);
        let message = format!("`{}` is a unit variant and takes no arguments", self.last_name(callee).name);
        let d = Diagnostic::new(Stage::Types, Code::E0412, span, message).with_found(self.src(span));
        let parens = Span { start: cspan.end, ..span };
        let inside = self.src(Span { start: parens.start + 1, end: parens.end - 1, ..span });
        let d = match kind == CallKind::Plain && args.is_empty() && inside.trim().is_empty() {
            true => d.with_fix(Fix::delete("remove the parentheses", parens)),
            false => {
                d.with_rule(format!("a unit variant is a value, written without `(…)` (`{}`, §4.4)", self.src(cspan)))
            }
        };
        self.diag(d)
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
        for (arg, &(mode, pt)) in args.iter().zip(params) {
            let ps = self.shallow(pt);
            let coerce = match self.ty(ps) {
                Ty::Builtin(BuiltinTy::Span, a) => Some((a[0], None)),
                Ty::Array(inner, len) => match self.ty(self.shallow(inner)) {
                    Ty::Builtin(BuiltinTy::Span, a) => Some((a[0], Some(len))),
                    _ => None,
                },
                _ => None,
            };
            let planar = matches!(coerce, Some((_, Some(_))));
            match coerce {
                None => {
                    let callee = self.src(span);
                    let callee = callee.split('(').next().unwrap_or("").trim().to_string();
                    self.with_why(format!("an argument of `{callee}`"), pt, |ck| ck.check_expr(arg.expr, Some(pt)))?;
                }
                Some((elem, planar)) => {
                    let aspan = self.expr(arg.expr).span;
                    let at = match (planar, &self.expr(self.ast.without_parens(arg.expr)).kind) {
                        (Some(_), ExprKind::Array(parts)) if !parts.is_empty() => {
                            self.planar_literal(arg.expr, parts, elem)?
                        }
                        _ => self.check_expr(arg.expr, None)?,
                    };
                    // A literal variable is passed as no `Span` (S-860).
                    let at_s = self.known_shape(at, aspan, "argument")?;
                    let ok = match (planar, self.ty(at_s)) {
                        // A length unified, as of any array (a const parameter `N`).
                        (Some(n), Ty::Array(ch, m)) => {
                            let cause = self.cause(aspan, None);
                            self.infer.unify_len(&mut self.a.types, n, m, &cause).is_ok() && self.views(ch, elem, aspan)
                        }
                        (Some(_), Ty::Error) => true,
                        (Some(_), _) => false,
                        (None, _) => self.views(at_s, elem, aspan),
                    };
                    if !ok {
                        return Err(self.not_a_view(aspan, pt, at));
                    }
                }
            }
            if mode == Mode::Inout && !self.inout_place(arg.expr, planar) {
                return Err(self.no_inout_place(arg.expr, "an `inout` argument", "§5.1"));
            }
        }
        Ok(())
    }

    /// Whether a value of the type `t` is passed as a `Span[elem]` (§5.3):
    /// an array, a `Buf` or a `Span` of the element (the error type too).
    fn views(&mut self, t: TyId, elem: TyId, at: Span) -> bool {
        let cause = self.cause(at, None);
        match self.ty(self.shallow(t)) {
            Ty::Array(el, _) => self.infer.unify(&mut self.a.types, el, elem, &cause).is_ok(),
            Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a) => {
                self.infer.unify(&mut self.a.types, a[0], elem, &cause).is_ok()
            }
            Ty::Error => true,
            _ => false,
        }
    }

    /// The type of the planar literal `e` (`[a, b]` at `[Span[elem]; N]`,
    /// S-196, §5.3): each element is passed as a `Span` of its own, of any
    /// kind and length, so `[Span[elem]; k]` (`k` checked against `N` by the
    /// caller), recorded through the parentheses. The lowering converts each
    /// element (`coerce`).
    fn planar_literal(&mut self, e: ExprId, parts: &[ExprId], elem: TyId) -> R<TyId> {
        let view = self.a.types.intern(Ty::Builtin(BuiltinTy::Span, vec![elem]));
        for &x in parts {
            let (t, at) = (self.check_expr(x, None)?, self.expr(x).span);
            if !self.views(t, elem, at) {
                return Err(self.not_a_view(at, view, t));
            }
        }
        let t = self.a.types.intern(Ty::Array(view, Len::Const(parts.len() as u32)));
        let mut x = e;
        loop {
            self.record(x, t);
            match self.expr(x).kind {
                ExprKind::Paren(inner) => x = inner,
                _ => return Ok(t),
            }
        }
    }

    /// E0401: `found` at `at` is passed where `want`, a `Span` or a planar
    /// array of them, is (§5.3); a literal variable as `an integer` or `a
    /// float` ([`Checker::described`], S-860), another type not known yet
    /// (`[]`) as written (§18.1: no variable of the inference in a message).
    fn not_a_view(&mut self, at: Span, want: TyId, found: TyId) -> Stop {
        let open = self.infer.lit_of(&self.a.types, found).is_none() && self.infer.has_vars(&self.a.types, found);
        let want = self.display(want);
        let found = if open { format!("`{}`", self.src(at)) } else { self.described(found) };
        let msg = format!("expected `{want}` (or an array / `Buf` of the same element), found {found} (§5.3)");
        self.err(Code::E0401, at, msg)
    }

    /// Whether `e` can be passed as `inout` (§5.1, §5.3, S-178): a place, a
    /// partial view of one ([`view_base`]), and in a planar argument an array
    /// literal of those (`inout [a, b]`). The modes take the views and the
    /// literals from W4-08.
    fn inout_place(&self, e: ExprId, planar: bool) -> bool {
        let e = self.ast.without_parens(e);
        if let Some(base) = view_base((self.ast, &self.info, self.a), e, |t| self.shallow(t)) {
            return self.inout_place(base, false);
        }
        match &self.expr(e).kind {
            ExprKind::Array(parts) if planar => parts.iter().all(|&p| self.inout_place(p, false)),
            _ => self.is_place(e),
        }
    }

    /// The receiver of an `inout self` method, written with `!` or not, is
    /// an `inout` argument (§5.2, S-178).
    fn inout_receiver(&mut self, callee: ExprId) -> R<()> {
        match &self.expr(callee).kind {
            ExprKind::Field { base, .. } if !self.inout_place(*base, false) => {
                Err(self.no_inout_place(*base, "the receiver of an `inout self` method", "§5.2"))
            }
            _ => Ok(()),
        }
    }

    /// E0415: `what` is no place (§5.1; a place that cannot change is the E0701 of the modes).
    fn no_inout_place(&mut self, e: ExprId, what: &str, section: &str) -> Stop {
        let msg = format!(
            "{what} must be a place (a `var`, an `inout` parameter, or a field / element of one), not a constant, a temporary or the result of a call ({section})"
        );
        self.err(Code::E0415, self.expr(e).span, msg)
    }
}
