//! The calls of functions and methods, and their arguments.

use super::conversions::ConversionCall;
use super::named::Use;
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
        // Before the call of a flow (§4.5, S-811: `lp::[F32]~(x)`).
        self.type_args_of(callee)?;
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
            // `Buf.zeroed`) or a variant, as the names stage resolved the
            // callee.
            let named = crate::names::body::named(self.ast, callee);
            let record = self.names.paths.get(&named).cloned().map(|r| self.item_record(r));
            if let Some(PathRes::Item { entity, owner }) = record {
                let name = self.last_name(named);
                return match entity {
                    Entity::Builtin(Builtin::Panic) => self.check_panic(e, &name, args, expected),
                    _ => self.check_fn_call(e, callee, (entity, owner), &name, args, expected, kind),
                };
            }
            // 2. A method `recv.name(...)` of the value before it, with type
            // arguments of its own or not (`v.m::[I32](x)`, §4.5).
            if let ExprKind::Field { base, name } = &self.expr(named).kind {
                let (base, name) = (*base, name.clone());
                let recv = self.check_expr(base, None)?;
                let recv = self.known(recv, self.expr(base).span, "receiver")?;
                return self.check_method_call(e, callee, recv, &name, args, expected, kind);
            }
            // 3. `….f[…](...)`, an element of a field or the type arguments
            // of a method (§4.5, §6.1).
            if let Some(head) = self.member_head(callee) {
                return self.check_member_brackets(e, callee, head, args, expected, kind);
            }
        }
        // 4. A function value.
        let ft = self.check_expr(callee, None)?;
        self.call_value(e, callee, ft, args, kind)
    }

    /// The call `e` of the value `callee` of the type `ft`.
    pub(super) fn call_value(&mut self, e: ExprId, callee: ExprId, ft: TyId, args: &[Arg], kind: CallKind) -> R<TyId> {
        let ft = self.known_shape(ft, self.expr(callee).span, "callee")?;
        // A value of the error type: an unknown callee (§18.1, R-271).
        if matches!(self.ty(ft), Ty::Error) {
            return self.args_of_unknown_callee(args);
        }
        let Ty::Fn(f) = self.ty(ft) else { return Err(self.not_callable(callee, ft)) };
        if kind == CallKind::Bang {
            return Err(self.bang_on_value(e, callee));
        }
        self.info.targets.insert(e, Target::Value);
        self.check_args(args, &f.params, e)?;
        Ok(f.ret)
    }

    /// The call `panic(msg)` `e` (§9.2): it takes the type of its place (§7).
    /// A `!` on it is the modes stage's E0714, as on a constructor.
    fn check_panic(&mut self, e: ExprId, name: &Ident, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        // SPEC-GAP(S-888): in a flow body, a `panic` may be a constant
        // expression of the clocks (E0419, §11.3) or take the clock around it.
        if self.flow.is_some() {
            return Err(self.unsupported(name.span, Feature::PanicInFlow, &[]));
        }
        let [arg] = args else {
            let message = format!("this call takes 1 argument(s) but {} were given", args.len());
            return Err(self.err(Code::E0412, self.expr(e).span, message));
        };
        if self.ast.panic_message(arg).is_none() {
            let message = match arg.mode {
                Mode::Borrow => "the argument of `panic` is a string literal with no interpolation (§9.2)",
                _ => "the argument of `panic` has no mark: take off the `move` or `inout` (§9.2)",
            };
            return Err(self.err(Code::E0417, arg.span, message));
        }
        self.check_expr(arg.expr, None)?;
        self.info.targets.insert(e, Target::Panic);
        Ok(expected.unwrap_or_else(|| self.fresh()))
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
                if crate::names::unknown_callee(self.a, entity) {
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
                let own = Some(crate::names::body::named(self.ast, callee));
                let (targs, of) = self.generic_use(d, Use::Path { owner, own }, span)?;
                let (params, ret) = self.member_sig(d, f, &targs, of);
                // A conversion is judged by its source, which is not in its
                // result, before the result meets `expected` (§3.3, S-231).
                let conversion = self.conversion_to(d, of);
                if let (Some(exp), None) = (expected, conversion) {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, e)?;
                if let Some(to) = conversion {
                    self.literal_source(args, of);
                    let call = ConversionCall { e, expected };
                    self.conversion_use(name.span, targs[0], to, ret, Some(call))?;
                    if let Some(exp) = expected {
                        self.unify_at(span, ret, exp)?;
                    }
                }
                let inst = self.instance(d, targs, span, (self.buf_element(d), None))?;
                self.info.targets.insert(e, Target::Fn { def: d, of, inst });
                let fty = self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects.clone() }));
                self.record(callee, fty);
                Ok(ret)
            }
            Entity::Variant(d, i) => {
                let (targs, _) = self.generic_use(d, Use::Path { owner, own: None }, span)?;
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
                self.check_args(args, &params, e)?;
                self.finish_instance(d, targs, span)?;
                self.info.targets.insert(e, Target::Variant { def: d, index: i });
                Ok(ret)
            }
            Entity::Builtin(_) | Entity::Module(_) => unreachable!(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_method_call(
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
        // `recv.name[index](...)` ([`Self::check_member_brackets`]).
        let written = match self.expr(callee).kind {
            ExprKind::Index { index, .. } => Some(index),
            _ => None,
        };
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
                // The representative of a bound is no type of the program.
                let reach = match owner.filter(|_| !matches!(self.ty(recv), Ty::Param(_))) {
                    Some(d) => self.a.modules.member_reach(self.a.def(d), &mdef, name, self.m),
                    None if owner.is_some() => Ok(()),
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
                if let Some(index) = written {
                    return Err(self.method_brackets(callee, md, index));
                }
                if f.self_mode == Some(Mode::Inout) {
                    self.inout_receiver(callee)?;
                }
                let (targs, of) = self.generic_use(md, Use::Method { callee, recv }, span)?;
                // The impl's own generic arguments come from the receiver; of
                // std's `impl` of a sequence, its element (S-853).
                let mut element = None;
                if let Some(st) = self.a.self_ty_of(md).filter(|_| of.is_none()) {
                    if matches!(self.ty(st), Ty::Array(..) | Ty::Builtin(BuiltinTy::Span, _)) {
                        element = Some(Required::SeqElement { recv, method: name.name.clone() });
                    }
                    let st2 = self.a.types.subst(st, &targs);
                    self.unify_at(name.span, this, st2)?;
                }
                let (params, ret) = self.member_sig(md, f, &targs, of);
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, e)?;
                let inst = self.instance(md, targs, span, (element, None))?;
                self.a.note_use(self.a.def(md).name_span, name.span);
                self.info.targets.insert(e, Target::Method { def: md, of, inst });
                return Ok(ret);
            }
            if owner.is_some_and(|d| !matches!(self.a.def(d).kind, DefKind::Struct(_) | DefKind::Enum(_))) {
                return Ok(self.a.types.error());
            }
        }
        // A receiver of the error type, or of a type parameter with an
        // unknown bound (§18.1, S-689, R-271): an unknown method.
        let held = owner.is_some_and(|d| self.a.modules.holds_member(d, &name.name));
        if self.traits_unknown(recv) || held {
            return self.args_of_unknown_callee(args);
        }
        // A method of the spec this version has not (R-294).
        if let Some((builtin::Form::Method, feature)) = builtin::missing(&self.a.types, recv, &name.name) {
            let shown = format!("{}.{}", self.type_head(recv), name.name);
            return Err(self.unsupported(name.span, feature, &[&shown]));
        }
        if written.is_some() {
            return self.field_type(recv, name);
        }
        if let Some(called) = self.field_called(e, callee, recv, name, args, expected, kind) {
            return called;
        }
        // Type arguments after what is no member are not judged: the E0413
        // is that of no type arguments (§4.5, S-992).
        Err(self.removed_method(e, recv, name, args, expected, kind))
    }

    /// The record `r` with a member of a type parameter as an item: the type
    /// that stands before the name, as of an alias, is the parameter
    /// ([`Self::param_of`]).
    pub(super) fn item_record(&mut self, r: PathRes) -> PathRes {
        let PathRes::BoundMember { param, member } = r else { return r };
        let owner = Some(self.a.types.intern(Ty::Param(param)));
        PathRes::Item { entity: Entity::Member(member), owner }
    }

    /// The type parameter a member is read at, of the `owner` of its record
    /// ([`Self::item_record`]): an alias and `Self` stand for no type parameter.
    pub(super) fn param_of(&self, owner: Option<TyId>) -> Option<TyId> {
        owner.filter(|&t| matches!(self.ty(t), Ty::Param(_)))
    }

    /// The type `t` of the declaration of the member `d` at the type
    /// arguments `args`, and at the type parameter `of`: there the `Self` of
    /// a representative type, which its declaration has as that type, is `of`.
    pub(super) fn member_ty(&mut self, d: DefId, t: TyId, args: &[TyId], of: Option<TyId>) -> TyId {
        let t = self.a.types.subst(t, args);
        match (of, self.a.self_ty_of(d)) {
            (Some(of), Some(rep)) => self.a.types.replace(t, rep, of),
            _ => t,
        }
    }

    /// The parameters and the result of the function `f`, the member `d`,
    /// as [`Self::member_ty`] reads its types.
    fn member_sig(&mut self, d: DefId, f: &FnDef, args: &[TyId], of: Option<TyId>) -> (Vec<(Mode, TyId)>, TyId) {
        let params = f.params.iter().map(|p| (p.mode, self.member_ty(d, p.ty, args, of))).collect();
        (params, self.member_ty(d, f.ret, args, of))
    }

    /// The way out of the E0405 of a float literal converted to the type
    /// parameter `of`: the literal is a value of it by itself (§6.6, S-881).
    fn literal_source(&mut self, args: &[Arg], of: Option<TyId>) {
        let (Some(of), [arg]) = (of, args) else { return };
        let source = self.ast.without_parens(arg.expr);
        let lit = self.ast.negated_literal(source).unwrap_or(source);
        let is_float = matches!(self.expr(lit).kind, ExprKind::Lit(Lit::Float { .. }));
        if !is_float || !self.infer.float_fits(&self.ty(of)) {
            return;
        }
        let (t, src) = (self.display(of), self.src(self.expr(source).span));
        for item in self.deferred.iter_mut().rev() {
            if let DeferredKind::FloatLit { lit: l, rule } = &mut item.kind
                && *l == lit
            {
                *rule = Some(format!(
                    "a float literal is a value of `{t}` by itself: write it where `{t}` is expected (`let x: {t} = {src}`) (§6.6)"
                ));
                return;
            }
        }
    }

    /// The type the function `d` converts to, when it is a conversion
    /// function: of a member of the type parameter `of`, `of`.
    pub(super) fn conversion_to(&self, d: DefId, of: Option<TyId>) -> Option<TyId> {
        crate::prim::conversion_target(self.a, d).map(|to| of.unwrap_or(to))
    }

    /// Where the method `name` of a receiver of the type `recv` is looked
    /// up: the key of the `impl`s of a builtin type (of a type parameter, of
    /// the representative type of the member its bounds give), the owner of a
    /// user type, and the type its `self` stands for. The one lookup of the
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
            Ty::Param(i) => match self.generics.get(i as usize).map(|g| &g.kind) {
                Some(GenericKind::Type { bounds, .. }) => {
                    let rep = crate::traits::member_rep(bounds, name);
                    rep.map_or((None, None), |r| r.table(self.a))
                }
                _ => (None, None),
            },
            _ => (None, None),
        };
        // §5.3: an array and a `Buf` take from `Span[T]` the methods their
        // own `impl`s have not, as a `Span` of
        // their element `T`: one step, `Span` takes from none.
        let mut this = recv;
        if let Some(elem) = self.viewed_element(recv)
            && !key.and_then(|k| self.a.modules.assoc_builtin.get(&k)).is_some_and(|t| t.contains_key(name))
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

    /// Of std's `impl` of `Buf` (`Buf.zeroed`), called or as a value, the
    /// requirements are its element's (§4.5), as of a `Buf` written (R-351).
    pub(super) fn buf_element(&self, d: DefId) -> Option<Required> {
        let of_buf = self.a.self_ty_of(d).is_some_and(|t| matches!(self.ty(t), Ty::Builtin(BuiltinTy::Buf, _)));
        of_buf.then_some(Required::BufElement(BuiltinTy::Buf))
    }

    /// What the note of a type an argument decides says it is: an argument
    /// of the callee of the call `e`, by the name it is written with; of what
    /// has no name (`(id).(true)`), an argument. A callee after a value that
    /// is computed or on other lines goes by its last name (§18.1, R-364).
    fn argument_why(&self, e: ExprId) -> String {
        let ExprKind::Call { callee, .. } = self.expr(e).kind else { return "an argument".to_string() };
        let written = self.src(self.expr(callee).span);
        let name = match &self.expr(callee).kind {
            ExprKind::Field { name, .. } if written.contains(['(', '\n']) => name.name.clone(),
            ExprKind::Path(_) | ExprKind::Field { .. } | ExprKind::TypeArgs { .. } => written,
            _ => return "an argument".to_string(),
        };
        format!("an argument of `{name}`")
    }

    /// The arguments `args` of the call `e` at the parameters `params`.
    pub(crate) fn check_args(&mut self, args: &[Arg], params: &[(Mode, TyId)], e: ExprId) -> R<()> {
        if args.len() != params.len() {
            return Err(self.err(
                Code::E0412,
                self.expr(e).span,
                format!("this call takes {} argument(s) but {} were given", params.len(), args.len()),
            ));
        }
        let why = self.argument_why(e);
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
                    let kind = &self.expr(arg.expr).kind;
                    self.arg_closure = matches!(kind, ExprKind::Closure { .. }).then_some(arg.expr);
                    self.with_why(why.clone(), pt, |ck| ck.check_expr(arg.expr, Some(pt)))?;
                }
                Some((elem, planar)) => {
                    let aspan = self.expr(arg.expr).span;
                    let at = match (planar, &self.expr(self.ast.without_parens(arg.expr)).kind) {
                        (Some(_), ExprKind::Array(parts)) if !parts.is_empty() => {
                            self.planar_literal(arg.expr, parts, elem, mode)?
                        }
                        _ => self.check_expr(arg.expr, None)?,
                    };
                    // A literal variable is passed as no `Span` (S-860).
                    let at_s = self.known_shape(at, aspan, "argument")?;
                    let ok = match (planar, self.ty(at_s)) {
                        // A length unified, as of any array (a const parameter `N`).
                        (Some(n), Ty::Array(ch, m)) => {
                            let cause = self.cause(aspan, None);
                            self.infer.unify_len(&mut self.a.types, n, m, &cause).is_ok()
                                && self.views(ch, elem, aspan, mode)?
                        }
                        (Some(_), Ty::Error) => true,
                        (Some(_), _) => false,
                        (None, _) => self.views(at_s, elem, aspan, mode)?,
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
    /// an array, a `Buf` or a `Span` of the element (the error type too),
    /// and a `FixedStr[N]` as a `Span[U8]` of its used part (§4.2), which
    /// the parameter of the mode `mode` `inout` does not take (E0401: its
    /// bytes change by the appends alone). The element of a planar argument
    /// and a generic `Span[T]` (`T = U8`) take a `FixedStr` too, by this one
    /// judgment (§4.2, S-1008).
    fn views(&mut self, t: TyId, elem: TyId, at: Span, mode: Mode) -> R<bool> {
        let cause = self.cause(at, None);
        let el = match self.ty(self.shallow(t)) {
            Ty::Array(el, _) => el,
            Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a) => a[0],
            Ty::Named(d, _) if self.a.modules.lang.fixed_str(d).is_some() => {
                if mode == Mode::Inout {
                    let msg = format!(
                        "a `{}` is not passed as an `inout` `Span[U8]`: its bytes change by its appends alone (§4.2, §5.3)",
                        self.display(t)
                    );
                    return Err(self.err(Code::E0401, at, msg));
                }
                self.a.types.int(IntKind::U8)
            }
            Ty::Error => return Ok(true),
            _ => return Ok(false),
        };
        Ok(self.infer.unify(&mut self.a.types, el, elem, &cause).is_ok())
    }

    /// The type of the planar literal `e` (`[a, b]` at `[Span[elem]; N]`,
    /// S-196, §5.3): each element is passed as a `Span` of its own, of any
    /// kind and length, so `[Span[elem]; k]` (`k` checked against `N` by the
    /// caller), recorded through the parentheses. The lowering converts each
    /// element (`coerce`).
    fn planar_literal(&mut self, e: ExprId, parts: &[ExprId], elem: TyId, mode: Mode) -> R<TyId> {
        let view = self.a.types.intern(Ty::Builtin(BuiltinTy::Span, vec![elem]));
        for &x in parts {
            let (t, at) = (self.check_expr(x, None)?, self.expr(x).span);
            if !self.views(t, elem, at, mode)? {
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
        match crate::names::body::receiver(self.ast, callee) {
            Some(base) if !self.inout_place(base, false) => {
                Err(self.no_inout_place(base, "the receiver of an `inout self` method", "§5.2"))
            }
            _ => Ok(()),
        }
    }

    /// E0415: `what` is no place (§5.1; a place that cannot change is the E0701 of the modes),
    /// but none of an item that was not read ([`Checker::unread_root`]).
    fn no_inout_place(&mut self, e: ExprId, what: &str, section: &str) -> Stop {
        if self.unread_root(e) {
            return self.held_stop();
        }
        let msg = format!(
            "{what} must be a place (a `var`, an `inout` parameter, or a field / element of one), not a constant, a temporary or the result of a call ({section})"
        );
        self.err(Code::E0415, self.expr(e).span, msg)
    }
}
