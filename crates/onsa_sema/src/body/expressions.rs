//! The expressions: the literals, struct literals, blocks, `match`,
//! closures and operators.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ expressions

    pub(crate) fn check_expr(&mut self, e: ExprId, expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        let t = self.check_expr_inner(e, expected)?;
        if let Some(exp) = expected {
            self.unify_at(span, t, exp)?;
        }
        Ok(self.record(e, t))
    }

    fn check_expr_inner(&mut self, e: ExprId, expected: Option<TyId>) -> R<TyId> {
        let expr = self.expr(e);
        let span = expr.span;
        if self.flow.is_some()
            && let Some(t) = self.check_flow_expr(e, expected)?
        {
            return Ok(t);
        }
        match &expr.kind {
            // What a syntax error left unread (S-59): the error type, and no
            // diagnostic. The body of a failed item is not checked at all.
            ExprKind::Error => Ok(self.a.types.error()),
            ExprKind::Lit(lit) => self.check_lit(e, lit, expected),
            ExprKind::Path(_) | ExprKind::Field { .. } => self.check_name(e, expected),
            ExprKind::Hole => {
                // Reported at the end of the body (§18.1), once later statements
                // have had the chance to decide the type.
                let t = expected.unwrap_or_else(|| self.fresh());
                let Some(visible) = self.names.holes.get(&e) else { return Err(self.held_stop()) };
                let visible = visible.iter().map(|b| LocalId(b.0)).collect();
                self.defer(span, t, DeferredKind::Hole { visible });
                Ok(self.record(e, t))
            }
            ExprKind::Paren(inner) => self.check_expr(*inner, expected),
            // `move x` (§5.2, S-21): same type as its operand. Whether it is a
            // place is the modes stage's (R-198: its candidate asks the kinds).
            ExprKind::Move(inner) => self.check_expr(*inner, expected),
            ExprKind::Tuple(elems) => {
                if elems.is_empty() {
                    return Ok(self.unit());
                }
                let exp_elems: Option<Vec<TyId>> = expected.and_then(|t| match self.ty(self.shallow(t)) {
                    Ty::Tuple(ts) if ts.len() == elems.len() => Some(ts),
                    _ => None,
                });
                let mut ts = Vec::new();
                for (i, &el) in elems.iter().enumerate() {
                    let exp = exp_elems.as_ref().map(|v| v[i]);
                    ts.push(self.check_expr(el, exp)?);
                }
                Ok(self.a.types.intern(Ty::Tuple(ts)))
            }
            ExprKind::Array(elems) => {
                let exp_elem = expected.and_then(|t| match self.ty(self.shallow(t)) {
                    Ty::Array(el, _) => Some(el),
                    _ => None,
                });
                if elems.is_empty() {
                    // The element type is the expected one or a later statement's (§2.4, S-226).
                    let el = match exp_elem {
                        Some(el) => el,
                        None => {
                            let el = self.fresh();
                            self.defer(span, el, DeferredKind::Origin { what: "the element type of `[]`".into() });
                            el
                        }
                    };
                    return Ok(self.a.types.intern(Ty::Array(el, Len::Const(0))));
                }
                let first = self.check_expr(elems[0], exp_elem)?;
                for &el in &elems[1..] {
                    self.check_expr(el, Some(first))?;
                }
                Ok(self.a.types.intern(Ty::Array(first, Len::Const(elems.len() as u32))))
            }
            ExprKind::Repeat { elem, len } => {
                let exp_elem = expected.and_then(|t| match self.ty(self.shallow(t)) {
                    Ty::Array(el, _) => Some(el),
                    _ => None,
                });
                let n = self.const_len(*len)?;
                let et = self.check_expr(*elem, exp_elem)?;
                // The element is copied N times: a kind constraint that a later
                // statement may decide (§2.4, §4.7, S-235).
                self.defer(span, et, DeferredKind::Require { bound: Bound::Dup, what: Required::RepeatElement });
                Ok(match n {
                    Some(n) => self.a.types.intern(Ty::Array(et, n)),
                    None => self.a.types.error(),
                })
            }
            // The names stage stops the body at a type argument (E0200 until W5-10).
            ExprKind::Struct { type_args, .. } if !type_args.is_empty() => {
                onsa_diag::internal::bug(Some(span), "a type argument the names stage did not stop at")
            }
            ExprKind::Struct { path, fields, .. } => self.check_struct_lit(e, path, fields, expected, span),
            ExprKind::TypeArgs { .. } => {
                onsa_diag::internal::bug(Some(span), "a type argument the names stage did not stop at")
            }
            ExprKind::Block(b) => self.check_block(b, expected),
            // What only a flow body holds is the names stage's E0821 outside
            // one (§11.1). In a flow body, `if~` and `match~` are typed as
            // `if` and `match`, and the flow checks read the `~`
            // (`crate::flow::map`); `at`, `^` and `par` are theirs.
            ExprKind::If { tilde: Some(_), .. } | ExprKind::Match { tilde: Some(_), .. } if self.flow.is_none() => {
                onsa_diag::internal::bug(Some(span), "flow syntax the names stage did not stop at")
            }
            ExprKind::Closure { ret_clock: Some(_), .. } | ExprKind::Feedback(_) | ExprKind::Par { .. } => {
                onsa_diag::internal::bug(Some(span), "flow syntax the names stage did not stop at")
            }
            // The names stage reads the operand of `at` before its clock
            // (§18.1), and may stop in it with no error (S-675).
            ExprKind::At { expr, .. } => {
                self.check_expr(*expr, None)?;
                onsa_diag::internal::bug(Some(span), "flow syntax the names stage did not stop at")
            }
            ExprKind::If { cond, then, else_, .. } => {
                let bool_ = self.bool_();
                self.check_expr(*cond, Some(bool_))?;
                match else_ {
                    Some(el) => {
                        let t = self.check_expr(*then, expected)?;
                        // Merged with the other branch: not the reason of the outer expectation.
                        self.without_why(|ck| ck.check_expr(*el, Some(t)))?;
                        Ok(t)
                    }
                    None => {
                        let unit = self.unit();
                        self.check_expr(*then, Some(unit))?;
                        Ok(unit)
                    }
                }
            }
            ExprKind::Match { scrutinee, arms, .. } => self.check_match(*scrutinee, arms, expected, span),
            ExprKind::Closure { params, ret, ret_clock: None, effects, body } => {
                self.check_closure(e, params, *ret, effects.as_ref(), *body, expected)
            }
            ExprKind::Handle { .. } => Err(self.unsupported(span, Feature::EffectHandlers, &[])),
            ExprKind::Unsafe(_) => Err(self.unsupported(span, Feature::Unsafe, &[])),
            &ExprKind::Binary { op, op_span, lhs, rhs } => self.check_binary(op, op_span, lhs, rhs),
            ExprKind::Cast { expr: inner, ty } => {
                let it = self.check_expr(*inner, None)?;
                let from = self.known(it, self.expr(*inner).span, "operand of `as`")?;
                let to = self.lower_type_expr(*ty)?;
                // The error type (what a syntax error left unread, S-59) is not
                // checked: no diagnostic for it (R-71).
                let error = |t: TyId| matches!(self.a.types.get(t), Ty::Error);
                if crate::cast::cast_allowed(&self.a.types, from, to) || error(from) || error(to) {
                    return Ok(to);
                }
                let (fs, ts) = (self.display(from), self.display(to));
                let mut d = Diagnostic::new(
                    Stage::Types,
                    Code::E0411,
                    span,
                    format!(
                        "`as` only widens without losing information; `{fs}` to `{ts}` needs a conversion method (§3.3)"
                    ),
                )
                .with_found(self.src(span));
                if let Some(m) = crate::cast::cast_suggestion(&self.a.types, from, to) {
                    // `as` and the type after the operand change, the operand stays (S-251).
                    let rest = Span::new(span.file, self.expr(*inner).span.end, span.end);
                    d = d.with_fix(Fix::replace(format!("call `{m}`"), rest, m));
                }
                Err(self.diag(d))
            }
            ExprKind::Unary { op, expr: inner } => self.check_unary(e, *op, *inner, span),
            ExprKind::Call { callee, kind, args } => self.check_call(e, *callee, *kind, args, expected),
            ExprKind::TupleIndex { base, index, index_span } => {
                let bt = self.check_expr(*base, None)?;
                let bt = self.known_shape(bt, self.expr(*base).span, "value")?;
                self.tuple_element(bt, *index, *index_span)
            }
            ExprKind::Index { base, index } => {
                let bt = self.check_expr(*base, None)?;
                let bt = self.known_shape(bt, self.expr(*base).span, "value")?;
                let u32 = self.u32();
                self.check_expr(*index, Some(u32))?;
                match self.ty(bt) {
                    Ty::Array(el, _) => Ok(el),
                    Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, args) => Ok(args[0]),
                    Ty::Builtin(BuiltinTy::Str, _) => Err(self.err(
                        Code::E0413,
                        span,
                        "`Str` has no index; use `.bytes()` / `.chars()` or `.substr(from, to)` (§4.2)",
                    )),
                    Ty::Error => Ok(bt),
                    _ => {
                        let shown = self.described(bt);
                        Err(self.err(Code::E0413, span, format!("{shown} cannot be indexed")))
                    }
                }
            }
            ExprKind::Try(inner) => {
                let it = self.check_expr(*inner, None)?;
                let it = self.known_shape(it, self.expr(*inner).span, "operand of `?`")?;
                let ret = self.frames.last().unwrap().ret;
                let ret_s = self.shallow(ret);
                match (self.ty(it), self.ty(ret_s)) {
                    (Ty::Builtin(BuiltinTy::Option, a), Ty::Builtin(BuiltinTy::Option, _)) => Ok(a[0]),
                    (Ty::Builtin(BuiltinTy::Result, a), Ty::Builtin(BuiltinTy::Result, r)) => {
                        let cause = self.cause(span, None);
                        if self.infer.unify(&mut self.a.types, a[1], r[1], &cause).is_err() {
                            let (ea, er) = (self.display(a[1]), self.display(r[1]));
                            return Err(self.err(
                                Code::E0414,
                                span,
                                format!("`?` needs the same error type as the function (`{er}`); found `{ea}`; convert it with `map_err` (§9.1)"),
                            ));
                        }
                        Ok(a[0])
                    }
                    (Ty::Error, _) => Ok(it),
                    (Ty::Builtin(BuiltinTy::Option | BuiltinTy::Result, _), _) => {
                        let (shown, rs) = (self.display(it), self.display(ret));
                        Err(self.err(
                            Code::E0414,
                            span,
                            format!(
                                "`?` on `{shown}` needs the function to return the same kind; it returns `{rs}` (§9.1)"
                            ),
                        ))
                    }
                    _ => {
                        let shown = self.described(it);
                        Err(self.err(Code::E0414, span, format!("`?` needs an `Option` or `Result`; found {shown}")))
                    }
                }
            }
            // The parser makes a range only as a head; the words of the row
            // that finds one elsewhere (`range_outside_header`).
            ExprKind::Range(_) => {
                let row = onsa_syntax::foreign::row(onsa_syntax::foreign::RowId::RangeOutsideHeader);
                Err(self.diag(Diagnostic::new(Stage::Syntax, Code::E0002, span, row.message).with_rule(row.rule)))
            }
        }
    }

    fn check_lit(&mut self, e: ExprId, lit: &Lit, expected: Option<TyId>) -> R<TyId> {
        match lit {
            Lit::Int { value, .. } => {
                let _ = expected;
                let t = self.infer.fresh(&mut self.a.types, Some(LitKind::Int));
                let span = self.expr(e).span;
                self.defer(span, t, DeferredKind::IntLit { value: *value, neg: false, lit: Some(e) });
                Ok(t)
            }
            Lit::Float { .. } => {
                let t = self.infer.fresh(&mut self.a.types, Some(LitKind::Float));
                let span = self.expr(e).span;
                self.defer(span, t, DeferredKind::FloatLit { lit: e });
                Ok(t)
            }
            Lit::Char(_) => Ok(self.a.types.intern(Ty::Char)),
            Lit::Bool(_) => Ok(self.bool_()),
            Lit::Str(s) => {
                for (k, seg) in (0..).zip(&s.segments) {
                    if let StrSeg::Interp(path) = seg {
                        self.check_hole(e, k, path)?;
                    }
                }
                Ok(self.a.types.builtin(BuiltinTy::Str, vec![]))
            }
        }
    }

    /// The type of the element `index` (written at `at`) of a value of the
    /// known type `bt` (`t.0`, and in a hole `{t.0}`, §2.4).
    pub(super) fn tuple_element(&mut self, bt: TyId, index: u32, at: Span) -> R<TyId> {
        match self.ty(bt) {
            Ty::Tuple(ts) if (index as usize) < ts.len() => Ok(ts[index as usize]),
            Ty::Error => Ok(bt),
            // SPEC-GAP(S-260): an element of a struct whose unit failed in
            // the syntax stage gets no diagnostic, as a field does
            // (`field_type`; a tuple struct `struct Hz(F32)` is one, S-39).
            Ty::Named(d, _) if self.a.partly_read(d) => Ok(self.a.types.error()),
            _ => {
                let shown = self.described(bt);
                Err(self.err(Code::E0413, at, format!("{shown} has no element `{index}`")))
            }
        }
    }

    /// `[e; N]` / array length in an expression (§4.5; the forms are read in `constarg.rs`).
    /// `None`: a length the check does not read (§18.1, S-690).
    pub(crate) fn const_len(&mut self, len: ExprId) -> R<Option<Len>> {
        let generics = self.generics.clone();
        // A local or a parameter, by the record (§4.5: E0417, as a value that
        // is no constant).
        let (ast, names) = (self.ast, &self.names);
        let local = |e| crate::body::starts_at_local(ast, names, e);
        let scope = (&generics[..], self.self_ty, self.flow.is_some());
        match crate::constarg::expr(self.a, self.m, self.ast, self.text, scope, len, &local) {
            Ok((value, constant)) => {
                let u32 = self.u32();
                self.record(len, u32);
                match value {
                    crate::constarg::ConstU32::Value(v) => {
                        if let Some(d) = constant {
                            self.info.targets.insert(len, Target::Const(d));
                        }
                        Ok(Some(Len::Const(v)))
                    }
                    crate::constarg::ConstU32::Param(i) => Ok(Some(Len::Param(i))),
                }
            }
            Err(crate::constarg::ConstErr::Report(d) | crate::constarg::ConstErr::Uncomputed(d)) => Err(self.diag(d)),
            // A constant whose value was not read (S-59) or a name held as an
            // error: no diagnostic, and the check goes on (§18.1, S-690).
            Err(crate::constarg::ConstErr::Unknown) => {
                let u32 = self.u32();
                self.record(len, u32);
                self.a.read_held.insert(self.def);
                Ok(None)
            }
        }
    }

    /// The struct literal `e` (§4.4). An alias of the error type is no
    /// struct here: its path has no record (S-728, `names/body/paths.rs`).
    fn check_struct_lit(
        &mut self,
        e: ExprId,
        path: &Path,
        fields: &[(Ident, ExprId)],
        expected: Option<TyId>,
        span: Span,
    ) -> R<TyId> {
        let Some(&StructRes { entity, owner }) = self.names.structs.get(&e) else { return Err(self.held_stop()) };
        let d = match entity {
            Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Struct(_)) => d,
            _ => return Err(self.diag(crate::body::not_a_struct(self.src(path.span), path.span))),
        };
        let s = self.a.def(d).as_struct().unwrap().clone();
        let Fields::Named(defs) = &s.fields else {
            let name = self.src(path.span);
            return Err(self.err(
                Code::E0410,
                path.span,
                format!("`{name}` is not built with a field list; it has no named fields"),
            ));
        };
        let args = self.fresh_args(d);
        self.of_owner(d, &args, owner, span)?;
        // The expected type decides the generic arguments first (§4.7: expected
        // types flow downward; `Ring[F32, 4]` fixes `T` and `N` before the fields).
        // The expected type may be a variable a field of an outer literal bound (R-148).
        if let Some(exp) = expected
            && let Ty::Named(d2, exp_args) = self.ty(self.shallow(exp))
            && d2 == d
            && exp_args.len() == args.len()
        {
            for (&a, &x) in args.iter().zip(&exp_args) {
                self.unify_at(span, a, x)?;
            }
        }
        // SPEC-GAP(S-260): the fields of a struct whose unit failed in the
        // syntax stage are not all known: no diagnostic for an unknown or a
        // missing field.
        let failed = self.a.partly_read(d);
        let written: Vec<&Ident> = fields.iter().map(|(n, _)| n).collect();
        self.whole_reach(d, defs, &written, path.span, crate::structpat::Whole::Literal)?;
        let mut seen: Vec<&str> = Vec::new();
        for (name, value) in fields {
            if seen.contains(&name.name.as_str()) {
                return Err(self.err(Code::E0410, name.span, format!("field `{}` is given twice", name.name)));
            }
            seen.push(&name.name);
            let Some(f) = defs.iter().find(|f| f.name == name.name) else {
                if failed {
                    let error = self.a.types.error();
                    self.check_expr(*value, Some(error))?;
                    continue;
                }
                let shown = self.a.def(d).name.clone();
                return Err(self.err(Code::E0410, name.span, format!("`{shown}` has no field `{}`", name.name)));
            };
            self.a.note_use(f.span, name.span);
            let ft = self.a.types.subst(f.ty, &args);
            self.with_why(format!("the field `{}`", name.name), ft, |ck| ck.check_expr(*value, Some(ft)))?;
        }
        let missing: Vec<&str> = defs.iter().map(|f| f.name.as_str()).filter(|n| !seen.contains(n)).collect();
        if !missing.is_empty() && !failed {
            let shown = self.a.def(d).name.clone();
            return Err(self.err(
                Code::E0410,
                path.span,
                format!(
                    "missing field(s) {} of `{shown}`; struct literals name every field (§4.4)",
                    missing.iter().map(|m| format!("`{m}`")).collect::<Vec<_>>().join(", ")
                ),
            ));
        }
        let t = self.a.types.intern(Ty::Named(d, args.clone()));
        self.finish_instance(d, args, span)?;
        Ok(t)
    }

    pub(crate) fn check_block(&mut self, b: &Block, expected: Option<TyId>) -> R<TyId> {
        if let Some(f) = &mut self.flow {
            f.depth += 1;
        }
        let r = (|| -> R<TyId> {
            for &s in &b.stmts {
                self.check_stmt(s)?;
            }
            match b.tail {
                Some(t) => self.check_expr(t, expected),
                None => {
                    // A block that ends in `return` / `break` / `continue` diverges: it
                    // takes any type (a trailing `return e` is allowed, §6.1).
                    if self.ast.block_exits(b) { Ok(self.fresh()) } else { Ok(self.unit()) }
                }
            }
        })();
        if let Some(f) = &mut self.flow {
            f.depth -= 1;
        }
        r
    }

    fn check_match(&mut self, scrutinee: ExprId, arms: &[MatchArm], expected: Option<TyId>, span: Span) -> R<TyId> {
        let st = self.check_expr(scrutinee, None)?;
        let st = self.known(st, self.expr(scrutinee).span, "`match` operand")?;
        let mut result: Option<TyId> = expected;
        let mut rows: Vec<Vec<P>> = Vec::new();
        for arm in arms {
            let r = (|| -> R<()> {
                let p = self.bind_pat(arm.pat, st, false)?;
                if let Some(g) = arm.guard {
                    let bool_ = self.bool_();
                    self.check_expr(g, Some(bool_))?;
                } else {
                    rows.push(vec![p]);
                }
                // The arms after the first are merged with it (not the outer reason).
                let t = if result == expected {
                    self.check_expr(arm.body, result)?
                } else {
                    self.without_why(|ck| ck.check_expr(arm.body, result))?
                };
                if result.is_none() {
                    result = Some(t);
                }
                Ok(())
            })();
            r?;
        }
        // SPEC-GAP(S-260): the variants of an enum whose unit failed in the
        // syntax stage are not all known; its `match` is not counted. Nor is
        // the `match` of a value of the error type (§18.1, R-271).
        if !self.mentions_failed(st)
            && !matches!(self.ty(self.shallow(st)), Ty::Error)
            && let Some(missing) = self.missing_pattern(&rows, st)
        {
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Types,
                    Code::E0501,
                    span,
                    format!("`match` is not exhaustive; `{missing}` is not covered (§7)"),
                )
                .with_found(self.src(self.expr(scrutinee).span)),
            ));
        }
        Ok(result.unwrap_or_else(|| self.unit()))
    }

    fn check_closure(
        &mut self,
        e: ExprId,
        params: &[Param],
        ret: Option<onsa_syntax::ast::TypeId>,
        effects: Option<&onsa_syntax::ast::EffectRow>,
        body: ExprId,
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let exp_fn: Option<FnTy> = expected.and_then(|t| match self.ty(self.shallow(t)) {
            Ty::Fn(f) => Some(f),
            _ => None,
        });
        if let Some(f) = &exp_fn
            && f.params.len() != params.len()
        {
            return Err(self.err(
                Code::E0412,
                span,
                format!("this function takes {} parameter(s) but {} are expected here", params.len(), f.params.len()),
            ));
        }
        let mut ptys = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let t = match p.ty {
                Some(t) => {
                    let lowered = self.lower_type_expr(t)?;
                    if let Some(f) = &exp_fn {
                        self.unify_at(self.ast.ty(t).span, lowered, f.params[i].1)?;
                    }
                    lowered
                }
                None => match &exp_fn {
                    Some(f) => f.params[i].1,
                    None => {
                        return Err(self.diag(
                            Diagnostic::new(
                                Stage::Types,
                                Code::E0420,
                                p.span,
                                "the parameter type of an anonymous function must be known here; annotate it (§6.1)",
                            )
                            .with_found(self.src(p.span)),
                        ));
                    }
                },
            };
            ptys.push((p.mode, t));
        }
        let ret_ty = match ret {
            Some(t) => self.lower_type_expr(t)?,
            None => match &exp_fn {
                Some(f) => f.ret,
                None => self.fresh(),
            },
        };
        let effects = match effects {
            // As the names stage read it (S-738).
            Some(_) => self.names.effects.get(&e).cloned().ok_or_else(|| self.held_stop())?,
            None => exp_fn.as_ref().map(|f| f.effects.clone()).unwrap_or_default(),
        };
        let rt = exp_fn.as_ref().map(|f| f.rt).unwrap_or(false);
        // The body runs in its own frame: `return` targets the closure (its
        // captures are the record's, §5.3).
        self.frames.push(Frame { ret: ret_ty, loop_depth: 0 });
        let r = (|| -> R<()> {
            for (k, (p, (_, t))) in (0..).zip(params.iter().zip(&ptys)) {
                match &p.name {
                    ParamName::Ident(id) => {
                        let local = self.local_of(Origin::Closure { closure: e, param: k })?;
                        self.bind_local(local, *t, id.span)?;
                    }
                    ParamName::SelfParam(s) => {
                        return Err(self.err(Code::E0002, *s, "an anonymous function has no `self`"));
                    }
                    ParamName::Wild(_) => {}
                }
            }
            self.check_expr(body, Some(ret_ty))?;
            Ok(())
        })();
        self.frames.pop();
        r?;
        Ok(self.a.types.intern(Ty::Fn(FnTy { rt, params: ptys, ret: ret_ty, effects })))
    }

    /// One operator of a chain (the tree of §3.1): the left operand, the
    /// right one, then what the operator requires of them (S-255).
    fn check_binary(&mut self, op: BinOp, op_span: Span, lhs: ExprId, rhs: ExprId) -> R<TyId> {
        let t = self.check_expr(lhs, None)?;
        Ok(match op.group() {
            OpGroup::And | OpGroup::Or => {
                let bool_ = self.bool_();
                self.unify_at(self.expr(lhs).span, t, bool_)?;
                self.check_expr(rhs, Some(bool_))?;
                bool_
            }
            OpGroup::Comparison => {
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                self.require_op(OpNeed::Binary(op), t, op_span)?;
                self.bool_()
            }
            OpGroup::Bitwise if matches!(op, BinOp::Shl | BinOp::Shr) => {
                let u32 = self.u32();
                self.check_expr(rhs, Some(u32))?;
                self.require_op(OpNeed::Binary(op), t, op_span)?;
                t
            }
            OpGroup::Bitwise | OpGroup::Additive | OpGroup::Multiplicative | OpGroup::Remainder => {
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                self.require_op(OpNeed::Binary(op), t, op_span)?;
                t
            }
        })
    }

    /// A prefix `-` or `!` (§3.2, §3.4).
    fn check_unary(&mut self, e: ExprId, op: UnOp, inner: ExprId, span: Span) -> R<TyId> {
        let t = self.check_expr(inner, None)?;
        // A `-` whose operand is a literal is a part of the literal's value
        // (§4.7, S-184, S-227): the literal's own check covers the sign.
        if op == UnOp::Neg
            && let Some(lit) = self.ast.negated_literal(e)
        {
            self.info.neg_literals.insert(e);
            if let Some(item) = self
                .deferred
                .iter_mut()
                .rev()
                .find(|d| matches!(d.kind, DeferredKind::IntLit { lit: Some(l), .. } if l == lit))
            {
                item.span = span;
                if let DeferredKind::IntLit { neg, .. } = &mut item.kind {
                    *neg = true;
                }
            }
            return Ok(t);
        }
        let need = if op == UnOp::Neg { OpNeed::Neg } else { OpNeed::Not };
        self.require_op(need, t, span)?;
        Ok(t)
    }

    /// The trait an operator needs of its operand type `t` (§3.2, §6.3): judged here
    /// when it is decided, else after the statement that decides it (§4.7, S-235, R-55).
    /// E0401 at `span`, the operator.
    pub(crate) fn require_op(&mut self, op: OpNeed, t: TyId, span: Span) -> R<()> {
        // SPEC-GAP(S-857): an operand whose type is decided here is judged here, not after the
        // statement: in one statement, its E0401 comes before the E0401 of an operator that
        // waited and before a later type error of the statement.
        match self.operator_verdict(op, t) {
            Verdict::Met => Ok(()),
            Verdict::Wait => {
                self.defer(span, t, DeferredKind::Operator { op });
                Ok(())
            }
            Verdict::Unmet(msg) => Err(self.err(Code::E0401, span, msg)),
        }
    }

    /// Whether the type `t` has what the operator `op` needs: the one judgment of the
    /// operators, at the operator and in a deferred item. A literal variable decides it
    /// by its kind (an integer literal has every trait of an operator but the `-` of an
    /// unsigned type; a float literal has none of the integer operators). Any other
    /// variable left waits for the statement that decides it.
    pub(crate) fn operator_verdict(&mut self, op: OpNeed, t: TyId) -> Verdict {
        let s = self.shallow(t);
        let int_only = match op {
            OpNeed::Binary(b) => op_bound(b).is_none(),
            OpNeed::Neg => false,
            OpNeed::Not => true,
        };
        if matches!(self.ty(s), Ty::Var(_)) {
            return match self.infer.lit_of(&self.a.types, s) {
                Some(LitKind::Float) if int_only => Verdict::Unmet(match op {
                    OpNeed::Binary(b) => format!("`{}` is defined for integers only (§3.4)", b.symbol()),
                    _ => not_unmet(LitKind::Float.words()),
                }),
                Some(LitKind::Int) if op == OpNeed::Neg => Verdict::Wait,
                Some(_) => Verdict::Met,
                None => Verdict::Wait,
            };
        }
        if self.infer.has_vars(&self.a.types, s) {
            return Verdict::Wait;
        }
        // The bounds look into the type: the variables bound in it are followed first.
        let r = self.infer.resolve(&mut self.a.types, s);
        let ty = self.ty(r);
        let met = self.traits_unknown(r)
            || match op {
                OpNeed::Binary(b) => match op_bound(b) {
                    Some(bound) => self.satisfies(r, bound),
                    None => matches!(ty, Ty::Int(_)),
                },
                OpNeed::Neg => match ty {
                    Ty::Int(k) => k.signed(),
                    Ty::Float(_) => true,
                    Ty::Param(_) => self.satisfies(r, Bound::Num),
                    _ => false,
                },
                OpNeed::Not => matches!(ty, Ty::Bool | Ty::Int(_)),
            };
        if met {
            return Verdict::Met;
        }
        let shown = self.display(r);
        Verdict::Unmet(match (op, ty) {
            (OpNeed::Binary(b), _) => match op_bound(b) {
                Some(bound) => {
                    format!("`{}` is not defined for `{shown}` (it needs `{}`; §3.2)", b.symbol(), bound.name())
                }
                None => format!("`{}` is defined for integers only; found `{shown}` (§3.4)", b.symbol()),
            },
            (OpNeed::Neg, Ty::Int(k)) => format!("`-` on the unsigned type `{}`; it has no unary `-` (§3.4)", k.name()),
            (OpNeed::Neg, _) => format!("`-` needs a signed integer or float; found `{shown}`"),
            (OpNeed::Not, _) => not_unmet(&format!("`{shown}`")),
        })
    }
}

/// The trait a binary operator needs of its operands (§3.2, §6.3); `None` for the
/// operators of the integers only (the bitwise ones, the wrapping and saturating
/// ones, §3.4).
fn op_bound(op: BinOp) -> Option<Bound> {
    use BinOp::*;
    match op {
        Eq | Ne => Some(Bound::PartialEq),
        Lt | Le | Gt | Ge => Some(Bound::PartialOrd),
        Add | Sub | Mul | Div | Rem => Some(Bound::Num),
        BitAnd | BitOr | BitXor | Shl | Shr | WrapAdd | WrapSub | WrapMul | SatAdd | SatSub | SatMul => None,
        // `check_binary` gives them `Bool` and asks for no trait.
        And | Or => onsa_diag::internal::bug(None, "the trait of `&&` / `||` asked"),
    }
}

/// The E0401 of `!` on a type that is neither `Bool` nor an integer (`found`: the type
/// in backquotes, or `a float` for a float literal whose type is still open).
fn not_unmet(found: &str) -> String {
    format!("`!` needs `Bool` or an integer; found {found}")
}
