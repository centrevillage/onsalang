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
            ExprKind::Path(p) => {
                if p.segments.len() == 1 {
                    let name = p.segments[0].clone();
                    self.check_single_path(e, &name, expected)
                } else {
                    let chain: Vec<(ExprId, Ident)> = p.segments.iter().map(|s| (e, s.clone())).collect();
                    self.check_chain(&chain, expected)
                }
            }
            ExprKind::Field { .. } => {
                if let Some(chain) = self.name_chain(e) {
                    self.check_chain(&chain, expected)
                } else {
                    let ExprKind::Field { base, name } = &expr.kind else { unreachable!() };
                    let bt = self.check_expr(*base, None)?;
                    let bt = self.known(bt, self.expr(*base).span, "value")?;
                    self.field_type(bt, name)
                }
            }
            ExprKind::Hole => {
                // Reported at the end of the body (§18.1), once later statements
                // have had the chance to decide the type.
                let t = expected.unwrap_or_else(|| self.fresh());
                let visible: Vec<LocalId> =
                    self.scopes.iter().flat_map(|s| s.names.iter().map(|(_, id)| *id)).collect();
                self.defer(span, t, DeferredKind::Hole { visible });
                Ok(self.record(e, t))
            }
            ExprKind::Paren(inner) => self.check_expr(*inner, expected),
            ExprKind::Move(inner) => {
                // `move x` (§5.2, S-21): same type as its operand, which must be a place.
                let t = self.check_expr(*inner, expected)?;
                if !self.is_place(*inner) {
                    let ispan = self.expr(*inner).span;
                    return Err(self.err(
                        Code::E0711,
                        ispan,
                        "`move` needs a place (a variable or its field); other values are already owned by the expression",
                    ));
                }
                Ok(t)
            }
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
                Ok(self.a.types.intern(Ty::Array(et, n)))
            }
            ExprKind::Struct { type_args, .. } if !type_args.is_empty() => {
                Err(self.type_args_unsupported(type_args[0].1.span))
            }
            ExprKind::Struct { path, fields, .. } => self.check_struct_lit(path, fields, expected, self.expr(e).span),
            ExprKind::TypeArgs { args, .. } => Err(self.type_args_unsupported(args.span)),
            ExprKind::Block(b) => self.check_block(b, expected),
            // The flow syntax outside a flow body does not reach here
            // (`crate::flow_syntax`). In a flow body, `if~` and `match~` are
            // typed as `if` and `match`, and the flow checks read the `~`
            // (`crate::flow::map`); `at` and `^` are theirs.
            ExprKind::If { tilde: Some(t), .. } if self.flow.is_none() => Err(self.flow_form(*t, FlowForm::IfTilde)),
            ExprKind::Match { tilde: Some(t), .. } if self.flow.is_none() => {
                Err(self.flow_form(*t, FlowForm::MatchTilde))
            }
            ExprKind::Closure { ret_clock: Some(c), .. } | ExprKind::At { clock: c, .. } => {
                Err(self.flow_form(c.span, FlowForm::Clock))
            }
            ExprKind::Feedback(_) => Err(self.flow_form(span, FlowForm::Feedback)),
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
            ExprKind::Par { .. } => Err(self.err(
                Code::E0401,
                span,
                "`par` replicates flow instances and is only written inside a flow body (§11.5)",
            )),
            &ExprKind::Binary { op, op_span, lhs, rhs } => self.check_binary(op, op_span, lhs, rhs),
            ExprKind::Cast { expr: inner, ty } => {
                let it = self.check_expr(*inner, None)?;
                let from = self.known(it, self.expr(*inner).span, "operand of `as`")?;
                let to = self.lower_type_expr(*ty)?;
                // The error type (what a syntax error left unread, S-59) is not
                // checked: no diagnostic for it (R-71).
                let error = |t: TyId| matches!(self.a.types.get(t), Ty::Error);
                if builtin::cast_allowed(&self.a.types, from, to) || error(from) || error(to) {
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
                if let Some(m) = builtin::cast_suggestion(&self.a.types, from, to) {
                    let inner_src = self.src(self.expr(*inner).span);
                    d = d.with_fix(Fix::replace(format!("call `{m}`"), span, format!("{inner_src}{m}")));
                }
                Err(self.diag(d))
            }
            ExprKind::Unary { op, expr: inner } => {
                let t = self.check_expr(*inner, None)?;
                let s = self.shallow(t);
                match op {
                    UnOp::Neg => {
                        // A `-` whose operand is a literal is a part of the literal's value
                        // (§4.7, S-184, S-227): the literal's own check covers the sign.
                        if let Some(lit) = self.ast.negated_literal(e) {
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
                        match self.ty(s) {
                            Ty::Int(k) if k.signed() => Ok(t),
                            Ty::Float(_) | Ty::Error => Ok(t),
                            Ty::Var(_) if self.infer.lit_of(&self.a.types, s).is_some() => {
                                self.defer(span, t, DeferredKind::UnsignedNeg);
                                Ok(t)
                            }
                            Ty::Param(_) if self.satisfies(s, Bound::Num) => Ok(t),
                            Ty::Var(_) => Err(self.known(t, span, "operand of `-`").unwrap_err()),
                            _ => {
                                let shown = self.display(t);
                                Err(self.err(
                                    Code::E0401,
                                    span,
                                    format!("`-` needs a signed integer or float; found `{shown}`"),
                                ))
                            }
                        }
                    }
                    UnOp::Not => match self.ty(s) {
                        Ty::Bool | Ty::Int(_) | Ty::Error => Ok(t),
                        Ty::Var(_) if self.infer.lit_of(&self.a.types, s) == Some(LitKind::Int) => Ok(t),
                        Ty::Var(_) => Err(self.known(t, span, "operand of `!`").unwrap_err()),
                        _ => {
                            let shown = self.display(t);
                            Err(self.err(Code::E0401, span, format!("`!` needs `Bool` or an integer; found `{shown}`")))
                        }
                    },
                }
            }
            ExprKind::Call { callee, kind, args } => self.check_call(e, *callee, *kind, args, expected),
            ExprKind::TupleIndex { base, index, index_span } => {
                let bt = self.check_expr(*base, None)?;
                let bt = self.known(bt, self.expr(*base).span, "value")?;
                match self.ty(bt) {
                    Ty::Tuple(ts) if (*index as usize) < ts.len() => Ok(ts[*index as usize]),
                    Ty::Named(d, args) => {
                        if let DefKind::Struct(s) = &self.a.def(d).kind
                            && let Fields::Tuple(inner) = s.fields
                            && *index == 0
                        {
                            return Ok(self.subst(inner, &args));
                        }
                        let shown = self.display(bt);
                        Err(self.err(Code::E0413, *index_span, format!("`{shown}` has no element `{index}`")))
                    }
                    Ty::Error => Ok(bt),
                    _ => {
                        let shown = self.display(bt);
                        Err(self.err(Code::E0413, *index_span, format!("`{shown}` has no element `{index}`")))
                    }
                }
            }
            ExprKind::Index { base, index } => {
                let bt = self.check_expr(*base, None)?;
                let bt = self.known(bt, self.expr(*base).span, "value")?;
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
                        let shown = self.display(bt);
                        Err(self.err(Code::E0413, span, format!("`{shown}` cannot be indexed")))
                    }
                }
            }
            ExprKind::Try(inner) => {
                let it = self.check_expr(*inner, None)?;
                let it = self.known(it, self.expr(*inner).span, "operand of `?`")?;
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
                        let shown = self.display(it);
                        Err(self.err(Code::E0414, span, format!("`?` needs an `Option` or `Result`; found `{shown}`")))
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
                for seg in &s.segments {
                    if let StrSeg::Interp(path) = seg {
                        let head = &path.segments[0];
                        let Some(id) = self.lookup_local(&head.name) else {
                            return Err(self.name_err(
                                Code::E0302,
                                head.span,
                                format!("cannot find `{}` for the interpolation", head.name),
                            ));
                        };
                        let mut t = self.local_ty(id);
                        for seg in &path.segments[1..] {
                            let base = self.known(t, seg.span, "value")?;
                            t = self.field_type(base, seg)?;
                        }
                    }
                }
                Ok(self.a.types.builtin(BuiltinTy::Str, vec![]))
            }
        }
    }

    /// `[e; N]` / array length in an expression (§4.5; the forms are read in `constarg.rs`).
    pub(crate) fn const_len(&mut self, len: ExprId) -> R<Len> {
        let generics = self.generics.clone();
        match crate::constarg::expr(self.a, self.m, self.ast, self.text, &generics, len) {
            Ok((value, constant)) => {
                let u32 = self.u32();
                self.record(len, u32);
                match value {
                    crate::constarg::ConstU32::Value(v) => {
                        if let Some(d) = constant {
                            self.info.targets.insert(len, Target::Const(d));
                        }
                        Ok(Len::Const(v))
                    }
                    crate::constarg::ConstU32::Param(i) => Ok(Len::Param(i)),
                }
            }
            Err(crate::constarg::ConstErr::Report(d) | crate::constarg::ConstErr::Uncomputed(d)) => Err(self.diag(d)),
            // A constant whose value was not read (S-59): the check of this
            // body stops there without a diagnostic.
            Err(crate::constarg::ConstErr::Unknown) => {
                self.failed = true;
                Err(Stop)
            }
        }
    }

    fn check_struct_lit(
        &mut self,
        path: &Path,
        fields: &[(Ident, ExprId)],
        expected: Option<TyId>,
        span: Span,
    ) -> R<TyId> {
        let entity = match self.a.resolve_path(self.m, path) {
            Ok(en) => en,
            Err(err) => return Err(self.resolve_error(path, err)),
        };
        let d = match entity {
            Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Struct(_)) => d,
            _ => {
                let name = self.src(path.span);
                return Err(self.err(Code::E0401, path.span, format!("`{name}` is not a struct")));
            }
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
            let ft = self.subst(f.ty, &args);
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
        self.push_scope();
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
                    let diverges = b.stmts.last().is_some_and(|&s| {
                        matches!(self.ast.stmt(s).kind, StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue)
                    });
                    if diverges { Ok(self.fresh()) } else { Ok(self.unit()) }
                }
            }
        })();
        if let Some(f) = &mut self.flow {
            f.depth -= 1;
        }
        self.pop_scope();
        r
    }

    fn check_match(&mut self, scrutinee: ExprId, arms: &[MatchArm], expected: Option<TyId>, span: Span) -> R<TyId> {
        let st = self.check_expr(scrutinee, None)?;
        let st = self.known(st, self.expr(scrutinee).span, "`match` operand")?;
        // §7 (S-21): `match x` binds borrows; only `match move x` gives the arms ownership.
        let borrow = !matches!(self.expr(scrutinee).kind, ExprKind::Move(_));
        let mut result: Option<TyId> = expected;
        let mut rows: Vec<Vec<P>> = Vec::new();
        for arm in arms {
            self.push_scope();
            let r = (|| -> R<()> {
                let p = self.bind_pat(arm.pat, st, false, borrow, LocalKind::MatchBind)?;
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
            self.pop_scope();
            r?;
        }
        // SPEC-GAP(S-260): the variants of an enum whose unit failed in the
        // syntax stage are not all known; its `match` is not counted.
        if !self.mentions_failed(st)
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
            Some(row) => {
                let mut set = crate::ty::EffectSet::default();
                for p in &row.effects {
                    let n = p.segments.last().unwrap();
                    if n.name == "Alloc" {
                        set.alloc = true;
                    } else {
                        return Err(self.unsupported(n.span, Feature::Effects, &[&n.name]));
                    }
                }
                set
            }
            None => exp_fn.as_ref().map(|f| f.effects.clone()).unwrap_or_default(),
        };
        let rt = exp_fn.as_ref().map(|f| f.rt).unwrap_or(false);
        // The body runs in its own frame: `return` targets the closure, captures are recorded.
        let frame =
            Frame { local_base: self.info.locals.len() as u32, ret: ret_ty, loop_depth: 0, captures: Vec::new() };
        self.frames.push(frame);
        self.push_scope();
        let r = (|| -> R<()> {
            for (p, (_, t)) in params.iter().zip(&ptys) {
                match &p.name {
                    ParamName::Ident(id) => {
                        self.declare(id, *t, LocalKind::ClosureParam(p.mode), p.mode == Mode::Borrow)?;
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
        self.pop_scope();
        let frame = self.frames.pop().unwrap();
        r?;
        self.info.captures.insert(e, frame.captures);
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
                let s = self.shallow(t);
                let bound = if matches!(op, BinOp::Eq | BinOp::Ne) { Bound::PartialEq } else { Bound::PartialOrd };
                self.require_operand(s, bound, op, op_span)?;
                self.bool_()
            }
            OpGroup::Bitwise if matches!(op, BinOp::Shl | BinOp::Shr) => {
                let u32 = self.u32();
                self.check_expr(rhs, Some(u32))?;
                let s = self.shallow(t);
                self.require_int(s, op, op_span)?;
                t
            }
            OpGroup::Bitwise => {
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                let s = self.shallow(t);
                self.require_int(s, op, op_span)?;
                t
            }
            OpGroup::Additive | OpGroup::Multiplicative | OpGroup::Remainder => {
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                let s = self.shallow(t);
                if matches!(
                    op,
                    BinOp::WrapAdd | BinOp::WrapSub | BinOp::WrapMul | BinOp::SatAdd | BinOp::SatSub | BinOp::SatMul
                ) {
                    self.require_int(s, op, op_span)?;
                } else {
                    self.require_operand(s, Bound::Num, op, op_span)?;
                }
                t
            }
        })
    }

    /// The operand type of an operator must support it (via its builtin trait, §3.2).
    pub(crate) fn require_operand(&mut self, s: TyId, bound: Bound, op: BinOp, span: Span) -> R<()> {
        match self.ty(s) {
            Ty::Var(_) => match (self.infer.lit_of(&self.a.types, s), bound) {
                (Some(_), Bound::Num | Bound::PartialEq | Bound::PartialOrd) => Ok(()),
                (Some(_), _) => Ok(()),
                (None, _) => Err(self.known(s, span, &format!("operand of `{}`", op.symbol())).unwrap_err()),
            },
            _ => {
                if self.satisfies(s, bound) {
                    Ok(())
                } else {
                    let shown = self.display(s);
                    Err(self.err(
                        Code::E0401,
                        span,
                        format!(
                            "`{}` is not defined for `{shown}` (it needs `{}`; §3.2)",
                            op.symbol(),
                            bound_name(bound)
                        ),
                    ))
                }
            }
        }
    }

    fn require_int(&mut self, s: TyId, op: BinOp, span: Span) -> R<()> {
        match self.ty(s) {
            Ty::Int(_) | Ty::Error => Ok(()),
            Ty::Var(_) => match self.infer.lit_of(&self.a.types, s) {
                Some(LitKind::Int) => Ok(()),
                Some(LitKind::Float) => {
                    Err(self.err(Code::E0401, span, format!("`{}` is defined for integers only (§3.4)", op.symbol())))
                }
                None => Err(self.known(s, span, &format!("operand of `{}`", op.symbol())).unwrap_err()),
            },
            _ => {
                let shown = self.display(s);
                Err(self.err(
                    Code::E0401,
                    span,
                    format!("`{}` is defined for integers only; found `{shown}` (§3.4)", op.symbol()),
                ))
            }
        }
    }
}
