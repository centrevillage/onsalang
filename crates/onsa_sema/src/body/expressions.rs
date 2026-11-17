//! The expressions: the literals, struct literals, blocks, `match`,
//! closures and operators.

use super::arms::Arms;
use super::*;
use crate::constarg::Unheld;
use crate::traits::{Class, op_bound};

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ expressions

    pub(crate) fn check_expr(&mut self, e: ExprId, expected: Option<TyId>) -> R<TyId> {
        self.check_expr_as(e, expected, None)
    }

    /// `e`, with `expected` the type of an earlier part of a merge that
    /// joins function types when `join` (§4.7, S-1031): a function found in
    /// `e` is joined with it, and `e` has its own type. What gives `e`'s
    /// expected type on (a block to its end, parentheses, a merge) gives
    /// `join` too.
    pub(crate) fn check_expr_as(&mut self, e: ExprId, expected: Option<TyId>, join: Option<Merge>) -> R<TyId> {
        self.check_passed(e, expected, join, None)
    }

    /// `e`, a tail of what is being checked (§5.2: of a block, a branch of
    /// an `if`, an arm of a `match`, through parentheses), which passes on
    /// `joining` and the view `viewing`.
    pub(crate) fn check_tail(&mut self, e: ExprId, expected: Option<TyId>, join: Option<Merge>) -> R<TyId> {
        self.check_passed(e, expected, join, self.viewing)
    }

    /// `e` with `joining` and `viewing` set to `join` and `view`, and back.
    pub(crate) fn check_passed(
        &mut self,
        e: ExprId,
        expected: Option<TyId>,
        join: Option<Merge>,
        view: Option<Viewing>,
    ) -> R<TyId> {
        let outer = (std::mem::replace(&mut self.joining, join), std::mem::replace(&mut self.viewing, view));
        let t = self.check_expr_fit(e, expected);
        (self.joining, self.viewing) = outer;
        t
    }

    fn check_expr_fit(&mut self, e: ExprId, expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        if let Some(part) = self.info.diverging.evaluated_part(self.ast, e) {
            return Err(self.never_carried_out(span, part));
        }
        let t = match self.viewing {
            Some(v) => self.check_viewed(e, expected, v)?,
            None => self.check_expr_inner(e, expected)?,
        };
        let Some(exp) = expected else { return self.record_within(e, t) };
        // A path and an anonymous function in parentheses were fit inside.
        let found = match self.expr(e).kind {
            ExprKind::Closure { .. } => Found::Closure(None),
            _ => Found::Other,
        };
        let fns = self.fit_at(span, t, exp, found)?;
        // A function fit to a function type has the type expected, so that
        // what is made of it (a tuple, an arm) has it; one joined has its
        // own, and `e` keeps its own (§8.1, §4.7).
        let found = self.record_within(e, t)?;
        Ok(if fns && self.joining.is_none() { exp } else { found })
    }

    /// `e` at a position that passes the view `v` ([`BodyInfo::views`]),
    /// each part as `tails::tails` reads it: a node (a parenthesis, a block,
    /// an `if` with an `else`, a `match`) and what diverges have the view's
    /// type and pass it on; a tail is converted, a planar literal there
    /// opened ([`Self::planar_literal`]), and what is in them is checked
    /// with no view.
    // SPEC-GAP(S-1116): the branches of a node are of one type first (§4.7),
    // so a literal of channels and a planar array variable in two arms is E0401.
    fn check_viewed(&mut self, e: ExprId, expected: Option<TyId>, v: Viewing) -> R<TyId> {
        let node = matches!(
            self.expr(e).kind,
            ExprKind::Paren(_) | ExprKind::Block(_) | ExprKind::If { else_: Some(_), .. } | ExprKind::Match { .. }
        );
        let tail = !node && !self.info.diverging.expr(e);
        self.view_marks.push((e, tail));
        if !tail {
            return self.check_expr_inner(e, expected);
        }
        self.viewing = None;
        match (&self.expr(e).kind, v.planar) {
            (ExprKind::Array(parts), Some(_)) => self.planar_literal(e, parts, v.elem, v.mode),
            _ => self.check_expr_inner(e, expected),
        }
    }

    /// Whether a merge (`if`, `match`, an array) with the expected type
    /// `expected` of its branches joins their function types (§4.7,
    /// S-1031): with none, or one that is an undecided variable itself.
    fn undecided(&self, expected: Option<TyId>) -> bool {
        expected
            .is_none_or(|t| self.infer.is_unresolved(&self.a.types, t) && self.infer.lit_of(&self.a.types, t).is_none())
    }

    /// The expected type of the next branch of a merge after the branches
    /// of the types `ts` (§4.7): the first that is decided, so that each
    /// pair of function types is joined (S-1031), else the first.
    fn join_hint(&self, ts: &[TyId], expected: Option<TyId>) -> Option<TyId> {
        let decided = ts.iter().find(|&&t| !self.infer.is_unresolved(&self.a.types, t));
        decided.or(ts.first()).copied().or(expected)
    }

    /// The type of a merge at `span` whose branches of the types `ts` are
    /// joined (§4.7, S-1031): their join, which a branch of an undecided
    /// variable (the value of a `None` read, a diverging branch) takes once.
    pub(super) fn join_arms(&mut self, span: Span, ts: &[TyId]) -> R<TyId> {
        let mut t = ts[0];
        for &u in &ts[1..] {
            t = self.infer.join(&mut self.a.types, t, u);
        }
        for &u in ts {
            if self.infer.is_unresolved(&self.a.types, u) {
                self.unify_at(span, u, t)?;
            }
        }
        Ok(t)
    }

    /// The type of `e`, the `?` on `inner` (§9.1), with the constructors it
    /// keeps and leaves by in [`BodyInfo::tries`].
    fn check_try(&mut self, e: ExprId, inner: ExprId, span: Span) -> R<TyId> {
        let it = self.check_expr(inner, None)?;
        let it = self.known_shape(it, self.expr(inner).span, "operand of `?`")?;
        let ret = self.frames.last().unwrap().ret;
        let (d, a, lang) = match self.ty(it) {
            Ty::Error => return Ok(it),
            Ty::Named(d, a) => match self.a.modules.lang.of(d) {
                Some(lang) => (d, a, lang),
                None => return Err(self.try_on_other(span, it)),
            },
            _ => return Err(self.try_on_other(span, it)),
        };
        let ret_s = self.shallow(ret);
        let r = match self.ty(ret_s) {
            Ty::Named(r, args) if r == d => args,
            _ => {
                let (shown, rs) = (self.display(it), self.display(ret));
                return Err(self.err(
                    Code::E0414,
                    span,
                    format!("`?` on `{shown}` needs the function to return the same kind; it returns `{rs}` (§9.1)"),
                ));
            }
        };
        let variants = &self.a.def(d).as_enum().unwrap().variants;
        let (keep, exit) = (variants[lang.keep as usize].fields[0], variants[lang.exit as usize].fields.clone());
        // What the early return keeps is the function's.
        for f in exit {
            let (found, want) = (self.a.types.subst(f, &a), self.a.types.subst(f, &r));
            let cause = self.cause(span, None);
            if self.infer.unify(&mut self.a.types, found, want, &cause).is_err() {
                let (ea, er) = (self.display(found), self.display(want));
                return Err(self.err(
                    Code::E0414,
                    span,
                    format!("`?` needs the same error type as the function (`{er}`); found `{ea}`; convert it with `map_err` (§9.1)"),
                ));
            }
        }
        self.info.tries.insert(e, TryArms { keep: lang.keep, exit: lang.exit });
        Ok(self.a.types.subst(keep, &a))
    }

    /// E0414 for the `?` on `it`, which is no lang enum (§9.1).
    fn try_on_other(&mut self, span: Span, it: TyId) -> Stop {
        let shown = self.described(it);
        self.err(Code::E0414, span, format!("`?` needs an `Option` or `Result`; found {shown}"))
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
            ExprKind::Paren(inner) => self.check_tail(*inner, expected, self.joining),
            // `move x` (§5.2, S-21): same type as its operand. Whether it is a
            // place is the modes stage's (R-198: its candidate asks the kinds).
            ExprKind::Move(inner) => self.check_expr_as(*inner, expected, self.joining),
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
                            let what = ArgumentName::Text("the element type of `[]`".into());
                            self.defer(span, el, DeferredKind::Origin { what, rule: None });
                            el
                        }
                    };
                    return Ok(self.a.types.intern(Ty::Array(el, Len::Const(0))));
                }
                let join = self.undecided(exp_elem).then_some(Merge::Elements);
                let mut ts = vec![self.check_expr_as(elems[0], exp_elem, join)?];
                for &el in &elems[1..] {
                    ts.push(self.check_expr_as(el, self.join_hint(&ts, exp_elem), join)?);
                }
                let el = if join.is_some() { self.join_arms(span, &ts)? } else { ts[0] };
                Ok(self.a.types.intern(Ty::Array(el, Len::Const(elems.len() as u32))))
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
                let Some(n) = n else {
                    // An array that is the error type decides no element: one
                    // left open is no error of its own (§18.1).
                    let error = self.a.types.error();
                    self.unify_at(span, et, error)?;
                    return Ok(error);
                };
                Ok(self.a.types.intern(Ty::Array(et, n)))
            }
            ExprKind::Struct { path, fields, rest, type_args } => {
                self.reported_args(type_args.iter().map(|(k, _)| (e, *k as u32)))?;
                self.check_struct_lit(e, path, fields, rest.as_ref(), expected, span)
            }
            // The type arguments after the names of a chain (§4.5), which
            // the names stage gave to them.
            ExprKind::TypeArgs { base, .. } => {
                self.type_args_of(e)?;
                // After a member of a value, not called: a field, or what is
                // no field, as with no type arguments (E0413, S-992).
                if !self.names.members.contains_key(&e) {
                    self.written = Some((*base, span));
                    return self.check_expr_as(*base, expected, self.joining);
                }
                // The error of the member comes first (§4.5, S-992).
                self.check_expr(*base, None)?;
                Err(self.args_after_field(e))
            }
            ExprKind::Block(b) => self.check_block(e, self.block_of(e, b), expected),
            // What only a flow body holds is the names stage's E0821 outside
            // one (§11.1). In a flow body, `if~` and `match~` are typed as
            // `if` and `match`, and the flow checks read the `~`
            // (`crate::flow::map`); `at`, `^` and `par` are theirs.
            ExprKind::If { tilde: Some(_), .. } | ExprKind::Match { tilde: Some(_), .. } if self.flow.is_none() => {
                Err(self.flow_syntax(span))
            }
            ExprKind::Closure { ret_clock: Some(_), .. } | ExprKind::Feedback(_) | ExprKind::Par { .. } => {
                Err(self.flow_syntax(span))
            }
            // The names stage reads the operand of `at` before its clock
            // (§18.1), and may stop in it with no error (S-675).
            ExprKind::At { expr, .. } => {
                self.check_expr(*expr, None)?;
                Err(self.flow_syntax(span))
            }
            ExprKind::If { cond, then, else_, .. } => {
                let bool_ = self.bool_();
                self.check_expr(*cond, Some(bool_))?;
                match else_ {
                    Some(el) => {
                        let join = self.joining.or(self.undecided(expected).then_some(Merge::Branches));
                        let t = self.check_tail(*then, expected, join)?;
                        // Merged with the other branch: not the reason of the outer expectation.
                        let u = self.without_why(|ck| ck.check_tail(*el, Some(t), join.and(Some(Merge::Branches))))?;
                        if join.is_some() { self.join_arms(span, &[t, u]) } else { Ok(t) }
                    }
                    None => {
                        let unit = self.unit();
                        self.check_expr(*then, Some(unit))?;
                        Ok(unit)
                    }
                }
            }
            ExprKind::Match { scrutinee, arms, .. } => self.check_match(e, *scrutinee, self.arms_of(e, arms), expected),
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
                let d = self.cast_error(span, *inner, *ty, from, to);
                Err(self.diag(d))
            }
            ExprKind::Unary { op, expr: inner } => match self.joined_left(e) {
                // `a`, then `-x` on the next line, in the form of the candidate `a - x` (§6.1).
                Some(a) => self.check_binary(BinOp::Sub, Span::new(span.file, span.start, span.start + 1), a, *inner),
                None => self.check_unary(e, *op, *inner, span),
            },
            ExprKind::Call { callee, kind, args } => self.check_call(e, *callee, *kind, args, expected),
            ExprKind::TupleIndex { base, index, index_span } => {
                let bt = self.check_expr(*base, None)?;
                let bt = self.known_shape(bt, self.expr(*base).span, "value")?;
                self.tuple_element(bt, *index, *index_span)
            }
            ExprKind::Index { base, index } => {
                let bt = self.check_expr(*base, None)?;
                self.element(e, *base, bt, *index)
            }
            ExprKind::Try(inner) => self.check_try(e, *inner, span),
            // The parser makes a range only as a head; the words of the row
            // that finds one elsewhere (`range_outside_header`).
            ExprKind::Range(_) => {
                let row = onsa_syntax::foreign::row(onsa_syntax::foreign::RowId::RangeOutsideHeader);
                Err(self.diag(Diagnostic::new(Stage::Syntax, Code::E0002, span, row.message).with_rule(row.rule)))
            }
        }
    }

    /// The type of `e`, `base[index]`, where `base` has the type `bt`.
    pub(super) fn element(&mut self, e: ExprId, base: ExprId, bt: TyId, index: ExprId) -> R<TyId> {
        let span = self.expr(e).span;
        let bt = self.known_shape(bt, self.expr(base).span, "value")?;
        let u32 = self.u32();
        self.check_expr(index, Some(u32))?;
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
                self.defer(span, t, DeferredKind::FloatLit { lit: e, rule: None });
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
                match self.fixed_literal(self.expr(e).span, s, expected)? {
                    Some(t) => Ok(t),
                    None => Ok(self.a.types.builtin(BuiltinTy::Str, vec![])),
                }
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

    /// `[e; N]` / array length in an expression (§4.5; the forms are read in
    /// `constarg.rs`, from the records of the names of the body). `None`: a
    /// length the check does not read (§18.1, S-690).
    /// The end of the check at what only a flow body holds, outside one, and
    /// at what a flow body cannot contain: the names stage stopped before it
    /// with no error (a name held as an error in a constant expression,
    /// S-692, after which this check goes on, S-690; R-430), else it would
    /// have reported its E0821 (§11.1) or E0806 (§11.2).
    pub(crate) fn flow_syntax(&mut self, span: Span) -> Stop {
        if !self.names.complete {
            return self.held_stop();
        }
        onsa_diag::internal::bug(Some(span), "a form of a flow the names stage did not stop at")
    }

    pub(crate) fn const_len(&mut self, len: ExprId) -> R<Option<Len>> {
        match self.const_expr(len) {
            Ok((value, constant)) => {
                let u32 = self.u32();
                self.record(len, u32);
                match value {
                    crate::constarg::ConstU32::Value(v) => {
                        if let Some(d) = constant {
                            self.info.targets.insert(len, Target::Const { def: d, of: None, inst: None });
                        }
                        Ok(Some(Len::Const(v)))
                    }
                    crate::constarg::ConstU32::Param(i) => Ok(Some(Len::Param(i))),
                }
            }
            Err(Unheld::Report(d) | Unheld::Uncomputed(d)) => Err(self.diag(d)),
            // A constant whose value was not read (S-59) or a name held as an
            // error: no diagnostic, and the check goes on (§18.1, S-690).
            Err(Unheld::Unknown) => {
                let u32 = self.u32();
                self.record(len, u32);
                self.a.read_held.insert(self.def);
                Ok(None)
            }
        }
    }

    /// The constant expression `e` of the body, read by the one reader
    /// (`crate::constarg`) from the records of the names of the body, which
    /// knows the errors of the headings ([`crate::constarg::ConstErr::unheld`]).
    pub(crate) fn const_expr(&mut self, e: ExprId) -> Result<(crate::constarg::ConstU32, Option<DefId>), Unheld> {
        let cx = crate::constarg::ConstCx { m: self.m, ast: self.ast, text: self.text, names: &self.names };
        crate::constarg::expr(self.a, &cx, e).map_err(crate::constarg::ConstErr::unheld)
    }

    /// The struct literal `e` (§4.4). An alias of the error type is no
    /// struct here: its path has no record (S-728, `names/body/paths.rs`).
    fn check_struct_lit(
        &mut self,
        e: ExprId,
        path: &Path,
        fields: &[(Ident, ExprId)],
        rest: Option<&onsa_syntax::ast::StructRest>,
        expected: Option<TyId>,
        span: Span,
    ) -> R<TyId> {
        let Some(&StructRes { entity, owner }) = self.names.structs.get(&e) else { return Err(self.held_stop()) };
        let d = match entity {
            Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Struct(_)) => d,
            _ => return Err(self.diag(crate::names::body::not_a_struct(self.src(path.span), path.span))),
        };
        self.generated_at(d, path.span)?;
        let s = self.a.def(d).as_struct().unwrap().clone();
        // A literal of a generated `In` or `Out` passes its fields as views,
        // by the mode of the argument it is (§11.6); out of one, it is an
        // owned row, the modes' E0710 (§5.4).
        let mode = self.arg_literal.take().filter(|&(x, _)| x == e).map_or(Mode::Borrow, |(_, m)| m);
        let views = s.flow_ty.is_some_and(crate::def::FlowTy::views);
        if views {
            self.info.planar.insert(e);
        }
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
        let whole = crate::structpat::Whole::Literal { filled: rest.is_some() };
        self.whole_reach(d, defs, &written, path.span, whole)?;
        let mut seen: Vec<&str> = Vec::new();
        for (name, value) in fields {
            if seen.contains(&name.name.as_str()) {
                return Err(self.err(Code::E0410, name.span, format!("field `{}` is given twice", name.name)));
            }
            seen.push(&name.name);
            let Some((k, _)) = self.a.named_field(d, &name.name) else {
                if failed {
                    let error = self.a.types.error();
                    self.check_expr(*value, Some(error))?;
                    continue;
                }
                let shown = self.a.shown_name(d);
                return Err(self.err(Code::E0410, name.span, format!("`{shown}` has no field `{}`", name.name)));
            };
            let f = &defs[k];
            self.a.note_use(f.span, name.span);
            let ft = self.a.types.subst(f.ty, &args);
            let why = format!("the field `{}`", name.name);
            match self.view_param(ft).filter(|_| views) {
                Some(v) => self.with_why(why, ft, |ck| ck.view_arg(*value, ft, v, mode))?,
                None => _ = self.with_why(why, ft, |ck| ck.check_expr(*value, Some(ft)))?,
            }
        }
        if !failed {
            self.literal_rest(d, (defs, &seen), rest.copied(), path.span)?;
        }
        let t = self.a.types.intern(Ty::Named(d, args.clone()));
        self.finish_instance(d, args, span)?;
        Ok(t)
    }

    fn check_block(&mut self, id: ExprId, b: &'a Block, expected: Option<TyId>) -> R<TyId> {
        if let Some(f) = &mut self.flow {
            f.depth += 1;
        }
        self.blocks.push((id, b, 0));
        let r = (|| -> R<TyId> {
            for (i, &s) in b.stmts.iter().enumerate() {
                self.blocks.last_mut().unwrap().2 = i;
                self.check_stmt(s)?;
                self.after_stmt()?;
            }
            match b.tail {
                Some(t) => self.check_tail(t, expected, self.joining),
                // A block that ends in a diverging statement takes any type
                // (§7; a trailing `return e` is allowed, §6.1).
                None if self.info.diverging.block(self.ast, b) => Ok(expected.unwrap_or_else(|| self.fresh())),
                None => {
                    let unit = self.unit();
                    // A value of the wrong type is reported at the last
                    // statement, which gives no value (§6.1, S-40).
                    if let (Some(&last), Some(expected)) = (b.stmts.last(), expected) {
                        self.unify_at(self.ast.stmt(last).span, unit, expected)?;
                    }
                    Ok(unit)
                }
            }
        })();
        self.blocks.pop();
        if let Some(f) = &mut self.flow {
            f.depth -= 1;
        }
        r
    }

    fn check_match(&mut self, e: ExprId, scrutinee: ExprId, arms: &'a [MatchArm], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        let st = self.check_expr(scrutinee, None)?;
        let st = self.known(st, self.expr(scrutinee).span, "`match` operand")?;
        let join = self.joining.or(self.undecided(expected).then_some(Merge::Branches));
        let (mut seen, mut types) = (Seen::default(), Vec::new());
        self.read_arms(&Arms { expr: e, arms, st, expected, join }, &mut seen, &mut types)?;
        if self.judges_arms(st)
            && let Some(missing) = self.missing_pattern(&mut seen, st)
        {
            let message = match &missing {
                Missing::Value(value) => format!("`match` is not exhaustive; `{value}` is not covered (§7)"),
                Missing::OverLimit => "`match` is not known to be exhaustive (§7)".to_string(),
            };
            let d = Diagnostic::new(Stage::Types, Code::E0501, span, message)
                .with_found(self.src(self.expr(scrutinee).span));
            return Err(self.diag(match missing {
                Missing::Value(_) => d,
                Missing::OverLimit => d.with_rule("the arms are too many ways to read through; write a `_` arm"),
            }));
        }
        match expected {
            _ if join.is_some() && !types.is_empty() => self.join_arms(span, &types),
            Some(t) => Ok(t),
            None => Ok(self.unit()),
        }
    }

    /// Whether the arms of a `match` of a value of type `st` are judged, for
    /// exhaustiveness and for reachability alike.
    // SPEC-GAP(S-260): the variants of an enum whose unit failed in the
    // syntax stage are not all known; its `match` is not judged. Nor is the
    // `match` of a value of the error type (§18.1, R-271).
    pub(super) fn judges_arms(&self, st: TyId) -> bool {
        !self.mentions_failed(st) && !matches!(self.ty(self.shallow(st)), Ty::Error)
    }

    /// The arms of `m` in turn: the pattern, then whether the arms before it
    /// leave it a value (§7, E0503, before its body, S-876), then the guard
    /// and the body. An arm with a guard is asked about but covers nothing.
    /// Stops at an arm that gets no value and gives its index, with nothing
    /// reported ([`Self::read_arms`]).
    pub(super) fn check_arms(&mut self, m: &Arms<'_>, seen: &mut Seen, types: &mut Vec<TyId>) -> R<Option<usize>> {
        let (st, expected) = (m.st, m.expected);
        for (k, arm) in m.arms.iter().enumerate() {
            let waiting = (self.deferred.len(), self.deferred_end.len());
            let p = self.bind_pat(arm.pat, st, false);
            let bad = std::mem::take(&mut self.bad_consts);
            let p = p?;
            // Before the E0020: the guard form of an arm that is covered is
            // an E0503 of this stage (§18.1), and the arm is one to delete.
            if self.judges_arms(st) && !self.reachable(seen, &p, st) {
                // What a literal of the pattern waits for goes with the arm.
                self.deferred.truncate(waiting.0);
                self.deferred_end.truncate(waiting.1);
                return Ok(Some(k));
            }
            if !bad.is_empty() {
                return Err(self.reject_constants(arm, bad));
            }
            if let Some(g) = arm.guard {
                let bool_ = self.bool_();
                self.check_expr(g, Some(bool_))?;
            } else {
                seen.add(p, self.ast.pat(arm.pat).span);
            }
            // The arms after the first are merged with it (not the outer reason).
            let join = if types.is_empty() { m.join } else { m.join.and(Some(Merge::Branches)) };
            let hint = if join.is_some() { self.join_hint(types, expected) } else { expected };
            let t = if hint == expected {
                self.check_tail(arm.body, hint, join)?
            } else {
                self.without_why(|ck| ck.check_tail(arm.body, hint, join))?
            };
            types.push(t);
        }
        Ok(None)
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
        // Read here: the body checks arguments of its own.
        let is_arg = self.arg_closure.take() == Some(e);
        let exp_fn: Option<FnTy> = expected.and_then(|t| match self.ty(self.shallow(t)) {
            Ty::Fn(f) => Some(f),
            _ => None,
        });
        let (from, effects, rt) = self.closure_row(e, effects.is_some(), exp_fn.as_ref(), expected)?;
        self.info.closure_rows.insert(e, from);
        if let (Some(f), Some(exp)) = (&exp_fn, expected)
            && f.params.len() != params.len()
        {
            return self.closure_of_other_arity(span, params, ret, effects, f, exp);
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
                    ParamName::Wild(_) if p.mode == Mode::Move => {
                        self.unbound(Unbound::Param { closure: Some(e), index: k }, p.span, vec![*t]);
                    }
                    ParamName::Wild(_) => {}
                }
            }
            self.check_expr(body, Some(ret_ty))?;
            Ok(())
        })();
        self.frames.pop();
        r?;
        let t = self.a.types.intern(Ty::Fn(FnTy { rt, params: ptys, ret: ret_ty, effects }));
        // Written as an argument, it may have the candidate of S-872 ([`Self::modes_help`]).
        if is_arg
            && exp_fn.is_some()
            && let Some(exp) = expected
        {
            self.fit_at(span, t, exp, Found::Closure(Some(params)))?;
        }
        Ok(t)
    }

    /// The row of the anonymous function `e` (`written` or not) with the
    /// type `expected` (`exp_fn` when a function type), and where it comes
    /// from, kept for the notes of an E0601 (S-1041); and whether it is
    /// `rt`. A later branch of a merge takes neither (§4.7, S-1032 (ii-3)),
    /// in a branch of it too (an `else if`, an `if` or a `match` in a
    /// branch, S-1061); the first has no type before it (none expected).
    fn closure_row(
        &mut self,
        e: ExprId,
        written: bool,
        exp_fn: Option<&FnTy>,
        expected: Option<TyId>,
    ) -> R<(RowFrom, crate::ty::EffectSet, bool)> {
        let later = self.joining.is_some() && !self.undecided(expected);
        let none = crate::ty::EffectSet::default();
        let (from, row) = match (exp_fn, expected) {
            // As the names stage read it (S-738).
            _ if written => (RowFrom::Written, self.names.effects.get(&e).cloned().ok_or_else(|| self.held_stop())?),
            _ if later => (RowFrom::Joining, none),
            (Some(f), Some(t)) => (RowFrom::Expected(t), f.effects.clone()),
            (None, Some(t)) if matches!(self.ty(self.shallow(t)), Ty::Error) => (RowFrom::Unread, none),
            _ => (RowFrom::NoneExpected, none),
        };
        Ok((from, row, !later && exp_fn.is_some_and(|f| f.rt)))
    }

    /// The E0401 of an anonymous function with another number of parameters
    /// than the function type `f` expected, as of a function item (§8.1,
    /// S-894): its type as written, a type left out shown as not known.
    fn closure_of_other_arity(
        &mut self,
        span: Span,
        params: &[Param],
        ret: Option<onsa_syntax::ast::TypeId>,
        effects: crate::ty::EffectSet,
        f: &FnTy,
        exp: TyId,
    ) -> R<TyId> {
        let mut ptys = Vec::new();
        for p in params {
            let t = match p.ty {
                Some(t) => self.lower_type_expr(t)?,
                None => self.fresh(),
            };
            ptys.push((p.mode, t));
        }
        let ret = ret.map_or(Ok(f.ret), |t| self.lower_type_expr(t))?;
        let t = self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params: ptys, ret, effects }));
        self.unify_at(span, t, exp)?;
        Ok(t)
    }

    /// One operator of a chain (the tree of §3.1): the left operand, the
    /// right one, then what the operator requires of them (S-255).
    fn check_binary(&mut self, op: BinOp, op_span: Span, lhs: ExprId, rhs: ExprId) -> R<TyId> {
        Ok(match op.group() {
            OpGroup::Comparison => return self.check_comparison(op, op_span, lhs, rhs),
            OpGroup::And | OpGroup::Or => {
                let t = self.check_expr(lhs, None)?;
                let bool_ = self.bool_();
                self.unify_at(self.expr(lhs).span, t, bool_)?;
                self.check_expr(rhs, Some(bool_))?;
                bool_
            }
            OpGroup::Bitwise if matches!(op, BinOp::Shl | BinOp::Shr) => {
                let t = self.check_expr(lhs, None)?;
                let u32 = self.u32();
                self.check_expr(rhs, Some(u32))?;
                self.require_op(OpNeed::Binary(op), t, op_span)?;
                t
            }
            OpGroup::Bitwise | OpGroup::Additive | OpGroup::Multiplicative | OpGroup::Remainder => {
                let t = self.check_expr(lhs, None)?;
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                self.require_op(OpNeed::Binary(op), t, op_span)?;
                t
            }
        })
    }

    /// A comparison (§3.2): a string literal with no interpolation on one side,
    /// through parentheses (S-1009), has the type of the other side as its
    /// expected type (§4.7, S-614 C2), so the other side is checked first.
    fn check_comparison(&mut self, op: BinOp, op_span: Span, lhs: ExprId, rhs: ExprId) -> R<TyId> {
        let ast = self.ast;
        let plain = |e: ExprId| {
            let kind = &ast.expr(ast.without_parens(e)).kind;
            matches!(kind, ExprKind::Lit(Lit::Str(s)) if s.value().is_some())
        };
        let (left, right) = (plain(lhs), plain(rhs));
        let t = if left && !right {
            let t = self.check_expr(rhs, None)?;
            self.check_expr(lhs, Some(t))?;
            t
        } else {
            let t = self.check_expr(lhs, None)?;
            let rt = self.check_expr(rhs, right.then_some(t))?;
            self.unify_at(self.expr(rhs).span, rt, t)?;
            t
        };
        self.require_op(OpNeed::Binary(op), t, op_span)?;
        Ok(self.bool_())
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
        // An operand whose type is decided here is judged here, not after the statement
        // (S-857): in one statement, its E0401 comes before the E0401 of an operator that
        // waited and before a later type error of the statement.
        match self.operator_verdict(op, t) {
            Verdict::Met => Ok(()),
            Verdict::Wait => {
                self.defer(span, t, DeferredKind::Operator { op });
                Ok(())
            }
            Verdict::Unmet(msg) => {
                let d = Diagnostic::new(Stage::Types, Code::E0401, span, msg).with_found(self.src(span));
                let d = self.with_bound_fix(d, op, t);
                Err(self.diag(d))
            }
        }
    }

    /// Whether the type `t` has what the operator `op` needs: the one judgment of the
    /// operators, at the operator and in a deferred item. A literal variable decides it
    /// by its kind (an integer literal has every trait of an operator but the `-` of an
    /// unsigned type; a float literal has the traits of a float). Any other variable
    /// left waits for the statement that decides it.
    pub(crate) fn operator_verdict(&mut self, op: OpNeed, t: TyId) -> Verdict {
        let s = self.shallow(t);
        let need = op_bound(op);
        if matches!(self.ty(s), Ty::Var(_)) {
            return match self.infer.lit_of(&self.a.types, s) {
                Some(LitKind::Float) if !Class::Float.implements(need) => {
                    Verdict::Unmet(op_unmet(op, LitKind::Float.words()))
                }
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
        if self.satisfies(r, need) {
            return Verdict::Met;
        }
        Verdict::Unmet(op_unmet(op, &format!("`{}`", self.display(r))))
    }
}

/// The E0401 of the operator `op` on `found` (the type in backquotes, or `a float` for
/// a float literal whose type is still open).
fn op_unmet(op: OpNeed, found: &str) -> String {
    format!("`{}` is not defined for {found} (it needs `{}`; §3.2)", op.symbol(), op_bound(op).name())
}
