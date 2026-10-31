//! The flow mode of the checker (T3-1; §11.2–§11.5): the inputs and the
//! `let`s of a flow body, its statements and expressions, `par`, and the
//! calls of instances, delays and `sample_rate()`.

use super::*;
use crate::body::BANG_ON_NO_INOUT_SELF;
use crate::flow_names::FlowBuiltin;
use crate::names::body::{Origin, PathRes};
use crate::resolve::{Callee, NameKind};

impl<'a> Checker<'a> {
    pub(super) fn fcx(&mut self) -> &mut FlowCx {
        self.flow.as_mut().expect("flow mode")
    }

    /// Entry point: declare the inputs, pre-declare the `let`s, check the body.
    pub(crate) fn check_flow_body(&mut self, body: ExprId, out: TyId) {
        self.flow = Some(FlowCx::default());
        self.frames.push(Frame { ret: out, loop_depth: 0 });
        let r = (|| -> R<()> {
            self.declare_flow_inputs()?;
            self.prescan_lets(body)?;
            self.check_expr(body, Some(out))?;
            Ok(())
        })();
        let _ = r;
        self.frames.pop();
    }

    fn declare_flow_inputs(&mut self) -> R<()> {
        let inputs: Vec<FlowInput> = self.a.def(self.def).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
        for (k, input) in (0..).zip(inputs) {
            let id = self.local_of(Origin::FlowInput(k))?;
            self.bind_local(id, input.ty, input.span)?;
            let rate = FlowRate::from_rate(input.rate);
            self.fcx().inputs.push((id, rate));
        }
        Ok(())
    }

    /// §11.2: the body is `let`s followed by the output expression. Every
    /// `let` binding is declared up front with a fresh type so that the first
    /// argument of `prev` / `delay` / `vdelay` can refer to a later one.
    fn prescan_lets(&mut self, body: ExprId) -> R<()> {
        let span = self.expr(body).span;
        let ExprKind::Block(b) = &self.expr(body).kind else {
            return Err(self.flow_err(
                Code::E0806,
                span,
                "a flow body is a block of `let`s and an output expression (§11.2)",
            ));
        };
        let stmts = b.stmts.clone();
        let tail = b.tail;
        let ast = self.ast;
        for s in stmts {
            let stmt = ast.stmt(s);
            if let StmtKind::Let { pat, init, ty, .. } = stmt.kind {
                let mut locals = Vec::new();
                self.predeclare_pat(pat, &mut locals)?;
                // The annotation types the locals from the start, so that a
                // feedback reference above the `let` reads it (`prev~(^s.l)`).
                let annotation = match ty {
                    Some(t) => {
                        let lowered = self.lower_type_expr(t)?;
                        // A constructor with no record (a name held as an
                        // error) stops the check at its `let`, after the
                        // statements before it (§18.1, S-692).
                        if self.ctors_recorded(pat) {
                            self.flow_unify_pat(pat, lowered)?;
                        }
                        Some(lowered)
                    }
                    // SPEC-GAP(S-395): with no annotation the locals stay unknown
                    // above the `let`, so `^s.l` there is E0420 (§4.7); the type is
                    // not taken from the value of the later `let`.
                    None => None,
                };
                let name = match &ast.pat(pat).kind {
                    PatKind::Bind(id) => Some(id.name.clone()),
                    _ => None,
                };
                let k = self.fcx().pending.len();
                for &l in &locals {
                    self.fcx().let_of_local.insert(l, k);
                }
                self.fcx().pending.push(PendingLet { stmt: s, pat, init, locals, name, annotation, span: stmt.span });
            }
        }
        match tail {
            Some(t) => {
                self.fcx().output = Some(t);
                Ok(())
            }
            None => {
                let end = Span::new(span.file, span.end.saturating_sub(1), span.end);
                Err(self.flow_err(Code::E0806, end, "a flow body ends with its output expression (§11.2)"))
            }
        }
    }

    /// Whether every constructor the pattern `pat` names has its record.
    fn ctors_recorded(&self, pat: PatId) -> bool {
        let names = &self.names;
        match &self.ast.pat(pat).kind {
            PatKind::Path(_) => names.pats.contains_key(&pat),
            PatKind::TupleStruct { elems, .. } => {
                names.pats.contains_key(&pat) && elems.iter().all(|&q| self.ctors_recorded(q))
            }
            PatKind::Struct { fields, .. } => {
                names.pats.contains_key(&pat) && fields.iter().all(|(_, q)| self.ctors_recorded(*q))
            }
            PatKind::Tuple(ps) | PatKind::Or(ps) => ps.iter().all(|&q| self.ctors_recorded(q)),
            PatKind::Bind(_) | PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) => true,
        }
    }

    fn predeclare_pat(&mut self, pat: PatId, locals: &mut Vec<LocalId>) -> R<()> {
        let ast = self.ast;
        match &ast.pat(pat).kind {
            PatKind::Bind(id) => {
                let t = self.fresh();
                let lid = self.local_of_pat(pat)?;
                self.bind_local(lid, t, id.span)?;
                self.info.pat_locals.insert(pat, lid);
                locals.push(lid);
                Ok(())
            }
            PatKind::Tuple(elems) | PatKind::TupleStruct { elems, .. } => {
                for &e in &elems.clone() {
                    self.predeclare_pat(e, locals)?;
                }
                Ok(())
            }
            PatKind::Struct { fields, .. } => {
                for (_, fp) in &fields.clone() {
                    self.predeclare_pat(*fp, locals)?;
                }
                Ok(())
            }
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::Or(_) => Ok(()),
        }
    }

    /// E0801: a `let` name read before its definition (its own initializer
    /// included); a later `let` is read only as `^name` (§11.2).
    pub(crate) fn flow_use_local(&mut self, id: LocalId, span: Span) -> R<()> {
        let f = self.fcx();
        if let Some(&k) = f.let_of_local.get(&id)
            && !f.defined.contains(&id)
        {
            let name = self.info.locals[id.0 as usize].name.clone();
            let def_span = self.fcx().pending[k].span;
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Flow, Code::E0801,
                    span,
                    format!(
                        "`{name}` is defined below; names are defined from the top, and a later `let` is read as `^{name}` in the first argument of `prev~` / `delay~` / `vdelay~` (§11.2)"
                    ),
                )
                .with_found(name)
                .with_note(def_span, "defined here"),
            ));
        }
        Ok(())
    }

    /// Statements in flow mode (§11.2, E0806).
    pub(crate) fn check_flow_stmt(&mut self, s: StmtId) -> R<()> {
        let ast = self.ast;
        let stmt = ast.stmt(s);
        let span = stmt.span;
        let what = match &stmt.kind {
            StmtKind::Let { pat, init, .. } => return self.check_flow_let(s, *pat, *init),
            StmtKind::Var { .. } => "`var`; a flow has no mutable variables, state lives in `prev~` / `delay~`",
            StmtKind::Assign { .. } => "assignment; every signal is defined once by `let`",
            StmtKind::For { .. } => "`for`; a flow body has no loops (use `par` to replicate structure)",
            StmtKind::While { .. } => "`while`; a flow body has no loops",
            StmtKind::Break | StmtKind::Continue => "loop control; a flow body has no loops",
            StmtKind::Return(_) => "`return`; the output is the final expression",
            StmtKind::Assert(_) => "`assert`; checks are written as tests on `render` (§11.8)",
            StmtKind::Expr(_) => "an expression statement; a flow body is `let`s followed by one output expression",
        };
        Err(self.flow_err(Code::E0806, span, format!("a flow body cannot contain {what} (§11.2)")))
    }

    fn check_flow_let(&mut self, s: StmtId, pat: PatId, init: ExprId) -> R<()> {
        let span = self.ast.stmt(s).span;
        if self.fcx().depth != 1 {
            return Err(self.flow_err(
                Code::E0806,
                span,
                "`let` is written at the top level of a flow body only; nested blocks hold one expression (§11.2)",
            ));
        }
        let Some(k) = self.fcx().pending.iter().position(|p| p.stmt == s) else {
            return Err(self.flow_err(Code::E0806, span, "unexpected `let` in a flow body"));
        };
        // The annotation is a value type (§11.2), lowered when the `let` was
        // pre-declared; the clock is written on the value (`let ps = p at
        // sample`, §11.3).
        let expected = self.fcx().pending[k].annotation;
        let it = self.check_expr(init, expected)?;
        self.flow_unify_pat(pat, it)?;
        let f = self.fcx();
        let locals = f.pending[k].locals.clone();
        f.defined.extend(locals);
        Ok(())
    }

    /// Unify a `let` pattern with the pre-declared locals (irrefutable patterns only).
    fn flow_unify_pat(&mut self, pat: PatId, ty: TyId) -> R<()> {
        let ast = self.ast;
        let p = ast.pat(pat);
        let span = p.span;
        match &p.kind {
            PatKind::Wild => Ok(()),
            PatKind::Bind(_) => {
                let lid = self.info.pat_locals[&pat];
                let lt = self.local_ty(lid);
                self.unify_at(span, ty, lt)
            }
            PatKind::Tuple(elems) => {
                let elems = elems.clone();
                let s = self.known(ty, span, "matched value")?;
                let Ty::Tuple(ts) = self.ty(s) else {
                    let shown = self.display(ty);
                    return Err(self.flow_err(
                        Code::E0401,
                        span,
                        format!("expected a tuple pattern target, found `{shown}`"),
                    ));
                };
                if ts.len() != elems.len() {
                    return Err(self.flow_err(
                        Code::E0401,
                        span,
                        format!("a tuple of {} element(s) cannot match this pattern of {}", ts.len(), elems.len()),
                    ));
                }
                for (&el, &t) in elems.iter().zip(&ts) {
                    self.flow_unify_pat(el, t)?;
                }
                Ok(())
            }
            PatKind::Struct { path, fields, rest } => {
                let (path, fields, rest) = (path.clone(), fields.clone(), *rest);
                self.struct_pattern(
                    Stage::Flow,
                    span,
                    ty,
                    crate::structpat::Written { pat, path: &path, fields: &fields, rest },
                    &mut |ck, fp, ft, _| ck.flow_unify_pat(fp, ft),
                )?;
                Ok(())
            }
            PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::TupleStruct { .. } | PatKind::Or(_) => {
                Err(self.flow_err(
                    Code::E0502,
                    span,
                    "this pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
                ))
            }
        }
    }

    /// Expression forms that flow mode handles itself or forbids (E0806).
    /// `None` hands the expression back to the ordinary checker.
    pub(crate) fn check_flow_expr(&mut self, e: ExprId, expected: Option<TyId>) -> R<Option<TyId>> {
        let expr = self.expr(e);
        let span = expr.span;
        let what = match &expr.kind {
            ExprKind::Closure { .. } => "an anonymous function; flows call named `rt` functions only",
            ExprKind::Handle { .. } => "`handle`; flows have no effects",
            ExprKind::Unsafe(_) => "`unsafe`",
            ExprKind::Try(_) => "`?`; a flow has no error path",
            ExprKind::Move(_) => "`move`; signals are values and are never moved",
            ExprKind::Par { var, range, body } => {
                let (var, range, body) = (var.clone(), *range, *body);
                return self.check_par(e, &var, &range, body, expected).map(Some);
            }
            ExprKind::At { expr: inner, clock } => {
                let (inner, clock) = (*inner, clock.clone());
                return self.check_at(e, inner, &clock, expected).map(Some);
            }
            ExprKind::Feedback(name) => {
                let name = name.clone();
                return self.check_feedback(e, &name).map(Some);
            }
            _ => return Ok(None),
        };
        Err(self.flow_err(Code::E0806, span, format!("a flow body cannot contain {what} (§11.2)")))
    }

    /// `par i in a..<b { e }` (§11.5): `i` is an `Init`-rate `U32`, the result is `[T; b - a]`.
    /// `par i in a..=b` (`b - a + 1` instances) is E0200 until W7-04 (S-224).
    fn check_par(
        &mut self,
        e: ExprId,
        var: &Ident,
        range: &RangeHead,
        body: ExprId,
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        self.range_end_forms(range)?;
        let lo = self.flow_const_u32(range.lo, "a `par` bound")?;
        let hi = self.flow_const_u32(range.hi, "a `par` bound")?;
        let end = range.end;
        let (empty, count) = match end {
            RangeEnd::Excluded => (hi <= lo, "`b - a`"),
            RangeEnd::Included => (hi < lo, "`b - a + 1`"),
        };
        if empty {
            let sym = end.symbol();
            return Err(self.flow_err(
                Code::E0808,
                span,
                format!("`par` replicates {count} instances; the bounds `{lo}{sym}{hi}` give none (§11.5)"),
            ));
        }
        if end == RangeEnd::Included {
            return Err(self.closed_range_unsupported(range, Stage::Flow, Feature::InclusiveRangePar));
        }
        let exp_elem = expected.and_then(|t| match self.ty(self.shallow(t)) {
            Ty::Array(el, _) => Some(el),
            _ => None,
        });
        let r = (|| -> R<TyId> {
            let u32 = self.u32();
            let lid = self.local_of(Origin::Par(e))?;
            self.bind_local(lid, u32, var.span)?;
            self.fcx().pars.insert(e, (lid, lo, hi));
            self.fcx().par_depth += 1;
            let r = self.check_expr(body, exp_elem);
            self.fcx().par_depth -= 1;
            r
        })();
        let t = r?;
        Ok(self.a.types.intern(Ty::Array(t, Len::Const(hi - lo))))
    }

    /// Calls in flow mode (§11.5): flow instances `f~(...)`, the delays
    /// `prev~` / `delay~` / `vdelay~`, `sample_rate()`, as the names stage
    /// decided them (its `~`: E0811, E0812, the E0806 of `lp!(x)`, R-286;
    /// `names/body/flow.rs`). `None` hands the call back to the ordinary
    /// checker (functions, methods, constructors).
    pub(crate) fn check_flow_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        kind: CallKind,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<Option<TyId>> {
        if let Some(d) = self.names.instance(e) {
            return self.check_instance(e, d, args, expected).map(Some);
        }
        let span = self.expr(e).span;
        // The builtin names (§2.2), as the names stage found them (one an
        // item or a `use` of the module takes is an E0304 there, held as an
        // error in the body, §18.1, S-675).
        let builtin = match self.names.paths.get(&callee) {
            Some(&PathRes::FlowBuiltin(b)) => Some(b),
            _ => None,
        };
        match (builtin, kind) {
            (Some(FlowBuiltin::Delay(d)), CallKind::Flow) => self.check_delay(e, d, args, expected).map(Some),
            (Some(FlowBuiltin::SampleRate), CallKind::Plain) => self.check_sample_rate(e, args).map(Some),
            (Some(FlowBuiltin::SampleTick), CallKind::Plain) => {
                Err(self.unsupported_in(Stage::Flow, span, Feature::SampleTick, &[]))
            }
            // `sample_rate!()`, `sample_tick!()` (W7-04).
            (Some(FlowBuiltin::SampleRate | FlowBuiltin::SampleTick), CallKind::Bang) => {
                Err(self.bang_on_builtin(span))
            }
            // The names stage stopped in the callee of an instance with no
            // diagnostic (a name held as an error, §18.1, S-675), where the
            // check stops too.
            (None, CallKind::Flow) if !self.names.complete => {
                self.check_expr(callee, None)?;
                onsa_diag::internal::bug(Some(span), "an instance the names stage did not record")
            }
            // Any other `~`, a delay without it, and a flow or a delay with
            // `!` are the names stage's (`names/body/flow.rs`).
            (Some(_), _) | (None, CallKind::Flow) => {
                onsa_diag::internal::bug(Some(span), "a mark of a call of a flow body the names stage passed")
            }
            (None, CallKind::Plain | CallKind::Bang) if self.names_a_flow(callee) => {
                onsa_diag::internal::bug(Some(span), "a call of a flow the names stage passed")
            }
            (None, _) => Ok(None),
        }
    }

    /// Whether the record of `callee` names a flow, by the table of the
    /// names stage ([`NameKind::at_callee`]).
    fn names_a_flow(&self, callee: ExprId) -> bool {
        matches!(self.names.paths.get(&callee), Some(&PathRes::Item { entity, .. })
            if NameKind::of(entity, &self.a.defs).is_some_and(|k| k.at_callee(false) == Callee::Flow))
    }

    /// E0714 for `!` on a builtin name of a flow (`sample_rate!()`, §5.2;
    /// its E0806 is W7-04's).
    fn bang_on_builtin(&mut self, span: Span) -> crate::body::Stop {
        let fix = self.src(span).replacen("!(", "(", 1);
        self.diag(
            Diagnostic::new(Stage::Flow, Code::E0714, span, BANG_ON_NO_INOUT_SELF)
                .with_found(self.src(span))
                .with_fix(Fix::replace("remove `!`", span, fix)),
        )
    }

    fn plain_args(&mut self, args: &[Arg]) -> R<()> {
        for a in args {
            if a.mode != Mode::Borrow {
                return Err(self.flow_err(
                    Code::E0806,
                    a.span,
                    "a flow body cannot contain `inout` / `move` arguments; signals are read-only values (§11.2)",
                ));
            }
        }
        Ok(())
    }

    /// `f~(args)` (§11.5): one argument per input, typed by the input's value type.
    fn check_instance(&mut self, e: ExprId, d: DefId, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        if self.a.heading_failed(d) {
            // A flow whose heading a syntax error cut (S-59): its inputs are
            // not known, and the instance is not checked against them.
            self.plain_args(args)?;
            return self.args_of_unknown_callee(args);
        }
        let f = self.a.def(d).as_flow().unwrap().clone();
        let name = self.a.def(d).name.clone();
        if args.len() != f.inputs.len() {
            return Err(self.flow_err(
                Code::E0412,
                span,
                format!("flow `{name}` takes {} input(s) but {} were given", f.inputs.len(), args.len()),
            ));
        }
        self.plain_args(args)?;
        if let Some(exp) = expected {
            self.unify_at(span, f.out, exp)?;
        }
        // An argument of an instance takes no `^` (§11.2), even in the first
        // argument of a delay.
        let lookback = std::mem::take(&mut self.fcx().lookback);
        let r = (|| -> R<Vec<ExprId>> {
            let mut arg_exprs = Vec::new();
            for (arg, input) in args.iter().zip(&f.inputs) {
                self.check_expr(arg.expr, Some(input.ty))?;
                arg_exprs.push(arg.expr);
            }
            Ok(arg_exprs)
        })();
        self.fcx().lookback = lookback;
        let arg_exprs = r?;
        self.fcx().calls.push(NodeCall {
            expr: e,
            kind: NodeKind::Instance(d),
            args: arg_exprs,
            init: None,
            init_expr: None,
            ty: f.out,
        });
        Ok(f.out)
    }

    /// `sample_rate()` (§11.4).
    fn check_sample_rate(&mut self, e: ExprId, args: &[Arg]) -> R<TyId> {
        if !args.is_empty() {
            let span = self.expr(e).span;
            return Err(self.flow_err(
                Code::E0412,
                span,
                format!("`{SAMPLE_RATE}` takes 0 argument(s) but {} were given", args.len()),
            ));
        }
        let f32 = self.a.types.float(FloatKind::F32);
        self.fcx().sample_rate_calls.push(e);
        Ok(f32)
    }

    /// `prev~(e)`, `delay~(e, N)`, `vdelay~(e, d, MAX)`, each with an
    /// optional last `init` (§11.4).
    fn check_delay(&mut self, e: ExprId, d: Delay, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        let name = d.name();
        let most = d.init_index() + 1;
        if args.len() != most && args.len() != most - 1 {
            return Err(self.flow_err(
                Code::E0412,
                span,
                format!(
                    "`{name}~` takes {} or {most} arguments (the last, `init`, may be omitted) but {} were given",
                    most - 1,
                    args.len()
                ),
            ));
        }
        self.plain_args(args)?;
        // The first argument may look back to a later `let` with `^` (§11.2).
        self.fcx().lookback += 1;
        self.fcx().delay_arg += 1;
        let r = self.check_expr(args[0].expr, expected);
        self.fcx().lookback -= 1;
        self.fcx().delay_arg -= 1;
        let t = r?;
        let init_expr = args.get(d.init_index()).map(|a| a.expr);
        let constant = d.const_index().map(|k| args[k].expr);
        let len = match d {
            Delay::Prev => 0,
            Delay::Fixed => {
                let n_expr = constant.expect("the length of `delay~`");
                let n = self.flow_const_u32(n_expr, "the length of `delay~`")?;
                if n == 1 {
                    // The name and the length change, the rest of the call stays (S-251):
                    // the length goes with the `,` before it.
                    let name = Span::new(span.file, span.start, span.start + Delay::Fixed.name().len() as u32);
                    let length = Span::new(span.file, self.expr(args[0].expr).span.end, self.expr(n_expr).span.end);
                    let edits = if self.src(name) == Delay::Fixed.name() {
                        vec![Edit::replace(name, Delay::Prev.name()), Edit::delete(length)]
                    } else {
                        // Not written as the bare name: the whole call is written again.
                        let mut shown = vec![self.src(self.expr(args[0].expr).span)];
                        shown.extend(init_expr.map(|i| self.src(self.expr(i).span)));
                        vec![Edit::replace(span, format!("{}~({})", Delay::Prev.name(), shown.join(", ")))]
                    };
                    return Err(self.diag(
                        Diagnostic::new(Stage::Flow, Code::E0807, span, "a 1-sample delay is written `prev~` (§11.4)")
                            .with_found(self.src(span))
                            .with_fix(Fix::new("write `prev~`", edits)),
                    ));
                }
                if n < 2 {
                    return Err(self.flow_err(
                        Code::E0808,
                        self.expr(n_expr).span,
                        "`delay~` needs a length of at least 2 (§11.4)",
                    ));
                }
                n
            }
            Delay::Variable => {
                self.check_expr(args[1].expr, Some(t))?;
                let max_expr = constant.expect("the maximum of `vdelay~`");
                let max = self.flow_const_u32(max_expr, "the maximum of `vdelay~`")?;
                if max < 1 {
                    return Err(self.flow_err(
                        Code::E0808,
                        self.expr(max_expr).span,
                        "`vdelay~` needs a maximum of at least 1 (§11.4)",
                    ));
                }
                self.fcx().float_checks.push((span, e));
                max
            }
        };
        let kind = NodeKind::Delay(d, len);
        let init = match init_expr {
            Some(i) => {
                self.check_expr(i, Some(t))?;
                Some(match consteval::eval(self, i) {
                    Some(v) => InitArg::Const(v),
                    None => InitArg::Init(i),
                })
            }
            None => None,
        };
        // K-08, R-13: the store of a delay inside the first argument of a
        // delay comes before the outer one reads it (W7-07).
        if self.fcx().delay_arg > 0 {
            return Err(self.unsupported_in(Stage::Flow, span, Feature::NestedDelays, &[]));
        }
        let arg_exprs: Vec<ExprId> = args.iter().map(|a| a.expr).collect();
        self.fcx().calls.push(NodeCall { expr: e, kind, args: arg_exprs, init, init_expr, ty: t });
        Ok(t)
    }
}
