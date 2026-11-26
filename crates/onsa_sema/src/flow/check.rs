//! The flow mode of the checker (T3-1; §11.2–§11.5): the inputs and the
//! `let`s of a flow body, its statements and expressions, `par`, `at`,
//! `^name`, and the calls of instances, delays and `sample_rate()`. The
//! clocks are the walk's (`flow/clocks.rs`), which reads the clock of `at`
//! the names stage recorded; the forms the representation cannot hold yet
//! are its E0200 (`onsa_diag/src/unsupported.rs`, the works named on each).

use super::*;
use crate::clock::{Base, ClockName, ClockRef, Ratio};
use crate::def::Bound;
use crate::deferred::DeferredKind;
use crate::flow_names::FlowBuiltin;
use crate::names::body::{ModifierCall, NoFlowForm, Origin, PathRes, no_flow_form};
use crate::requirement::Required;
use crate::resolve::{Callee, NameKind};
use crate::ty::TyId;
use onsa_syntax::ast::RatioOp;

impl<'a> Checker<'a> {
    pub(super) fn fcx(&mut self) -> &mut FlowCx {
        self.flow.as_mut().expect("flow mode")
    }

    /// An error of the flow stage found while the types are checked: held,
    /// the first in the order of the file, and the check goes on
    /// ([`FlowCx::held`]).
    fn flow_hold(&mut self, d: Diagnostic) {
        Diagnostic::keep_first(&mut self.fcx().held, d);
    }

    /// [`Self::flow_hold`] of the diagnostic of `code` at `span`.
    fn flow_hold_at(&mut self, code: Code, span: Span, msg: impl Into<String>) {
        let d = Diagnostic::new(Stage::Flow, code, span, msg).with_found(self.src(span));
        self.flow_hold(d);
    }

    /// [`Self::flow_hold`] of the E0200 of `feature` at `span` (S-224).
    pub(super) fn flow_hold_gate(&mut self, feature: Feature, span: Span) {
        let d = feature.diagnostic(Stage::Flow, span, &[]).with_found(self.src(span));
        self.flow_hold(d);
    }

    /// Entry point: declare the inputs, pre-declare the `let`s, check the body.
    pub(crate) fn check_flow_body(&mut self, body: ExprId, out: TyId) {
        self.flow = Some(FlowCx { diags_before: self.a.diagnostics.len(), ..FlowCx::default() });
        self.frames.push(Frame { ret: out, loop_depth: 0 });
        let r = (|| -> R<()> {
            self.declare_flow_inputs()?;
            self.prescan_lets(body)?;
            self.check_expr(body, Some(out))?;
            Ok(())
        })();
        let _ = r;
        // A chain whose N multiply past 2^24 (§11.9, S-1089) is E0808 at the
        // modifier past which they are, and in error: before its clock is
        // shown, whose ratio is then within 2^24 either way. One with an N
        // in error has that error alone (its ratio is not known, §18.1).
        let mut past = Vec::new();
        for c in self.fcx().chains.values_mut() {
            let first = c.ratio.and_then(|_| super::plan::past(c.mods.iter().map(|m| &m.plan), 0));
            if let Some(m) = first {
                c.ratio = None;
                let msg = format!(
                    "the N of the `.down~` and `.up~` of this chain multiply to 2^{}, past 2^24 (§11.9)",
                    c.size
                );
                let note = format!("the N on the path: `{}`", super::plan::shown(c.mods.iter().map(|m| &m.plan)));
                past.push((m.name, msg, note));
            }
        }
        for (at, msg, note) in past {
            let d = Diagnostic::new(Stage::Flow, Code::E0808, at, msg).with_found(self.src(at));
            self.flow_hold(d.with_note(at, note));
        }
        self.frames.pop();
    }

    fn declare_flow_inputs(&mut self) -> R<()> {
        let inputs: Vec<FlowInput> = self.a.def(self.def).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
        for (k, input) in (0..).zip(inputs) {
            let id = self.local_of(Origin::FlowInput(k))?;
            // The body's view of it: an array of N at `sample * N` (§11.9).
            let ty = input.body_ty(&mut self.a.types);
            self.bind_local(id, ty, input.span)?;
            self.fcx().inputs.push(id);
        }
        Ok(())
    }

    /// §11.2: the body is `let`s followed by the output expression. Every
    /// `let` binding is declared up front with a fresh type so that the first
    /// argument of `prev` / `delay` / `vdelay` can refer to a later one.
    fn prescan_lets(&mut self, body: ExprId) -> R<()> {
        let span = self.expr(body).span;
        // A body with no output is the names stage's E0806 (`names/body/flow_forms.rs`).
        let ExprKind::Block(b) = &self.expr(body).kind else { return Err(self.flow_syntax(span)) };
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
                    // With no annotation the locals stay unknown above the
                    // `let` and in its value, so `^s.l` there is E0420 (§4.7,
                    // S-395), whose note shows the `let`
                    // ([`Self::unannotated_let_below`]).
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
            None => Err(self.flow_syntax(span)),
        }
    }

    /// The statement of a `let` of the flow body after `at`, or around it,
    /// with no annotation whose local is of the type variable `t`: what a `^`
    /// at `at` reads before the value types it (§4.7, S-395), a `^` above the
    /// `let` or in its own value.
    pub(crate) fn unannotated_let_below(&self, t: TyId, at: Span) -> Option<Span> {
        let lets = self.flow.as_ref()?.pending.iter().filter(|p| p.annotation.is_none() && p.span.end > at.start);
        lets.filter(|p| p.locals.iter().any(|&l| self.shallow(self.local_ty(l)) == t)).map(|p| p.span).next()
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

    /// The bindings of the `let` pattern `pat`, not in an `Or` (the `let`'s
    /// E0502), each with a fresh type.
    fn predeclare_pat(&mut self, pat: PatId, locals: &mut Vec<LocalId>) -> R<()> {
        let mut binds = Vec::new();
        crate::pat::each_bind(self.ast, pat, false, &mut |q, name| binds.push((q, name.span)));
        for (q, span) in binds {
            let t = self.fresh();
            let lid = self.local_of_pat(q)?;
            self.bind_local(lid, t, span)?;
            self.info.pat_locals.insert(q, lid);
            locals.push(lid);
        }
        Ok(())
    }

    /// Statements in flow mode (§11.2): the `let`s of the top level; the
    /// names stage reported any other (its E0806, `names/body/flow_forms.rs`).
    pub(crate) fn check_flow_stmt(&mut self, s: StmtId) -> R<()> {
        let stmt = self.ast.stmt(s);
        match &stmt.kind {
            StmtKind::Let { pat, init, .. } if self.fcx().depth == 1 => self.check_flow_let(s, *pat, *init),
            _ => Err(self.flow_syntax(stmt.span)),
        }
    }

    fn check_flow_let(&mut self, s: StmtId, pat: PatId, init: ExprId) -> R<()> {
        let span = self.ast.stmt(s).span;
        let Some(k) = self.fcx().pending.iter().position(|p| p.stmt == s) else {
            onsa_diag::internal::bug(Some(span), "a `let` of a flow body not declared ahead")
        };
        // The annotation is a value type (§11.2), lowered when the `let` was
        // pre-declared; the clock is written on the value (`let ps = p at
        // sample`, §11.3).
        let expected = self.fcx().pending[k].annotation;
        let it = self.check_expr(init, expected)?;
        self.flow_unify_pat(pat, it)
    }

    /// Unify a `let` pattern with the pre-declared locals (irrefutable patterns only).
    /// Its errors (E0401, E0410, E0502) are of the types stage, as in a
    /// function (§18.1, the stages of the table of the codes).
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
                let Some(ts) = self.tuple_pattern(ty, span, elems.len())? else {
                    // The error type: its elements are errors too (§18.1).
                    let s = self.shallow(ty);
                    for &el in &elems {
                        self.flow_unify_pat(el, s)?;
                    }
                    return Ok(());
                };
                for (&el, &t) in elems.iter().zip(&ts) {
                    self.flow_unify_pat(el, t)?;
                }
                Ok(())
            }
            PatKind::Struct { path, fields, rest } => {
                let (path, fields, rest) = (path.clone(), fields.clone(), *rest);
                self.struct_pattern(
                    span,
                    ty,
                    crate::structpat::Written { pat, path: &path, fields: &fields, rest },
                    &mut |ck, fp, ft, _| ck.flow_unify_pat(fp, ft),
                )?;
                Ok(())
            }
            PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::TupleStruct { .. } | PatKind::Or(_) => {
                Err(self.err(
                    Code::E0502,
                    span,
                    "this pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
                ))
            }
        }
    }

    /// Expression forms that flow mode handles itself; what the names stage
    /// reported as the E0806 of a form a flow body cannot contain stops it.
    /// `None` hands the expression back to the ordinary checker.
    pub(crate) fn check_flow_expr(&mut self, e: ExprId, expected: Option<TyId>) -> R<Option<TyId>> {
        let expr = self.expr(e);
        // The statements of a block are `check_flow_stmt`'s.
        if let Some(form) = no_flow_form(self.ast, e)
            && !matches!(form, NoFlowForm::Stmts(_))
        {
            return Err(self.flow_syntax(expr.span));
        }
        match &expr.kind {
            ExprKind::Par { var, range, body, .. } => {
                let (var, range, body) = (var.clone(), *range, *body);
                self.check_par(e, &var, &range, body, expected).map(Some)
            }
            ExprKind::At { expr: inner, .. } => {
                let inner = *inner;
                self.check_at(e, inner, expected).map(Some)
            }
            ExprKind::Feedback(_) => self.check_feedback(e).map(Some),
            _ => Ok(None),
        }
    }

    /// `par~ i in a..<b { e }` and `par~ i in a..=b { e }` (§11.5): `i` is
    /// an `Init`-rate `U32`, the result is `[T; N]` of the `N` instances
    /// (`b - a`, `b - a + 1`), counted without an end past `b` (S-257).
    fn check_par(
        &mut self,
        e: ExprId,
        var: &Ident,
        range: &RangeHead,
        body: ExprId,
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        // The ends are constant expressions (§4.5, S-966), read by their form there.
        let lo = self.flow_const_u32(range.lo)?;
        let hi = self.flow_const_u32(range.hi)?;
        // With an end in error, or no instances or more than a `U32` counts
        // (held), the body is checked and the `par~` is of the error type, so
        // that no later use of it is an error (§18.1).
        let count = match (lo, hi) {
            (Some(lo), Some(hi)) => self.par_count(span, range.end, lo, hi),
            _ => None,
        };
        let exp_elem = expected.and_then(|t| match self.ty(self.shallow(t)) {
            Ty::Array(el, _) => Some(el),
            _ => None,
        });
        let r = (|| -> R<TyId> {
            let u32 = self.u32();
            let lid = self.local_of(Origin::Par(e))?;
            self.bind_local(lid, u32, var.span)?;
            // The plan reads the first and the count, and a flow with an error has none.
            let (from, n) = lo.zip(count).unwrap_or_default();
            self.fcx().pars.insert(e, (lid, from, n, range.end));
            self.check_expr(body, exp_elem)
        })();
        let t = r?;
        Ok(match count {
            Some(n) => self.a.types.intern(Ty::Array(t, Len::Const(n))),
            None => self.a.types.error(),
        })
    }

    /// The number of the instances of `par~` over `lo` and `hi` with `end`
    /// (§11.5), in a width with no overflow; none (an E0808, held) when the
    /// range is empty or the number does not fit in `U32`.
    fn par_count(&mut self, span: Span, end: RangeEnd, lo: u32, hi: u32) -> Option<u32> {
        let (n, count) = match end {
            RangeEnd::Excluded => (i64::from(hi) - i64::from(lo), "`b - a`"),
            RangeEnd::Included => (i64::from(hi) - i64::from(lo) + 1, "`b - a + 1`"),
        };
        let gives = if n <= 0 {
            "none".to_string()
        } else if let Ok(n) = u32::try_from(n) {
            return Some(n);
        } else {
            // S-1147: a count past `U32` is E0808, as an N past its limit is.
            format!("{n}, more than the size `N` of `[T; N]`, a `U32`, holds")
        };
        let msg = format!(
            "`par` / `par~` replicates {count} instances; the bounds `{lo}{}{hi}` give {gives} (§11.5)",
            end.symbol()
        );
        self.flow_hold_at(Code::E0808, span, msg);
        None
    }

    /// Calls in flow mode (§11.5): flow instances `f~(...)`, the delays
    /// `prev~` / `delay~` / `vdelay~`, `sample_rate()`, as the names stage
    /// decided them (its marks: E0811, E0812, the E0806 of `!(`, R-286;
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
        if let Some(m) = self.names.modifier(e) {
            return self.check_modifier(e, m, args, expected).map(Some);
        }
        let span = self.expr(e).span;
        // The builtin names (§2.2), as the names stage found them (one an
        // item or a `use` of the module takes is an E0304 there, held as an
        // error in the body, §18.1, S-675).
        let builtin = match self.names.paths.get(&crate::names::body::named(self.ast, callee)) {
            Some(&PathRes::FlowBuiltin(b)) => Some(b),
            _ => None,
        };
        match (builtin, kind) {
            (Some(FlowBuiltin::Delay(d)), CallKind::Flow) => self.check_delay(e, d, args, expected).map(Some),
            (Some(b @ (FlowBuiltin::SampleRate | FlowBuiltin::SampleTick)), CallKind::Plain) => {
                self.check_time(e, b, args).map(Some)
            }
            // The names stage stopped in the callee of an instance with no
            // diagnostic (a name held as an error, §18.1, S-675), where the
            // check stops too.
            (None, CallKind::Flow) if !self.names.complete => {
                self.check_expr(callee, None)?;
                onsa_diag::internal::bug(Some(span), "an instance the names stage did not record")
            }
            // Any other `~`, a delay without it, and `!(` and `.(` are the
            // names stage's (`names/body/flow.rs`).
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
        matches!(self.names.paths.get(&crate::names::body::named(self.ast, callee)), Some(&PathRes::Item { entity, .. })
            if NameKind::of(entity, &self.a.defs).is_some_and(|k| k.at_callee(false) == Callee::Flow))
    }

    /// `f~(args)` (§11.5): one argument per input, typed by the input's value type.
    fn check_instance(&mut self, e: ExprId, d: DefId, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        if self.a.heading_failed(d) {
            // A flow whose heading a syntax error cut (S-59): its inputs are
            // not known, and the instance is not checked against them.
            self.fcx().unread = true;
            return self.args_of_unknown_callee(args);
        }
        let f = self.a.def(d).as_flow().unwrap().clone();
        let name = self.a.def(d).name.clone();
        if args.len() != f.inputs.len() {
            return Err(self.err(
                Code::E0412,
                span,
                format!("flow `{name}` takes {} input(s) but {} were given", f.inputs.len(), args.len()),
            ));
        }
        if let Some(exp) = expected {
            self.unify_at(span, f.out, exp)?;
        }
        let mut arg_exprs = Vec::new();
        for (arg, input) in args.iter().zip(&f.inputs) {
            self.check_expr(arg.expr, Some(input.ty))?;
            arg_exprs.push(arg.expr);
        }
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

    /// The modifier `m` of the call `e` (§11.9, §11.10): the type of its
    /// receiver, and one argument, the N of `.down~` and `.up~` (a constant
    /// expression of type `U32`, a power of 2 that is 2 or more, else the
    /// E0808 of the flow stage, S-969, S-1077) or the `Bool` condition of
    /// `.when~` and `.reset_if~` (§11.10). Each is
    /// recorded once in the chain of its head ([`ModifierChain`]).
    fn check_modifier(&mut self, e: ExprId, m: ModifierCall, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let t = self.check_expr(m.receiver, expected)?;
        // S-1090: the number of the arguments is E0412, as of a delay.
        let [arg] = args else {
            let msg = format!("the modifier `{}~` takes 1 argument but {} were given", m.modifier.name(), args.len());
            return Err(self.err(Code::E0412, self.expr(e).span, msg));
        };
        // Its ratio (none of `when~` and `reset_if~`), `Err` of an N in error.
        let ratio = match m.modifier.ratio_op() {
            Some(op) => match self.flow_const_u32(arg.expr)?.map(|n| Ratio::of_n(op, n)) {
                Some(Some(r)) => Ok(Some(r)),
                Some(None) => {
                    let msg =
                        format!("the N of `.{}~(N)` is a power of 2 that is 2 or more (§11.9)", m.modifier.name());
                    self.flow_hold_at(Code::E0808, self.expr(arg.expr).span, msg);
                    Err(())
                }
                // A failed constant (§18.1) or a gate of its own.
                None => Err(()),
            },
            // The rest of `.when~` and `.reset_if~`: the walk of the clocks of its condition.
            None => {
                let bool = self.bool_();
                self.check_expr(arg.expr, Some(bool))?;
                Ok(None)
            }
        };
        let fresh = ModifierChain { ratio: Some(Ratio(0)), size: 0, mods: Vec::new() };
        let chain = self.fcx().chains.entry(m.head).or_insert(fresh);
        // Past 2^24 is the E0808 of the chain (`check_flow_body`).
        let r = ratio.ok().flatten();
        chain.size = chain.size.saturating_add(r.map_or(0, |r| r.0.unsigned_abs()));
        chain.ratio = chain.ratio.zip(ratio.ok()).map(|(a, r)| Ratio(a.0.saturating_add(r.map_or(0, |r| r.0))));
        let cond = m.modifier.ratio_op().is_none().then_some(arg.expr);
        let plan = PlanModifier { modifier: m.modifier, ratio: r, cond, name: m.name, reset: None, port: None };
        chain.mods.push(ChainModifier { call: e, receiver: m.receiver, plan });
        Ok(t)
    }

    /// `sample_rate()`, an `F32`, and `sample_tick()`, a `U32` (§11.4), of
    /// no argument (E0412): each call recorded, the one place that finds
    /// them (D-15), which the walk of the clocks reads.
    fn check_time(&mut self, e: ExprId, b: FlowBuiltin, args: &[Arg]) -> R<TyId> {
        if !args.is_empty() {
            let span = self.expr(e).span;
            let msg = format!("`{}` takes 0 argument(s) but {} were given", b.name(), args.len());
            return Err(self.err(Code::E0412, span, msg));
        }
        if b == FlowBuiltin::SampleTick {
            self.fcx().sample_tick_calls.push(e);
            return Ok(self.a.types.int(IntKind::U32));
        }
        self.fcx().sample_rate_calls.push(e);
        Ok(self.a.types.float(FloatKind::F32))
    }

    /// `prev~(e)`, `delay~(e, N)`, `vdelay~(e, d, MAX)`, each with an
    /// optional last `init` (§11.4). The number of the arguments is of the
    /// types stage, the length of the flow stage (held, [`Self::flow_hold`]).
    fn check_delay(&mut self, e: ExprId, d: Delay, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        let name = d.name();
        let most = d.init_index() + 1;
        if args.len() != most && args.len() != most - 1 {
            // The number of the arguments is of the types stage, as of an
            // instance and `sample_rate()` (§18.1, the table of the codes).
            return Err(self.err(
                Code::E0412,
                span,
                format!(
                    "`{name}~` takes {} or {most} arguments (the last, `init`, may be omitted) but {} were given",
                    most - 1,
                    args.len()
                ),
            ));
        }
        let saved = args[Delay::SAVED].expr;
        let t = self.check_expr(saved, expected)?;
        let init_expr = args.get(d.init_index()).map(|a| a.expr);
        let constant = d.const_index().map(|k| args[k].expr);
        let d_expr = d.d_index().map(|k| args[k].expr);
        let len = match d {
            Delay::Prev => Some(0),
            Delay::Fixed => {
                let n_expr = constant.expect("the length of `delay~`");
                let n = self.flow_const_u32(n_expr)?;
                if n == Some(1) {
                    // The name and the length change, the rest of the call stays (S-251):
                    // the length goes with the `,` before it.
                    let name = Span::new(span.file, span.start, span.start + Delay::Fixed.name().len() as u32);
                    let length = Span::new(span.file, self.expr(saved).span.end, self.expr(n_expr).span.end);
                    let edits = if self.src(name) == Delay::Fixed.name() {
                        vec![Edit::replace(name, Delay::Prev.name()), Edit::delete(length)]
                    } else {
                        // Not written as the bare name: the whole call is written again.
                        let mut shown = vec![self.src(self.expr(saved).span)];
                        shown.extend(init_expr.map(|i| self.src(self.expr(i).span)));
                        vec![Edit::replace(span, format!("{}~({})", Delay::Prev.name(), shown.join(", ")))]
                    };
                    self.flow_hold(
                        Diagnostic::new(Stage::Flow, Code::E0807, span, "a 1-sample delay is written `prev~` (§11.4)")
                            .with_found(self.src(span))
                            .with_fix(Fix::new("write `prev~`", edits)),
                    );
                } else if n == Some(0) {
                    let at = self.expr(n_expr).span;
                    self.flow_hold_at(Code::E0808, at, "`delay~` needs a length of at least 2 (§11.4)");
                }
                n
            }
            Delay::Variable => {
                // §11.4: `T: Float`, a requirement of the types stage (§4.5, S-1135).
                let what = Required::Param { param: "T".into(), owner: format!("`{name}~`"), std: true };
                self.defer(span, t, DeferredKind::Require { bound: Bound::Float, what });
                self.check_expr(d_expr.expect("the `d` of `vdelay~`"), Some(t))?;
                let max_expr = constant.expect("the maximum of `vdelay~`");
                // Its range is of the flow stage, after the types ([`hold_vdelay_max`]).
                self.flow_const_u32(max_expr)?
            }
        };
        // The call is recorded before its `init` is checked: the range of the
        // maximum of a `vdelay~` is judged past an error there.
        let args = args.iter().map(|a| a.expr).collect();
        let at = self.fcx().calls.len();
        self.fcx().calls.push(NodeCall { expr: e, kind: NodeKind::Delay(d, len), args, init: None, init_expr, ty: t });
        if let Some(i) = init_expr {
            self.check_expr(i, Some(t))?;
            let init = match consteval::eval(self, i) {
                Some(v) => InitArg::Const(v),
                None => InitArg::Init(i),
            };
            self.fcx().calls[at].init = Some(init);
        }
        Ok(t)
    }

    /// `e at k` in a flow body (§11.3): the type of `e`; the clock of the
    /// names stage's record ([`crate::names::body::BodyNames::clocks`]),
    /// which the walk of the clocks reads ([`FlowCx::at_clocks`]).
    fn check_at(&mut self, e: ExprId, inner: ExprId, expected: Option<TyId>) -> R<TyId> {
        let t = self.check_expr_as(inner, expected, self.joining)?;
        let clock = match self.names_record(e, self.names.clocks.get(&e).copied())? {
            ClockRef::Name(name) => name.clock(),
            // §11.11: in error, as a derived clock no expression writes.
            ClockRef::Event => {
                let span = self.at_clock(e);
                let msg = "`at event` is no clock of an expression: it is written at the inputs and the output of a flow only (§11.3, §11.11)";
                let rule = "an event value is at the clock of its event; `at sample` and `at (sample / N)` read its last value";
                let found = self.src(span);
                self.flow_hold(Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(found).with_rule(rule));
                Clock::Error
            }
            ClockRef::Derived(base, op, n) => self.derived_clock(e, base, op, n)?,
        };
        self.fcx().at_clocks.insert(e, clock);
        Ok(t)
    }

    /// The place of the clock of the `at` `e`.
    fn at_clock(&self, e: ExprId) -> Span {
        match &self.expr(e).kind {
            ExprKind::At { clock, .. } => clock.span,
            _ => onsa_diag::internal::bug(Some(self.expr(e).span), "a clock of no `at`"),
        }
    }

    /// The clock of the derived clock `(base op n)` of `e at k` (§11.3,
    /// S-1078, S-1077): `n` a constant expression of type `U32` as the length
    /// of a delay is (§4.5), its ratio of [`Ratio::of_n`], else E0808 at `n`.
    /// An expression writes `(sample / N)` only: a base that is not `sample`
    /// and `(sample * N)` (S-567 K3) are E0815 at the clock, with no
    /// candidate. In error with any of them (S-1133): after those E0815 it
    /// makes no clock `k` for the result, which rests on the failed check
    /// (S-1133 (1)).
    fn derived_clock(&mut self, e: ExprId, base: Base, op: RatioOp, n: ExprId) -> R<Clock> {
        let value = self.flow_const_u32(n)?;
        if base != Base::Clock(ClockName::Sample) || op == RatioOp::Mul {
            let msg = format!(
                "the derived clock of an expression is `(sample / N)`, never faster than the `sample` of the body; `({} {} N)` stands in the inputs and the output of a flow (§11.3, §11.9)",
                base.name(),
                op.symbol()
            );
            self.flow_hold_at(Code::E0815, self.at_clock(e), msg);
            return Ok(Clock::Error);
        }
        let Some(value) = value else { return Ok(Clock::Error) };
        match Ratio::of_n(op, value) {
            Some(r) => Ok(Clock::Tick(r)),
            None => {
                let msg = "the N of a derived clock is a power of 2 that is 2 or more (§11.3, §11.9)";
                self.flow_hold_at(Code::E0808, self.expr(n).span, msg);
                Ok(Clock::Error)
            }
        }
    }

    /// `^name` in a flow body (§11.2): a later `let` of the body, read in the
    /// first argument of a delay, as the names stage recorded it (its E0801,
    /// E0020 and the E0200 in a `par`, `names/body/flow_order.rs`).
    fn check_feedback(&mut self, e: ExprId) -> R<TyId> {
        let record = match self.names.paths.get(&e) {
            Some(&PathRes::Local(b)) => Some(LocalId(b.0)),
            _ => None,
        };
        let id = self.names_record(e, record)?;
        self.info.targets.insert(e, Target::Local(id));
        Ok(self.local_ty(id))
    }

    /// The record `r` of the names stage at the node `e` of a flow body: none
    /// where it stopped before it with no diagnostic (§18.1, S-692).
    fn names_record<T>(&mut self, e: ExprId, r: Option<T>) -> R<T> {
        match r {
            Some(r) => Ok(r),
            None if !self.names.complete => Err(self.held_stop()),
            None => onsa_diag::internal::bug(
                Some(self.expr(e).span),
                "a node of a flow body the names stage did not record",
            ),
        }
    }
}

/// The range of the maximum of a `vdelay~` (§11.4), the one judgment of it:
/// at least 1, and at most 2^24 when its `d` is an `F32` (the type of its
/// first argument, through aliases and the variables of the inference: of
/// the typed body; S-88, R-100), which is judged of a body the check ended
/// only. An E0808 at it, held ([`FlowCx::held`]). `F64` has no such limit.
pub(super) fn hold_vdelay_max(a: &Analysis, module: &Module, body: &BodyInfo, fcx: &mut FlowCx) {
    const MOST: u32 = 1 << 24;
    for call in &fcx.calls {
        let NodeKind::Delay(d @ Delay::Variable, Some(max)) = call.kind else { continue };
        let f32 = || body.expr_types.get(&call.expr).is_some_and(|&t| *a.types.get(t) == Ty::Float(FloatKind::F32));
        let msg = if max == 0 {
            "`vdelay~` needs a maximum of at least 1 (§11.4)".to_string()
        } else if max > MOST && body.complete && f32() {
            format!(
                "the maximum of a `vdelay~` whose `d` is an `F32` is at most 2^24 ({MOST}), the integers an `F32` holds (§11.4)"
            )
        } else {
            continue;
        };
        let Some(&max_expr) = d.const_index().and_then(|k| call.args.get(k)) else { continue };
        let span = module.parsed.ast.expr(max_expr).span;
        let diag = Diagnostic::new(Stage::Flow, Code::E0808, span, msg).with_found(span.text_in(&module.text));
        Diagnostic::keep_first(&mut fcx.held, diag);
    }
}
