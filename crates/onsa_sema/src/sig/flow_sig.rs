//! The signatures of flows (T2-3, §11): the inputs and the output with their
//! types and rates. What reads the types of other items (the members a flow
//! generates, the check of the value types) and `@param` are the next stage's
//! (`generated`).

use super::*;

/// What the stage of the items a flow generates reads of a flow's heading
/// (§11.6, R-273): the inputs and the output whose value types it checks,
/// in the order of the heading, once every type is lowered.
pub(super) struct FlowHeading {
    pub(super) flow: DefId,
    /// Each input checked: its index in the inputs, its parameter in the
    /// declaration (its `@param`) and the span of its type.
    pub(super) inputs: Vec<(usize, usize, Span)>,
    /// The span of the output's type, when it is checked.
    pub(super) out: Option<Span>,
}

impl<'p> Sema<'p> {
    // ------------------------------------------------------------ flows

    /// The types and rates of the inputs and the output of the flow `id`;
    /// `None` of a heading a syntax error cut.
    pub(super) fn lower_flow(&mut self, cx: Cx<'p>, id: DefId, f: &onsa_syntax::ast::FlowDecl) -> Option<FlowHeading> {
        // A heading a syntax error cut (S-59): its users see an error.
        if self.a.heading_failed(id) {
            let error = self.a.types.error();
            if let DefKind::Flow(fd) = &mut self.a.defs[id.0 as usize].kind {
                fd.out = error;
            }
            return None;
        }
        // The inputs are values the whole heading sees (§5.1, S-741).
        let types = f.params.iter().filter_map(|p| p.ty).chain([f.ret]).collect();
        let locals = heading_locals(self.a, &cx, (&f.params, &[], true), (types, Vec::new()));
        let cx = Cx { locals, ..cx };
        let mut inputs = Vec::new();
        let mut heading = FlowHeading { flow: id, inputs: Vec::new(), out: None };
        for (k, p) in f.params.iter().enumerate() {
            let (name, name_span) = match &p.name {
                ParamName::Ident(i) => (i.name.clone(), i.span),
                ParamName::Wild(s) => ("_".into(), *s),
                ParamName::SelfParam(s) => {
                    self.report(id, Diagnostic::new(Stage::Names, Code::E0002, *s, "a flow has no `self`"));
                    continue;
                }
            };
            if p.mode != Mode::Borrow {
                self.report(
                    id,
                    Diagnostic::new(
                        Stage::Names,
                        Code::E0806,
                        p.span,
                        "flow inputs have no `inout` / `move`; they are read-only signals",
                    ),
                );
            }
            let Some(t) = p.ty else { continue };
            let lowered = self.lower_type(&cx, t);
            let tspan = cx.ast.ty(t).span;
            // The clock after the type (§11.3).
            let (written, clock) = match &p.clock {
                Some(c) => self.port_clock(&cx, c, EventSrc::input(inputs.len())),
                None => {
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Names,
                            Code::E0810,
                            tspan,
                            "a flow input needs a clock after its type: `at init`, `at block` or `at sample` (§11.3)",
                        )
                        .with_found(src(&cx, tspan)),
                    );
                    (None, None)
                }
            };
            // An input whose type or clock is in error stays, as the error
            // type, so that the body sees its name (no cascade in the unit, R-71).
            // An input of the error type keeps its clock (§18.1, S-692).
            let clock_span = p.clock.as_ref().map(|c| c.name.span);
            let input =
                |clock, ty| FlowInput { name, clock, written, clock_span, ty, param: None, span: p.span, name_span };
            let Some(clock) = clock else {
                inputs.push(input(Clock::Error, self.a.types.error()));
                continue;
            };
            if !matches!(self.a.types.get(lowered), Ty::Error) {
                heading.inputs.push((inputs.len(), k, tspan));
            }
            inputs.push(input(clock, lowered));
        }
        let out_lowered = self.lower_type(&cx, f.ret);
        let rspan = cx.ast.ty(f.ret).span;
        // The output's clock (§11.3, §11.9): of an output of the error type it
        // is not read (§18.1).
        let out_error = matches!(self.a.types.get(out_lowered), Ty::Error);
        let clock = match &f.ret_clock {
            _ if out_error => None,
            Some(c) => match self.port_clock(&cx, c, EventSrc::OUTPUT).1 {
                Some(k @ (Clock::Tick(_) | Clock::Event(_))) => Some(k),
                Some(_) => {
                    let msg = "the output of a flow is at the clock `sample`, `(sample / N)`, `(sample * N)` or `event` in this version (§11.3, §11.6)";
                    self.report(
                        id,
                        Diagnostic::new(Stage::Names, Code::E0810, c.span, msg).with_found(src(&cx, c.span)),
                    );
                    None
                }
                None => None,
            },
            None => {
                let msg = "a flow output needs its clock after its type: `-> T at sample` (§11.3)";
                self.report(id, Diagnostic::new(Stage::Names, Code::E0810, rspan, msg).with_found(src(&cx, rspan)));
                None
            }
        };
        let out = match clock {
            Some(_) => {
                heading.out = Some(rspan);
                out_lowered
            }
            None if out_error => out_lowered,
            None => self.a.types.error(),
        };
        let clock = clock.unwrap_or(Clock::Error);
        if let DefKind::Flow(fd) = &mut self.a.defs[id.0 as usize].kind {
            fd.inputs = inputs;
            fd.out = out;
            fd.out_clock = clock;
            fd.out_clock_span = f.ret_clock.as_ref().map(|c| c.name.span);
        }
        Some(heading)
    }

    /// The clock `c` written after the type of an input or the output of a
    /// flow (§11.3, S-359, S-1078): what the names stage reads of it, and
    /// the clock, none with a diagnostic (reported). A name of the clocks
    /// (`event`, the clock of the port, of the source `event`, §11.11), or a derived clock of `sample` whose N is a constant expression of
    /// `U32`, as an array length is (§4.5: E0401, E0408, E0417), a power of 2
    /// that is 2 or more (E0808, §11.9); another base is E0810 at the clock,
    /// and a name not found E0302.
    fn port_clock(
        &mut self,
        cx: &Cx<'p>,
        c: &onsa_syntax::ast::Clock,
        event: EventSrc,
    ) -> (Option<ClockRef>, Option<Clock>) {
        let written = match crate::clock::resolve_at(c) {
            Ok(r) => r,
            Err(d) => {
                self.report(cx.def, d);
                return (None, None);
            }
        };
        let clock = match written {
            ClockRef::Name(n) => Some(n.clock()),
            ClockRef::Event => Some(Clock::Event(event)),
            ClockRef::Derived(Base::Clock(ClockName::Sample), op, n) => self.port_ratio(cx, op, n),
            ClockRef::Derived(base, op, _) => {
                let msg = format!(
                    "the base of a derived clock of an input or the output of a flow is `sample`, not `{}`: `(sample {} N)` (§11.3)",
                    base.name(),
                    op.symbol()
                );
                self.report(
                    cx.def,
                    Diagnostic::new(Stage::Names, Code::E0810, c.span, msg).with_found(src(cx, c.span)),
                );
                None
            }
        };
        (Some(written), clock)
    }

    /// The tick of `(sample op n)` of a port ([`Self::port_clock`]): the
    /// ratio of [`Ratio::of_n`] of the value of `n`, else E0808 at `n`.
    fn port_ratio(&mut self, cx: &Cx<'p>, op: onsa_syntax::ast::RatioOp, n: onsa_syntax::ast::ExprId) -> Option<Clock> {
        let value = match self.read_const(cx, n) {
            Ok((crate::constarg::ConstU32::Value(v), _)) => v,
            // A flow has no generics (§11.2).
            Ok((crate::constarg::ConstU32::Param(_), _)) => {
                onsa_diag::internal::bug(Some(cx.ast.expr(n).span), "a const parameter in the heading of a flow")
            }
            // In its own words, of the N (§4.5: as the array lengths).
            Err(crate::constarg::ConstErr::Uncomputed(_)) => {
                let span = cx.ast.expr(n).span;
                self.report(
                    cx.def,
                    Feature::DerivedClockNExprs.diagnostic(Stage::Names, span, &[]).with_found(src(cx, span)),
                );
                return None;
            }
            Err(e) => {
                self.const_error(cx.def, e);
                return None;
            }
        };
        if let Some(r) = Ratio::of_n(op, value) {
            return Some(Clock::Tick(r));
        }
        let span = cx.ast.expr(n).span;
        let msg = "the N of a derived clock is a power of 2 that is 2 or more (§11.3, §11.9)";
        self.report(cx.def, Diagnostic::new(Stage::Flow, Code::E0808, span, msg).with_found(src(cx, span)));
        None
    }
}
