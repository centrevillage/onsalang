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
        let mut inputs = Vec::new();
        let mut heading = FlowHeading { flow: id, inputs: Vec::new(), out: None };
        for (k, p) in f.params.iter().enumerate() {
            let name = match &p.name {
                ParamName::Ident(i) => i.name.clone(),
                ParamName::Wild(_) => "_".into(),
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
            // The clock after the type (§11.3): the rate of the input (W3-10).
            let rate = match &p.clock {
                Some(c) => match crate::flow_names::clock_rate(c) {
                    Ok(r) => Some(r),
                    Err(d) => {
                        self.report(id, d);
                        None
                    }
                },
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
                    None
                }
            };
            // An input whose type or clock is in error stays, as the error
            // type, so that the body sees its name (no cascade in the unit, R-71).
            // An input of the error type keeps its clock (§18.1, S-692).
            let Some(rate) = rate else {
                let error = self.a.types.error();
                inputs.push(FlowInput { name, rate: Rate::Sig, ty: error, param: None, span: p.span });
                continue;
            };
            if matches!(self.a.types.get(lowered), Ty::Error) {
                inputs.push(FlowInput { name, rate, ty: lowered, param: None, span: p.span });
                continue;
            }
            heading.inputs.push((inputs.len(), k, tspan));
            inputs.push(FlowInput { name, rate, ty: lowered, param: None, span: p.span });
        }
        let out_lowered = self.lower_type(&cx, f.ret);
        let rspan = cx.ast.ty(f.ret).span;
        // The output's clock is `sample` in this version (§11.3, §11.6, §19.1).
        let out_clock = match &f.ret_clock {
            Some(c) => match crate::flow_names::clock_rate(c) {
                Ok(Rate::Sig) => None,
                Ok(_) => Some(
                    Diagnostic::new(
                        Stage::Names,
                        Code::E0810,
                        c.span,
                        "the output of a flow is at the clock `sample` in this version (§11.6)",
                    )
                    .with_found(src(&cx, c.span)),
                ),
                Err(d) => Some(d),
            },
            None => Some(
                Diagnostic::new(
                    Stage::Names,
                    Code::E0810,
                    rspan,
                    "a flow output needs its clock after its type: `-> T at sample` (§11.3)",
                )
                .with_found(src(&cx, rspan)),
            ),
        };
        let out = match (out_clock, self.a.types.get(out_lowered)) {
            (_, Ty::Error) => out_lowered,
            (None, _) => {
                heading.out = Some(rspan);
                out_lowered
            }
            (Some(d), _) => {
                self.report(id, d);
                self.a.types.error()
            }
        };
        if let DefKind::Flow(fd) = &mut self.a.defs[id.0 as usize].kind {
            fd.inputs = inputs;
            fd.out = out;
        }
        Some(heading)
    }
}
