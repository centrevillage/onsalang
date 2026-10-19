//! The signatures of flows (T2-3, §11): the inputs and the output with their
//! rates, `@param`, and the members a flow generates (§11.6).

use super::*;

impl<'p> Sema<'p> {
    // ------------------------------------------------------------ flows

    pub(super) fn lower_flow(&mut self, cx: Cx<'p>, id: DefId, f: &onsa_syntax::ast::FlowDecl) {
        // A heading a syntax error cut (S-59): its users see an error.
        if self.a.heading_failed(id) {
            let error = self.a.types.error();
            if let DefKind::Flow(fd) = &mut self.a.defs[id.0 as usize].kind {
                fd.out = error;
            }
            return;
        }
        let mut inputs = Vec::new();
        for p in &f.params {
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
                        Stage::Flow,
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
                            Stage::Flow,
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
            let (Some(rate), false) = (rate, matches!(self.a.types.get(lowered), Ty::Error)) else {
                let error = self.a.types.error();
                inputs.push(FlowInput { name, rate: Rate::Sig, ty: error, param: None, span: p.span });
                continue;
            };
            self.check_rate_value_type(&cx, id, lowered, tspan, rate == Rate::Sig);
            let param = self.lower_param_attr(&cx, id, &p.attrs, rate, lowered);
            inputs.push(FlowInput { name, rate, ty: lowered, param, span: p.span });
        }
        let out_lowered = self.lower_type(&cx, f.ret);
        let rspan = cx.ast.ty(f.ret).span;
        // The output's clock is `sample` in this version (§11.3, §11.6, §19.1).
        let out_clock = match &f.ret_clock {
            Some(c) => match crate::flow_names::clock_rate(c) {
                Ok(Rate::Sig) => None,
                Ok(_) => Some(
                    Diagnostic::new(
                        Stage::Flow,
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
                    Stage::Flow,
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
                self.check_rate_value_type(&cx, id, out_lowered, rspan, true);
                out_lowered
            }
            (Some(d), _) => {
                self.report(id, d);
                self.a.types.error()
            }
        };
        let members = self.flow_members(&cx, id, &inputs, out);
        if let DefKind::Flow(fd) = &mut self.a.defs[id.0 as usize].kind {
            fd.inputs = inputs;
            fd.out = out;
            fd.members = members;
        }
    }

    /// §11.3: the value type of a rate must be Copy; §11.6: at the boundary
    /// (`sample` inputs and the output) only scalars, `[scalar; N]`, and structs
    /// of those.
    fn check_rate_value_type(&mut self, _cx: &Cx<'p>, id: DefId, ty: TyId, span: Span, boundary: bool) {
        if let Some(k) = self.a.kind_of(ty)
            && k != crate::Kind::Copy
        {
            self.report(
                id,
                Diagnostic::new(
                    Stage::Flow,
                    Code::E0810,
                    span,
                    format!("the value type of a signal must be Copy; `{}` is {}", self.a.display_type(ty), k.name()),
                ),
            );
            return;
        }
        if boundary && self.boundary_outputs(ty).is_none() {
            self.report(
                id,
                Diagnostic::new(
                    Stage::Flow, Code::E0810,
                    span,
                    "`sample` inputs and outputs are scalars, `[scalar; N]`, or structs of those; nested arrays cannot cross the boundary (§11.6)",
                ),
            );
        }
    }

    /// The `process` outputs for an output value type (§11.6): `(name, elem, array len)`.
    fn boundary_outputs(&self, ty: TyId) -> Option<Vec<(String, TyId, Option<Len>)>> {
        let is_scalar = |t: TyId| matches!(self.a.types.get(t), Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char);
        let one = |name: &str, t: TyId| -> Option<(String, TyId, Option<Len>)> {
            match self.a.types.get(t) {
                Ty::Array(e, len) if is_scalar(*e) => Some((name.to_string(), *e, Some(*len))),
                _ if is_scalar(t) => Some((name.to_string(), t, None)),
                _ => None,
            }
        };
        match self.a.types.get(ty) {
            Ty::Named(d, args) if args.is_empty() => match &self.a.defs[d.0 as usize].kind {
                DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }) => {
                    fs.iter().map(|f| one(&f.name, f.ty)).collect()
                }
                _ => None,
            },
            Ty::Error => Some(Vec::new()),
            _ => one("out", ty).map(|o| vec![o]),
        }
    }

    fn lower_param_attr(&mut self, cx: &Cx<'p>, id: DefId, attrs: &[Attr], rate: Rate, ty: TyId) -> Option<ParamMeta> {
        let attr = attrs.iter().find(|a| a.name.name == onsa_syntax::attrs::PARAM)?;
        // A number of `@param` is a value of the input's type (§11.7): a float
        // literal is rounded once to it (§2.4, R-20), and out of its range is
        // E0408 (R-45).
        let width = match self.a.types.get(ty) {
            Ty::Float(k) => k.width(),
            _ => onsa_syntax::FloatWidth::F64,
        };
        let float = |text: &str| onsa_syntax::float_value(text, width);
        if rate != Rate::Ctl {
            self.report(
                id,
                Diagnostic::new(Stage::Flow, Code::E0809, attr.span, "`@param` goes on `block` inputs only (§11.7)"),
            );
            return None;
        }
        let mut meta = ParamMeta::empty(attr.span, width);
        for arg in &attr.args {
            let AttrArg::Named { key, value } = arg else {
                self.report(
                    id,
                    Diagnostic::new(Stage::Flow, Code::E0809, attr.span, "`@param` takes `key: value` pairs"),
                );
                continue;
            };
            let num = |e: onsa_syntax::ast::ExprId| -> Option<Result<f64, FloatRange>> {
                match &cx.ast.expr(e).kind {
                    ExprKind::Lit(Lit::Float { text }) => Some(float(text)),
                    ExprKind::Lit(Lit::Int { value, .. }) => Some(Ok(*value as f64)),
                    ExprKind::Unary { op: UnOp::Neg, expr } => match &cx.ast.expr(*expr).kind {
                        ExprKind::Lit(Lit::Float { text }) => Some(float(text).map(|v| -v)),
                        ExprKind::Lit(Lit::Int { value, .. }) => Some(Ok(-(*value as f64))),
                        _ => None,
                    },
                    _ => None,
                }
            };
            let string = |e: onsa_syntax::ast::ExprId| -> Option<String> {
                match &cx.ast.expr(e).kind {
                    ExprKind::Lit(Lit::Str(s)) => Some(
                        s.segments
                            .iter()
                            .map(|seg| match seg {
                                onsa_syntax::ast::StrSeg::Text(t) => t.clone(),
                                _ => String::new(),
                            })
                            .collect(),
                    ),
                    _ => None,
                }
            };
            let vspan = cx.ast.expr(*value).span;
            let bad = |s: &mut Self, what: &str| {
                s.report(
                    id,
                    Diagnostic::new(Stage::Flow, Code::E0809, vspan, format!("`@param` `{}` must be {what}", key.name)),
                );
            };
            match key.name.as_str() {
                "min" | "max" | "default" | "step" => match num(*value).map(|v| v.map_err(FloatRange::why)) {
                    Some(Ok(v)) => match key.name.as_str() {
                        "min" => meta.min = Some(v),
                        "max" => meta.max = Some(v),
                        "default" => meta.default = Some(v),
                        _ => meta.step = Some(v),
                    },
                    Some(Err(Some(why))) => {
                        self.report(
                            id,
                            Diagnostic::new(
                                Stage::Types,
                                Code::E0408,
                                vspan,
                                format!("this literal is out of range for the type of the input: {why} (§2.4, §11.7)"),
                            )
                            .with_found(src(cx, vspan)),
                        );
                    }
                    // A text that is no float has the lexer's E0001 (`1.5abc`).
                    Some(Err(None)) | None => bad(self, "a numeric literal"),
                },
                "unit" | "label" | "id" => match string(*value) {
                    Some(v) => match key.name.as_str() {
                        "unit" => meta.unit = Some(v),
                        "label" => meta.label = Some(v),
                        _ => meta.id = Some(v),
                    },
                    None => bad(self, "a string literal"),
                },
                "scale" => match string(*value) {
                    Some(v) if v == "linear" || v == "log" => meta.scale = Some(v),
                    _ => bad(self, "\"linear\" or \"log\""),
                },
                other => {
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Flow, Code::E0809,
                            key.span,
                            format!("unknown `@param` key `{other}`; keys are min max default step unit scale label id (§11.7)"),
                        )
                        .with_found(other.to_string()),
                    );
                }
            }
        }
        Some(meta)
    }

    /// Generated namespace items of a flow (§11.6).
    fn flow_members(&mut self, cx: &Cx<'p>, flow: DefId, inputs: &[FlowInput], out: TyId) -> Vec<(String, DefId)> {
        let (module, vis, span, name_span) = {
            let d = &self.a.defs[flow.0 as usize];
            (d.module, d.vis, d.span, d.name_span)
        };
        let mk = |s: &mut Self, name: &str, kind: DefKind| -> DefId {
            s.add_def(Def { name: name.to_string(), module, vis, span, name_span, kind, item: None, owner: Some(flow) })
        };
        let mk_struct = |s: &mut Self, name: &str, fields: Vec<FieldDef>, flow_ty: FlowTy| -> DefId {
            let fields = if flow_ty == FlowTy::State { Fields::Opaque } else { Fields::Named(fields) };
            mk(
                s,
                name,
                DefKind::Struct(StructDef {
                    generics: Vec::new(),
                    fields,
                    derives: Some(Vec::new()),
                    flow_ty: Some(flow_ty),
                }),
            )
        };
        let field = |name: &str, ty: TyId| FieldDef { name: name.to_string(), ty, vis: Vis::Pub, span: name_span };

        let state = mk_struct(self, "State", Vec::new(), FlowTy::State);
        let config_fields = inputs.iter().filter(|i| i.rate == Rate::Init).map(|i| field(&i.name, i.ty)).collect();
        let config = mk_struct(self, "Config", config_fields, FlowTy::Config);
        let params_fields = inputs.iter().filter(|i| i.rate == Rate::Ctl).map(|i| field(&i.name, i.ty)).collect();
        let params = mk_struct(self, "Params", params_fields, FlowTy::Params);

        let outputs = self.boundary_outputs(out).unwrap_or_default();
        let out_fields = outputs
            .iter()
            .map(|(n, e, len)| {
                let buf = self.a.types.builtin(BuiltinTy::Buf, vec![*e]);
                let t = match len {
                    Some(l) => self.a.types.intern(Ty::Array(buf, *l)),
                    None => buf,
                };
                field(n, t)
            })
            .collect();
        let out_struct = mk_struct(self, "Out", out_fields, FlowTy::Out);

        let u32 = self.a.types.int(IntKind::U32);
        let f32 = self.a.types.float(FloatKind::F32);
        let unit = self.a.types.unit();
        let size = mk(self, "SIZE", DefKind::Const(ConstDef { ty: u32, value: None, int_value: None }));
        let bulk = mk(self, "BULK_SIZE", DefKind::Const(ConstDef { ty: u32, value: None, int_value: None }));

        let state_ty = self.a.types.intern(Ty::Named(state, Vec::new()));
        let config_ty = self.a.types.intern(Ty::Named(config, Vec::new()));
        let params_ty = self.a.types.intern(Ty::Named(params, Vec::new()));
        let out_ty = self.a.types.intern(Ty::Named(out_struct, Vec::new()));
        let sp = |_s: &mut Self, name: &str, mode: Mode, ty: TyId| ParamSig {
            name: name.to_string(),
            mode,
            ty,
            span: name_span,
        };
        let span_of = |s: &mut Self, elem: TyId, len: Option<Len>| -> TyId {
            let span = s.a.types.builtin(BuiltinTy::Span, vec![elem]);
            match len {
                Some(l) => s.a.types.intern(Ty::Array(span, l)),
                None => span,
            }
        };
        let mk_fn =
            |s: &mut Self, name: &str, params: Vec<ParamSig>, ret: TyId, rt: bool, alloc: bool, which: FlowFn| {
                mk(
                    s,
                    name,
                    DefKind::Fn(FnDef {
                        generics: Vec::new(),
                        self_mode: None,
                        params,
                        ret,
                        rt,
                        effects: EffectSet { alloc, ..Default::default() },
                        body: None,
                        target: false,
                        flow_fn: Some(which),
                        fp_relaxed: false,
                    }),
                )
            };

        // Sig inputs become `name: Span[T]` (or `[Span[T]; N]` for planar channels, §5.3).
        let sig_inputs: Vec<(String, TyId, Option<Len>)> = inputs
            .iter()
            .filter(|i| i.rate == Rate::Sig)
            .map(|i| match self.a.types.get(i.ty).clone() {
                Ty::Array(e, l) => (i.name.clone(), e, Some(l)),
                _ => (i.name.clone(), i.ty, None),
            })
            .collect();

        let init = {
            let ps = vec![sp(self, "cfg", Mode::Borrow, config_ty), sp(self, "sample_rate", Mode::Borrow, f32)];
            mk_fn(self, "init", ps, state_ty, false, false, FlowFn::Init)
        };
        let reset = {
            let ps = vec![sp(self, "s", Mode::Inout, state_ty)];
            mk_fn(self, "reset", ps, unit, true, false, FlowFn::Reset)
        };
        let process = {
            let mut ps = vec![sp(self, "s", Mode::Inout, state_ty), sp(self, "params", Mode::Borrow, params_ty)];
            for (n, e, l) in &sig_inputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Borrow, t));
            }
            for (n, e, l) in &outputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Inout, t));
            }
            mk_fn(self, "process", ps, unit, true, false, FlowFn::Process)
        };
        let mut members = vec![
            ("State".to_string(), state),
            ("Config".to_string(), config),
            ("Params".to_string(), params),
            ("Out".to_string(), out_struct),
            ("SIZE".to_string(), size),
            ("BULK_SIZE".to_string(), bulk),
            ("init".to_string(), init),
            ("reset".to_string(), reset),
            ("process".to_string(), process),
        ];
        // `process_inplace` only when inputs and outputs pair up by type (§11.6).
        let pairs = sig_inputs.len() == outputs.len()
            && !outputs.is_empty()
            && sig_inputs.iter().zip(&outputs).all(|(i, o)| i.1 == o.1 && i.2 == o.2);
        if pairs {
            let mut ps = vec![sp(self, "s", Mode::Inout, state_ty), sp(self, "params", Mode::Borrow, params_ty)];
            for (n, e, l) in &outputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Inout, t));
            }
            let f = mk_fn(self, "process_inplace", ps, unit, true, false, FlowFn::ProcessInplace);
            members.push(("process_inplace".into(), f));
        }
        let render = {
            let mut ps = vec![sp(self, "cfg", Mode::Borrow, config_ty), sp(self, "params", Mode::Borrow, params_ty)];
            for (n, e, l) in &sig_inputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Borrow, t));
            }
            if sig_inputs.is_empty() {
                ps.push(sp(self, "frames", Mode::Borrow, u32));
            }
            ps.push(sp(self, "sample_rate", Mode::Borrow, f32));
            mk_fn(self, "render", ps, out_ty, false, true, FlowFn::Render)
        };
        members.push(("render".into(), render));
        let all_defaults = inputs
            .iter()
            .filter(|i| i.rate == Rate::Ctl)
            .all(|i| i.param.as_ref().is_some_and(|p| p.default.is_some()));
        if all_defaults {
            let f = mk_fn(self, "params_default", Vec::new(), params_ty, false, false, FlowFn::ParamsDefault);
            members.push(("params_default".into(), f));
        }
        let _ = cx;
        members
    }
}
