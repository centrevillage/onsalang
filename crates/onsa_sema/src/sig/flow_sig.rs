//! The signatures of flows (T2-3, §11): the inputs and the output with their
//! rates, `@param`, and the members a flow generates (§11.6).

use super::*;

/// An item a flow generates (§11.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Generated {
    Type(FlowTy),
    Size,
    BulkSize,
    Fn(FlowFn),
}

/// The items a flow generates, in their order (§11.6): the one list the
/// names stage makes their defs of ([`Sema::generated_defs`]) and the
/// signature fills ([`Sema::flow_members`]).
const GENERATED: &[(&str, Generated)] = &[
    ("State", Generated::Type(FlowTy::State)),
    ("Config", Generated::Type(FlowTy::Config)),
    ("Params", Generated::Type(FlowTy::Params)),
    ("Out", Generated::Type(FlowTy::Out)),
    ("SIZE", Generated::Size),
    ("BULK_SIZE", Generated::BulkSize),
    ("init", Generated::Fn(FlowFn::Init)),
    ("reset", Generated::Fn(FlowFn::Reset)),
    ("process", Generated::Fn(FlowFn::Process)),
    ("process_inplace", Generated::Fn(FlowFn::ProcessInplace)),
    ("render", Generated::Fn(FlowFn::Render)),
    ("params_default", Generated::Fn(FlowFn::ParamsDefault)),
];

impl<'p> Sema<'p> {
    /// The defs of every item the flow `flow` may generate, made with it in
    /// the names stage, so that a `use` and a type written before the flow
    /// find them (§11.6, §15.1, R-50): of their kinds, with no types until the
    /// signature of the flow fills them. Of a flow whose heading was cut, they
    /// are cut too (their uses are errors, R-71).
    pub(crate) fn generated_defs(&mut self, flow: DefId) {
        let d = self.a.def(flow);
        let (module, vis, span, name_span) = (d.module, d.vis, d.span, d.name_span);
        let (u32, unit) = (self.a.types.int(IntKind::U32), self.a.types.unit());
        let mut members = Vec::new();
        for &(name, g) in GENERATED {
            let kind = match g {
                Generated::Type(t) => {
                    let fields = if t == FlowTy::State { Fields::Opaque } else { Fields::Named(Vec::new()) };
                    let derives = Some(Vec::new());
                    DefKind::Struct(StructDef { generics: Vec::new(), fields, derives, flow_ty: Some(t) })
                }
                Generated::Size | Generated::BulkSize => {
                    DefKind::Const(ConstDef { ty: u32, value: None, int_value: None })
                }
                Generated::Fn(which) => DefKind::Fn(FnDef {
                    generics: Vec::new(),
                    self_mode: None,
                    params: Vec::new(),
                    ret: unit,
                    rt: false,
                    effects: EffectSet::default(),
                    body: None,
                    target: false,
                    flow_fn: Some(which),
                    fp_relaxed: false,
                }),
            };
            let def = Def { name: name.to_string(), module, vis, span, name_span, kind, item: None, owner: Some(flow) };
            let m = self.add_def(def);
            if self.a.heading_failed(flow) {
                self.a.failed.insert(m, onsa_syntax::ast::Failed::Heading);
            }
            members.push((name.to_string(), m));
        }
        if let DefKind::Flow(fd) = &mut self.a.defs[flow.0 as usize].kind {
            fd.members = members;
        }
    }

    /// Whether the items `flow` generates by the types of its signature are
    /// not known: an input or the output has the error type in it (a type not
    /// found, a clock not read, a cut heading; also as an element, a field or
    /// a type argument), and a `use` of one is failed with no diagnostic
    /// (§18.1, R-50).
    pub(crate) fn members_unknown(&self, flow: DefId) -> bool {
        let Some(f) = self.a.def(flow).as_flow() else { return false };
        let mut seen = HashSet::new();
        std::iter::once(f.out).chain(f.inputs.iter().map(|i| i.ty)).any(|t| self.has_error(t, &mut seen))
    }

    /// Whether `ty` has the error type in it; of a struct, in its fields
    /// (`seen`: the structs looked at, so that a cycle ends).
    fn has_error(&self, ty: TyId, seen: &mut HashSet<DefId>) -> bool {
        let each = |ts: &[TyId], seen: &mut HashSet<DefId>| ts.iter().any(|&t| self.has_error(t, seen));
        match self.a.types.get(ty) {
            Ty::Error => true,
            Ty::Array(e, _) => self.has_error(*e, seen),
            Ty::Tuple(ts) | Ty::Builtin(_, ts) => each(ts, seen),
            Ty::Fn(f) => {
                let ts: Vec<TyId> = f.params.iter().map(|&(_, t)| t).chain([f.ret]).collect();
                each(&ts, seen)
            }
            Ty::Named(d, args) => {
                if each(args, seen) {
                    return true;
                }
                let fields: Vec<TyId> = match &self.a.def(*d).kind {
                    DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }) if seen.insert(*d) => {
                        fs.iter().map(|f| f.ty).collect()
                    }
                    _ => Vec::new(),
                };
                each(&fields, seen)
            }
            _ => false,
        }
    }

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
    /// An element of the error type may be a scalar (§18.1, R-271).
    fn boundary_outputs(&self, ty: TyId) -> Option<Vec<(String, TyId, Option<Len>)>> {
        let is_scalar =
            |t: TyId| matches!(self.a.types.get(t), Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Error);
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

    /// The def of `g` that [`Sema::generated_defs`] made for `flow`, of the
    /// kind its signature gives.
    fn fill_generated(&mut self, flow: DefId, g: Generated, kind: DefKind) -> DefId {
        let at = GENERATED.iter().position(|&(_, x)| x == g);
        let made = self.a.def(flow).as_flow().zip(at).and_then(|(f, at)| f.members.get(at));
        let Some(&(_, d)) = made else {
            onsa_diag::internal::bug(Some(self.a.def(flow).name_span), "a generated item with no def")
        };
        self.a.defs[d.0 as usize].kind = kind;
        d
    }

    /// The items the flow generates (§11.6), of the types of its signature:
    /// the kinds of the defs [`Sema::generated_defs`] made. The ones its types
    /// do not give (`process_inplace`, `params_default`) are not in its
    /// namespace, and a `use` of them fails ([`Sema::fail_ungenerated`]).
    fn flow_members(&mut self, cx: &Cx<'p>, flow: DefId, inputs: &[FlowInput], out: TyId) -> Vec<(String, DefId)> {
        let (name_span, vis) = (self.a.def(flow).name_span, self.a.def(flow).vis);
        let mk_struct = |s: &mut Self, fields: Vec<FieldDef>, flow_ty: FlowTy| -> DefId {
            let fields = if flow_ty == FlowTy::State { Fields::Opaque } else { Fields::Named(fields) };
            let def = StructDef { generics: Vec::new(), fields, derives: Some(Vec::new()), flow_ty: Some(flow_ty) };
            s.fill_generated(flow, Generated::Type(flow_ty), DefKind::Struct(def))
        };
        // The fields of a generated struct have the visibility of the flow
        // (§11.6, S-36).
        let field = |name: &str, ty: TyId| FieldDef { name: name.to_string(), ty, vis, span: name_span };

        let state = mk_struct(self, Vec::new(), FlowTy::State);
        let config_fields = inputs.iter().filter(|i| i.rate == Rate::Init).map(|i| field(&i.name, i.ty)).collect();
        let config = mk_struct(self, config_fields, FlowTy::Config);
        let params_fields = inputs.iter().filter(|i| i.rate == Rate::Ctl).map(|i| field(&i.name, i.ty)).collect();
        let params = mk_struct(self, params_fields, FlowTy::Params);

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
        let out_struct = mk_struct(self, out_fields, FlowTy::Out);

        let u32 = self.a.types.int(IntKind::U32);
        let f32 = self.a.types.float(FloatKind::F32);
        let unit = self.a.types.unit();
        for g in [Generated::Size, Generated::BulkSize] {
            self.fill_generated(flow, g, DefKind::Const(ConstDef { ty: u32, value: None, int_value: None }));
        }

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
        let mk_fn = |s: &mut Self, params: Vec<ParamSig>, ret: TyId, rt: bool, alloc: bool, which: FlowFn| {
            let f = FnDef {
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
            };
            s.fill_generated(flow, Generated::Fn(which), DefKind::Fn(f));
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

        let ps = vec![sp(self, "cfg", Mode::Borrow, config_ty), sp(self, "sample_rate", Mode::Borrow, f32)];
        mk_fn(self, ps, state_ty, false, false, FlowFn::Init);
        let ps = vec![sp(self, "s", Mode::Inout, state_ty)];
        mk_fn(self, ps, unit, true, false, FlowFn::Reset);
        let mut ps = vec![sp(self, "s", Mode::Inout, state_ty), sp(self, "params", Mode::Borrow, params_ty)];
        for (n, e, l) in &sig_inputs {
            let t = span_of(self, *e, *l);
            ps.push(sp(self, n, Mode::Borrow, t));
        }
        for (n, e, l) in &outputs {
            let t = span_of(self, *e, *l);
            ps.push(sp(self, n, Mode::Inout, t));
        }
        mk_fn(self, ps, unit, true, false, FlowFn::Process);
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
            mk_fn(self, ps, unit, true, false, FlowFn::ProcessInplace);
        }
        let mut ps = vec![sp(self, "cfg", Mode::Borrow, config_ty), sp(self, "params", Mode::Borrow, params_ty)];
        for (n, e, l) in &sig_inputs {
            let t = span_of(self, *e, *l);
            ps.push(sp(self, n, Mode::Borrow, t));
        }
        if sig_inputs.is_empty() {
            ps.push(sp(self, "frames", Mode::Borrow, u32));
        }
        ps.push(sp(self, "sample_rate", Mode::Borrow, f32));
        mk_fn(self, ps, out_ty, false, true, FlowFn::Render);
        let all_defaults = inputs
            .iter()
            .filter(|i| i.rate == Rate::Ctl)
            .all(|i| i.param.as_ref().is_some_and(|p| p.default.is_some()));
        if all_defaults {
            mk_fn(self, Vec::new(), params_ty, false, false, FlowFn::ParamsDefault);
        }
        let _ = cx;
        let absent = |g: Generated| match g {
            Generated::Fn(FlowFn::ProcessInplace) => !pairs,
            Generated::Fn(FlowFn::ParamsDefault) => !all_defaults,
            _ => false,
        };
        let made = self.a.def(flow).as_flow().map(|f| f.members.clone()).unwrap_or_default();
        made.into_iter().zip(GENERATED).filter(|(_, (_, g))| !absent(*g)).map(|(m, _)| m).collect()
    }
}
