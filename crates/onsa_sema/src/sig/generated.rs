//! The items a flow generates (§11.6) and `@param` (§11.7), the stage after
//! the signatures: what they read of the types is lowered by then.

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
/// names stage makes their defs of ([`Sema::generated_defs`]) and this
/// stage fills ([`Sema::lower_generated`]).
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
    /// find them (§11.6, §15.1, R-50): of their kinds, with no types until
    /// [`Sema::lower_generated`] fills them. Of a flow whose heading was cut, they
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

    // ------------------------------------------------------------ generated

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

    /// The stage of the items flows generate and of `@param` (§11.6, §11.7),
    /// after every signature (R-273). Each step is done for every flow before
    /// the next, so that what a step reads is made, whatever the order of the
    /// declarations: the items of the inputs, then those of the output (they
    /// read the fields of the output's type: a struct, lowered, or an item of
    /// the inputs of a flow; an `Out` has no scalar field, so that it gives no
    /// output, made or not), then the check of the value types and `@param`
    /// in the order of the heading, then what `@param` gives
    /// ([`Self::check_generated`], after the well-formedness of the types
    /// written, which reads an alias with an error in an input as the error
    /// type, S-757). Whether each flow's inputs and output pair up.
    pub(super) fn lower_generated(&mut self, flows: &[FlowHeading]) -> Vec<bool> {
        for h in flows {
            self.fill_by_inputs(h.flow);
        }
        flows.iter().map(|h| self.fill_by_output(h.flow)).collect()
    }

    pub(super) fn check_generated(&mut self, flows: Vec<FlowHeading>, pairs: Vec<bool>) {
        for (h, pairs) in flows.iter().zip(pairs) {
            let cx = self.cx_for(h.flow, Vec::new(), None);
            let Some((cx, f)) = cx.as_ref().and_then(|cx| Some((cx, flow_decl(cx, self.a.def(h.flow).item?)?))) else {
                onsa_diag::internal::bug(Some(self.a.def(h.flow).name_span), "a flow lowered with no declaration")
            };
            for &(k, at, span) in &h.inputs {
                let (rate, ty) = (self.flow_def(h.flow).inputs[k].rate, self.flow_def(h.flow).inputs[k].ty);
                self.check_rate_value_type(cx, h.flow, ty, span, rate == Rate::Sig);
                let param = self.lower_param_attr(cx, h.flow, &f.params[at].attrs, rate, ty);
                if let DefKind::Flow(fd) = &mut self.a.defs[h.flow.0 as usize].kind {
                    fd.inputs[k].param = param;
                }
            }
            if let Some(span) = h.out {
                let out = self.flow_def(h.flow).out;
                self.check_rate_value_type(cx, h.flow, out, span, true);
            }
            self.fill_by_params(h.flow, pairs);
        }
    }

    fn flow_def(&self, flow: DefId) -> &FlowDef {
        let Some(f) = self.a.def(flow).as_flow() else {
            onsa_diag::internal::bug(Some(self.a.def(flow).name_span), "the generated items of a def that is no flow")
        };
        f
    }

    /// The def of `g` that [`Sema::generated_defs`] made for `flow`, read
    /// before [`Sema::fill_by_params`] leaves out the ones not generated.
    fn generated(&self, flow: DefId, g: Generated) -> DefId {
        let at = GENERATED.iter().position(|&(_, x)| x == g);
        let made = at.and_then(|at| self.flow_def(flow).members.get(at));
        let Some(&(_, d)) = made else {
            onsa_diag::internal::bug(Some(self.a.def(flow).name_span), "a generated item with no def")
        };
        d
    }

    /// The def of `g` that [`Sema::generated_defs`] made for `flow`, of the
    /// kind its signature gives.
    fn fill_generated(&mut self, flow: DefId, g: Generated, kind: DefKind) -> DefId {
        let d = self.generated(flow, g);
        self.a.defs[d.0 as usize].kind = kind;
        d
    }

    fn fill_struct(&mut self, flow: DefId, flow_ty: FlowTy, fields: Vec<FieldDef>) -> DefId {
        let fields = if flow_ty == FlowTy::State { Fields::Opaque } else { Fields::Named(fields) };
        let def = StructDef { generics: Vec::new(), fields, derives: Some(Vec::new()), flow_ty: Some(flow_ty) };
        self.fill_generated(flow, Generated::Type(flow_ty), DefKind::Struct(def))
    }

    /// A field of a struct `flow` generates: of the visibility of the flow
    /// (§11.6, S-36).
    fn generated_field(&self, flow: DefId, name: &str, ty: TyId) -> FieldDef {
        let d = self.a.def(flow);
        FieldDef { name: name.to_string(), ty, vis: d.vis, span: d.name_span }
    }

    fn generated_ty(&mut self, flow: DefId, t: FlowTy) -> TyId {
        let d = self.generated(flow, Generated::Type(t));
        self.a.types.intern(Ty::Named(d, Vec::new()))
    }

    /// The items the inputs of `flow` give (§11.6): `State`, `Config`,
    /// `Params`, `SIZE` and `BULK_SIZE`, the kinds of the defs
    /// [`Sema::generated_defs`] made.
    fn fill_by_inputs(&mut self, flow: DefId) {
        let inputs = self.flow_def(flow).inputs.clone();
        let fields = |s: &Self, rate: Rate| -> Vec<FieldDef> {
            inputs.iter().filter(|i| i.rate == rate).map(|i| s.generated_field(flow, &i.name, i.ty)).collect()
        };
        self.fill_struct(flow, FlowTy::State, Vec::new());
        for t in [FlowTy::Config, FlowTy::Params] {
            let fs = t.input_rate().map(|r| fields(self, r)).unwrap_or_default();
            self.fill_struct(flow, t, fs);
        }
        let u32 = self.a.types.int(IntKind::U32);
        for g in [Generated::Size, Generated::BulkSize] {
            self.fill_generated(flow, g, DefKind::Const(ConstDef { ty: u32, value: None, int_value: None }));
        }
    }

    /// The items the output of `flow` gives (§11.6): `Out` and the functions
    /// but `params_default` ([`Sema::fill_by_params`]). Whether
    /// `process_inplace` is generated (its inputs and outputs pair up).
    fn fill_by_output(&mut self, flow: DefId) -> bool {
        let (inputs, out) = (self.flow_def(flow).inputs.clone(), self.flow_def(flow).out);
        let name_span = self.a.def(flow).name_span;
        let outputs = self.boundary_outputs(out).unwrap_or_default();
        let out_fields = outputs
            .iter()
            .map(|(n, e, len)| {
                let buf = self.a.types.builtin(BuiltinTy::Buf, vec![*e]);
                let t = match len {
                    Some(l) => self.a.types.intern(Ty::Array(buf, *l)),
                    None => buf,
                };
                self.generated_field(flow, n, t)
            })
            .collect();
        self.fill_struct(flow, FlowTy::Out, out_fields);

        let u32 = self.a.types.int(IntKind::U32);
        let f32 = self.a.types.float(FloatKind::F32);
        let unit = self.a.types.unit();
        let state_ty = self.generated_ty(flow, FlowTy::State);
        let config_ty = self.generated_ty(flow, FlowTy::Config);
        let params_ty = self.generated_ty(flow, FlowTy::Params);
        let out_ty = self.generated_ty(flow, FlowTy::Out);
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
        self.fill_fn(flow, ps, state_ty, false, false, FlowFn::Init);
        let ps = vec![sp(self, "s", Mode::Inout, state_ty)];
        self.fill_fn(flow, ps, unit, true, false, FlowFn::Reset);
        let mut ps = vec![sp(self, "s", Mode::Inout, state_ty), sp(self, "params", Mode::Borrow, params_ty)];
        for (n, e, l) in &sig_inputs {
            let t = span_of(self, *e, *l);
            ps.push(sp(self, n, Mode::Borrow, t));
        }
        for (n, e, l) in &outputs {
            let t = span_of(self, *e, *l);
            ps.push(sp(self, n, Mode::Inout, t));
        }
        self.fill_fn(flow, ps, unit, true, false, FlowFn::Process);
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
            self.fill_fn(flow, ps, unit, true, false, FlowFn::ProcessInplace);
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
        self.fill_fn(flow, ps, out_ty, false, true, FlowFn::Render);
        pairs
    }

    /// `params_default` when every `block` input has a `default` (§11.7),
    /// then the members of `flow`: the items its types give. The ones they
    /// do not give (`process_inplace` when its inputs and outputs do not
    /// pair up, `params_default`) are not in its namespace, and a `use` of
    /// them fails ([`Sema::fail_ungenerated`]).
    fn fill_by_params(&mut self, flow: DefId, pairs: bool) {
        let inputs = &self.flow_def(flow).inputs;
        let all_defaults = inputs
            .iter()
            .filter(|i| i.rate == Rate::Ctl)
            .all(|i| i.param.as_ref().is_some_and(|p| p.default.is_some()));
        if all_defaults {
            let params_ty = self.generated_ty(flow, FlowTy::Params);
            self.fill_fn(flow, Vec::new(), params_ty, false, false, FlowFn::ParamsDefault);
        }
        let absent = |g: Generated| match g {
            Generated::Fn(FlowFn::ProcessInplace) => !pairs,
            Generated::Fn(FlowFn::ParamsDefault) => !all_defaults,
            _ => false,
        };
        let made = self.flow_def(flow).members.clone();
        let members = made.into_iter().zip(GENERATED).filter(|(_, (_, g))| !absent(*g)).map(|(m, _)| m).collect();
        if let DefKind::Flow(fd) = &mut self.a.defs[flow.0 as usize].kind {
            fd.members = members;
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn fill_fn(&mut self, flow: DefId, params: Vec<ParamSig>, ret: TyId, rt: bool, alloc: bool, which: FlowFn) {
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
        self.fill_generated(flow, Generated::Fn(which), DefKind::Fn(f));
    }
}

/// The declaration of a flow item (also `target flow`).
fn flow_decl<'p>(cx: &Cx<'p>, item: onsa_syntax::ast::ItemId) -> Option<&'p onsa_syntax::ast::FlowDecl> {
    match &cx.ast.item(item).kind {
        ItemKind::Flow(f) => Some(f),
        ItemKind::Target(inner) => match &**inner {
            ItemKind::Flow(f) => Some(f),
            _ => None,
        },
        _ => None,
    }
}
