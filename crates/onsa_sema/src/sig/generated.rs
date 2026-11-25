//! The items a flow generates (§11.6) and `@param` (§11.7), the stage after
//! the signatures: what they read of the types is lowered by then.

use super::*;

/// Why the type of a `sample` input or output does not cross the boundary
/// (§11.6): its E0810.
enum Unfit {
    /// A type of none of the forms; whether it is or has a nested array.
    Form(bool),
    /// A struct as an input (R-41, R-279: an output only).
    Struct,
    /// No channel (S-1110, S-407): a struct with no field (`None`), or an
    /// array of length 0, with the name of its field in the struct.
    NoChannel(Option<(Option<String>, TyId)>),
}

/// Where the value type of an input or the output of a flow is, of the
/// boundary (§11.6, §11.9): an input of a periodic tick, the output, at
/// their clocks, or neither.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Boundary {
    Input(Clock),
    Output(Clock),
    Inside,
}

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
    ("In", Generated::Type(FlowTy::In)),
    ("Out", Generated::Type(FlowTy::Out)),
    ("Rendered", Generated::Type(FlowTy::Rendered)),
    ("SIZE", Generated::Size),
    ("BULK_SIZE", Generated::BulkSize),
    ("init", Generated::Fn(FlowFn::Init)),
    ("reset", Generated::Fn(FlowFn::Reset)),
    ("process", Generated::Fn(FlowFn::Process)),
    ("process_inplace", Generated::Fn(FlowFn::ProcessInplace)),
    ("render", Generated::Fn(FlowFn::Render)),
];

impl Generated {
    /// Of an item the inputs of a flow decide (§11.6), whether the clocks
    /// `rates` of the inputs give it: `Config` and `Params` of an input of
    /// their rate (S-112), `In` of two `sample` inputs or more (S-30); `init`
    /// always, as only its parameter `cfg` (of `Config`) is of the inputs.
    /// These are the items a flow whose clocks are not read keeps as failed
    /// (R-471). None of an item the inputs do not decide.
    fn of_inputs(self, rates: &[Option<ClockRef>]) -> Option<bool> {
        let host = || rates.iter().map(|r| r.and_then(ClockRef::host));
        match self {
            Generated::Type(FlowTy::In) => Some(host().filter(|&r| r == Some(ClockName::Sample)).count() >= 2),
            Generated::Type(t) => t.input_clock().map(|r| host().any(|h| h == Some(r))),
            Generated::Fn(FlowFn::Init) => Some(true),
            _ => None,
        }
    }
}

/// The name of the item `g` in [`GENERATED`].
fn name_of(g: Generated) -> &'static str {
    let named = GENERATED.iter().find(|(_, x)| *x == g);
    named.map_or_else(|| onsa_diag::internal::bug(None, format!("no name of {g:?}")), |(n, _)| n)
}

impl FlowTy {
    /// The name of the type (`State`), of [`GENERATED`]: what a later stage
    /// shows, which selects the type by its `FlowTy`, not by this name.
    pub fn name(self) -> &'static str {
        name_of(Generated::Type(self))
    }

    /// The parameter of the functions of the flow that takes the type
    /// (§11.6): `cfg` of `Config`, `params` of `Params`; none of the others.
    pub fn param_name(self) -> Option<&'static str> {
        match self {
            FlowTy::Config => Some("cfg"),
            FlowTy::Params => Some("params"),
            FlowTy::State | FlowTy::In | FlowTy::Out | FlowTy::Rendered => None,
        }
    }
}

/// Whether `name` is of a function of the list (§11.6): a name of no type,
/// whether the flow generates it or not (S-708).
pub(crate) fn listed_fn(name: &str) -> bool {
    GENERATED.iter().any(|&(n, g)| n == name && matches!(g, Generated::Fn(_)))
}

impl Analysis {
    /// §11.6: the scalar and, of an array, the length of the channel a value
    /// of the type `t` crosses the boundary as: the one judgment of the type
    /// of an input and of each part of an output.
    fn channel(&self, t: TyId) -> Result<(TyId, Option<Len>), Unfit> {
        let is_scalar =
            |t: TyId| matches!(self.types.get(t), Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Error);
        match self.types.get(t) {
            // S-1110, S-407: N is 1 at least.
            Ty::Array(e, Len::Const(0)) if is_scalar(*e) => Err(Unfit::NoChannel(Some((None, t)))),
            Ty::Array(e, len) if is_scalar(*e) => Ok((*e, Some(*len))),
            _ if is_scalar(t) => Ok((t, None)),
            Ty::Array(e, _) => Err(Unfit::Form(matches!(self.types.get(*e), Ty::Array(..)))),
            _ => Err(Unfit::Form(false)),
        }
    }

    /// Whether a `sample` input is of the type `t` (§11.6), a value type of a
    /// signal with no error.
    pub(crate) fn crosses_as_input(&self, t: TyId) -> bool {
        self.channel(t).is_ok()
    }

    /// The E0302 `d` of the item `name` that `flow` does not generate, with
    /// the notes of why (§11.6, R-480): of `process_inplace`, that the flow
    /// gives events, or the types of the `sample` inputs and of the outputs
    /// that do not pair up, and the rule of `process` with separate buffers.
    /// The one place of these notes, for every E0302 of the item: a `use`, a
    /// path of a body.
    pub(crate) fn with_ungenerated_notes(&self, d: Diagnostic, flow: DefId, name: &str) -> Diagnostic {
        let generated = GENERATED.iter().find(|&&(n, _)| n == name).map(|&(_, g)| g);
        let (Some(Generated::Fn(FlowFn::ProcessInplace)), Some(f)) = (generated, self.def(flow).as_flow()) else {
            return d;
        };
        let (k, process) = (&self.def(flow).name, name_of(Generated::Fn(FlowFn::Process)));
        if f.gives_events() {
            return d
                .with_rule(format!("`{k}.{name}` is not generated, as the output of `{k}` is at `event` (§11.6)"))
                .with_rule(format!("use `{k}.{process}` with a separate buffer for the events"));
        }
        let Some((ins, outs)) = &f.unpaired else { return d };
        let list = |ts: &[TyId]| match ts {
            [] => "none".to_string(),
            ts => ts.iter().map(|&t| format!("`{}`", self.display_type(t))).collect::<Vec<_>>().join(", "),
        };
        d.with_rule(format!(
            "`{k}.{name}` is generated when the `sample` inputs and the outputs of `{k}` agree in number and in \
             types, in order (§11.6: a struct output by its fields, an array as one type); the `sample` inputs of \
             `{k}` are {} and its outputs {}",
            list(ins),
            list(outs)
        ))
        .with_rule(format!("use `{k}.{process}` with separate buffers"))
    }
}

impl<'p> Sema<'p> {
    /// The defs of every item the flow `flow` may generate, made with it in
    /// the names stage, so that a `use` and a type written before the flow
    /// find them (§11.6, §15.1, R-50): of their kinds, with no types until
    /// [`Sema::lower_generated`] fills them. Of a flow whose heading was cut, they
    /// are cut too (their uses are errors, R-71). `Config` and `Params` are
    /// of a flow with an input of their rate alone (§11.6, S-112, R-264), and
    /// `In` of one with two `sample` inputs or more (S-30), by the clocks of
    /// `rates` (of the inputs, `None` of a clock not read); of a clock not
    /// read or a cut heading, all, as what the flow has is not known (§18.1,
    /// R-471), and those the inputs decide (`Config`, `Params`, `In`,
    /// `init`) are kept as of a cut heading: their uses get no diagnostic
    /// (`Out` is of the output alone, S-1087). Whether it has `Out` and
    /// `process_inplace` its types decide (S-1087: [`Sema::fill_by_output`],
    /// [`Sema::trim_members`]).
    pub(crate) fn generated_defs(&mut self, flow: DefId, rates: &[Option<ClockRef>]) {
        let d = self.a.def(flow);
        let (module, vis, span, name_span) = (d.module, d.vis, d.span, d.name_span);
        let (u32, unit) = (self.a.types.int(IntKind::U32), self.a.types.unit());
        let known = !self.a.heading_failed(flow) && rates.iter().all(Option::is_some);
        let mut members = Vec::new();
        for &(name, g) in GENERATED {
            let by_inputs = g.of_inputs(rates);
            let kind = match g {
                _ if known && by_inputs == Some(false) => continue,
                Generated::Type(t) => {
                    let fields = if t == FlowTy::State { Fields::Opaque } else { Fields::Named(Vec::new()) };
                    let derives = Some(Vec::new());
                    DefKind::Struct(StructDef { generics: Vec::new(), fields, derives, flow_ty: Some(t) })
                }
                Generated::Size | Generated::BulkSize => {
                    DefKind::Const(ConstDef { ty: u32, value: None, int_value: None, param: None, of_attr: None })
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
                    derived: None,
                    fp_relaxed: false,
                }),
            };
            let owner = Some(flow);
            let def =
                Def { name: name.to_string(), module, vis, span, name_span, kind, item: None, owner, export: None };
            let m = self.add_def(def);
            if self.a.heading_failed(flow) || !known && by_inputs.is_some() {
                self.a.failed.insert(m, onsa_syntax::ast::Failed::Heading);
            }
            members.push((name.to_string(), m));
        }
        if let DefKind::Flow(fd) = &mut self.a.defs[flow.0 as usize].kind {
            fd.members = members;
        }
    }

    /// Whether the items `flow` generates by the types of its signature are
    /// not known (§18.1, R-50, S-1087): the output, and when `inputs` an
    /// input too (`process_inplace`; `Out` is of the output alone), has the
    /// error type in it (a type not found, a clock not read, a cut heading;
    /// also as an element, a field or a type argument), or is a `sample`
    /// type that does not cross the boundary (its E0810), or an event output
    /// of an [`Self::unfit_event`]. Such an item is kept, as of a cut heading:
    /// its uses get no diagnostic.
    fn members_unknown(&mut self, flow: DefId, inputs: bool) -> bool {
        let f = self.flow_def(flow);
        let (out, events) = (f.out, f.gives_events());
        let ins =
            f.inputs.iter().filter(|_| inputs).map(|i| (i.ty, (i.host() == Some(ClockName::Sample)).then_some(true)));
        let tys: Vec<(TyId, Option<bool>)> = std::iter::once((out, (!events).then_some(false))).chain(ins).collect();
        let mut seen = HashSet::default();
        self.unfit_event(flow)
            || tys.into_iter().any(|(t, edge)| {
                self.has_error(t, &mut seen) || edge.is_some_and(|input| self.boundary_outputs(t, input).is_err())
            })
    }

    /// Whether `flow` has an event output of a type no event has: no signal's
    /// (its E0810), or with a second-class part (its E0710). The one test of
    /// the items of such a flow and of the error of its port.
    fn unfit_event(&self, flow: DefId) -> bool {
        let (f, span) = (self.flow_def(flow), self.a.def(flow).name_span);
        let under = crate::bounds::Bounds { a: self.a, generics: &[] };
        f.gives_events()
            && (self.signal_type_error(f.out, span).is_some() || wellformed::no_kind_argument(&under, f.out, false))
    }

    /// The item `g` of `flow`, not known ([`Self::members_unknown`]): its
    /// uses get no diagnostic, as of a cut heading.
    fn unknown_member(&mut self, flow: DefId, g: Generated) {
        if let Some(d) = self.generated(flow, g) {
            self.a.failed.insert(d, onsa_syntax::ast::Failed::Heading);
        }
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

    /// §11.3: the value type of a signal is Copy and holds no function type
    /// (S-372), in this order: its E0810 at `span`, of the type as a whole.
    /// The one judgment of the inputs, read by the well-formedness of the
    /// types at the turn of the flow (an input with it is the error type to
    /// its users, S-1123), and of the output ([`Self::check_rate_value_type`]).
    pub(super) fn signal_type_error(&self, ty: TyId, span: Span) -> Option<Diagnostic> {
        crate::signal::signal_type_error(self.a, ty, span)
    }

    /// The E0810 of the value type `ty` of an input or the output of `id`
    /// ([`Self::signal_type_error`]), and at the boundary, §11.6: only
    /// scalars, `[scalar; N]`, and (an output) structs of those. Whether it
    /// reports one.
    fn check_rate_value_type(&mut self, id: DefId, ty: TyId, span: Span, boundary: Boundary) -> bool {
        if let Some(d) = self.signal_type_error(ty, span) {
            self.report(id, d);
            return true;
        }
        let (input, clock) = match boundary {
            Boundary::Inside => return false,
            Boundary::Input(c) => (true, c.shown(span)),
            Boundary::Output(c) => (false, c.shown(span)),
        };
        let fit = self.boundary_outputs(ty, input);
        let shown = |t: TyId| self.a.display_type(t);
        let msg = match fit {
            Ok(_) => return false,
            // R-245: the type, and the forms that cross.
            Err(Unfit::Form(nested)) => format!(
                "`{}` cannot cross the boundary{}: a `{clock}` input or output is a scalar or `[scalar; N]`, \
                 and an output may be a struct of those (§11.6)",
                shown(ty),
                if nested { ", as nested arrays do not" } else { "" }
            ),
            Err(Unfit::Struct) => format!(
                "`{}` is a struct, which crosses the boundary as an output only: a `{clock}` input is a scalar or \
                 `[scalar; N]` (§11.6)",
                shown(ty)
            ),
            Err(Unfit::NoChannel(None)) => format!(
                "a `{clock}` input or output needs at least one channel; the struct `{}` has no field (§11.6)",
                shown(ty)
            ),
            Err(Unfit::NoChannel(Some((f, t)))) => {
                let of = f.map_or_else(|| format!("`{}`", shown(t)), |f| format!("the field `{f}`, `{}`,", shown(t)));
                format!("a `{clock}` input or output needs at least one channel; {of} is an array of length 0 (§11.6)")
            }
        };
        self.report(id, Diagnostic::new(Stage::Flow, Code::E0810, span, msg));
        true
    }

    /// The `process` outputs for an output value type (§11.6): `(name, elem, array len)`.
    /// An element of the error type may be a scalar (§18.1, R-271); the error type, none.
    /// Of an `input`, a struct is none of the forms (R-41, R-279), known to be
    /// a struct with the error type in its fields too. The fields of a struct
    /// are read with its type arguments applied (R-491).
    fn boundary_outputs(&mut self, ty: TyId, input: bool) -> Result<Vec<(String, TyId, Option<Len>)>, Unfit> {
        let fields: Option<Vec<(String, TyId)>> = match self.a.types.get(ty).clone() {
            Ty::Named(d, _) if input && matches!(self.a.def(d).kind, DefKind::Struct(_)) => return Err(Unfit::Struct),
            Ty::Named(d, args) => match &self.a.def(d).kind {
                DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }) if fs.is_empty() => {
                    return Err(Unfit::NoChannel(None));
                }
                DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }) => {
                    let fs: Vec<(String, TyId)> = fs.iter().map(|f| (f.name.clone(), f.ty)).collect();
                    Some(fs.into_iter().map(|(name, t)| (name, self.a.types.subst(t, &args))).collect())
                }
                _ => return Err(Unfit::Form(false)),
            },
            Ty::Error => return Ok(Vec::new()),
            _ => None,
        };
        let one = |field: Option<&str>, t: TyId| match self.a.channel(t) {
            Ok((e, len)) => Ok((field.unwrap_or("out").to_string(), e, len)),
            Err(Unfit::NoChannel(_)) => Err(Unfit::NoChannel(Some((field.map(str::to_string), t)))),
            Err(u) => Err(u),
        };
        match fields {
            Some(fs) => fs.iter().map(|(name, t)| one(Some(name), *t)).collect(),
            None => one(None, ty).map(|o| vec![o]),
        }
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
            // What the loops do not see: a port whose clock or type is in error.
            let lost = |i: &FlowInput| i.clock == Clock::Error || self.a.types.has_error(i.ty);
            let mut in_error = h.out.is_none() || self.flow_def(h.flow).inputs.iter().any(lost);
            for &(k, at, span) in &h.inputs {
                let input = &self.flow_def(h.flow).inputs[k];
                let (clock, caller, ty) = (input.clock, input.caller_clock(), input.ty);
                // A type with the error type in it has its diagnostic (§18.1):
                // of an input of the E0810 of [`Self::signal_type_error`] too.
                // S-1204 (2): an input of any periodic tick, `sample / N` and
                // `sample * N` too, has the value types of the `sample` input.
                let place = if matches!(caller, Clock::Tick(_)) { Boundary::Input(caller) } else { Boundary::Inside };
                let unfit = self.check_rate_value_type(h.flow, ty, span, place) || self.a.types.has_error(ty);
                in_error |= unfit;
                let attr = Attr::find(&f.params[at].attrs, onsa_syntax::attrs::PARAM);
                // The `@param` of an input of a type no signal has, or with a
                // diagnostic, is not read (§6.5: as the arguments of an
                // attribute in excess).
                // SPEC-GAP(S-1121): its other E0809 are not reported either.
                let param =
                    attr.filter(|_| !unfit).and_then(|a| self.lower_param_attr(cx, h.flow, a, clock, (ty, span)));
                // R-489: nor is the `@param` it must have.
                if attr.is_none() && !unfit {
                    self.check_exported_input(h.flow, k);
                }
                if let DefKind::Flow(fd) = &mut self.a.defs[h.flow.0 as usize].kind {
                    fd.inputs[k].param = param;
                }
            }
            if let Some(span) = h.out {
                let out = self.flow_def(h.flow).out;
                let f = self.flow_def(h.flow);
                // The forms of the boundary of an event are W10-07's (§11.11).
                let place = if f.gives_events() { Boundary::Inside } else { Boundary::Output(f.out_clock) };
                in_error |= self.check_rate_value_type(h.flow, out, span, place) || self.unfit_event(h.flow);
            }
            if let DefKind::Flow(fd) = &mut self.a.defs[h.flow.0 as usize].kind {
                fd.ports_in_error = in_error;
            }
            if let Some(d) = self.a.def(h.flow).export.and_then(|at| self.a.boundary_gate(h.flow, at)) {
                self.report(h.flow, d);
            }
            self.trim_members(h.flow, pairs);
        }
    }

    /// The E0809 of the `block` input `k`, with no `@param`, of a flow with
    /// `@export` (§11.7, §14.2: the check reports it), with no candidate (S-833: `@param` or `@host`, and the values are
    /// the writer's). `@host` is not in the table of the attributes yet (§6.5).
    fn check_exported_input(&mut self, flow: DefId, k: usize) {
        let input = &self.flow_def(flow).inputs[k];
        if self.a.def(flow).export.is_none() || input.clock != Clock::Block {
            return;
        }
        let name = &self.a.def(flow).name;
        let msg = format!("the `block` input `{}` of the exported flow `{name}` has no `@param`", input.name);
        let d = Diagnostic::new(Stage::Flow, Code::E0809, input.span, msg)
            .with_rule("a `block` input of a flow with `@export` takes `@param` (§11.7)");
        self.report(flow, d);
    }

    fn flow_def(&self, flow: DefId) -> &FlowDef {
        let Some(f) = self.a.def(flow).as_flow() else {
            onsa_diag::internal::bug(Some(self.a.def(flow).name_span), "the generated items of a def that is no flow")
        };
        f
    }

    /// The def of `g` that [`Sema::generated_defs`] made for `flow`, read
    /// before [`Sema::trim_members`] leaves out the ones not generated; none
    /// of a `Config` or `Params` it did not make.
    fn generated(&self, flow: DefId, g: Generated) -> Option<DefId> {
        let (name, _) = GENERATED.iter().find(|&&(_, x)| x == g)?;
        self.flow_def(flow).members.iter().find(|(n, _)| n == name).map(|&(_, d)| d)
    }

    /// The def of `g` that [`Sema::generated_defs`] made for `flow`, of the
    /// kind its signature gives.
    fn fill_generated(&mut self, flow: DefId, g: Generated, kind: DefKind) {
        let Some(d) = self.generated(flow, g) else {
            onsa_diag::internal::bug(Some(self.a.def(flow).name_span), "a generated item with no def")
        };
        self.a.defs[d.0 as usize].kind = kind;
    }

    fn fill_struct(&mut self, flow: DefId, flow_ty: FlowTy, fields: Vec<FieldDef>) {
        let fields = if flow_ty == FlowTy::State { Fields::Opaque } else { Fields::Named(fields) };
        let def = StructDef { generics: Vec::new(), fields, derives: Some(Vec::new()), flow_ty: Some(flow_ty) };
        self.fill_generated(flow, Generated::Type(flow_ty), DefKind::Struct(def));
    }

    /// A field of a struct `flow` generates: of the visibility of the flow
    /// (§11.6, S-36).
    fn generated_field(&self, flow: DefId, name: &str, ty: TyId) -> FieldDef {
        let d = self.a.def(flow);
        FieldDef { name: name.to_string(), ty, vis: d.vis, span: d.name_span, ty_span: d.name_span, default: None }
    }

    /// The type `t` of `flow`; none of a `Config` or `Params` it has not.
    fn generated_ty(&mut self, flow: DefId, t: FlowTy) -> Option<TyId> {
        let d = self.generated(flow, Generated::Type(t))?;
        Some(self.a.types.intern(Ty::Named(d, Vec::new())))
    }

    /// The type of the channels of `elem` (§11.6): `b[elem]`, or `[b[elem]; N]`
    /// of an array of length `N` (`b` is `Span` of `In`, `Out` and the
    /// parameters, `Buf` of `Rendered`).
    fn channels(&mut self, b: BuiltinTy, (elem, len): (TyId, Option<Len>)) -> TyId {
        let one = self.a.types.builtin(b, vec![elem]);
        match len {
            Some(l) => self.a.types.intern(Ty::Array(one, l)),
            None => one,
        }
    }

    /// The fields of `channels` (name, element, length) as channels of `b`
    /// ([`Self::channels`]).
    fn channel_fields(&mut self, flow: DefId, b: BuiltinTy, channels: &[(String, TyId, Option<Len>)]) -> Vec<FieldDef> {
        let typed: Vec<(&String, TyId)> = channels.iter().map(|(n, e, l)| (n, self.channels(b, (*e, *l)))).collect();
        typed.into_iter().map(|(n, t)| self.generated_field(flow, n, t)).collect()
    }

    /// The `sample` inputs of `flow`: name, element and length of an array.
    fn sig_inputs(&self, flow: DefId) -> Vec<(String, TyId, Option<Len>)> {
        let inputs = self.flow_def(flow).inputs.iter().filter(|i| i.host() == Some(ClockName::Sample));
        inputs
            .map(|i| match self.a.types.get(i.ty) {
                Ty::Array(e, l) => (i.name.clone(), *e, Some(*l)),
                _ => (i.name.clone(), i.ty, None),
            })
            .collect()
    }

    /// The value types of `channels` (name, element, length of an array).
    fn value_tys(&mut self, channels: &[(String, TyId, Option<Len>)]) -> Vec<TyId> {
        channels.iter().map(|&(_, e, l)| l.map_or(e, |l| self.a.types.intern(Ty::Array(e, l)))).collect()
    }

    /// The items the inputs of `flow` give (§11.6): `State`, `Config`,
    /// `Params`, `In`, `SIZE` and `BULK_SIZE`, the kinds of the defs
    /// [`Sema::generated_defs`] made.
    fn fill_by_inputs(&mut self, flow: DefId) {
        let inputs = self.flow_def(flow).inputs.clone();
        let fields = |s: &Self, clock: ClockName| -> Vec<FieldDef> {
            let of = |i: &&FlowInput| i.host() == Some(clock);
            inputs.iter().filter(of).map(|i| s.generated_field(flow, &i.name, i.ty)).collect()
        };
        self.fill_struct(flow, FlowTy::State, Vec::new());
        for t in [FlowTy::Config, FlowTy::Params] {
            if self.generated(flow, Generated::Type(t)).is_some() {
                let fs = t.input_clock().map(|r| fields(self, r)).unwrap_or_default();
                self.fill_struct(flow, t, fs);
            }
        }
        if self.generated(flow, Generated::Type(FlowTy::In)).is_some() {
            let mut fs = self.channel_fields(flow, BuiltinTy::Span, &self.sig_inputs(flow));
            // The field of an input that does not cross (its E0810) is not
            // known: its uses get no diagnostic (§18.1).
            let error = self.a.types.error();
            for (f, i) in fs.iter_mut().zip(inputs.iter().filter(|i| i.host() == Some(ClockName::Sample))) {
                if self.boundary_outputs(i.ty, true).is_err() {
                    f.ty = error;
                }
            }
            self.fill_struct(flow, FlowTy::In, fs);
        }
        let u32 = self.a.types.int(IntKind::U32);
        let size = ConstDef { ty: u32, value: None, int_value: None, param: None, of_attr: None };
        for g in [Generated::Size, Generated::BulkSize] {
            self.fill_generated(flow, g, DefKind::Const(size.clone()));
        }
    }

    /// The items the output of `flow` gives (§11.6): `Out`, `Rendered` and
    /// the functions, whose `cfg` and `params` are of a flow with `Config`
    /// and `Params` alone (S-112). `Out` is of an output that is a struct
    /// and no event (S-1087); of an output not known, it and `Rendered` are
    /// not known.
    /// Whether `process_inplace` is generated (its inputs and outputs pair
    /// up, and it gives no events).
    fn fill_by_output(&mut self, flow: DefId) -> bool {
        let (out, events) = (self.flow_def(flow).out, self.flow_def(flow).gives_events());
        let name_span = self.a.def(flow).name_span;
        // The E0810 of an output that does not cross is of `check_generated`.
        let outputs = self.boundary_outputs(out, false).unwrap_or_default();
        let views = self.channel_fields(flow, BuiltinTy::Span, &outputs);
        self.fill_struct(flow, FlowTy::Out, views);
        // Of an event output, its positions and values, of any type (§11.6).
        let events_out = events.then(|| {
            let pos = self.a.types.int(IntKind::U32);
            vec![("out".to_string(), self.a.types.intern(Ty::Tuple(vec![pos, out])), None)]
        });
        let bufs = self.channel_fields(flow, BuiltinTy::Buf, events_out.as_ref().unwrap_or(&outputs));
        self.fill_struct(flow, FlowTy::Rendered, bufs);
        if self.members_unknown(flow, false) {
            self.unknown_member(flow, Generated::Type(FlowTy::Out));
            self.unknown_member(flow, Generated::Type(FlowTy::Rendered));
        } else if events || !matches!(self.a.types.get(out), Ty::Named(..)) {
            self.absent_member(flow, Generated::Type(FlowTy::Out));
        }

        let u32 = self.a.types.int(IntKind::U32);
        let f32 = self.a.types.float(FloatKind::F32);
        let unit = self.a.types.unit();
        let generated = (self.generated_ty(flow, FlowTy::State), self.generated_ty(flow, FlowTy::Rendered));
        let (state_ty, rendered_ty) = match generated {
            (Some(s), Some(r)) => (s, r),
            _ => onsa_diag::internal::bug(Some(name_span), "a flow with no `State` or `Rendered`"),
        };
        let sp = |_s: &mut Self, name: &str, mode: Mode, ty: TyId| ParamSig {
            name: name.to_string(),
            mode,
            ty,
            span: name_span,
        };
        let mut by_input = |t: FlowTy| {
            let named = self.generated_ty(flow, t).zip(t.param_name());
            named.map(|(ty, name)| sp(self, name, Mode::Borrow, ty))
        };
        let (cfg, params) = (by_input(FlowTy::Config), by_input(FlowTy::Params));
        // The `sample` inputs and the output as §11.6 counts them (S-30): no
        // input, one `Span`, or the `In` the names stage made of two or more;
        // the output a `Span`, or the `Out` of a struct.
        let sig_inputs = self.sig_inputs(flow);
        let one = |s: &mut Self, chans: &[(String, TyId, Option<Len>)]| {
            chans.first().map(|&(_, e, l)| s.channels(BuiltinTy::Span, (e, l)))
        };
        let input = match self.generated_ty(flow, FlowTy::In) {
            Some(t) => Some(t),
            None => one(self, &sig_inputs),
        };
        let input = input.map(|t| sp(self, "input", Mode::Borrow, t));
        let output = match self.generated_ty(flow, FlowTy::Out) {
            Some(t) => t,
            None => one(self, &outputs).unwrap_or_else(|| self.a.types.error()),
        };
        let output = sp(self, "output", Mode::Inout, output);

        let ps = cfg.iter().cloned().chain([sp(self, "sample_rate", Mode::Borrow, f32)]).collect();
        self.fill_fn(flow, ps, state_ty, false, false, FlowFn::Init);
        let ps = vec![sp(self, "s", Mode::Inout, state_ty)];
        self.fill_fn(flow, ps, unit, true, false, FlowFn::Reset);
        let head: Vec<ParamSig> = [sp(self, "s", Mode::Inout, state_ty)].into_iter().chain(params.clone()).collect();
        let ps = head.iter().cloned().chain(input.clone()).chain([output.clone()]).collect();
        self.fill_fn(flow, ps, unit, true, false, FlowFn::Process);
        // `process_inplace` only when inputs and outputs pair up by type (§11.6).
        let pairs = !events
            && sig_inputs.len() == outputs.len()
            && !outputs.is_empty()
            && sig_inputs.iter().zip(&outputs).all(|(i, o)| i.1 == o.1 && i.2 == o.2);
        if pairs {
            self.fill_fn(flow, [head, vec![output]].concat(), unit, true, false, FlowFn::ProcessInplace);
        } else {
            let unpaired = Some((self.value_tys(&sig_inputs), self.value_tys(&outputs)));
            if let DefKind::Flow(fd) = &mut self.a.defs[flow.0 as usize].kind {
                fd.unpaired = unpaired;
            }
        }
        // `frames` of a flow with no `input` (§11.6).
        let frames = input.is_none().then(|| sp(self, "frames", Mode::Borrow, u32));
        let mut ps: Vec<ParamSig> = cfg.into_iter().chain(params).chain(input).chain(frames).collect();
        ps.push(sp(self, "sample_rate", Mode::Borrow, f32));
        self.fill_fn(flow, ps, rendered_ty, false, true, FlowFn::Render);
        pairs
    }

    /// The members of `flow`: the items its types give. `process_inplace`,
    /// when it is not generated (`pairs`), is not in its namespace,
    /// and a `use` of it fails ([`Sema::fail_ungenerated`]); when that is not
    /// known, it is kept ([`Self::members_unknown`]), and it, `process` and
    /// `render`, whose parameters are not known, get no diagnostic at their
    /// calls (§18.1, R-471).
    fn trim_members(&mut self, flow: DefId, pairs: bool) {
        if self.members_unknown(flow, true) {
            let crosses = |g: &Generated| matches!(g, Generated::Fn(f) if f.crosses_boundary());
            for g in GENERATED.iter().map(|&(_, g)| g).filter(crosses) {
                self.unknown_member(flow, g);
            }
            return;
        }
        let inplace = self.generated(flow, Generated::Fn(FlowFn::ProcessInplace));
        if let (false, DefKind::Flow(fd)) = (pairs, &mut self.a.defs[flow.0 as usize].kind) {
            fd.members.retain(|&(_, d)| Some(d) != inplace);
        }
    }

    /// The item `g` of `flow`, which its types decide it has not (`Out`,
    /// S-1087): out of its namespace, and kept apart so that its name still
    /// finds it in the types stage, which reports it
    /// ([`crate::Analysis::not_generated`]).
    fn absent_member(&mut self, flow: DefId, g: Generated) {
        let d = self.generated(flow, g);
        if let DefKind::Flow(fd) = &mut self.a.defs[flow.0 as usize].kind {
            let (absent, kept) = fd.members.drain(..).partition(|&(_, m)| Some(m) == d);
            (fd.absent, fd.members) = (absent, kept);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn fill_fn(&mut self, flow: DefId, params: Vec<ParamSig>, ret: TyId, rt: bool, alloc: bool, which: FlowFn) {
        // With no std (unit tests), there is no `Alloc` to have.
        let mut effects = EffectSet::default();
        if let (true, Some(d)) = (alloc, self.a.alloc()) {
            effects.insert(d);
        }
        let f = FnDef {
            generics: Vec::new(),
            self_mode: None,
            params,
            ret,
            rt,
            effects,
            body: None,
            target: false,
            flow_fn: Some(which),
            derived: None,
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
