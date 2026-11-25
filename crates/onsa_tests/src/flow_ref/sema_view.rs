//! The tables of `onsa_sema` the evaluator reads, in this one file (way (1) of the
//! design memo): the types and targets of the names of a body, the locals and variants
//! the patterns name, the fields of a struct, the values of the constants and the clock
//! of the inputs of a flow. W7-02 to W7-04 rewrite the tables of a flow's body, and the
//! clock of W7-02 changes type: they are met here. A table that is not there (the check
//! stopped, or a work has not written it yet) is [`Fault::Unavailable`], never a guess.

use onsa_diag::Span;
use onsa_driver::Analyzed;
use onsa_sema::clock::{Clock, ClockName};
use onsa_sema::def::{FieldDef, Fields, FlowDef, FlowFn, FlowInput, FlowTy, FnDef, StructDef, VariantDef};
use onsa_sema::flow_names::{FlowBuiltin, Modifier};
use onsa_sema::prim::PrimRow;
use onsa_sema::{Analysis, BodyInfo, ConstValue, DefId, DefKind, LocalId, LocalInfo, LocalKind, ModId, Package};
use onsa_sema::{Target, Ty, TyId};
use onsa_syntax::ast::{Ast, CallKind, ExprId, ExprKind, PatId, PatKind};

use super::scalar::Fault;

fn need<T>(x: Option<T>, what: &'static str) -> Result<T, Fault> {
    x.ok_or(Fault::Unavailable(what))
}

/// A checked package.
#[derive(Clone, Copy)]
pub struct View<'a> {
    analysis: &'a Analysis,
    pkg: &'a Package,
}

/// A body (of a flow, a function, a test or a `const`) with its syntax tree and tables.
#[derive(Clone, Copy)]
pub struct Body<'a> {
    pub view: View<'a>,
    pub ast: &'a Ast,
    pub info: &'a BodyInfo,
    pub module: ModId,
    /// The declaration whose body it is: the names stage records the calls of a flow by it.
    pub def: DefId,
}

impl<'a> View<'a> {
    pub fn new(checked: &'a Analyzed) -> View<'a> {
        View { analysis: &checked.analysis, pkg: &checked.pkg }
    }

    pub fn ty(self, id: TyId) -> &'a Ty {
        self.analysis.types.get(id)
    }

    /// Is the type Copy (§4.6: the kind is decided by the structure, an array, a tuple, a struct and an enum of Copy
    /// elements are Copy)? The one place of the judgement is the checker's (D-15); an unjudged type is not Copy.
    pub fn is_copy(self, id: TyId) -> bool {
        self.analysis.kind_of(id) == Some(onsa_sema::Kind::Copy)
    }

    /// Where the name of a declaration is written.
    pub fn name_span(self, def: DefId) -> Span {
        self.analysis.def(def).name_span
    }

    /// The body of a declaration, when its tables are whole (`BodyInfo::complete`).
    pub fn body(self, def: DefId) -> Result<Body<'a>, Fault> {
        let d = self.analysis.def(def);
        let info = match &d.kind {
            DefKind::Flow(_) => self.analysis.flows.get(&def).map(|f| &f.body),
            _ => self.analysis.bodies.get(&def),
        };
        let (info, module) =
            (need(info, "no tables for a body")?, need(self.analysis.ast(self.pkg, d.module), "no tree")?);
        need(info.complete.then_some(()), "a body whose tables are not whole")?;
        Ok(Body { view: self, ast: &module.parsed.ast, info, module: d.module, def })
    }

    /// The declaration of a flow: its inputs and its body (`body` has the tables of the body).
    pub fn flow(self, def: DefId) -> Result<&'a FlowDef, Fault> {
        match &self.analysis.def(def).kind {
            DefKind::Flow(f) => Ok(f),
            _ => need(None, "a name that is not a flow"),
        }
    }

    /// The value the checker worked out for a `const`; none for the ones it does not evaluate (`F32.NAN`).
    pub fn const_value(self, def: DefId) -> Option<&'a ConstValue> {
        self.analysis.const_values.get(&def)
    }

    /// The initializer of a `const` (or of the default of a field), with its body.
    pub fn const_init(self, def: DefId) -> Result<(Body<'a>, ExprId), Fault> {
        match &self.analysis.def(def).kind {
            DefKind::Const(c) => Ok((self.body(def)?, need(c.value, "a const without an initializer")?)),
            _ => need(None, "a name that is not a const"),
        }
    }

    /// The module and the name a module writes for a declaration (`t.wrap01`; `t.P.lp` for `lp` of `impl P`, `t.Q.lp`
    /// for that of `impl Q`): a name a test's host tells functions apart by. A host that is not a table of names
    /// (W7-19) asks the `DefId`, which is one for each declaration.
    pub fn qualified_name(self, def: DefId) -> String {
        let (a, module) = (self.analysis, &self.analysis.modules.get(self.analysis.def(def).module).path);
        [module.clone(), a.shown_name(def)].into_iter().filter(|s| !s.is_empty()).collect::<Vec<_>>().join(".")
    }

    /// Is the declaration in the std (its module is of the package of that role)?
    pub fn in_std(self, def: DefId) -> bool {
        self.analysis.modules.is_std(self.analysis.def(def).module)
    }

    /// The function a generated one is (`render`) and the flow it belongs to (§11.6).
    pub fn flow_fn(self, def: DefId) -> Option<(FlowFn, DefId)> {
        let d = self.analysis.def(def);
        Some((d.as_fn()?.flow_fn?, d.owner?))
    }

    /// The row of the table of primitives a function is (`len`, `is_nan`, `to_bits`: not told by their names).
    pub fn prim(self, def: DefId) -> Option<&'a PrimRow> {
        self.analysis.prims.get(&def)
    }

    /// The flows of the package.
    pub fn flows(self) -> Vec<DefId> {
        let a = self.analysis;
        let mods = self.pkg.modules.iter().filter_map(|m| a.module_of_file(m.file));
        let defs = mods.flat_map(|m| a.defs_of_module(m));
        defs.filter(|(_, d)| matches!(d.kind, DefKind::Flow(_))).map(|(id, _)| id).collect()
    }

    /// The `len` of an array (std's `impl [T; N]`, a plain function: a `Span`'s is the primitive `Len`): the function of the
    /// name of that primitive, in its module, with no row of its own and an array for its `impl`. The one place that says
    /// which callee it is.
    pub fn array_len(self) -> Option<DefId> {
        let a = self.analysis;
        let (span_len, _) = a.prims.iter().find(|(_, row)| matches!(row, PrimRow::Len))?;
        let named = a.def(*span_len);
        let of_array = |d: &onsa_sema::def::Def| {
            let owner = d.owner.and_then(|o| a.def(o).as_impl());
            owner.is_some_and(|i| matches!(self.ty(i.self_ty), Ty::Array(..)))
        };
        let mut same =
            a.defs_of_module(named.module).filter(|(id, d)| d.name == named.name && !a.prims.contains_key(id));
        same.find(|(_, d)| of_array(d)).map(|(id, _)| id)
    }

    /// The struct a type is and what it is of a flow, when a flow generated it (`Config`, `Params`, `In`, `Rendered`).
    pub fn flow_ty(self, ty: TyId) -> Option<(DefId, FlowTy)> {
        match self.ty(ty) {
            Ty::Named(d, _) => match &self.analysis.def(*d).kind {
                DefKind::Struct(s) => s.flow_ty.map(|f| (*d, f)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The `test` blocks of the package, in the order they are declared.
    pub fn tests(self) -> Vec<(DefId, String, ExprId)> {
        let a = self.analysis;
        let mods = self.pkg.modules.iter().filter_map(|m| a.module_of_file(m.file));
        let defs = mods.flat_map(|m| a.defs_of_module(m));
        let test = |(id, d): (DefId, &'a onsa_sema::def::Def)| match &d.kind {
            DefKind::Test { name, body } => Some((id, name.clone(), *body)),
            _ => None,
        };
        defs.filter_map(test).collect()
    }

    /// The path of the module of a declaration (`math`, `core.num`; empty for a package root).
    pub fn module_path(self, def: DefId) -> &'a str {
        &self.analysis.modules.get(self.analysis.def(def).module).path
    }

    /// The name a module writes for a declaration, with its type when it is a member (`F32.round_from`).
    pub fn shown_name(self, def: DefId) -> String {
        self.analysis.shown_name(def)
    }

    /// A type as source writes it (user types by their short names).
    pub fn display_type(self, ty: TyId) -> String {
        self.analysis.display_type(ty)
    }

    /// Whether the type `def` has a hand-written `impl Default` (§6.4), whose `default()` is its default.
    pub fn default_by_hand(self, def: DefId) -> bool {
        self.analysis.modules.trait_impls.contains_key(&(onsa_sema::def::Bound::Default, def))
    }

    /// The `default` function of the hand-written `impl Default` of the type `def` and the type it returns (§6.4).
    pub fn hand_default(self, def: DefId) -> Result<(DefId, TyId), Fault> {
        let imp =
            need(self.analysis.modules.trait_impls.get(&(onsa_sema::def::Bound::Default, def)), "an impl Default")?;
        let imp = need(self.analysis.def(*imp).as_impl(), "an impl that is not one")?;
        // `Default` has the one member `default` (§6.4), so the one function of its `impl` is it.
        let f = need(imp.fns.first().filter(|_| imp.fns.len() == 1), "an impl Default that has not one function")?;
        Ok((*f, imp.self_ty))
    }

    /// The function `def` as a callee with no type argument (a function that is not generic, called by name).
    pub fn fn_callee(self, def: DefId) -> Result<Callee<'a>, Fault> {
        let func = need(self.analysis.def(def).as_fn(), "a callee that is not a function")?;
        Ok(Callee { def, func, method: false, type_args: &[] })
    }

    /// The fields of a struct in the order of the declaration, with the declared default of each.
    pub fn struct_fields(self, def: DefId) -> Result<&'a [FieldDef], Fault> {
        match &self.analysis.def(def).kind {
            DefKind::Struct(StructDef { fields: Fields::Named(fields), .. }) => Ok(fields),
            _ => need(None, "a name that is not a struct with its fields"),
        }
    }

    /// The variants of an enum in the order of the declaration (the number of a variant is its place).
    pub fn variants(self, def: DefId) -> Result<&'a [VariantDef], Fault> {
        match &self.analysis.def(def).kind {
            DefKind::Enum(e) => Ok(&e.variants),
            _ => need(None, "a name that is not an enum"),
        }
    }
}

/// What the callee of a call of a flow is: a builtin (a delay, `sample_rate()`, `sample_tick()`) or a flow of the user.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Called {
    Builtin(FlowBuiltin),
    Flow(DefId),
}

impl<'a> Body<'a> {
    /// The builtin the call `call` names, as the names stage found it (an item or a `use` that takes the name first is
    /// not one, E0304): the evaluator does not tell them by the spelling (D-15).
    fn builtin(&self, call: ExprId) -> Option<FlowBuiltin> {
        let ExprKind::Call { callee, .. } = &self.ast.expr(call).kind else { return None };
        self.view.analysis.flow_builtin(self.def, onsa_sema::named(self.ast, *callee))
    }

    /// What the call `call` of a flow makes an instance of: a builtin, or the flow the names stage recorded for it
    /// (`util.lp~(x)` too, D-15). A call the stage has no flow for is a qualifier (`.when~`, W7-10) and not evaluated.
    pub fn called(&self, call: ExprId) -> Result<Called, Fault> {
        if let Some(b) = self.builtin(call) {
            return Ok(Called::Builtin(b));
        }
        match self.view.analysis.instance_of(self.def, call) {
            Some(def) => Ok(Called::Flow(def)),
            None => need(None, "a call that is no instance of a flow (a qualifier)"),
        }
    }

    /// The modifier the call `e` is, its receiver and the head of its chain (`lp~(x).down~(2)` is `down` of `lp~(x)`, §11.10), as the names stage recorded it
    /// (R-512, D-15). A call of a flow of a module (`util.down~(x)`) is not one.
    pub fn modifier(&self, e: ExprId) -> Option<(Modifier, ExprId, ExprId)> {
        self.view.analysis.modifier_of(self.def, e)
    }

    /// Is `e` the call `sample_rate()` or `sample_tick()`? They are written with no `~`, and the table has no target for them.
    #[inline(never)]
    pub fn time_call(&self, e: ExprId) -> bool {
        let time = matches!(self.builtin(e), Some(FlowBuiltin::SampleRate | FlowBuiltin::SampleTick));
        time && matches!(self.ast.expr(e).kind, ExprKind::Call { kind: CallKind::Plain, .. }) && !self.names(e)
    }

    pub fn ty_id(&self, e: ExprId) -> Result<TyId, Fault> {
        need(self.info.expr_types.get(&e).copied(), "an expression with no type")
    }
    pub fn ty(&self, e: ExprId) -> Result<&'a Ty, Fault> {
        Ok(self.view.ty(self.ty_id(e)?))
    }
    pub fn target(&self, e: ExprId) -> Result<&'a Target, Fault> {
        need(self.info.targets.get(&e), "a name with no target")
    }
    /// The local a pattern binds (`PatKind::Bind`).
    pub fn pat_local(&self, p: PatId) -> Result<LocalId, Fault> {
        need(self.info.pat_locals.get(&p).copied(), "a pattern with no local")
    }
    /// The locals a pattern binds (each `PatKind::Bind` in it): the one place that says which locals it makes.
    pub fn pat_locals(&self, p: PatId) -> Result<Vec<LocalId>, Fault> {
        let mut out = Vec::new();
        self.collect_locals(p, &mut out)?;
        Ok(out)
    }
    fn collect_locals(&self, p: PatId, out: &mut Vec<LocalId>) -> Result<(), Fault> {
        match &self.ast.pat(p).kind {
            PatKind::Bind(_) => out.push(self.pat_local(p)?),
            PatKind::TupleStruct { elems: ps, .. } | PatKind::Tuple(ps) | PatKind::Or(ps) => {
                ps.iter().try_for_each(|q| self.collect_locals(*q, out))?
            }
            PatKind::Struct { fields, .. } => fields.iter().try_for_each(|(_, q)| self.collect_locals(*q, out))?,
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
        }
        Ok(())
    }
    /// Is the local bound inside the expression `e` (an arm of a `match`)?
    pub fn bound_within(&self, l: LocalId, e: ExprId) -> bool {
        let (at, span) = (self.info.locals.get(l.0 as usize).map(|l| l.span), self.ast.expr(e).span);
        at.is_some_and(|at| span.start <= at.start && at.end <= span.end)
    }
    /// Does `e` read a local that a `match` arm binds outside `root` (the `n` of `match~ k { n => lp~(x, n) }` in the argument of
    /// `lp~`: the argument is `root`)? One bound within `root` is made by it.
    pub fn reads_arm_binding(&self, e: ExprId, root: ExprId) -> bool {
        let arm = |l: &LocalId| {
            let kind = self.info.locals.get(l.0 as usize).map(|i| &i.kind);
            matches!(kind, Some(LocalKind::MatchBind)) && !self.bound_within(*l, root)
        };
        let names = matches!(self.ast.expr(e).kind, ExprKind::Path(_))
            && matches!(self.info.targets.get(&e), Some(Target::Local(l)) if arm(l));
        names || self.ast.sub_exprs(e).into_iter().any(|x| self.reads_arm_binding(x, root))
    }
    /// The number of the variant a pattern names.
    pub fn pat_ctor(&self, p: PatId) -> Result<u32, Fault> {
        need(self.info.pat_ctors.get(&p).copied(), "a pattern with no variant")
    }
    /// Does the table give a target to `e`? (`F32.PI` and `Mode.Off` have one, the field `p.x` has not.)
    pub fn names(&self, e: ExprId) -> bool {
        self.info.targets.contains_key(&e)
    }
    /// Does a path pattern name a variant (else a constant)?
    pub fn is_ctor(&self, p: PatId) -> bool {
        self.info.pat_ctors.contains_key(&p)
    }
    /// The constant a path pattern names.
    pub fn pat_const(&self, p: PatId) -> Result<&'a Target, Fault> {
        need(self.info.pat_consts.get(&p), "a pattern with no constant")
    }
    /// What a call names (`f(x)`, `T.f(x)`, `x.m(y)`), with the type arguments of its instance.
    pub fn callee(&self, call: ExprId) -> Result<Callee<'a>, Fault> {
        let (def, of, inst, method) = match self.target(call)? {
            Target::Fn { def, of, inst } => (*def, of, inst, false),
            Target::Method { def, of, inst } => (*def, of, inst, true),
            _ => return need(None, "a call that is not of a function"),
        };
        // The `def` of a member of the bound of a type parameter is that of a representative type, not the callee.
        need(of.is_none().then_some(()), "a member of the bound of a type parameter")?;
        let func = need(self.view.analysis.def(def).as_fn(), "a callee that is not a function")?;
        let type_args = match inst {
            Some(i) => &need(self.info.instances.get(i.0 as usize), "an instance not in the table")?.args[..],
            None => &[],
        };
        Ok(Callee { def, func, method, type_args })
    }

    /// The local each argument of a call of `f` is bound to, in the order of the arguments (the receiver first): the
    /// locals of the parameters are in the order of the heading, each within the span of its parameter of the signature,
    /// and a `_` has none.
    pub fn params(&self, f: &FnDef) -> Result<Vec<Option<LocalId>>, Fault> {
        let params = self.info.locals.iter().enumerate();
        let mut locals =
            params.filter(|(_, l)| matches!(l.kind, LocalKind::Param(_) | LocalKind::SelfParam(_))).peekable();
        let mut out = Vec::new();
        if f.self_mode.is_some() {
            out.push(Some(LocalId(need(locals.next(), "a method with no `self` local")?.0 as u32)));
        }
        for p in &f.params {
            let within = |l: &LocalInfo| p.span.start <= l.span.start && l.span.end <= p.span.end;
            out.push(locals.next_if(|(_, l)| within(l)).map(|(at, _)| LocalId(at as u32)));
        }
        need(locals.peek().is_none().then_some(out), "a local of a parameter that the signature has not")
    }

    /// The local of the variable of a `par~`, by where it is written: the `i` of `par~ i in 0 ..< 4`.
    pub fn par_var(&self, at: Span) -> Result<LocalId, Fault> {
        let found = self.info.locals.iter().position(|l| l.span == at && matches!(l.kind, LocalKind::Let));
        need(found.map(|n| LocalId(n as u32)), "a `par~` variable with no local")
    }

    /// The local of the `var` written at `at` (the span of its name).
    pub fn var_local(&self, at: Span) -> Result<LocalId, Fault> {
        let found = self.info.locals.iter().position(|l| l.span == at);
        need(found.map(|n| LocalId(n as u32)), "a `var` with no local")
    }

    /// The type of a local.
    pub fn local_ty(&self, l: LocalId) -> Result<&'a Ty, Fault> {
        Ok(self.view.ty(need(self.info.locals.get(l.0 as usize), "a local not in the table")?.ty))
    }

    /// The local of an input of a flow or of a parameter of a function (`self` included), by its name.
    pub fn input(&self, name: &str) -> Option<LocalId> {
        let at = self
            .info
            .locals
            .iter()
            .position(|l| l.name == name && matches!(l.kind, LocalKind::Param(_) | LocalKind::SelfParam(_)))?;
        Some(LocalId(at as u32))
    }
}

/// The function a call names: a method has its receiver for the first argument. Its type arguments are those of the
/// instance the call made of it (none for a function that is not generic).
pub struct Callee<'a> {
    pub def: DefId,
    pub func: &'a FnDef,
    pub method: bool,
    pub type_args: &'a [TyId],
}

impl Callee<'_> {
    /// A `target` function is a primitive of the backend: its call is not one of §12.5, and its body (`abs` has one)
    /// is not run by the evaluator, so the host gives its value.
    pub fn primitive(&self) -> bool {
        self.func.target
    }
}

/// A stage of a flow (§11.3): `init`, `block`, and a tick of the ratio `2^r` of `sample` (`Tick(0)` is `sample`, a slower tick `r < 0`, §11.9). The inputs
/// of a declaration are at the first three today; W7-17 has the others.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    Init,
    Block,
    /// The stage of an event source (§11.11, W7-11 U2): the input of that index of the declaration, or a call (`events::call_src`); `EVENT` for an event input or output as a declaration says it, before its source is known.
    Event(u32),
    Tick(i32),
}

impl Stage {
    /// The stage of the `sample` of the body: a const of the type, so that it is written as a variant and matched as one.
    #[allow(non_upper_case_globals)]
    pub const Sample: Stage = Stage::Tick(0);
}

/// An event as a declaration says it (`input_stage`, `output_stage`): the source is the input (its index) or the call of the caller, which this does not know.
pub const EVENT: u32 = u32::MAX;

/// The stage a clock is made in. A tick of any ratio has its own: `sample / N` is
/// `Tick(-k)` and `sample * N` `Tick(k)` (§11.9).
pub(super) fn stage_of(clock: Clock) -> Result<Stage, Fault> {
    match clock {
        Clock::Init => Ok(Stage::Init),
        Clock::Block => Ok(Stage::Block),
        Clock::Tick(onsa_sema::clock::Ratio(r)) => Ok(Stage::Tick(r)),
        Clock::Event(_) => Ok(Stage::Event(EVENT)),
        _ => Err(Fault::Unavailable("a clock of no stage the evaluator has")),
    }
}

/// The ratio `r` of the tick an input is declared at, as a caller reads it (`sample * 2^r`, §11.9): `None` for the parameter kinds.
pub(super) fn input_ratio(input: &FlowInput) -> Option<i32> {
    match input.caller_clock() {
        Clock::Tick(onsa_sema::clock::Ratio(r)) => Some(r),
        _ => None,
    }
}

/// The stage of an input: its `Clock` as the body reads it (`FlowInput::body_clock`).
pub fn input_stage(input: &FlowInput) -> Result<Stage, Fault> {
    stage_of(input.body_clock())
}

/// The inputs of `decl` that are at `stage`, in the order of the heading.
pub fn inputs_at(decl: &FlowDef, stage: Stage) -> Result<Vec<&FlowInput>, Fault> {
    let mut mine = Vec::new();
    for (n, i) in decl.inputs.iter().enumerate() {
        let here = match (input_stage(i)?, stage) {
            (Stage::Event(_), Stage::Event(k)) => k == n as u32,
            (s, t) => s == t,
        };
        if here {
            mine.push(i);
        }
    }
    Ok(mine)
}

/// The clock of the input number `n` of `decl` as its body reads it: an event input is the source of its index (§11.11).
pub fn input_clock(decl: &FlowDef, n: usize) -> Result<super::flow::Clock, Fault> {
    let input = decl.inputs.get(n).ok_or(Fault::Internal("an input that is not there"))?;
    Ok(match input_stage(input)? {
        Stage::Event(_) => super::flow::Clock::Event(n as u32),
        s => s.into(),
    })
}

/// The stage of the clock `name` an `at` writes (§11.3), if it is one of the three.
pub fn clock_stage(name: &str) -> Option<Stage> {
    ClockName::of_name(name).map(name_stage)
}

/// The clock of the output of a flow (§11.3), as its declaration made it: `sample * 2^r` for a caller to read (§11.9).
pub fn output_stage(decl: &FlowDef) -> Result<Stage, Fault> {
    stage_of(decl.out_clock)
}

fn name_stage(name: ClockName) -> Stage {
    match name {
        ClockName::Init => Stage::Init,
        ClockName::Block => Stage::Block,
        ClockName::Sample => Stage::Sample,
    }
}
