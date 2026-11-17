//! The tables of `onsa_sema` the evaluator reads, in this one file (way (1) of the
//! design memo): the types and targets of the names of a body, the locals and variants
//! the patterns name, the fields of a struct, the values of the constants and the clock
//! of the inputs of a flow. W7-02 to W7-04 rewrite the tables of a flow's body, and the
//! clock of W7-02 changes type: they are met here. A table that is not there (the check
//! stopped, or a work has not written it yet) is [`Fault::Unavailable`], never a guess.

use onsa_diag::Span;
use onsa_driver::Analyzed;
use onsa_sema::def::{FieldDef, Fields, FlowDef, FlowInput, FnDef, StructDef, VariantDef};
use onsa_sema::flow_names::FlowBuiltin;
use onsa_sema::ty::Rate;
use onsa_sema::{
    Analysis, BodyInfo, ConstValue, DefId, DefKind, Entity, LocalId, LocalInfo, LocalKind, ModId, Package,
};
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
}

impl<'a> View<'a> {
    pub fn new(checked: &'a Analyzed) -> View<'a> {
        View { analysis: &checked.analysis, pkg: &checked.pkg }
    }

    pub fn ty(self, id: TyId) -> &'a Ty {
        self.analysis.types.get(id)
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
        Ok(Body { view: self, ast: &module.parsed.ast, info, module: d.module })
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
    /// What `callee` names (no binding hides a builtin, E0304); not a path is a qualifier (`.when~`, W7-10).
    pub fn called(&self, callee: ExprId) -> Result<Called, Fault> {
        let ExprKind::Path(p) = &self.ast.expr(onsa_sema::named(self.ast, callee)).kind else {
            return need(None, "a qualifier of an instance");
        };
        if let [one] = p.segments.as_slice() {
            if let Some(b) = FlowBuiltin::named(&one.name) {
                return Ok(Called::Builtin(b));
            }
        }
        match self.view.analysis.resolve_path(self.module, p) {
            Ok(Entity::Def(d)) if matches!(self.view.analysis.def(d).kind, DefKind::Flow(_)) => Ok(Called::Flow(d)),
            _ => Err(Fault::Internal("the callee of a call of a flow is no flow")),
        }
    }

    /// Is `e` the call `sample_rate()` or `sample_tick()`? They are written with no `~`, and the table has no target for them.
    #[inline(never)]
    pub fn time_call(&self, e: ExprId) -> bool {
        let ExprKind::Call { callee, kind: CallKind::Plain, .. } = &self.ast.expr(e).kind else { return false };
        let time =
            matches!(self.called(*callee), Ok(Called::Builtin(FlowBuiltin::SampleRate | FlowBuiltin::SampleTick)));
        time && !self.names(e)
    }

    pub fn ty(&self, e: ExprId) -> Result<&'a Ty, Fault> {
        Ok(self.view.ty(*need(self.info.expr_types.get(&e), "an expression with no type")?))
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

/// The clock of an input of a flow, as the evaluator tells the stages apart (§11.3): the three
/// clocks of a declaration today; the others come with W7-09 and W7-17.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    Init,
    Block,
    Sample,
}

/// The one place that reads the clock of an input: W7-02 turns its type into `Clock`.
pub fn input_stage(input: &FlowInput) -> Stage {
    rate_stage(input.rate)
}

/// The stage of the clock `name` an `at` writes (§11.3), if it is one of the three.
pub fn clock_stage(name: &str) -> Option<Stage> {
    Rate::of_clock(name).map(rate_stage)
}

/// The clock of the output of a flow (§11.3): always `sample` today (W7-09 and W7-17 bring the others).
pub fn output_stage(_: &FlowDef) -> Stage {
    rate_stage(Rate::Sig)
}

fn rate_stage(rate: Rate) -> Stage {
    match rate {
        Rate::Init => Stage::Init,
        Rate::Ctl => Stage::Block,
        Rate::Sig => Stage::Sample,
    }
}
