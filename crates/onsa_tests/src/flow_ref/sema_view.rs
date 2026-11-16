//! The tables of `onsa_sema` the evaluator reads, in this one file (way (1) of the
//! design memo): the types and targets of the names of a body, the locals and variants
//! the patterns name, the fields of a struct, the values of the constants and the clock
//! of the inputs of a flow. W7-02 to W7-04 rewrite the tables of a flow's body, and the
//! clock of W7-02 changes type: they are met here. A table that is not there (the check
//! stopped, or a work has not written it yet) is [`Fault::Unavailable`], never a guess.

use onsa_driver::Analyzed;
use onsa_sema::def::{FieldDef, Fields, FlowInput, StructDef, VariantDef};
use onsa_sema::ty::Rate;
use onsa_sema::{Analysis, BodyInfo, ConstValue, DefId, DefKind, LocalId, LocalKind, Package};
use onsa_sema::{Target, Ty, TyId};
use onsa_syntax::ast::{Ast, ExprId, PatId};

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
}

impl<'a> View<'a> {
    pub fn new(checked: &'a Analyzed) -> View<'a> {
        View { analysis: &checked.analysis, pkg: &checked.pkg }
    }

    pub fn ty(self, id: TyId) -> &'a Ty {
        self.analysis.types.get(id)
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
        Ok(Body { view: self, ast: &module.parsed.ast, info })
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

impl<'a> Body<'a> {
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
    /// The local of an input of the flow, by its name.
    pub fn input(&self, name: &str) -> Option<LocalId> {
        let at = self.info.locals.iter().position(|l| l.name == name && matches!(l.kind, LocalKind::Param(_)))?;
        Some(LocalId(at as u32))
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
    match input.rate {
        Rate::Init => Stage::Init,
        Rate::Ctl => Stage::Block,
        Rate::Sig => Stage::Sample,
    }
}
