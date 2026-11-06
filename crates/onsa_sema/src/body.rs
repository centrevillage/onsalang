//! Function-body checking (T2-5 .. T2-7, T2-10, T2-11): the inference of spec
//! §4.7 — statement order, unification variables, downward expected types —
//! plus generics instantiation, closures as arguments, builtin methods
//! and `const` evaluation; the names and the bindings are the names stage's
//! record (`crate::names::body`). Argument modes / exclusivity (T2-8)
//! and `rt` (T2-9) run after this pass over the tables in [`BodyInfo`].
//!
//! Where the code is: this module holds the tables ([`BodyInfo`], the locals,
//! the targets), the checker (`Checker`, `check_all`), its helpers and
//! locals, and the accessors that the later passes read. The
//! rest of the checking is in a module per part, each an `impl` of
//! `Checker`: `entry` (a function body, a `const`), `bounds`, `generics`,
//! `named` (the names the names stage resolved), `expressions`, `calls`, `statements` and `patterns`. The tests
//! are `body_tests.rs`.

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{
    Arg, Ast, BinOp, Block, CallKind, Expr, ExprId, ExprKind, Ident, Lit, MatchArm, Mode, OpGroup, Param, ParamName,
    PatId, PatKind, Path, RangeEnd, RangeHead, StmtId, StmtKind, StrSeg, UnOp,
};
use serde::{Deserialize, Serialize};

use crate::binding::{Bind, Head, HeadRow, LitClass};
use crate::builtin;
use crate::def::{Bound, DefKind, Fields, FnDef, GenericDef, GenericKind};
use crate::deferred::{ArgumentName, Deferred, DeferredKind, OpNeed, Required, Verdict};
use crate::exhaust::{Missing, P, Seen};
use crate::infer::{Cause, Infer, LitKind, Mismatch};
use crate::modes::Proj;
use crate::names::body::{BindingKind, BodyNames, Origin, PatRes, PathRes, StructRes};
use crate::resolve::{Builtin, Entity, ResolveError};
use crate::structpat::Written;
use crate::ty::{BuiltinTy, FnTy, IntKind, Len, Ty, TyId, Types};
use crate::{Analysis, DefId, Kind, ModId, Package, flatten};

pub(crate) mod bounds;
mod call_forms;
mod calls;
mod const_patterns;
mod conversions;
mod entry;
mod expressions;
mod generics;
mod named;
pub(crate) mod operator_fix;
mod patterns;
mod reach;
mod receivers;
mod removed;
pub(crate) mod slot;
mod statements;

// ---------------------------------------------------------------- tables

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LocalId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalKind {
    /// A function parameter with its mode.
    Param(Mode),
    /// The `self` receiver with its mode.
    SelfParam(Mode),
    Let,
    Var,
    /// `for` variable; `moved` for `for x in move xs`.
    For {
        moved: bool,
    },
    MatchBind,
    ClosureParam(Mode),
}

impl LocalKind {
    /// The kind of the binding of the record: a flow's input is a borrowed
    /// parameter, its `let` and the variable of a `par` are `let`s.
    fn of(kind: BindingKind) -> LocalKind {
        match kind {
            BindingKind::Param(m) => LocalKind::Param(m),
            BindingKind::SelfParam(m) => LocalKind::SelfParam(m),
            BindingKind::Let | BindingKind::FlowLet | BindingKind::ParVar => LocalKind::Let,
            BindingKind::Var => LocalKind::Var,
            BindingKind::For { moved } => LocalKind::For { moved },
            BindingKind::MatchBind => LocalKind::MatchBind,
            BindingKind::ClosureParam(m) => LocalKind::ClosureParam(m),
            BindingKind::FlowInput => LocalKind::Param(Mode::Borrow),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalInfo {
    pub name: String,
    pub span: Span,
    /// Resolved at the end of the body (may still contain `Ty::Param` in generic bodies).
    pub ty: TyId,
    pub kind: LocalKind,
    /// Its state (§5.4), settled after the types stage ([`crate::binding`]);
    /// the types stage does not read it.
    pub state: Bind,
}

impl LocalInfo {
    pub(crate) fn set_state(&mut self, state: Bind) {
        self.state = state;
    }

    /// A function-type parameter of the default mode (§5.2, S-190), of a
    /// function or an anonymous function: second-class in its body, as it
    /// may hold captures (§13.5). By its declared type (an alias resolved);
    /// not a `T` a function type fills, nor an `inout` or `move` one.
    pub fn fn_param(&self, types: &Types) -> bool {
        matches!(self.kind, LocalKind::Param(Mode::Borrow) | LocalKind::ClosureParam(Mode::Borrow))
            && matches!(types.get(self.ty), Ty::Fn(_))
    }
}

/// Instantiation of a generic def at a call site (for monomorphization).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Instance {
    pub def: DefId,
    /// One per generic parameter of the def (const parameters as `ConstVal`).
    pub args: Vec<TyId>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InstId(pub u32);

/// What a path, field chain, or call resolved to.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Target {
    Local(LocalId),
    /// A `const N` generic parameter used as a `U32` value.
    ConstParam(u32),
    /// A function item (as a value, or the callee of a `Call`). `of`: see
    /// [`Target::Method`].
    Fn {
        def: DefId,
        of: Option<TyId>,
        inst: Option<InstId>,
    },
    /// A constant. `inst` holds the type arguments of a constant of a generic
    /// `impl`, read as a value (S-304); `None` for any other constant, and
    /// where a length or a constant expression reads one by its value. `of`:
    /// see [`Target::Method`].
    Const {
        def: DefId,
        of: Option<TyId>,
        inst: Option<InstId>,
    },
    /// A unit variant (value) or tuple variant (constructor / callee).
    Variant {
        def: DefId,
        index: u32,
    },
    /// `panic` (§9.2).
    Panic,
    /// `x.m(...)` on a user type: the method def; the receiver is the callee's `base`.
    ///
    /// `of` is the type parameter of a member of its bounds (`T.ZERO`,
    /// `T.round_from(k)`, `x.checked_add(y)`). Then `def` is the member of the
    /// representative type ([`crate::traits::MEMBERS`]), and only the form of
    /// its declaration may be read (its kind, `self`, the modes, `rt`, the
    /// effects), which is the same for every type of the bound. What depends
    /// on the type (its value, its types, the type in a message) is not read
    /// from it: the types stage reads the declaration at `of`, and lowering
    /// binds the use to the member of the instantiated type
    /// (`Lowerer::instance_target`).
    Method {
        def: DefId,
        of: Option<TyId>,
        inst: Option<InstId>,
    },
    /// A method of the compiler's table (`xs.len()` of an array,
    /// `crate::builtin`).
    BuiltinMethod {
        name: String,
        /// The mode of `self`, as the types stage chose it (§5.2; the modes
        /// stage reads it, not the name).
        self_mode: Mode,
    },
    /// A call through a function value (closure or `fn` value).
    Value,
}

/// The constructors of a `?` (§9.1), by their index: that of the value it
/// takes out, and that of the early return, which keeps its elements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct TryArms {
    pub keep: u32,
    pub exit: u32,
}

/// Typed body of one function, test, or `const` initializer.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct BodyInfo {
    /// Type of every expression, fully resolved (variables substituted).
    pub expr_types: HashMap<ExprId, TyId>,
    pub locals: Vec<LocalInfo>,
    /// Path / field-chain / call expressions → what they refer to.
    pub targets: HashMap<ExprId, Target>,
    /// `PatKind::Bind` patterns → the local they introduce.
    pub pat_locals: HashMap<PatId, LocalId>,
    /// The constructor patterns of an enum (`S.Circle(r)`, `Self.Dot`,
    /// `None`) → the index of the constructor they name, as the names stage
    /// resolved their path: the lowering reads it (D-15).
    pub pat_ctors: HashMap<PatId, u32>,
    /// The constants of the patterns (`LIMIT`, `cfg.LIMIT`, `I64.MAX`), each
    /// a [`Target::Const`]: the lowering compares with them (§7, S-185).
    pub pat_consts: HashMap<PatId, Target>,
    pub instances: Vec<Instance>,
    /// Closure expression → outer locals it captures (by copy, §5.3).
    pub captures: HashMap<ExprId, Vec<LocalId>>,
    /// A hole of a string literal (§2.4), by the literal and the index of the
    /// hole in its segments → what the name its path ends at refers to.
    pub hole_targets: HashMap<(ExprId, u32), Target>,
    /// `-e` expressions whose operand, without parentheses, is a numeric literal:
    /// the `-` is a part of the literal's value (§4.7, S-184, S-227). The lowering
    /// folds exactly these (R-03); every other `-` negates a value.
    pub neg_literals: HashSet<ExprId>,
    /// The `?` expressions that passed the check → their constructors: the
    /// lowering reads them (S-71, D-15).
    pub tries: HashMap<ExprId, TryArms>,
    /// What diverges (§7), as the names stage recorded it.
    pub diverging: onsa_syntax::tails::Diverging,
    /// The rows of the heads of the bindings (§5.4), and the marks of the
    /// static values, the literals that need no drop and the owned aggregate
    /// literals with their first element, settled with the states of the
    /// locals ([`crate::binding`]).
    pub heads: HashMap<Head, HeadRow>,
    pub lits: HashMap<ExprId, LitClass>,
    /// `false` when checking stopped at the first error (tables are partial).
    pub complete: bool,
    /// The body reads what the check does not read (§18.1, S-692: a name the
    /// names stage holds as an error, a member of a def a syntax error cut):
    /// the check went on, and a fix of the name can show an error it did not
    /// report. Its signature is not changed, so its users are not affected,
    /// except the callers of an rt function: a call on a value of the error
    /// type makes no edge of the rt recursion (`Analysis::reached`).
    pub read_unread: bool,
    /// The paths of Affine fields taken out of owned locals (S-85, §5.2),
    /// each once, in the order the modes stage walked them: their roots are
    /// moved, and what is left is dropped where it is taken
    /// (`rt::rest_drops_alloc`; lowered from W8-04).
    pub taken: Vec<Taken>,
}

/// A path of fields taken out of the owned local `root` at `at` (S-85).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Taken {
    pub at: Span,
    pub root: LocalId,
    /// Its steps: fields and tuple elements only.
    pub(crate) path: Vec<Proj>,
}

// ---------------------------------------------------------------- checker

pub(crate) struct Stop;
pub(crate) type R<T> = Result<T, Stop>;

/// A function or closure body being checked.
pub(crate) struct Frame {
    pub(crate) ret: TyId,
    pub(crate) loop_depth: u32,
}

pub(crate) struct Checker<'a> {
    pub(crate) a: &'a mut Analysis,
    pub(crate) ast: &'a Ast,
    pub(crate) text: &'a str,
    pub(crate) m: ModId,
    pub(crate) def: DefId,
    generics: Vec<GenericDef>,
    self_ty: Option<TyId>,
    pub(crate) infer: Infer,
    pub(crate) frames: Vec<Frame>,
    /// The blocks being checked, innermost last: the node, the block and the
    /// item it is at ([`Checker::open_block`]; what stops at a statement
    /// reads what follows it here, §7).
    pub(crate) blocks: Vec<(ExprId, &'a Block, usize)>,
    pub(crate) info: BodyInfo,
    pub(crate) failed: bool,
    /// The constants of a type no pattern compares found in the pattern
    /// being bound, with their types ([`Checker::bind_pat`]).
    bad_consts: Vec<(Span, TyId)>,
    /// Flow mode (T3-1, `flow.rs`): set while checking a flow body.
    pub(crate) flow: Option<crate::flow::FlowCx>,
    /// Checks that wait for a type a later statement decides (`deferred.rs`).
    pub(crate) deferred: Vec<Deferred>,
    /// The items of `deferred` looked at by the last statement, and the binding
    /// generation then (`check_deferred_now` skips them while nothing was bound).
    pub(crate) deferred_seen: usize,
    pub(crate) deferred_generation: u32,
    /// The items only the end of the body decides (E0405, E0406, E0421), and the
    /// number of items made so far (their order across both lists).
    pub(crate) deferred_end: Vec<Deferred>,
    pub(crate) deferred_count: u32,
    /// Where an expected type comes from (`an argument of `f``), for the note of
    /// E0416 (§4.5): it names a binding only when that very expected type is the
    /// one unified (an argument, an annotation, the result, a field); every other
    /// binding gets a note with its position alone.
    why: Option<(String, TyId)>,
    /// The anonymous function written directly as the argument being checked
    /// (the one whose E0401 has a candidate, §8.1; not one in parentheses).
    pub(crate) arg_closure: Option<ExprId>,
    /// The names of the body, which the names stage resolved (W4-04).
    pub(crate) names: crate::names::body::BodyNames,
    /// The local of each binding no pattern makes, by its [`Origin`].
    origins: HashMap<Origin, LocalId>,
    /// The locals given their type so far (a branch of a choice after the
    /// first unifies with it, §7).
    typed: Vec<bool>,
    /// The expression of the body, under which a candidate finds the place
    /// of an expression (`slot.rs`).
    root: ExprId,
    /// The names the defs of each module bind, made in the check of the
    /// package where a candidate asks (`removed.rs`).
    bound: &'a mut HashMap<ModId, HashSet<String>>,
}

/// The body of the def `id` the types stage checks, with the type `Self`
/// stands for there and the type the body has: of a function, a test, a
/// `const` and a flow; none of another def and of a declaration with no
/// body.
fn body_of(a: &mut Analysis, id: DefId) -> Option<(Option<TyId>, ExprId, TyId)> {
    let self_ty = a.self_ty_of(id);
    Some(match &a.def(id).kind {
        DefKind::Fn(f) => (self_ty, f.body?, f.ret),
        DefKind::Test { body, .. } => {
            let body = *body;
            (None, body, a.types.unit())
        }
        DefKind::Const(c) => (self_ty, c.value?, c.ty),
        // Flow bodies (T3-1): the same inference, in flow mode (`flow.rs`).
        DefKind::Flow(f) => (None, f.body, f.out),
        _ => return None,
    })
}

/// Check every body of the package and its dependencies.
pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) {
    let flat = flatten(pkg);
    let mut bound = HashMap::default();
    for id in a.new_defs() {
        let def = a.def(id);
        if def.item.is_none() {
            continue;
        }
        // A panic names this declaration (S-67).
        let _scope = onsa_diag::internal::item_scope(def.span);
        let m = def.module;
        let Some(module) = a.modules.source(&flat, m) else { continue };
        let Some((self_ty, body, ret)) = body_of(a, id) else { continue };
        let generics = generics_of(a, id);
        // The body of an item whose unit has a syntax error is not checked
        // (spec §18.1, S-59).
        if a.failed.contains_key(&id) {
            continue;
        }
        // Nor is a body whose unit failed in the names stage (§18.1, S-78: in
        // its signature too), or whose names walk stopped at an error it
        // reported (its record ends there).
        let mut names = a.names.remove(&id).unwrap_or_default();
        if names.reported || a.failures.skips(id, Stage::Types) {
            let body = BodyInfo::default();
            match a.def(id).kind {
                DefKind::Flow(_) => drop(a.flows.insert(id, crate::flow::FlowInfo { body, ..Default::default() })),
                _ => drop(a.bodies.insert(id, body)),
            }
            a.names.insert(id, names);
            continue;
        }
        // What the body reads and the check does not goes to `read_held` as
        // for a signature (`Analysis::unread_path`, `record_if_held`); it is
        // moved to the body below.
        let held = a.read_held.contains(&id);
        let (locals, origins) = locals_of(a, &names);
        let diverging = std::mem::take(&mut names.diverging);
        let mut info = BodyInfo { locals, diverging, ..Default::default() };
        info.captures = names.captures.iter().map(|(e, bs)| (*e, bs.iter().map(|b| LocalId(b.0)).collect())).collect();
        let typed = vec![false; info.locals.len()];
        let float_params =
            (0..).zip(&generics).filter(|(_, g)| bounds::param_holds(g, Bound::Float)).map(|(i, _)| i).collect();
        let mut ck = Checker {
            a,
            ast: &module.parsed.ast,
            text: &module.text,
            m,
            def: id,
            generics,
            self_ty,
            infer: Infer::new(float_params),
            frames: Vec::new(),
            blocks: Vec::new(),
            info,
            failed: false,
            bad_consts: Vec::new(),
            deferred: Vec::new(),
            deferred_seen: 0,
            deferred_generation: 0,
            deferred_end: Vec::new(),
            deferred_count: 0,
            why: None,
            arg_closure: None,
            flow: None,
            names,
            origins,
            typed,
            root: body,
            bound: &mut bound,
        };
        let is_const = matches!(ck.a.def(id).kind, DefKind::Const(_));
        let is_flow = matches!(ck.a.def(id).kind, DefKind::Flow(_));
        if is_const {
            ck.check_const(body, ret);
        } else if is_flow {
            ck.check_flow_body(body, ret);
        } else {
            ck.check_fn_body(body, ret);
        }
        let fcx = ck.flow.take();
        let names = std::mem::take(&mut ck.names);
        let mut info = ck.finish();
        if (!held && a.read_held.remove(&id)) || names.read_unread {
            info.read_unread = true;
        }
        a.names.insert(id, names);
        match fcx {
            Some(fcx) => crate::flow::finish_flow(a, module, id, info, fcx),
            None => {
                a.bodies.insert(id, info);
            }
        }
    }
}

/// The generic parameters a body sees: a function's own, those of the owner
/// of an associated `const` or of a default of a field; a test and a flow have
/// none.
pub(crate) fn generics_of(a: &Analysis, def: DefId) -> Vec<GenericDef> {
    let d = a.def(def);
    match &d.kind {
        DefKind::Fn(f) => f.generics.clone(),
        DefKind::Const(_) => d.owner.map(|o| a.def(o).generics().to_vec()).unwrap_or_default(),
        _ => Vec::new(),
    }
}

/// The expression of the body of a function, a test or a `const` (the bodies
/// the modes stage reads; not a flow's).
pub(crate) fn root_of(a: &Analysis, def: DefId) -> Option<ExprId> {
    match &a.def(def).kind {
        DefKind::Fn(f) => f.body,
        DefKind::Test { body, .. } => Some(*body),
        DefKind::Const(c) => c.value,
        _ => None,
    }
}

/// The local of each binding no pattern makes (a parameter, a `var`), by
/// its origin: the local of the binding `b` is `LocalId(b.0)`.
pub(crate) fn origins(names: &BodyNames) -> HashMap<Origin, LocalId> {
    (names.bindings.iter().enumerate())
        .filter(|(_, b)| b.sites.is_empty())
        .map(|(i, b)| (b.origin, LocalId(i as u32)))
        .collect()
}

/// The locals of a body, one for each binding of its record (`LocalId(b.0)`
/// for the binding `b`), with the error type until the check gives them
/// theirs and the state of the table of §5.4 with no head (owned, for a
/// binding of a head: settled after the check, [`crate::binding`]); and
/// their [`origins`].
fn locals_of(a: &mut Analysis, names: &BodyNames) -> (Vec<LocalInfo>, HashMap<Origin, LocalId>) {
    let error = a.types.error();
    let mut locals = Vec::new();
    for b in &names.bindings {
        let kind = LocalKind::of(b.kind);
        let (name, span, state) = (b.name.clone(), b.span, Bind::Owned);
        let mut l = LocalInfo { name, span, ty: error, kind, state };
        l.set_state(crate::binding::row(b.kind, None));
        locals.push(l);
    }
    (locals, origins(names))
}

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ helpers

    pub(crate) fn src(&self, span: Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    /// A diagnostic of the typing pass (stage `Types`).
    pub(crate) fn err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(Stage::Types, code, span, msg).with_found(self.src(span)))
    }

    /// A type that holds a struct or enum whose unit failed in the syntax
    /// stage (S-260): its fields and variants are not all known.
    fn mentions_failed(&self, t: TyId) -> bool {
        match self.ty(self.shallow(t)) {
            Ty::Named(d, args) => self.a.partly_read(d) || args.iter().any(|&a| self.mentions_failed(a)),
            Ty::Tuple(ts) | Ty::Builtin(_, ts) => ts.iter().any(|&a| self.mentions_failed(a)),
            Ty::Array(e, _) => self.mentions_failed(e),
            _ => false,
        }
    }

    /// A path that does not resolve: its diagnostic, or none when the path
    /// names what the check does not read (`Analysis::unread_path`: a member
    /// of a struct or enum whose unit failed in the syntax stage, or a name
    /// the names stage holds as an error, §18.1, S-462, S-675): in a value
    /// place, the check of this body stops there without a diagnostic, and
    /// the body is not complete (S-692).
    // SPEC-GAP(S-260): the members of a failed struct or enum get no diagnostic.
    pub(crate) fn resolve_error(&mut self, path: &onsa_syntax::ast::Path, err: ResolveError) -> Stop {
        if self.a.unread_path(self.def, self.m, path, &err) {
            self.failed = true;
            return Stop;
        }
        self.diag(err.into_diagnostic())
    }

    /// A name that does not resolve in a body: a diagnostic of the names
    /// stage (spec §18.1), so that it hides a type error of its unit (S-214).
    pub(crate) fn name_err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(Stage::Names, code, span, msg).with_found(self.src(span)))
    }

    /// E0200 for `feature` (S-224), with the details its phrase takes.
    pub(crate) fn unsupported(&mut self, span: Span, feature: Feature, details: &[&str]) -> Stop {
        self.unsupported_in(Stage::Types, span, feature, details)
    }

    /// E0200 for `feature` found by `stage`.
    pub(crate) fn unsupported_in(&mut self, stage: Stage, span: Span, feature: Feature, details: &[&str]) -> Stop {
        self.diag(feature.diagnostic(stage, span, details).with_found(self.src(span)))
    }

    /// E0200 for a range with its end (`a..=b`, S-224) in the head of a
    /// `for` (W8-03, the types stage) or a `par` (W7-04, the flow stage),
    /// once its ends are checked; it is never read as `a..<b` (R-81).
    pub(crate) fn closed_range_unsupported(&mut self, r: &RangeHead, stage: Stage, feature: Feature) -> Stop {
        let (lo, hi) = (self.expr(r.lo).span, self.expr(r.hi).span);
        self.unsupported_in(stage, Span::new(lo.file, lo.start, hi.end), feature, &[])
    }

    /// E0401 for an end of a range whose form is no integer, whatever its
    /// type is inferred to be (§7, S-257; [`Checker::non_integer_form`]).
    /// The `for` and the `par` heads both check it first.
    pub(crate) fn range_end_forms(&mut self, r: &RangeHead) -> R<()> {
        for e in [r.lo, r.hi] {
            if let Some(form) = self.non_integer_form(e) {
                let span = self.expr(e).span;
                let msg = format!("the ends of a range are integers; found {form} (§7)");
                return Err(self.err(Code::E0401, span, msg));
            }
        }
        Ok(())
    }

    /// The form of a value that is no integer in the operands of `e`
    /// (through parentheses, prefix and binary operators; a cast makes an
    /// integer): a float, string, character or `Bool` literal, a tuple, an
    /// array. The one check of the integer positions that are read before
    /// their type is inferred (the ends of a range, the constants of a
    /// flow), so that a message names the form, not a type variable (`?0`).
    pub(crate) fn non_integer_form(&self, e: ExprId) -> Option<&'static str> {
        match &self.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::Unary { expr: x, .. } => self.non_integer_form(*x),
            ExprKind::Binary { lhs, rhs, .. } => self.non_integer_form(*lhs).or_else(|| self.non_integer_form(*rhs)),
            ExprKind::Lit(Lit::Float { .. }) => Some("a float literal"),
            ExprKind::Lit(Lit::Str(_)) => Some("a string literal"),
            ExprKind::Lit(Lit::Char(_)) => Some("a character literal"),
            ExprKind::Lit(Lit::Bool(_)) => Some("a `Bool` literal"),
            ExprKind::Tuple(_) => Some("a tuple"),
            ExprKind::Array(_) | ExprKind::Repeat { .. } => Some("an array"),
            _ => None,
        }
    }

    /// A diagnostic of the flow checks (`flow.rs`, stage `Flow`).
    pub(crate) fn flow_err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(Stage::Flow, code, span, msg).with_found(self.src(span)))
    }

    pub(crate) fn diag(&mut self, d: Diagnostic) -> Stop {
        if !self.failed {
            self.failed = true;
            self.a.diagnostics.push(d);
        }
        Stop
    }

    pub(crate) fn ty(&self, t: TyId) -> Ty {
        self.a.types.get(t).clone()
    }

    pub(crate) fn shallow(&self, t: TyId) -> TyId {
        self.infer.shallow(&self.a.types, t)
    }

    pub(crate) fn display(&mut self, t: TyId) -> String {
        let r = self.infer.resolve(&mut self.a.types, t);
        let names: Vec<String> = self.generics.iter().map(|g| g.name.clone()).collect();
        // A variable left open: its literal kind, else a hole (R-353; no internal `?N`).
        let var_name = |i: u32| self.infer.var_lit(i).map_or("_", LitKind::braced).to_string();
        self.a.types.display_vars(
            r,
            &|d| self.a.def(d).name.clone(),
            &|i| names.get(i as usize).cloned().unwrap_or_else(|| format!("<{i}>")),
            &var_name,
        )
    }

    pub(crate) fn unit(&mut self) -> TyId {
        self.a.types.unit()
    }

    pub(crate) fn bool_(&mut self) -> TyId {
        self.a.types.bool()
    }

    pub(crate) fn u32(&mut self) -> TyId {
        self.a.types.int(IntKind::U32)
    }

    pub(crate) fn fresh(&mut self) -> TyId {
        self.infer.fresh(&mut self.a.types, None)
    }

    pub(crate) fn record(&mut self, e: ExprId, t: TyId) -> TyId {
        self.info.expr_types.insert(e, t);
        t
    }

    pub(crate) fn expr(&self, e: ExprId) -> &'a Expr {
        self.ast.expr(e)
    }

    /// Unify, reporting E0401 at `span` on failure.
    pub(crate) fn unify_at(&mut self, span: Span, actual: TyId, expected: TyId) -> R<()> {
        match self.mismatch_at(span, actual, expected) {
            Some(d) => Err(self.diag(d)),
            None => Ok(()),
        }
    }

    /// Unify, giving the E0401 at `span` on failure, for the caller to report.
    pub(crate) fn mismatch_at(&mut self, span: Span, actual: TyId, expected: TyId) -> Option<Diagnostic> {
        let cause = self.cause(span, Some(expected));
        let Err(mismatch) = self.infer.unify(&mut self.a.types, actual, expected, &cause) else {
            return None;
        };
        let (a, e) = (self.display(actual), self.display(expected));
        let (found, wanted) = (self.infer.lit_of(&self.a.types, actual), self.infer.lit_of(&self.a.types, expected));
        let text = match (mismatch, found, wanted) {
            (Mismatch::Literal, Some(k), _) => format!("{} literal cannot have type `{e}`", k.words()),
            (Mismatch::Literal, None, Some(k)) => format!("expected {}, found `{a}`", k.words()),
            // A literal in a part of the types (`fn({integer})`): neither is one.
            _ => format!("expected `{e}`, found `{a}`"),
        };
        let d = Diagnostic::new(Stage::Types, Code::E0401, span, text).with_found(self.src(span));
        // The other side of a float literal (§6.6, S-881).
        let other = match (found, wanted) {
            (Some(LitKind::Float), _) => expected,
            (None, Some(LitKind::Float)) => actual,
            _ => return Some(d),
        };
        let other = self.shallow(other);
        Some(match self.ty(other) {
            Ty::Param(_) => {
                let t = self.display(other);
                d.with_rule(format!(
                    "a float literal is a value of `{t}` only when the bounds of `{t}` include `Float` (§6.6)"
                ))
            }
            _ => d,
        })
    }

    /// The cause of a binding made while unifying at `span` with `expected`.
    pub(crate) fn cause(&self, span: Span, expected: Option<TyId>) -> Cause {
        let why = match (&self.why, expected) {
            (Some((w, t)), Some(e)) if *t == e => Some(w.clone()),
            _ => None,
        };
        Cause::At { span, why }
    }

    /// Check with `why` naming where the expected type `expected` comes from.
    pub(crate) fn with_why<T>(&mut self, why: String, expected: TyId, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let outer = self.why.replace((why, expected));
        let r = f(self);
        self.why = outer;
        r
    }

    /// Check without a reason: a statement, or a branch merged with another one.
    pub(crate) fn without_why<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let outer = self.why.take();
        let r = f(self);
        self.why = outer;
        r
    }

    /// E0420: the operand's type must be known at this point (§4.7).
    pub(crate) fn known(&mut self, t: TyId, span: Span, what: &str) -> R<TyId> {
        let s = self.shallow(t);
        if matches!(self.ty(s), Ty::Var(_)) {
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Types,
                    Code::E0420,
                    span,
                    format!("the type of this {what} must be known here; add an annotation (§4.7)"),
                )
                .with_found(self.src(span)),
            ));
        }
        Ok(s)
    }

    /// [`Checker::known`] for an operation whose answer the kind of a literal variable
    /// already decides (a function value called, `.x`, `.0`, `[i]`, the operand of `?`;
    /// S-854): such a variable passes, and the operation reports the error of an
    /// annotated type, named by [`Checker::described`].
    pub(crate) fn known_shape(&mut self, t: TyId, span: Span, what: &str) -> R<TyId> {
        let s = self.shallow(t);
        if self.infer.lit_of(&self.a.types, s).is_some() { Ok(s) } else { self.known(t, span, what) }
    }

    /// A type in the words of a diagnostic: `` `F32` ``, or `an integer` / `a float` for a
    /// literal variable (S-854: the value may be a binding, so not "literal").
    pub(crate) fn described(&mut self, t: TyId) -> String {
        match self.infer.lit_of(&self.a.types, t) {
            Some(k) => k.words().into(),
            None => format!("`{}`", self.display(t)),
        }
    }

    // ------------------------------------------------------------ locals

    /// The local of the binding `origin` names (one no pattern makes).
    pub(crate) fn local_of(&mut self, origin: Origin) -> R<LocalId> {
        match self.origins.get(&origin) {
            Some(&id) => Ok(id),
            // After the name that stopped the walk (§18.1, S-692).
            None => Err(self.held_stop()),
        }
    }

    /// The local the pattern `pat` binds.
    pub(crate) fn local_of_pat(&mut self, pat: PatId) -> R<LocalId> {
        match self.names.pats.get(&pat) {
            Some(PatRes::Bind(b)) => Ok(LocalId(b.0)),
            _ => Err(self.held_stop()),
        }
    }

    /// Give the local `id` its type at `span`, or, when a branch of a choice
    /// before this one gave it one, unify with it (§7).
    pub(crate) fn bind_local(&mut self, id: LocalId, ty: TyId, span: Span) -> R<()> {
        let i = id.0 as usize;
        if std::mem::replace(&mut self.typed[i], true) {
            let lt = self.info.locals[i].ty;
            return self.unify_at(span, ty, lt);
        }
        self.info.locals[i].ty = ty;
        Ok(())
    }

    /// Whether the chain of names `e` ends at (`a.b.c`) starts at a local, by
    /// the record of its head.
    pub(crate) fn of_a_local(&self, e: ExprId) -> bool {
        starts_at_local(self.ast, &self.names, e)
    }

    pub(crate) fn local_ty(&self, id: LocalId) -> TyId {
        self.info.locals[id.0 as usize].ty
    }
}

impl<'a> Checker<'a> {
    pub(crate) fn body_type(&self, e: ExprId) -> Option<TyId> {
        self.info.expr_types.get(&e).copied()
    }

    pub(crate) fn target_of(&self, e: ExprId) -> Option<Target> {
        self.info.targets.get(&e).cloned()
    }
}

/// Whether the chain of names `e` ends at (`a.b.c`) of the body of `ast`
/// starts at a local, by the record of its head in `names`.
pub(crate) fn starts_at_local(ast: &Ast, names: &crate::names::body::BodyNames, e: ExprId) -> bool {
    let mut cur = e;
    while let ExprKind::Field { base, .. } = &ast.expr(cur).kind {
        cur = *base;
    }
    matches!(names.paths.get(&cur), Some(PathRes::Local(_)))
}

/// The E0714 of `!` on a call of no `inout self` method (§5.2), wherever it
/// stands: the types stage's, the flow stage's and the modes stage's.
pub(crate) const BANG_ON_NO_INOUT_SELF: &str = "`!` marks `inout self` method calls only (§5.2)";

/// The base of `e` when `e` is a partial view of it (S-217: `xs.slice(a, b)`):
/// a call of a method of std whose type, as `ty` reads it, is a `Span` (std
/// alone returns one, S-861), known by that and not by its name (Q-14). The
/// one rule of the typing (`inout`, S-178) and of the states of the bindings
/// (§5.4).
pub(crate) fn view_base(
    (ast, info, a): (&Ast, &BodyInfo, &Analysis),
    e: ExprId,
    ty: impl Fn(TyId) -> TyId,
) -> Option<ExprId> {
    let ExprKind::Call { callee, .. } = &ast.expr(e).kind else { return None };
    let ExprKind::Field { base, .. } = &ast.expr(*callee).kind else { return None };
    let span = info.expr_types.get(&e).is_some_and(|&t| matches!(a.types.get(ty(t)), Ty::Builtin(BuiltinTy::Span, _)));
    let std = matches!(info.targets.get(&e), Some(Target::Method { def, .. }) if a.modules.is_std(a.def(*def).module));
    (span && std).then_some(*base)
}

/// E0401 for the struct literal whose path `shown` at `span` names a type
/// that is no struct (`I32 { x: 1 }`, a type parameter `T { x: 1 }`; the form
/// in a kind, not E0308, §15.1, S-713).
pub(crate) fn not_a_struct(shown: String, span: Span) -> Diagnostic {
    let msg = format!("`{shown}` is not a struct");
    Diagnostic::new(Stage::Types, Code::E0401, span, msg).with_found(shown)
}
