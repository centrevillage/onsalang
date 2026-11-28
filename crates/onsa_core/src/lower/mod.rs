//! Lowering (T3-3) and monomorphization (T3-4): from the typed AST of
//! `onsa_sema` to Core. Entry: [`lower`].
//!
//! Roots are every non-generic function, method, `test` and `const` of the
//! user package. Generic functions are instantiated on demand from the
//! `Instance` tables of the bodies that call them, deduplicated by
//! `(def, generic args)` and named `name__F32` / `sum__F32__4`. Types are
//! instantiated the same way (`Ring__F32__4`); `Option[T]` / `Result[T, E]`
//! become ordinary enums (`Option__F32`).
//!
//! Flows are lowered by [`flow`] (T3-5): every flow of the user package is a
//! root, and a flow is also lowered on demand when a body refers to one of
//! its members (`voice.init`, `voice.State`).
//!
//! Unsupported features (E0200, S-67): lowering reports every one, not only
//! the first of an item. The innermost expression (or `match` arm pattern)
//! that uses one becomes a placeholder, and the item is lowered again
//! ([`Lowerer::lower_item`]). A type lowering does not lower (§18.1) is no
//! placeholder: it stops its unit (a function's instance, a `test`, a
//! constant, a flow) with one E0200 for each unsupported part, at the first
//! binding of it ([`Lowerer::bind_tys`]) or at the first expression of it,
//! and no other E0200 of the unit; a unit that relies on a stopped constant
//! or flow by an expression goes on with that expression a placeholder and
//! no report, and a flow that makes an instance of a stopped flow stops with
//! none. The limits (W8-01 takes them over):
//! - A feature outside an expression and an arm pattern (a `let` pattern, a
//!   `const` initializer with bindings) stops its item: the rest of that item
//!   is not reported.
//! - A generic function lowered for several types reports an expression
//!   once: the later instances find it a placeholder already, so another
//!   unsupported feature at the same expression of a later instance is not
//!   reported.

mod body;
mod build;
mod derived;
mod eq;
mod fixed_str;
pub mod flow;
pub mod fold;
mod limits;
pub mod moves;
mod storage;
mod types;

use std::collections::{HashMap, HashSet};

use onsa_diag::unsupported::Feature;
use onsa_diag::{Diagnostic, Span, Stage};
use onsa_sema::def::{DefKind, DerivedFn, GenericKind};
use onsa_sema::ty::{BuiltinTy, Len, Measure, Ty as STy, TyId};
use onsa_sema::{Analysis, DefId, ModId, Package};
use onsa_syntax::ast::{ExprId, PatId};

use crate::ir::*;

/// A generic argument after monomorphization.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(CTy),
    Const(u32),
}

/// Why lowering of an item stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FailKind {
    /// The program uses a feature this version does not lower (E0200, Q-09).
    Unsupported,
    /// A type of a feature this version does not lower (E0200), with its
    /// report ([`types::BadTy::fail`]): no placeholder, it stops the unit.
    UnsupportedType(types::BadTy),
    /// The unit relies on one a type stopped, which reported it ([`stopped`]).
    Stopped,
    /// Lowering reached a state it cannot be in: an internal error (S-67),
    /// never a diagnostic.
    Internal,
    /// An instance over a limit (§4.4 E0422, §4.5 E0423): lowering stops, and
    /// this is the one diagnostic (§18.1).
    Limit,
    /// A field of a type met an instance not made yet (`types`): inside the
    /// maker of the types only, and an internal error out of it.
    Pending,
}

/// Where an unsupported feature was found: an expression, or the pattern
/// of a `match` arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Hole {
    Expr(ModId, ExprId),
    Pat(ModId, PatId),
}

pub(crate) struct Fail {
    pub kind: FailKind,
    pub span: Span,
    pub msg: String,
    /// The innermost expression whose lowering failed (unsupported features
    /// only): the next attempt lowers it as a placeholder and goes on.
    pub hole: Option<Hole>,
    /// The E0200 of an unsupported feature, made by the list of what this
    /// version does not support (`onsa_diag::unsupported`, S-224).
    pub report: Option<Box<Diagnostic>>,
}

pub(crate) type R<T> = Result<T, Fail>;

/// An unsupported feature at `span` (E0200), with the details its phrase
/// takes (`onsa_diag::unsupported`).
pub(crate) fn unsupported(span: Span, feature: Feature, details: &[&str]) -> Fail {
    gated(feature.diagnostic(Stage::Build, span, details))
}

/// The unsupported feature of the E0200 `d`.
pub(crate) fn gated(d: Diagnostic) -> Fail {
    Fail { kind: FailKind::Unsupported, span: d.span, msg: d.message.clone(), hole: None, report: Some(Box::new(d)) }
}

/// The unit at `span` relies on one a type stopped: the one way to a
/// [`FailKind::Stopped`], which has no report (the stopped one has it).
pub(crate) fn stopped(span: Span) -> Fail {
    Fail { kind: FailKind::Stopped, ..internal(span, "a unit stopped by a type, out of lowering") }
}

/// Why [`lower`] produced no Core.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerFailure {
    /// The diagnostics of lowering, in the order found: every unsupported
    /// feature the program uses (E0200), and every recursion of the `rt`
    /// functions that the instances close (E0903, `rt_cycles`); or the one
    /// limit passed (`limits`), alone. The driver removes the duplicates
    /// and orders them (S-67).
    Diagnostics(Vec<Diagnostic>),
    /// An internal error (S-67): the command stops. `span` is the source
    /// lowering was at.
    Internal { span: Span, message: String },
    /// The verifier rejected the Core lowering made (R-82): an internal
    /// error, with the item's Core (`dump_item`) for the bug report.
    Verify { error: crate::VerifyError, item_core: String },
}

/// Whether `outer` holds `inner` (the same file).
fn contains(outer: Span, inner: Span) -> bool {
    outer.file == inner.file && outer.start <= inner.start && inner.end <= outer.end
}

/// Attach the hole `h` to an unsupported feature, or a use of a stopped
/// constant or flow, that has none yet (the innermost expression or pattern
/// whose lowering failed).
pub(crate) fn at_hole(mut f: Fail, h: Hole) -> Fail {
    if matches!(f.kind, FailKind::Unsupported | FailKind::Stopped) && f.hole.is_none() {
        f.hole = Some(h);
    }
    f
}

/// A constant (of `const_ids`) or a flow (of `flow_fns`) a type stopped.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Stop {
    Const(DefId, Vec<GenericArg>),
    Flow(DefId),
}

pub(crate) struct Lowerer<'a> {
    pub pkg: &'a Package,
    pub a: &'a Analysis,
    pub m: Module,
    fn_ids: HashMap<(DefId, Vec<GenericArg>), FnId>,
    worklist: Vec<(DefId, Vec<GenericArg>, FnId)>,
    type_ids: HashMap<(DefId, Vec<GenericArg>), TypeId>,
    /// The reverse of `type_ids`: the state type of a flow has no row.
    type_defs: HashMap<TypeId, (DefId, Vec<GenericArg>)>,
    const_ids: HashMap<(DefId, Vec<GenericArg>), ConstId>,
    /// The measure (§4.4) of each instance of a type with arguments.
    type_measures: HashMap<TypeId, Measure>,
    /// The measure of each type of `m.tys`, by id, filled up to the one read
    /// ([`Lowerer::measure`]).
    measures: Vec<Measure>,
    /// The instances §4.5 counts so far, and [`LowerOptions::instance_limit`].
    instances: u32,
    instance_limit: u32,
    /// Of each function of `fn_ids`, the call that made it and the function
    /// that call is in: the path of an E0422.
    made_by: HashMap<FnId, (Span, Option<FnId>)>,
    /// The function of the worklist being lowered.
    lowering: Option<FnId>,
    /// The instances of types being filled, the innermost last (`types`).
    fills: Vec<types::Fill>,
    /// The instances of types lowering does not lower (`types`).
    bad_types: HashMap<TypeId, types::BadTy>,
    /// The constants and flows a type stopped, reported once (S-67).
    stopped: HashSet<Stop>,
    pub(crate) eq_fns: HashMap<CTy, FnId>,
    messages: HashMap<String, MsgId>,
    pub(crate) flow_fns: HashMap<DefId, flow::FlowFns>,
    /// The empty `Config` and `Params` of the flows with none ([`Lowerer::flow_ty`]).
    implicit_tys: HashMap<(DefId, onsa_sema::def::FlowTy), TypeId>,
    pub(crate) flows_in_progress: HashSet<DefId>,
    /// Of the flows being lowered, the innermost last ([`flow::HoistUses`]).
    pub(crate) hoist_uses: Vec<flow::HoistUses>,
    /// [`LowerOptions::bulk_threshold`]; `None`: everything fast.
    pub bulk_threshold: Option<u32>,
    /// Expressions and arm patterns that use an unsupported feature:
    /// lowered as placeholders, so that lowering goes on to the next one (S-67).
    pub(crate) holes: HashSet<Hole>,
    /// The E0200s of the forms the attempts of the item being lowered found:
    /// reported when it ends, unless a type stops the unit they are in.
    attempts: Vec<Diagnostic>,
    /// The attempts of one item: one more than the holes there can be (every
    /// expression and pattern of every module), so it is never reached while
    /// each attempt finds a new hole.
    max_attempts: usize,
    /// E0200 for every unsupported feature found (S-67).
    unsupported: Vec<Diagnostic>,
}

/// Options of a lowering.
#[derive(Debug, Clone)]
pub struct LowerOptions {
    /// Arrays of at least this many bytes in a flow state go to the bulk region (§12.4).
    /// No key of the manifest sets it: `onsa build` passes `None`, the tests
    /// of Core set it, and `memory.bulk` replaces it (W9-06).
    pub bulk_threshold: Option<u32>,
    /// Pointer width of the target in bytes (8 on the reference host).
    pub ptr_size: u32,
    /// The instances a package may have: [`limits::INSTANCE_LIMIT`]. No key
    /// of the manifest sets it: the tests of Core count with a small one.
    pub instance_limit: u32,
}

impl Default for LowerOptions {
    fn default() -> Self {
        let instance_limit = limits::INSTANCE_LIMIT;
        LowerOptions { bulk_threshold: None, ptr_size: crate::layout::PTR_SIZE, instance_limit }
    }
}

/// Lower the user package (and what it reaches in `std`) to Core.
pub fn lower(pkg: &Package, a: &Analysis) -> Result<Module, LowerFailure> {
    lower_with(pkg, a, &LowerOptions::default())
}

/// [`lower`] with options (the target's pointer width, `bulk_threshold`).
///
/// Lowering does not stop at the first unsupported feature of an item
/// (S-67): the innermost expression that uses it becomes a placeholder and
/// the item is lowered again (see the module's documentation). The Core is
/// then dropped, so no placeholder leaves this function. The first internal
/// failure stops lowering, and so does a Core too deep (V-22), before the
/// passes that recurse. A Core that comes out is verified ([`verified`]).
pub fn lower_with(pkg: &Package, a: &Analysis, opts: &LowerOptions) -> Result<Module, LowerFailure> {
    let flat = onsa_sema::flatten(pkg);
    let places: usize =
        flat.iter().flat_map(|p| p.modules.iter()).map(|m| m.parsed.ast.exprs.len() + m.parsed.ast.pats.len()).sum();
    let mut lw = Lowerer::new(pkg, a, opts, places);
    // Roots: non-generic items of the user package, in definition order.
    for (i, def) in a.defs.iter().enumerate() {
        let id = DefId(i as u32);
        if !a.modules.is_own(def.module) {
            continue;
        }
        match &def.kind {
            DefKind::Fn(f) if f.body.is_some() && lw.all_generics(id).is_empty() => {
                lw.lower_item(def.span, |lw| lw.fn_id(id, Vec::new(), def.span).map(drop))?
            }
            DefKind::Test { .. } => lw.lower_item(def.span, |lw| lw.fn_id(id, Vec::new(), def.span).map(drop))?,
            DefKind::Flow(_) => lw.lower_item(def.span, |lw| lw.ensure_flow(id).map(drop))?,
            // A value of an attribute is read by what it describes (`ParamInfo`).
            DefKind::Const(c)
                if c.value.is_some()
                    && c.of_attr.is_none()
                    && def.owner.is_none_or(|o| a.def(o).generics().is_empty()) =>
            {
                lw.lower_item(def.span, |lw| lw.const_id(id, Vec::new(), def.span).map(drop))?
            }
            _ => {}
        }
    }
    while let Some((def, args, fid)) = lw.worklist.pop() {
        let span = a.def(def).span;
        lw.lowering = Some(fid);
        lw.lower_item(span, |lw| lw.lower_fn(def, &args, fid))?;
    }
    let mut diagnostics = std::mem::take(&mut lw.unsupported);
    // V-22 before the walks, which recurse: of a Core too deep, the E0200s
    // if any (a Core with placeholders is dropped anyway).
    let deep = crate::verify::depth::module(&lw.m);
    if deep.is_ok() {
        // A placeholder is no call: what an E0200 hides is no edge of a cycle (S-911).
        diagnostics.extend(crate::rt_cycles::rt_cycles(&lw.m, a, &flat));
    }
    if !diagnostics.is_empty() {
        return Err(LowerFailure::Diagnostics(diagnostics));
    }
    deep.map_err(|e| verify_failure(&lw.m, e))?;
    finish(lw.m)
}

/// The passes after the items are lowered, in their one order, and the
/// verifier last: it reads what they make (`hoisted`, V-18; `moves`, V-20).
fn finish(mut module: Module) -> Result<Module, LowerFailure> {
    // No type is made after lowering: what reads the module reads the facts.
    module.fill_all_facts();
    // The comparisons the types decide and the assignments of a place to
    // itself (S-288), before the copies are counted.
    fold::fold_module(&mut module);
    // The indexes proved in range, on the Core folded (§9.2); its own phase.
    {
        let _bounds = onsa_diag::timing::phase(onsa_diag::timing::Phase::Bounds);
        crate::bounds::module(&mut module);
    }
    // After the fold, which may drop a loop that never runs with its `let`s.
    for i in 0..module.fns.len() {
        module.fns[i].hoisted = storage::hoisted(&module, &module.fns[i]);
    }
    module.moves = moves::collect(&module);
    verified(module)
}

/// The stage verifies its own output (R-82), so no caller of [`lower`]
/// gets a Core the verifier has not seen, in release builds too. Its own
/// phase, not counted in the lowering's.
pub(crate) fn verified(module: Module) -> Result<Module, LowerFailure> {
    let _verify = onsa_diag::timing::phase(onsa_diag::timing::Phase::Verify);
    match crate::verify::verify(&module) {
        Ok(()) => Ok(module),
        Err(e) => Err(verify_failure(&module, e)),
    }
}

/// The failure `e` of the verifier on `m`, with the Core of its item (R-82).
fn verify_failure(m: &Module, e: crate::VerifyError) -> LowerFailure {
    let (error, item_core) = crate::verify::failure(m, e);
    LowerFailure::Verify { error, item_core }
}

impl<'a> Lowerer<'a> {
    /// A lowering of `pkg` of the analysis `a` with nothing lowered yet, of
    /// `places` expressions and patterns in all its modules ([`lower_with`]).
    fn new(pkg: &'a Package, a: &'a Analysis, opts: &LowerOptions, places: usize) -> Lowerer<'a> {
        Lowerer {
            pkg,
            a,
            m: Module { facts: crate::layout::Facts::new(opts.ptr_size), ..Module::default() },
            fn_ids: HashMap::new(),
            worklist: Vec::new(),
            type_ids: HashMap::new(),
            type_defs: HashMap::new(),
            const_ids: HashMap::new(),
            type_measures: HashMap::new(),
            measures: Vec::new(),
            instances: 0,
            instance_limit: opts.instance_limit,
            made_by: HashMap::new(),
            lowering: None,
            fills: Vec::new(),
            bad_types: HashMap::new(),
            stopped: HashSet::new(),
            eq_fns: HashMap::new(),
            messages: HashMap::new(),
            flow_fns: HashMap::new(),
            implicit_tys: HashMap::new(),
            flows_in_progress: HashSet::new(),
            hoist_uses: Vec::new(),
            bulk_threshold: opts.bulk_threshold,
            holes: HashSet::new(),
            attempts: Vec::new(),
            max_attempts: places + 1,
            unsupported: Vec::new(),
        }
    }

    /// Lower one item (a function, a flow, a `const`) by `attempt`, again
    /// after each unsupported feature found in an expression or an arm
    /// pattern (S-67). `Err` is an internal error, which stops lowering.
    ///
    /// A unit that a type stops reports that E0200 alone (§18.1): the E0200s
    /// its attempts found in it are dropped ([`Self::stop`]). An internal
    /// failure is an internal error, whatever placeholders the attempt has.
    fn lower_item(&mut self, span: Span, mut attempt: impl FnMut(&mut Self) -> R<()>) -> Result<(), LowerFailure> {
        // A panic names this item (S-67).
        let _scope = onsa_diag::internal::item_scope(span);
        for left in (0..self.max_attempts).rev() {
            let Err(fail) = attempt(self) else { break };
            match fail.kind {
                FailKind::Internal | FailKind::Pending => {
                    return Err(LowerFailure::Internal { span: fail.span, message: fail.msg });
                }
                FailKind::Limit => {
                    let Some(d) = fail.report else {
                        return Err(LowerFailure::Internal { span: fail.span, message: fail.msg });
                    };
                    return Err(LowerFailure::Diagnostics(vec![*d]));
                }
                // No hole: it stopped itself, or by a constant or flow it relied
                // on not in an expression.
                FailKind::UnsupportedType(_) | FailKind::Stopped if fail.hole.is_none() => {
                    self.stop(fail, span);
                    break;
                }
                FailKind::Unsupported | FailKind::UnsupportedType(_) | FailKind::Stopped => {
                    match fail.report {
                        Some(d) => self.attempts.push(*d),
                        None if fail.kind == FailKind::Stopped => {}
                        None => {
                            return Err(LowerFailure::Internal {
                                span: fail.span,
                                message: format!("an unsupported feature without its diagnostic: {}", fail.msg),
                            });
                        }
                    }
                    match fail.hole {
                        Some(h) if self.holes.insert(h) => {}
                        _ => break,
                    }
                }
            }
            // A safety bound, not reached while every attempt finds a new hole.
            if left == 0
                && let Some(last) = self.attempts.last_mut()
            {
                let note = "this item may use more unsupported features that were not reported";
                last.notes.push(onsa_diag::Note::at(last.span, note));
            }
        }
        self.unsupported.append(&mut self.attempts);
        Ok(())
    }

    /// A unit declared at `within` that a type stops (S-67): the E0200s its
    /// attempts found in it are dropped (of a constant or a flow, from the
    /// attempts of the item that lowers it), then the E0200 of that type, if
    /// `f` is one (a unit it relied on reported its own), and the
    /// [`FailKind::Stopped`]. Its placeholders stay: no unit lowers it again
    /// (`fn_ids`, `stopped`), and its other instances stop at the same type,
    /// as a type that differs among them stops the unit that makes them.
    fn stop(&mut self, f: Fail, within: Span) -> Fail {
        self.attempts.retain(|d| !contains(within, d.span));
        if let Some(d) = f.report {
            self.unsupported.push(*d);
        }
        stopped(f.span)
    }

    /// `f` of the unit `key` declared at `within`: a type that stops it
    /// ([`Self::stop`]) is recorded, so that a later use finds it stopped and
    /// reports nothing.
    fn stop_unit(&mut self, key: Stop, within: Span, f: Fail) -> Fail {
        if f.hole.is_some() || !matches!(f.kind, FailKind::UnsupportedType(_) | FailKind::Stopped) {
            return f;
        }
        self.stopped.insert(key);
        self.stop(f, within)
    }

    pub(crate) fn msg(&mut self, text: &str) -> MsgId {
        if let Some(&id) = self.messages.get(text) {
            return id;
        }
        let id = MsgId(self.m.messages.len() as u32);
        self.m.messages.push(text.to_string());
        self.messages.insert(text.to_string(), id);
        id
    }

    /// Generic parameters of a def. Methods already list their impl's
    /// generics first (`sig.rs` lowers them that way).
    pub(crate) fn all_generics(&self, id: DefId) -> Vec<GenericKind> {
        self.a.def(id).generics().iter().map(|g| g.kind.clone()).collect()
    }

    /// The def is of a dependency, not of the user's package: its qualified
    /// name starts with its package's name. A place; the privileges of std
    /// read the role (`Modules::is_std`).
    fn is_dep_def(&self, id: DefId) -> bool {
        !self.a.modules.is_own(self.a.def(id).module)
    }

    /// `dsp.voice.wrap01`, `std.math.exp`, `methods.Point.new`, `voice.voice.init`.
    pub(crate) fn qual_name(&self, id: DefId) -> String {
        let def = self.a.def(id);
        let mut parts = Vec::new();
        let info = self.a.modules.get(def.module);
        if self.is_dep_def(id) {
            parts.push(self.a.modules.names[info.pkg].clone());
        }
        if !info.path.is_empty() {
            parts.push(info.path.clone());
        }
        parts.extend(def.owner.map(|o| self.a.owner_name(o)));
        match &def.kind {
            // `test dsp.voice "decays"`: the full name text (§11.8) after
            // `test `, so that the tests of two modules, and a test and a
            // function `test.decays`, never share a name (W2-10/b). The name
            // decides nothing: `onsa test` runs the functions with a mark.
            DefKind::Test { name, .. } => {
                let module = info.path.clone();
                format!("test {}", TestMark { module, name: name.clone() }.full_name())
            }
            _ => {
                parts.push(def.name.clone());
                // A default has the name of its field, which a member of the
                // type may have too (`Voice.count`, `fn count(self)`).
                let of_struct = def.owner.is_some_and(|o| matches!(self.a.def(o).kind, DefKind::Struct(_)));
                if of_struct && matches!(def.kind, DefKind::Const(_)) {
                    parts.push(DerivedFn::Default.name().to_string());
                }
                parts.join(".")
            }
        }
    }

    pub(crate) fn mangle(&self, t: CTy) -> String {
        match self.m.tys.kind(t) {
            TyKind::Int(k) => k.name().to_string(),
            TyKind::Float(k) => k.name().to_string(),
            TyKind::Bool => "Bool".into(),
            TyKind::Char => "Char".into(),
            TyKind::Unit => "Unit".into(),
            TyKind::Array(e, n) => format!("A{n}_{}", self.mangle(*e)),
            TyKind::Tuple(ts) => {
                format!("T{}_{}", ts.len(), ts.iter().map(|&t| self.mangle(t)).collect::<Vec<_>>().join("_"))
            }
            TyKind::Struct(id) | TyKind::Enum(id) => self.m.ty(*id).name.replace('.', "_"),
            TyKind::Span(e) => format!("Span_{}", self.mangle(*e)),
            TyKind::Buf(e) => format!("Buf_{}", self.mangle(*e)),
            TyKind::FnPtr(_) => "Fn".into(),
        }
    }

    fn mangle_args(&self, args: &[GenericArg]) -> String {
        args.iter()
            .map(|a| match a {
                GenericArg::Ty(t) => format!("__{}", self.mangle(*t)),
                GenericArg::Const(n) => format!("__{n}"),
            })
            .collect()
    }

    // ------------------------------------------------------------ types

    /// Convert a sema type under the generic arguments of the enclosing instance.
    pub(crate) fn core_ty(&mut self, t: TyId, args: &[GenericArg], span: Span) -> R<CTy> {
        self.measured_ty(t, args, span).map(|(ty, _)| ty)
    }

    /// [`Self::core_ty`] and the measure of the type, judged at each part
    /// of a form (`limits`), so that a wide form stops at the limit.
    fn measured_ty(&mut self, t: TyId, args: &[GenericArg], span: Span) -> R<(CTy, Measure)> {
        let a = self.a;
        // A form is made with its parts `()`, then each converted in its
        // place. A scalar is a leaf, at its fixed id.
        let fn_parts: Vec<TyId>;
        let (mut ty, parts): (TyKind, &[TyId]) = match a.types.get(t) {
            STy::Int(k) => return Ok((Types::int(*k), Measure::LEAF)),
            STy::Float(k) => return Ok((Types::float(*k), Measure::LEAF)),
            STy::Bool => return Ok((Types::BOOL, Measure::LEAF)),
            STy::Char => return Ok((Types::CHAR, Measure::LEAF)),
            STy::Unit => (TyKind::Unit, &[]),
            STy::Array(e, len) => {
                let n = match *len {
                    Len::Const(n) => n,
                    Len::Param(i) => match args.get(i as usize) {
                        Some(GenericArg::Const(n)) => *n,
                        _ => return Err(internal(span, "unbound const parameter")),
                    },
                    Len::Var(_) => return Err(internal(span, "unresolved array length")),
                };
                (TyKind::Array(Types::UNIT, n), std::slice::from_ref(e))
            }
            STy::Tuple(ts) => (TyKind::Tuple(vec![Types::UNIT; ts.len()].into()), ts),
            STy::Named(d, targs) => {
                let def = a.def(*d);
                let is_struct = match &def.kind {
                    DefKind::Alias(inner) => return self.measured_ty(*inner, args, span),
                    DefKind::Struct(_) => true,
                    DefKind::Enum(_) => false,
                    _ => return Err(internal(span, "type refers to a non-type def")),
                };
                let gargs = self.generic_args(targs, args, span)?;
                let id = self.named_ty(*d, gargs, span)?;
                let ty = self.ty(if is_struct { TyKind::Struct(id) } else { TyKind::Enum(id) });
                return Ok((ty, self.type_measure(id)));
            }
            STy::Builtin(b, targs) => match b {
                BuiltinTy::Span => (TyKind::Span(Types::UNIT), &targs[..1]),
                BuiltinTy::Buf => (TyKind::Buf(Types::UNIT), &targs[..1]),
                BuiltinTy::Ptr => return Err(self.bad_type(span, Feature::Ptr, None)),
                BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set => {
                    return Err(self.bad_type(span, Feature::SharedTypes, Some(b.name())));
                }
            },
            STy::Fn(f) => {
                fn_parts = f.params.iter().map(|&(_, t)| t).chain([f.ret]).collect();
                let params = f.params.iter().map(|(mode, _)| (core_mode(*mode), Types::UNIT)).collect();
                (TyKind::FnPtr(Box::new(FnSig { rt: f.rt, params, ret: Types::UNIT })), &fn_parts)
            }
            STy::Param(i) => match args.get(*i as usize) {
                Some(&GenericArg::Ty(t)) => return Ok((t, self.measure(t))),
                _ => return Err(internal(span, "unbound type parameter")),
            },
            STy::ConstVal(_) => return Err(internal(span, "const argument in type position")),
            STy::Var(_) | STy::Error => return Err(internal(span, "unresolved type")),
        };
        let mut m = limits::shape(&ty).map_or(Measure::LEAF, limits::form);
        if parts.is_empty() {
            return Ok((self.ty(ty), m));
        }
        for (i, &t) in parts.iter().enumerate() {
            let (part, own) = self.measured_ty(t, args, span)?;
            m = self.within(m.with(own), span)?;
            *limits::part_mut(&mut ty, i).ok_or_else(|| internal(span, "a part of no form"))? = part;
        }
        Ok((self.ty(ty), m))
    }

    /// The id of the type `k` (the one intern of lowering).
    pub(crate) fn ty(&mut self, k: TyKind) -> CTy {
        self.m.tys.intern(k)
    }

    pub(crate) fn generic_args(&mut self, targs: &[TyId], args: &[GenericArg], span: Span) -> R<Vec<GenericArg>> {
        let mut out = Vec::new();
        for &t in targs {
            match self.a.types.get(t) {
                STy::ConstVal(n) => out.push(GenericArg::Const(*n)),
                STy::Param(i) => match args.get(*i as usize) {
                    Some(g) => out.push(g.clone()),
                    None => return Err(internal(span, "unbound generic argument")),
                },
                _ => out.push(GenericArg::Ty(self.core_ty(t, args, span)?)),
            }
        }
        Ok(out)
    }

    pub(crate) fn enum_variants(&self, id: TypeId) -> Vec<(String, Vec<CTy>)> {
        match &self.m.ty(id).kind {
            TypeDefKind::Enum { variants } => variants.clone(),
            _ => Vec::new(),
        }
    }

    pub(crate) fn struct_fields(&self, id: TypeId) -> &[(String, CTy)] {
        match &self.m.ty(id).kind {
            TypeDefKind::Struct { fields } => fields,
            _ => &[],
        }
    }

    // ------------------------------------------------------------ functions

    /// The Core function for a def instance; queues it for lowering on first
    /// use, by the call at `call`.
    pub(crate) fn fn_id(&mut self, d: DefId, args: Vec<GenericArg>, call: Span) -> R<FnId> {
        if let Some(&id) = self.fn_ids.get(&(d, args.clone())) {
            return Ok(id);
        }
        self.count_instance(d, call)?;
        let id = FnId(self.m.fns.len() as u32);
        let name = format!("{}{}", self.qual_name(d), self.mangle_args(&args));
        let span = self.a.def(d).span;
        let fp_relaxed = matches!(&self.a.def(d).kind, DefKind::Fn(f) if f.fp_relaxed);
        self.m.fns.push(FnDef {
            name,
            params: Vec::new(),
            ret: Types::UNIT,
            sret: false,
            rt: false,
            locals: Vec::new(),
            body: None,
            span,
            fp_relaxed,
            test: None,
            decl: Some(d),
            hoisted: Vec::new(),
        });
        self.fn_ids.insert((d, args.clone()), id);
        self.made_by.insert(id, (call, self.lowering));
        self.worklist.push((d, args, id));
        Ok(id)
    }

    /// Fill the function `fid` that [`Self::fn_id`] put empty: the one place
    /// of its parts, with `sret` of its result (§12.7).
    pub(crate) fn fill_fn(
        &mut self,
        fid: FnId,
        params: Vec<Param>,
        ret: CTy,
        rt: bool,
        locals: Vec<Local>,
        body: Option<Block>,
    ) -> &mut FnDef {
        let sret = self.m.tys.is_aggregate(ret);
        let fd = &mut self.m.fns[fid.0 as usize];
        fd.params = params;
        fd.sret = sret;
        fd.ret = ret;
        fd.rt = rt;
        fd.locals = locals;
        fd.body = body;
        fd
    }

    /// The Core constant of the constant `d` at the arguments of its `impl`,
    /// or of the struct of a default (one for each instance, §6.6, S-304,
    /// S-918). A `ConstValue` depends on no
    /// parameter, and takes the type of the instance here. It stops: the
    /// constants an initializer reads, by a name or by the `...` of a struct
    /// literal, are a graph of defs with no cycle (E0312; the `...` is an edge
    /// to every default of its struct, `names/body/cycles.rs`), and a
    /// recursion goes down it, whatever the arguments. `span`: the use.
    ///
    /// A constant a type stops is reported once (S-67), and each use is
    /// [`FailKind::Stopped`]: the expression that reads it is a placeholder.
    pub(crate) fn const_id(&mut self, d: DefId, gargs: Vec<GenericArg>, span: Span) -> R<ConstId> {
        if let Some(&id) = self.const_ids.get(&(d, gargs.clone())) {
            return Ok(id);
        }
        let key = Stop::Const(d, gargs.clone());
        if self.stopped.contains(&key) {
            return Err(stopped(span));
        }
        let within = self.a.def(d).span;
        self.lower_const(d, gargs, span).map_err(|f| self.stop_unit(key, within, f))
    }

    fn lower_const(&mut self, d: DefId, gargs: Vec<GenericArg>, span: Span) -> R<ConstId> {
        let def = self.a.def(d).clone();
        let DefKind::Const(c) = &def.kind else { return Err(internal(def.span, "not a const")) };
        let at = body::Binding { ty: c.ty, at: def.span, decl: c.ty_span.unwrap_or(def.span) };
        let ty = body::bind_tys(self, [at], &gargs, def.span)?[0];
        let init = match self.a.const_values.get(&d) {
            Some(v) => self.const_value_expr(v, ty, def.span)?,
            None => {
                // Evaluated by the interpreter at build time (T3-9): lower the initializer.
                let Some(body) = self.a.bodies.get(&d) else {
                    return Err(internal(def.span, "a `const` whose initializer was not checked"));
                };
                let Some(v) = c.value else { return Err(internal(def.span, "const without initializer")) };
                let mut cx = body::FnCx::new(self, d, gargs.clone(), body, body::Ret::Made(ty))?;
                cx.constant = true;
                let e = body::lower_expr(self, &mut cx, v)?;
                // Not with a placeholder, whose locals are not told apart (S-1272).
                if !cx.locals.is_empty() && !cx.placeholder {
                    return Err(unsupported(def.span, Feature::ConstBindings, &[]));
                }
                e
            }
        };
        self.count_instance(d, span)?;
        let id = ConstId(self.m.consts.len() as u32);
        let name = format!("{}{}", self.qual_name(d), self.mangle_args(&gargs));
        self.m.consts.push(ConstDef { name, ty, init });
        self.const_ids.insert((d, gargs), id);
        Ok(id)
    }

    fn const_value_expr(&mut self, v: &onsa_sema::ConstValue, ty: CTy, span: Span) -> R<Expr> {
        use onsa_sema::ConstValue as C;
        let kind = match (v, self.m.tys.kind(ty).clone()) {
            (C::Int(n), TyKind::Int(_)) => ExprKind::Lit(Lit::Int(*n)),
            // Exact: the evaluation rounded the literal to `F32` once (R-20).
            (C::Float(f), TyKind::Float(FloatKind::F32)) => ExprKind::Lit(Lit::F32(*f as f32)),
            (C::Float(f), TyKind::Float(FloatKind::F64)) => ExprKind::Lit(Lit::F64(*f)),
            // Rounded once, now that the type is decided.
            (C::FloatText(t), TyKind::Float(k)) => ExprKind::Lit(build::float_text(t, k, span)?),
            (C::Bool(b), TyKind::Bool) => ExprKind::Lit(Lit::Bool(*b)),
            (C::Char(c), TyKind::Char) => ExprKind::Lit(Lit::Char(*c)),
            (C::Unit, TyKind::Unit) => ExprKind::Lit(Lit::Unit),
            (C::Array(xs), TyKind::Array(et, _)) => {
                let mut out = Vec::new();
                for x in xs {
                    out.push(self.const_value_expr(x, et, span)?);
                }
                ExprKind::Array(out)
            }
            (C::Tuple(xs), TyKind::Tuple(ts)) => {
                let mut out = Vec::new();
                for (x, &t) in xs.iter().zip(&ts) {
                    out.push(self.const_value_expr(x, t, span)?);
                }
                ExprKind::Tuple(out)
            }
            (C::Struct(xs), TyKind::Struct(id)) => {
                let mut out = Vec::new();
                for (k, x) in (0..).zip(xs) {
                    let t = self.struct_fields(id).get(k as usize).map(|&(_, t)| t);
                    let t = t.ok_or_else(|| internal(span, "const value does not match its type"))?;
                    out.push((k, self.const_value_expr(x, t, span)?));
                }
                ExprKind::Struct { ty: id, fields: out }
            }
            _ => return Err(internal(span, "const value does not match its type")),
        };
        Ok(Expr::new(ty, span, kind))
    }

    fn lower_fn(&mut self, d: DefId, args: &[GenericArg], fid: FnId) -> R<()> {
        let def = self.a.def(d).clone();
        match &def.kind {
            DefKind::Fn(f) => {
                if f.flow_fn.is_some() {
                    // Generated by a flow (§11.6): lowering the flow fills every member. One it does not make
                    // (`process` of a port of a derived clock) the check stops (E0200, E0810 from W10-01).
                    let owner = def.owner.ok_or_else(|| internal(def.span, "flow member without an owner"))?;
                    self.ensure_flow(owner)?;
                    if self.m.fn_(fid).body.is_none() {
                        return Err(internal(def.span, format!("`{}` of a flow that makes none", def.name)));
                    }
                    return Ok(());
                }
                if let Some(made) = f.derived {
                    return self.lower_derived(d, f, made, args, fid);
                }
                // Of the result, where its type is converted (§4.4) and written.
                let ret = body::Binding { ty: f.ret, at: def.span, decl: f.ret_span.unwrap_or(def.span) };
                if f.body.is_none() {
                    // `target`: declaration only.
                    if let Some(m) = f.self_mode {
                        return Err(internal(def.span, format!("bodyless method with self mode {m:?}")));
                    }
                    let binds = f.params.iter().map(|p| body::Binding { ty: p.ty, at: p.span, decl: p.name_span });
                    let tys = body::bind_tys(self, std::iter::once(ret).chain(binds), args, def.span)?;
                    let mut params = Vec::new();
                    let mut locals = Vec::new();
                    for (p, &ty) in f.params.iter().zip(&tys[1..]) {
                        let local = LocalId(locals.len() as u32);
                        locals.push(Local::value(p.name.clone(), ty));
                        params.push(Param { local, mode: core_mode(p.mode), ty });
                    }
                    self.fill_fn(fid, params, tys[0], f.rt, locals, None);
                    return Ok(());
                }
                let Some(info) = self.a.bodies.get(&d) else {
                    return Err(internal(def.span, "function body was not checked"));
                };
                if !info.complete {
                    return Err(internal(def.span, "function body has errors"));
                }
                let mut cx = body::FnCx::new(self, d, args.to_vec(), info, body::Ret::Of(ret))?;
                let params = body::bind_params(self, &mut cx, d, f)?;
                let block = body::lower_fn_body(self, &mut cx, f.body.unwrap())?;
                self.fill_fn(fid, params, cx.ret, f.rt, cx.locals, Some(block));
                Ok(())
            }
            DefKind::Test { name, body } => {
                let Some(info) = self.a.bodies.get(&d) else {
                    return Err(internal(def.span, "test body was not checked"));
                };
                if !info.complete {
                    return Err(internal(def.span, "test body has errors"));
                }
                let mut cx = body::FnCx::new(self, d, Vec::new(), info, body::Ret::Made(Types::UNIT))?;
                let block = body::lower_fn_body(self, &mut cx, *body)?;
                // The mark that identifies the test (§11.8, S-55).
                let module = self.a.modules.get(def.module).path.clone();
                self.fill_fn(fid, Vec::new(), Types::UNIT, false, cx.locals, Some(block)).test =
                    Some(TestMark { module, name: name.clone() });
                Ok(())
            }
            _ => Err(internal(def.span, "not a function")),
        }
    }
}

pub(crate) fn core_mode(m: onsa_syntax::ast::Mode) -> Mode {
    match m {
        onsa_syntax::ast::Mode::Borrow => Mode::Borrow,
        onsa_syntax::ast::Mode::Inout => Mode::Inout,
        onsa_syntax::ast::Mode::Move => Mode::Move,
    }
}

/// A state lowering cannot be in: an internal error (S-67), not E0200.
pub(crate) fn internal(span: Span, msg: impl Into<String>) -> Fail {
    Fail {
        kind: FailKind::Internal,
        span,
        msg: format!("internal lowering error: {}", msg.into()),
        hole: None,
        report: None,
    }
}
