//! The names stage of the bodies (spec §5.1, §15.1, §18.1): one walk of each
//! body (a function, a test, a `const` initializer, a flow) that resolves
//! its names once and keeps them in a record ([`BodyNames`]), which the
//! types stage, modes and the later stages read (D-15).
//!
//! The parts: this module (the record and the entry [`walk_bodies`]),
//! `scope` (the tree of the scopes, the bindings and the lookup of a local),
//! `exprs` (the walk of the statements, expressions and patterns, and of
//! a flow body) and `paths` (the names whose head is no local).
//!
//! The walk reports the first error of the names of a body (§18.1), and
//! the types stage does not check a body it reported in. The types stage
//! reads the record for the names of the expressions, patterns, struct
//! literals and types of the body, and makes its locals from the bindings
//! of the record.

mod exprs;
mod kinds;
mod paths;
pub(crate) use kinds::{method_named, value_called};
pub(crate) use paths::is_value;
mod scope;
#[cfg(test)]
mod tests;

use std::collections::{HashMap, VecDeque};

use onsa_diag::Diagnostic;
use onsa_syntax::ast::{Ast, ExprId, Ident, ItemKind, Mode, Param, ParamName, PatId, StmtId, StmtKind, TypeId};

use crate::def::{DefKind, FlowInput, GenericDef, ModId};
use crate::flow_names::FlowBuiltin;
use crate::resolve::Entity;
use crate::ty::TyId;
use crate::{Analysis, DefId, Package, flatten};

/// A binding of a body: an index of [`BodyNames::bindings`], in the order the
/// walk declares them: the source order, except that a `let` and a `var`
/// are declared after their value (`let x = { let y = 1; y }` declares `y`,
/// then `x`). The types stage gives the binding `b` the local `LocalId(b.0)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct BindingId(pub u32);

/// A scope of a body: an index of [`BodyNames::scopes`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ScopeId(pub u32);

/// The names of one body, made once by the names stage. A name chain
/// (`a.b.c`, `Field(Field(Path(a), b), c)`) has a record at each node the
/// names stage resolves: the nodes of the namespaces it passes and the node
/// where it stops, an item ([`PathRes::Item`]) whatever its kind; what
/// follows is a field or a method, which the types stage resolves. A chain
/// with a name the names stage holds as an error (§18.1, S-692) has no
/// record at any node, the namespaces before that name included. A binding
/// that hides a name it sees is the walk's E0304 (§5.1), which stops it
/// there: no use of the name after it has a record (§18.1). An
/// expression with no record is one the names stage does not decide (a
/// literal, an operator, a field of a value), one of a chain held as an
/// error, or one after the name that stopped the walk.
#[derive(Debug, Default, Clone)]
pub(crate) struct BodyNames {
    /// The bindings, by [`BindingId`].
    pub bindings: Vec<Binding>,
    /// A `Path`, `Field` or `Feedback` (`^y`) node of a name chain.
    pub paths: HashMap<ExprId, PathRes>,
    /// A pattern that binds a name or names a constructor.
    pub pats: HashMap<PatId, PatRes>,
    /// A struct literal (`P { … }`, `Self { … }`, through an alias).
    pub structs: HashMap<ExprId, StructRes>,
    /// A hole of a string literal (§2.4): the literal and the index of the
    /// hole in its [`onsa_syntax::ast::StrLit::segments`], to the names of
    /// the hole the names stage resolves (the index of the name in the path
    /// of the hole, and its record), in order; the last one is the end.
    pub interp: HashMap<(ExprId, u32), Vec<(u32, PathRes)>>,
    /// The tree of the scopes, by [`ScopeId`]; the first is the scope of the
    /// parameters of the body. A scope is opened by a block, an arm of a
    /// `match` (its pattern, guard and body), a `for` (its pattern and body,
    /// not the iterated value), the parameters of an anonymous function and
    /// the variable of a `par` (with its body).
    pub scopes: Vec<ScopeInfo>,
    /// An anonymous function to the bindings outside it that it reads (it
    /// captures them by copy, §5.3), in the order of their first read: those
    /// that the anonymous functions inside it read too.
    pub captures: HashMap<ExprId, Vec<BindingId>>,
    /// A typed hole `_` (E0421, §18.1) to the bindings visible at it, from
    /// the outermost scope, each in the order of the walk.
    pub holes: HashMap<ExprId, Vec<BindingId>>,
    /// The types written in the body (an annotation, the type after `as`, a
    /// parameter and the result of an anonymous function, §4.4), lowered once
    /// by the names stage: the type, and the diagnostic of the types stage at
    /// it (E0412, …), which the types stage reports when it reaches it.
    pub types: HashMap<TypeId, (TyId, Option<Diagnostic>)>,
    /// `false` when the walk stopped before the end of the body: at an error
    /// of the names stage ([`Self::reported`]), or at a name the names stage
    /// holds as an error (§18.1, S-692), where the types stage stops too with
    /// no diagnostic. The record is partial, and what comes after the stop is
    /// missing from it, the bindings, the [`Binding::reads`] and the captures
    /// included (a stage that reports E0309 from the record reads only a
    /// complete one). A name held as an error in a type does not stop it.
    pub complete: bool,
    /// The walk reported an error of the names stage (the first of the
    /// body): the types stage does not check the body (§18.1).
    pub reported: bool,
    /// A type of the body reads what the check does not read (a name held as
    /// an error, S-690): [`crate::body::BodyInfo::read_unread`].
    pub read_unread: bool,
}

/// One binding of a body (§5.1).
#[derive(Debug, Clone)]
pub(crate) struct Binding {
    pub name: String,
    /// The name where it is first bound.
    pub span: onsa_diag::Span,
    pub kind: BindingKind,
    /// The patterns that bind it: one, or one in each branch of a choice
    /// (`(x, 0) | (0, x)`, §7). Empty for a binding no pattern makes (a
    /// parameter, `self`, a `var`, an input of a flow, the variable of a
    /// `par`).
    pub sites: Vec<PatId>,
    /// Where its value comes from (W4-16 reads it with `sites`).
    pub origin: Origin,
    /// The scope it is declared in.
    pub scope: ScopeId,
    /// The reads of it (E0309, §5.1): every use of its name, a read in an
    /// anonymous function that captures it, a hole of a string (§2.4) and
    /// `^y` included, and an index in the target of an assignment. The root of
    /// the target of an assignment is no read, through fields, indexes, tuple
    /// elements and parentheses (`t.q = 1`, `xs[n] = 1` reads `n` and not
    /// `xs`, `(a).0 = 1`).
    pub reads: u32,
}

/// What a binding is; one-to-one with [`crate::body::LocalKind`], except the
/// bindings of a flow (an input, a `let`, the variable of a `par`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BindingKind {
    Param(Mode),
    SelfParam(Mode),
    Let,
    Var,
    For { moved: bool },
    MatchBind,
    ClosureParam(Mode),
    FlowInput,
    FlowLet,
    ParVar,
}

/// The root of the value of a binding; of a binding no pattern makes, the
/// one key the types stage finds it by.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Origin {
    /// A parameter of the function, by its index in the parameters of the
    /// signature (`FnDef::params`, which `self` is not one of).
    Param(u32),
    SelfParam,
    Let(StmtId),
    Var(StmtId),
    For(StmtId),
    /// A pattern of the arm `arm` of a `match` on `scrutinee`.
    Arm {
        scrutinee: ExprId,
        arm: u32,
    },
    /// A parameter of an anonymous function, by its index in its list.
    Closure {
        closure: ExprId,
        param: u32,
    },
    FlowInput(u32),
    /// The variable of the `par` expression.
    Par(ExprId),
}

/// What a node of a name chain resolves to.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PathRes {
    Local(BindingId),
    /// A const parameter of the item, by its index.
    ConstParam(u32),
    /// A type parameter of the item (`T.…`), by its index.
    TypeParam(u32),
    /// A namespace the chain passes: a module, a flow, a type (an alias by
    /// its def, `Self` by the type it stands for), at a node before the one
    /// it stops at.
    Namespace(Entity),
    /// The item at the node where the chain stops, whatever its kind: at
    /// its last name, or at the name after which a name is no member (a
    /// value, whose fields and methods follow: `g` of `g.y`; the receiver
    /// of a method, which the types stage reports when it is no value). A
    /// module or a type at the place of a value is the types stage's error
    /// (E0308 from W4-04 U8); a member of a def whose heading a syntax error
    /// cut is an error with no diagnostic there (S-59, R-71). `owner` is the
    /// type an alias or `Self` before it stands for (§4.4, S-91, S-595;
    /// `crate::names::typed`), which decides its type arguments; `Self`
    /// alone is the type, with its own `owner`.
    Item {
        entity: Entity,
        owner: Option<TyId>,
    },
    /// An associated item of a builtin type in the compiler's table
    /// (`F32.PI`, `Buf.zeroed`, `crate::builtin`); `ty` is the type it is a
    /// member of (a generic one by its key, [`Analysis::builtin_key`]), and
    /// `owner` as of [`PathRes::Item`] (`Buf[F32]` of `Samples.zeroed`).
    BuiltinAssoc {
        ty: TyId,
        name: String,
        owner: Option<TyId>,
    },
    /// A builtin name of a flow body (§2.2, §11.4), recorded where the flow
    /// stage reads it (the callee of a delay or of `sample_rate()`); anywhere
    /// else it is not found (S-720, `paths.rs`).
    FlowBuiltin(FlowBuiltin),
}

/// What a pattern binds or names.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PatRes {
    Bind(BindingId),
    /// The item the path of a pattern names (`None`, `Shape.Circle(r)`,
    /// `Point { x, y }`): a constructor, or what the types stage reports as
    /// none; `owner` as of [`PathRes::Item`].
    Ctor {
        entity: Entity,
        owner: Option<TyId>,
    },
}

/// The item the path of a struct literal names (a struct, or what the types
/// stage reports as none), and the type the literal names it by.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct StructRes {
    pub entity: Entity,
    pub owner: Option<TyId>,
}

/// A scope of a body: its parent, and the bindings declared in it in order.
#[derive(Debug, Clone, Default)]
pub(crate) struct ScopeInfo {
    pub parent: Option<ScopeId>,
    pub bindings: Vec<BindingId>,
}

/// A type written in a body, with the visible locals it names
/// ([`Walker::site`]).
type Site = (TypeId, Vec<String>);

/// The walk of a body stopped: the record is partial
/// ([`BodyNames::complete`]).
struct Stop;
type W = Result<(), Stop>;

/// Why the walk of a body stops at a name.
enum Fail {
    /// The error of the names stage at it.
    Report(Diagnostic),
    /// A name the names stage holds as an error, or what the check does not
    /// read ([`Analysis::unread`]): no diagnostic.
    Held,
    /// A form whose error is of a later stage, and which the walk does not
    /// read into: an assignment of a flow body (E0806 until W7-04), `unsafe`
    /// and `handle` (E0200, whose names this version does not read, S-713).
    Later,
}

/// Walk the body of every function, test, `const` initializer and flow of
/// the package and its dependencies (the defs `crate::body::check_all`
/// checks), after the names of the modules and the signatures are known,
/// and keep their records in [`Analysis::names`].
pub(crate) fn walk_bodies(pkg: &Package, a: &mut Analysis) {
    let flat = flatten(pkg);
    let mut names = HashMap::new();
    for i in 0..a.defs.len() {
        let (id, def) = (DefId(i as u32), &a.defs[i]);
        // A body whose unit has a syntax error is not checked (§18.1, S-59).
        let Some(item) = def.item else { continue };
        if a.failed.contains_key(&id) {
            continue;
        }
        let info = a.modules.get(def.module);
        let Some(module) = flat.get(info.pkg).and_then(|p| info.module.and_then(|mi| p.modules.get(mi))) else {
            continue;
        };
        let ast = &module.parsed.ast;
        // The type and const parameters a body sees: of the function, or of
        // the `impl` of an associated `const`; `Self` of an `impl`.
        let owner_generics = || def.owner.map_or(&[][..], |o| a.def(o).generics());
        let self_ty = def.owner.and_then(|o| match &a.def(o).kind {
            DefKind::Impl(i) => Some(i.self_ty),
            _ => None,
        });
        let (body, params, generics): (ExprId, &[Param], &[GenericDef]) = match &def.kind {
            DefKind::Fn(f) => match f.body {
                Some(b) => (b, fn_params(ast, item), &f.generics),
                None => continue,
            },
            DefKind::Test { body, .. } => (*body, &[], &[]),
            DefKind::Const(c) => match c.value {
                Some(v) => (v, &[], owner_generics()),
                None => continue,
            },
            DefKind::Flow(f) => (f.body, &[], &[]),
            _ => continue,
        };
        // A panic names this declaration (S-67).
        let _scope = onsa_diag::internal::item_scope(def.span);
        let mut w = Walker::new(a, def.module, ast, &module.text, (generics, self_ty));
        let flow = matches!(def.kind, DefKind::Flow(_));
        let done = match &def.kind {
            DefKind::Flow(f) => w.walk_flow(&f.inputs, body),
            _ => {
                // `self` is a binding of a method of an `impl`.
                let has_self = def.owner.is_some_and(|o| matches!(a.def(o).kind, DefKind::Impl(_)));
                w.walk_fn(params, has_self, body)
            }
        };
        let (mut out, fail, sites) = (w.out, w.failure, (w.type_sites, w.flow_types));
        out.complete = done.is_ok();
        let generics = generics.to_vec();
        let fail = lower_types(a, id, (ast, &module.text), (&generics, self_ty), sites, &mut out).or(fail);
        match fail {
            Some(Fail::Report(d)) => {
                out.complete = false;
                out.reported = true;
                a.diagnostics.push(d);
            }
            Some(Fail::Held | Fail::Later) => out.complete = false,
            None => {}
        }
        // The unused bindings of a flow body are the flow stage's (W7-04).
        if out.complete && !flow {
            a.diagnostics.extend(scope::unused(&out, ast));
        }
        names.insert(id, out);
    }
    a.names = names;
}

/// Lower the types written in the body of `def`, in the order of the walk
/// (`sites`, those before the name that stopped it), into the record: the
/// first error of the names stage among them comes before that name's, and
/// stops the body (§18.1). The types of the `let`s of a flow the walk did
/// not reach (`late`), which the types stage reads ahead of the statements,
/// are after the stop: an error of the names stage there is none, and the
/// locals they name are not looked up.
fn lower_types(
    a: &mut Analysis,
    def: DefId,
    (ast, text): (&Ast, &str),
    (generics, self_ty): (&[GenericDef], Option<TyId>),
    (sites, late): (Vec<Site>, VecDeque<(StmtId, Site)>),
    out: &mut BodyNames,
) -> Option<Fail> {
    let held = a.read_held.contains(&def);
    let m = a.def(def).module;
    let mut fail = None;
    let late = late.into_iter().map(|(_, (t, _))| ((t, Vec::new()), true));
    for ((t, locals), late) in sites.into_iter().map(|t| (t, false)).chain(late) {
        let (ty, diags) = crate::sig::lower_type_in_body(a, m, ast, text, generics, self_ty, def, (t, locals));
        let d = diags.into_iter().next();
        let names = d.as_ref().filter(|d| d.stage == onsa_diag::Stage::Names);
        match names {
            Some(_) if late => drop(out.types.insert(t, (ty, None))),
            Some(d) => {
                fail = Some(Fail::Report(d.clone()));
                break;
            }
            None => drop(out.types.insert(t, (ty, d))),
        }
    }
    // What a type reads and the check does not is the body's (S-690).
    out.read_unread = !held && a.read_held.remove(&def);
    fail
}

/// The parameters written in the heading of the function `item`.
fn fn_params(ast: &Ast, item: onsa_syntax::ast::ItemId) -> &[Param] {
    match &ast.item(item).kind {
        ItemKind::Fn(fd) => &fd.params,
        ItemKind::Target(inner) => match inner.as_ref() {
            ItemKind::Fn(fd) => &fd.params,
            _ => &[],
        },
        _ => &[],
    }
}

/// The walk of one body of the module `m`.
struct Walker<'a> {
    a: &'a Analysis,
    m: ModId,
    ast: &'a Ast,
    text: &'a str,
    /// The type and const parameters of the heading (§4.5).
    generics: &'a [GenericDef],
    /// The type of the `impl` whose member's body it is, which `Self` names
    /// (§2.2, S-595).
    self_ty: Option<TyId>,
    /// A flow body, whose builtin names are its own (§2.2, §11.4).
    flow: bool,
    out: BodyNames,
    scopes: scope::Scopes,
    choices: Vec<exprs::Choice>,
    /// What stopped the walk at a name.
    failure: Option<Fail>,
    /// The types written in the body, in the order of the walk, with the
    /// locals they name ([`Walker::typed`]).
    type_sites: Vec<Site>,
    /// While the `let`s of a flow body are declared ahead of it, the one
    /// declared; and the first stop among them, where the walk stops when
    /// it reaches its `let` (§18.1: in the order of the text).
    prescan: Option<StmtId>,
    flow_stop: Option<(StmtId, Fail)>,
    /// The types of the `let`s of a flow body, in order, until the walk
    /// reaches each (`lower_types`).
    flow_types: VecDeque<(StmtId, Site)>,
    /// In a constant expression of §4.5 (`Walker::const_expr`).
    in_const: bool,
}

impl<'a> Walker<'a> {
    fn new(
        a: &'a Analysis,
        m: ModId,
        ast: &'a Ast,
        text: &'a str,
        (generics, self_ty): (&'a [GenericDef], Option<TyId>),
    ) -> Walker<'a> {
        Walker {
            a,
            m,
            ast,
            text,
            generics,
            self_ty,
            flow: false,
            out: BodyNames::default(),
            scopes: scope::Scopes::default(),
            choices: Vec::new(),
            failure: None,
            type_sites: Vec::new(),
            prescan: None,
            flow_stop: None,
            flow_types: VecDeque::new(),
            in_const: false,
        }
    }

    /// Stop the walk at a name, for `why`.
    fn fail(&mut self, why: Fail) -> Stop {
        self.failure = Some(why);
        Stop
    }

    /// Stop the walk at a name of a pattern, for `why`. In a `let` of a flow
    /// body declared ahead of it, the stop waits for that `let` instead,
    /// after the statements in front of it (§18.1: in the order of the text,
    /// R-289), and the walk goes on declaring the names of the `let`s (the
    /// types stage declares them all before the statements, S-692).
    fn fail_at_let(&mut self, why: Fail) -> W {
        match self.prescan {
            Some(s) => {
                self.flow_stop.get_or_insert((s, why));
                Ok(())
            }
            None => Err(self.fail(why)),
        }
    }

    fn src(&self, span: onsa_diag::Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    /// A body with the parameters of its heading.
    fn walk_fn(&mut self, params: &[Param], has_self: bool, body: ExprId) -> W {
        self.open_scope();
        let mut index = 0;
        for p in params {
            match &p.name {
                ParamName::SelfParam(span) if has_self => {
                    let name = Ident { name: "self".into(), span: *span };
                    self.declare(&name, BindingKind::SelfParam(p.mode), Origin::SelfParam, None)?;
                }
                ParamName::SelfParam(_) => {}
                ParamName::Ident(name) => {
                    self.declare(name, BindingKind::Param(p.mode), Origin::Param(index), None)?;
                    index += 1;
                }
                ParamName::Wild(_) => index += 1,
            }
        }
        self.expr(body)?;
        self.close_scope();
        Ok(())
    }

    /// A flow body (§11.2), in the order the types stage declares: the
    /// inputs, the names of every `let` of the body, then the body. An error
    /// of the pattern of a `let` stops the walk at it, after the errors of
    /// the statements before it ([`Self::fail_at_let`]), and its type is read
    /// there. The walk stops at its first assignment: its error is the
    /// flow stage's (E0806) until W7-04 reports it in the names stage.
    fn walk_flow(&mut self, inputs: &[FlowInput], body: ExprId) -> W {
        self.flow = true;
        self.open_scope();
        for (k, input) in inputs.iter().enumerate() {
            let name = Ident { name: input.name.clone(), span: input.name_span };
            self.declare(&name, BindingKind::FlowInput, Origin::FlowInput(k as u32), None)?;
        }
        let ast = self.ast;
        let onsa_syntax::ast::ExprKind::Block(b) = &ast.expr(body).kind else { return self.expr(body) };
        for &s in &b.stmts {
            if let StmtKind::Let { pat, ty, .. } = ast.stmt(s).kind {
                self.prescan = Some(s);
                // The type sees the `let`s above it (§11.2), not its own names.
                let site = ty.map(|t| (s, self.site(t)));
                self.pattern(pat, BindingKind::FlowLet, Origin::Let(s))?;
                self.flow_types.extend(site);
            }
        }
        self.prescan = None;
        self.open_scope();
        for &s in &b.stmts {
            if let Some((_, why)) = self.flow_stop.take_if(|(at, _)| *at == s) {
                return Err(self.fail(why));
            }
            match &ast.stmt(s).kind {
                StmtKind::Let { init, .. } => {
                    if self.flow_types.front().is_some_and(|&(at, _)| at == s) {
                        self.type_sites.extend(self.flow_types.pop_front().map(|(_, t)| t));
                    }
                    self.expr(*init)?
                }
                _ => self.stmt(s)?,
            }
        }
        if let Some(t) = b.tail {
            self.expr(t)?;
        }
        self.close_scope();
        self.close_scope();
        Ok(())
    }
}
