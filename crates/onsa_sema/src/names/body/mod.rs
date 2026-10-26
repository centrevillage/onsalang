//! The names stage of the bodies (spec §5.1, §15.1, §18.1): one walk of each
//! body (a function, a test, a `const` initializer, a flow) that resolves
//! its names once and keeps them in a record ([`BodyNames`]), which the
//! types stage, modes and the later stages read (D-15).
//!
//! The parts: this module (the record and the entry [`walk_bodies`]),
//! `scope` (the tree of the scopes, the bindings and the lookup of a local)
//! and `exprs` (the walk of the statements, expressions and patterns).
//!
//! The walk makes the record only, and no diagnostic: the types stage
//! resolves the names of a body as before and reports their errors, until it
//! reads the record (W4-04 U3a, U3b).
#![allow(dead_code, reason = "the record is read from W4-04 U3a; the walk fills the rest of it in U2b")]

mod exprs;
mod scope;
#[cfg(test)]
mod tests;

use std::collections::HashMap;

use onsa_syntax::ast::{Ast, ExprId, Ident, ItemKind, Mode, Param, ParamName, PatId, StmtId};

use crate::def::DefKind;
use crate::resolve::Entity;
use crate::ty::TyId;
use crate::{Analysis, DefId, Package, flatten};

/// A binding of a body: an index of [`BodyNames::bindings`], in the order the
/// walk declares them: the source order, except that a `let` and a `var`
/// are declared after their value (`let x = { let y = 1; y }` declares `y`,
/// then `x`), as the types stage declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct BindingId(pub u32);

/// A scope of a body: an index of [`BodyNames::scopes`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ScopeId(pub u32);

/// The names of one body, made once by the names stage. A name chain
/// (`a.b.c`, `Field(Field(Path(a), b), c)`) has a record at each node the
/// names stage resolves: the nodes of the namespaces it passes and the node
/// of the value it ends at; what follows is a field or a method, which the
/// types stage resolves. An expression with no record is one the names stage
/// does not decide (a literal, an operator, a field of a value).
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
    /// `false` when the walk stopped before the end of the body (a type
    /// argument in an expression, `Feature::TypeArgsInExpressions`): the
    /// record is partial, and what comes after the stop is missing from it,
    /// the bindings, the [`Binding::reads`] and the captures included (a
    /// stage that reports E0309 from the record reads only a complete one).
    pub complete: bool,
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

/// The root of the value of a binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    /// A namespace the chain passes: a module, a flow, a type, an alias or
    /// `Self` (the nodes before the end).
    Namespace(Entity),
    /// A value of an item: through a module, a flow, a type, an alias or
    /// `Self`; `owner` is the type it is a member of as the chain names it
    /// (an alias or `Self` as the type they stand for).
    Item {
        entity: Entity,
        owner: Option<TyId>,
    },
    /// An associated item of a builtin type (`F32.PI`, `Buf.zeroed`).
    BuiltinAssoc {
        ty: TyId,
        name: String,
    },
    /// A builtin name of a flow (§11.4), as `crate::flow_names` spells it.
    FlowBuiltin(&'static str),
}

/// What a pattern binds or names.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PatRes {
    Bind(BindingId),
    Ctor { entity: Entity, owner: Option<TyId> },
}

/// The struct a struct literal makes, and the type the literal names it by.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct StructRes {
    pub def: DefId,
    pub owner: Option<TyId>,
}

/// A scope of a body: its parent, and the bindings declared in it in order.
#[derive(Debug, Clone, Default)]
pub(crate) struct ScopeInfo {
    pub parent: Option<ScopeId>,
    pub bindings: Vec<BindingId>,
}

/// The walk of a body stopped: the record is partial
/// ([`BodyNames::complete`]).
struct Stop;
type W = Result<(), Stop>;

/// Walk the body of every function, test and `const` initializer of the
/// package and its dependencies (the defs `crate::body::check_all` checks),
/// after the names of the modules and the signatures are known, and keep
/// their records in [`Analysis::names`].
pub(crate) fn walk_bodies(pkg: &Package, a: &mut Analysis) {
    let flat = flatten(pkg);
    let mut names = HashMap::new();
    for (i, def) in a.defs.iter().enumerate() {
        let id = DefId(i as u32);
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
        let (body, params): (ExprId, &[Param]) = match &def.kind {
            DefKind::Fn(f) => match f.body {
                Some(b) => (b, fn_params(ast, item)),
                None => continue,
            },
            DefKind::Test { body, .. } => (*body, &[]),
            DefKind::Const(c) => match c.value {
                Some(v) => (v, &[]),
                None => continue,
            },
            // A flow body (from W4-04 U2b).
            _ => continue,
        };
        // A panic names this declaration (S-67).
        let _scope = onsa_diag::internal::item_scope(def.span);
        // `self` is a binding of a method of an `impl`.
        let has_self = def.owner.is_some_and(|o| matches!(a.def(o).kind, DefKind::Impl(_)));
        let mut w = Walker::new(ast);
        let done = w.walk_fn(params, has_self, body);
        w.out.complete = done.is_ok();
        names.insert(id, w.out);
    }
    a.names = names;
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

/// The walk of one body.
struct Walker<'a> {
    ast: &'a Ast,
    out: BodyNames,
    scopes: scope::Scopes,
    choices: Vec<exprs::Choice>,
}

impl<'a> Walker<'a> {
    fn new(ast: &'a Ast) -> Walker<'a> {
        Walker { ast, out: BodyNames::default(), scopes: scope::Scopes::default(), choices: Vec::new() }
    }

    /// A body with the parameters of its heading.
    fn walk_fn(&mut self, params: &[Param], has_self: bool, body: ExprId) -> W {
        self.open_scope();
        let mut index = 0;
        for p in params {
            match &p.name {
                ParamName::SelfParam(span) if has_self => {
                    let name = Ident { name: "self".into(), span: *span };
                    self.declare(&name, BindingKind::SelfParam(p.mode), Origin::SelfParam, None);
                }
                ParamName::SelfParam(_) => {}
                ParamName::Ident(name) => {
                    self.declare(name, BindingKind::Param(p.mode), Origin::Param(index), None);
                    index += 1;
                }
                ParamName::Wild(_) => index += 1,
            }
        }
        self.expr(body)?;
        self.close_scope();
        Ok(())
    }
}
