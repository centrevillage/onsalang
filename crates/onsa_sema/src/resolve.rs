//! Modules, their tables of names, imports and cycles (spec §15.1, S-11,
//! S-17, S-20, S-611). The lookups of a path are in `crate::names::lookup`.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, FileId, Fix, Span, Stage};
use onsa_syntax::ast::{Ident, ItemId, Path, Vis};

use crate::def::{DefId, ModId};
use crate::ty::{BuiltinTy, TyId};

/// Names in scope everywhere (prelude, §15.1) and builtin types (§4.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    /// `I32`, `F32`, `Bool`, `Char`
    Scalar(TyId),
    /// `Str`, `Array`, `Option`, `Span`, ...
    Generic(BuiltinTy),
    /// `Some`
    Some,
    /// `None`
    None,
    /// `Ok`
    Ok,
    /// `Err`
    Err,
}

/// What a path resolves to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Entity {
    Module(ModId),
    Def(DefId),
    Builtin(Builtin),
    /// A variant of a user enum: `Shape.Circle`.
    Variant(DefId, u32),
    /// A member of a flow namespace (`voice.State`, `voice.init`), or an
    /// associated item of a type (`Point.new`, `F32.PI`); the def itself.
    Member(DefId),
}

/// A name a `use` bound in its module (§15.1): of the module's body only,
/// never of the namespace other modules read (S-611). `span` is the name in
/// the `use`.
#[derive(Debug, Clone, Copy)]
pub enum UseBinding {
    Bound {
        entity: Entity,
        span: Span,
    },
    /// A name of a `use` that failed (§18.1, S-462): in the names stage, or
    /// in the syntax stage with the name read. No binding (no E0304 with
    /// another), and an error where it is used when nothing else binds it.
    Failed {
        span: Span,
    },
}

impl UseBinding {
    pub fn entity(&self) -> Option<Entity> {
        match *self {
            UseBinding::Bound { entity, .. } => Some(entity),
            UseBinding::Failed { .. } => None,
        }
    }

    pub fn span(&self) -> Span {
        match *self {
            UseBinding::Bound { span, .. } | UseBinding::Failed { span } => span,
        }
    }
}

/// Where a fix candidate adds a `use` in the file of a module (spec §15.1,
/// R-39): after the last `use` of its top level read whole, or else before
/// its first unit (its doc comments and attributes included).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseAt {
    /// `"\nuse x"` at the end of the unit of the last `use`.
    After(u32),
    /// `"use x\n"` at the start of the first unit.
    Before(u32),
}

#[derive(Debug, Clone)]
pub struct Import {
    pub path: Path,
    pub names: Option<Vec<Ident>>,
    pub vis: Vis,
    pub span: Span,
    pub item: ItemId,
}

/// What a dependency of a `use` reaches (§15.1, S-594): the module of an
/// item taken, or a module taken and every module below it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DepTarget {
    At(ModId),
    Below(ModId),
}

impl DepTarget {
    /// The module the dependency is on, with what is below it or not.
    pub fn module(self) -> ModId {
        let (DepTarget::At(t) | DepTarget::Below(t)) = self;
        t
    }
}

/// A dependency of a `use`: `name` is the name it takes (or the last
/// element read), `span` the `use`.
#[derive(Debug, Clone, Copy)]
pub struct Dep {
    pub target: DepTarget,
    pub name: Span,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ModInfo {
    /// `dsp.voice`; empty for a package root.
    pub path: String,
    /// Index into the flattened package list (`crate::flatten`).
    pub pkg: usize,
    /// Index of the module in `Package::modules`; `None` for directory-only
    /// modules and package roots.
    pub module: Option<usize>,
    pub file: Option<FileId>,
    pub parent: Option<ModId>,
    /// The child modules (of a file, or of a directory only).
    pub children: HashMap<String, ModId>,
    /// The items of the module, by name: of its body and of its namespace.
    pub items: HashMap<String, DefId>,
    /// The names its `use` bound: of its body only (S-611). The first of a
    /// name is in the table.
    pub uses: HashMap<String, UseBinding>,
    /// The names its `pub use` take, the E0200 (§15.1, S-596): failed, and
    /// an error where another `use` takes them from it ([`UseBinding::Failed`]).
    pub pub_use_names: HashSet<String>,
    /// Every name its `use` bound, in the order written (E0304,
    /// `crate::names::clash`).
    pub bound: Vec<(String, Span)>,
    pub imports: Vec<Import>,
    /// The dependencies its `use` make (§15.1, S-594), in the order written.
    pub deps: Vec<Dep>,
    /// The names of its body and of its namespace that are an E0304 or an
    /// E0305 (§15.1, §18.1, S-675): a use of them is an error, whatever
    /// binds them.
    pub clashed: Clashed,
    /// A `use` of it was cut before its names were all read (R-180): a name
    /// of its body that is not found is an error.
    pub unread_use: bool,
    /// Where a candidate adds a `use`; `None` for a module with no file.
    pub use_at: Option<UseAt>,
}

/// The names of an E0304 or an E0305 in the spaces of a module (§15.1).
#[derive(Debug, Clone, Default)]
pub struct Clashed {
    pub body: HashSet<String>,
    pub namespace: HashSet<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveError {
    /// A name the names stage holds as an error (§18.1, S-462, S-675): of a
    /// `use` that failed or of an E0304 or E0305, reported where it is
    /// bound. Its uses get no diagnostic.
    Failed,
    NotFound {
        name: String,
        span: Span,
    },
    /// A name not visible here (E0303): `why` is from [`Modules::hidden_why`].
    NotVisible {
        name: String,
        span: Span,
        defined: Span,
        why: String,
    },
    /// `use kp.Shape.{Circle}`: a variant or an associated item of the
    /// type `ty`, which a `use` does not take (§15.1, R-50).
    OfAType {
        ty: String,
        name: String,
        span: Span,
    },
    /// `a.b` where `a` has no members.
    NotANamespace {
        name: String,
        span: Span,
    },
    /// The head of a path outside a `use` names a module or a package with
    /// no `use` of it (§15.1, R-39), or names the own package or module
    /// (`own`, S-673): the candidate of `crate::names::lookup`, or a rule
    /// that shows the form.
    NeedsUse {
        name: String,
        span: Span,
        own: bool,
        fix: Option<Fix>,
        rule: Option<String>,
    },
}

impl ResolveError {
    /// The diagnostic of the error; none of a name held as an error.
    pub fn diagnostic(self) -> Option<Diagnostic> {
        (self != ResolveError::Failed).then(|| self.into_diagnostic())
    }

    pub fn into_diagnostic(self) -> Diagnostic {
        match self {
            ResolveError::Failed => onsa_diag::internal::bug(None, "a diagnostic of a name held as an error"),
            ResolveError::NotFound { name, span } => {
                Diagnostic::new(Stage::Names, Code::E0302, span, format!("cannot find `{name}`")).with_found(name)
            }
            ResolveError::NotVisible { name, span, defined, why } => {
                Diagnostic::new(Stage::Names, Code::E0303, span, format!("`{name}` is not visible here: {why}"))
                    .with_found(name)
                    .with_note(defined, "defined here")
            }
            ResolveError::OfAType { ty, name, span } => Diagnostic::new(
                Stage::Names,
                Code::E0302,
                span,
                format!(
                    "`{ty}.{name}` is not taken by a `use`: the variants, the associated functions and the \
                     associated constants of a type are named through it"
                ),
            )
            .with_found(name.clone())
            .with_rule(format!("take `{ty}`, and write `{ty}.{name}` where it is used")),
            ResolveError::NotANamespace { name, span } => {
                Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` has no members")).with_found(name)
            }
            ResolveError::NeedsUse { name, span, own, fix, rule } => {
                let msg = if own {
                    format!("cannot find `{name}`: a path does not name its own package or module (§15.1)")
                } else {
                    format!("cannot find `{name}`: another module or a package is named only through a `use`")
                };
                let mut d = Diagnostic::new(Stage::Names, Code::E0302, span, msg).with_found(name);
                if let Some(fix) = fix {
                    d = d.with_fix(fix);
                }
                if let Some(rule) = rule {
                    d = d.with_rule(rule);
                }
                d
            }
        }
    }
}

/// The module graph and the tables of names. Owned by `Analysis`.
#[derive(Debug, Default)]
pub struct Modules {
    pub mods: Vec<ModInfo>,
    /// Package roots, by package index.
    pub roots: Vec<ModId>,
    /// Package names (`std`, the user package), by package index.
    pub names: Vec<String>,
    /// The heads of the paths of `use` (§15.1, S-37), by package index: the
    /// modules under the package's root and the roots of the packages it
    /// depends on, by name.
    pub heads: Vec<HashMap<String, ModId>>,
    /// The heads of each package that are an E0304 (a module under the
    /// root of the name of a package depended on, S-246): a path from them
    /// is an error (§18.1, S-675).
    pub clashed_heads: Vec<HashSet<String>>,
    /// Associated items of user types: `impl` methods and consts (§6.2, §6.6).
    pub assoc: HashMap<DefId, HashMap<String, DefId>>,
    /// Associated items of builtin types (`impl F32 { const PI }` in std),
    /// keyed by the scalar's `TyId`, or by `Builtin(b, [])` for generic
    /// builtins (`Buf.zeroed`).
    pub assoc_builtin: HashMap<TyId, HashMap<String, DefId>>,
    /// The graph of the dependencies of the `use` (E0310), made once every
    /// `use` is resolved (`crate::names::cycles`).
    pub(crate) graph: Option<crate::names::ImportGraph>,
}

impl Modules {
    pub fn get(&self, m: ModId) -> &ModInfo {
        &self.mods[m.0 as usize]
    }

    pub fn get_mut(&mut self, m: ModId) -> &mut ModInfo {
        &mut self.mods[m.0 as usize]
    }

    pub fn add(&mut self, info: ModInfo) -> ModId {
        self.mods.push(info);
        ModId(self.mods.len() as u32 - 1)
    }

    pub fn pkg_of(&self, m: ModId) -> usize {
        self.get(m).pkg
    }

    /// Whether `vis` declared in `decl` is usable from `from` (§15.1, S-36):
    /// `pub` out of the package, no word within the package, `priv` within
    /// the module. Every check of a visibility reads this one.
    pub fn visible(&self, vis: Vis, decl: ModId, from: ModId) -> bool {
        match vis {
            Vis::Pub => true,
            Vis::Default => self.pkg_of(decl) == self.pkg_of(from),
            Vis::Priv => decl == from,
        }
    }

    /// Why a name of visibility `own` is not visible from `from` (§15.1,
    /// S-36), for the message of its E0303: a member or a field whose type
    /// (`owner`, of the kind named) is not visible there is hidden by the
    /// type, else by its own visibility. Not visible, a name is `priv` out of
    /// its module or has no word out of its package.
    pub fn hidden_why(&self, own: Vis, owner: Option<(&str, &crate::def::Def)>, from: ModId) -> String {
        let why = |vis: Vis| match vis {
            Vis::Priv => "is `priv`, seen in its module alone",
            Vis::Default | Vis::Pub => "is not `pub`, seen in its package alone",
        };
        match owner {
            Some((kind, ty)) if !self.visible(ty.vis, ty.module, from) => {
                format!("its {kind} `{}` {}", ty.name, why(ty.vis))
            }
            _ => format!("it {}", why(own)),
        }
    }

    /// The root module of the package containing `m`.
    pub fn root_of(&self, m: ModId) -> ModId {
        self.roots[self.pkg_of(m)]
    }

    /// The module the head `name` of the path of a `use` written in `from`
    /// names (§15.1, S-37): a module under the package's root or the root
    /// of a package it depends on; never an item or a name a `use` bound.
    pub fn head(&self, from: ModId, name: &str) -> Option<ModId> {
        self.heads[self.pkg_of(from)].get(name).copied()
    }

    /// The path of `m` in a `use` written in `from` (§15.1): from the root of
    /// its package, after the name of the package when it is another one
    /// (`std.math`; `std` for its root). O(its length).
    pub fn abs_path(&self, from: ModId, m: ModId) -> Vec<String> {
        let info = self.get(m);
        let package = (info.pkg != self.pkg_of(from)).then(|| self.names[info.pkg].clone());
        package.into_iter().chain(info.path.split('.').filter(|s| !s.is_empty()).map(String::from)).collect()
    }
}
