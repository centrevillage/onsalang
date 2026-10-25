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
    /// A binding that failed (§18.1): the E0304 of a `use` of the name of an
    /// item of the module (`crate::names::clash`).
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
    /// Every name its `use` bound, in the order written (E0304,
    /// `crate::names::clash`).
    pub bound: Vec<(String, Span)>,
    pub imports: Vec<Import>,
    /// Where a candidate adds a `use`; `None` for a module with no file.
    pub use_at: Option<UseAt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveError {
    NotFound {
        name: String,
        span: Span,
    },
    NotVisible {
        name: String,
        span: Span,
        defined: Span,
    },
    /// `a.b` where `a` has no members.
    NotANamespace {
        name: String,
        span: Span,
    },
    /// The head of a path outside a `use` names a module or a package with
    /// no `use` of it (§15.1, R-39): the candidate adds the `use`, unless
    /// the `use` would close a cycle of imports.
    NeedsUse {
        name: String,
        span: Span,
        fix: Option<Fix>,
    },
}

impl ResolveError {
    pub fn into_diagnostic(self) -> Diagnostic {
        match self {
            ResolveError::NotFound { name, span } => {
                Diagnostic::new(Stage::Names, Code::E0302, span, format!("cannot find `{name}`")).with_found(name)
            }
            ResolveError::NotVisible { name, span, defined } => Diagnostic::new(
                Stage::Names,
                Code::E0303,
                span,
                format!("`{name}` is not visible here (it is not `pub`)"),
            )
            .with_found(name)
            .with_note(defined, "defined here"),
            ResolveError::NotANamespace { name, span } => {
                Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` has no members")).with_found(name)
            }
            ResolveError::NeedsUse { name, span, fix } => {
                let msg = format!("cannot find `{name}`: another module or a package is named only through a `use`");
                let d = Diagnostic::new(Stage::Names, Code::E0302, span, msg).with_found(name);
                match fix {
                    Some(fix) => d.with_fix(fix),
                    None => d,
                }
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
    /// Associated items of user types: `impl` methods and consts (§6.2, §6.6).
    pub assoc: HashMap<DefId, HashMap<String, DefId>>,
    /// Associated items of builtin types (`impl F32 { const PI }` in std),
    /// keyed by the scalar's `TyId`, or by `Builtin(b, [])` for generic
    /// builtins (`Buf.zeroed`).
    pub assoc_builtin: HashMap<TyId, HashMap<String, DefId>>,
    /// The edges of the graph of the imports ([`Modules::import_edges`]),
    /// made once, when first read: after every `use` is listed.
    edges: std::sync::OnceLock<Vec<Vec<(ModId, Span)>>>,
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

    /// Whether `vis` declared in `decl` is usable from `from`.
    pub fn visible(&self, vis: Vis, decl: ModId, from: ModId) -> bool {
        match vis {
            Vis::Pub => true,
            // W4-03: no visibility word is within the package (§15.1); until
            // then it is read as `priv`, within the module.
            Vis::Default | Vis::Priv => decl == from,
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

    /// Module import graph edges (same package only), for E0310.
    fn import_target(&self, from: ModId, path: &Path) -> Option<ModId> {
        let root = self.root_of(from);
        let mut cur = *self.get(root).children.get(&path.segments[0].name)?;
        for seg in &path.segments[1..] {
            match self.get(cur).children.get(&seg.name) {
                Some(&c) => cur = c,
                None => break,
            }
        }
        (cur != from).then_some(cur)
    }

    /// The edges of the graph of the imports, by module: the module each
    /// `use` imports, and the span of the `use`.
    /// Read after the names stage listed every `use` (`crate::names`).
    fn import_edges(&self) -> &[Vec<(ModId, Span)>] {
        self.edges.get_or_init(|| {
            let edge = |m: ModId, imp: &Import| self.import_target(m, &imp.path).map(|t| (t, imp.span));
            (0..self.mods.len())
                .map(|i| {
                    self.get(ModId(i as u32)).imports.iter().filter_map(|imp| edge(ModId(i as u32), imp)).collect()
                })
                .collect()
        })
    }

    /// A `use` of `path` added in `from` would close a cycle of the imports
    /// (E0310): the module it imports reaches `from` by the edges of
    /// [`Modules::check_cycles`].
    pub(crate) fn closes_cycle(&self, from: ModId, path: &Path) -> bool {
        let Some(start) = self.import_target(from, path) else { return false };
        let edges = self.import_edges();
        let mut seen = vec![false; self.mods.len()];
        let mut stack = vec![start];
        while let Some(m) = stack.pop() {
            if m == from {
                return true;
            }
            if !std::mem::replace(&mut seen[m.0 as usize], true) {
                stack.extend(edges[m.0 as usize].iter().map(|&(t, _)| t));
            }
        }
        false
    }

    /// Detect cyclic imports (§15.1, E0310). Returns one diagnostic per cycle
    /// and the modules in dependency order (imports first) for resolution.
    pub fn check_cycles(&self) -> (Vec<Diagnostic>, Vec<ModId>) {
        let n = self.mods.len();
        let edges = self.import_edges();
        let mut state = vec![0u8; n]; // 0 new, 1 visiting, 2 done
        let mut order = Vec::new();
        let mut diags = Vec::new();
        let mut reported: HashSet<(usize, usize)> = HashSet::new();
        fn dfs(
            i: usize,
            edges: &[Vec<(ModId, Span)>],
            state: &mut [u8],
            order: &mut Vec<ModId>,
            diags: &mut Vec<Diagnostic>,
            reported: &mut HashSet<(usize, usize)>,
            mods: &Modules,
        ) {
            state[i] = 1;
            for &(t, span) in &edges[i] {
                let j = t.0 as usize;
                match state[j] {
                    0 => dfs(j, edges, state, order, diags, reported, mods),
                    1 => {
                        if reported.insert((i, j)) {
                            diags.push(Diagnostic::new(
                                Stage::Names,
                                Code::E0310,
                                span,
                                format!(
                                    "`{}` and `{}` import each other (cyclic module import)",
                                    mods.get(ModId(i as u32)).path,
                                    mods.get(t).path
                                ),
                            ));
                        }
                    }
                    _ => {}
                }
            }
            state[i] = 2;
            order.push(ModId(i as u32));
        }
        for i in 0..n {
            if state[i] == 0 {
                dfs(i, edges, &mut state, &mut order, &mut diags, &mut reported, self);
            }
        }
        (diags, order)
    }
}
