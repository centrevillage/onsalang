//! Modules, scopes, imports and path resolution (spec §15.1, S-11, S-17, S-20).

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, FileId, Span, Stage};
use onsa_syntax::ast::{Ident, ItemId, Path, Vis};

use crate::def::{DefId, DefKind, ModId};
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

#[derive(Debug, Clone)]
pub struct Binding {
    pub entity: Entity,
    pub vis: Vis,
    pub span: Span,
    /// Came from `use` (true) or is declared here (false).
    pub import: bool,
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
    pub children: HashMap<String, ModId>,
    pub scope: HashMap<String, Binding>,
    pub imports: Vec<Import>,
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
        }
    }
}

/// The module graph and scopes. Owned by `Analysis`.
#[derive(Debug, Default)]
pub struct Modules {
    pub mods: Vec<ModInfo>,
    /// Package roots, by package index.
    pub roots: Vec<ModId>,
    /// Package names (`std`, the user package), by package index.
    pub names: Vec<String>,
    /// Associated items of user types: `impl` methods and consts (§6.2, §6.6).
    pub assoc: HashMap<DefId, HashMap<String, DefId>>,
    /// Associated items of builtin types (`impl F32 { const PI }` in std),
    /// keyed by the scalar's `TyId`, or by `Builtin(b, [])` for generic
    /// builtins (`Buf.zeroed`).
    pub assoc_builtin: HashMap<TyId, HashMap<String, DefId>>,
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
            Vis::Pkg => self.pkg_of(decl) == self.pkg_of(from),
            Vis::Private => decl == from,
        }
    }

    /// The root module of the package containing `m`.
    pub fn root_of(&self, m: ModId) -> ModId {
        self.roots[self.pkg_of(m)]
    }

    /// Resolve the first segment of a path from inside `from` (§15.1):
    /// module scope (items and imports), then prelude and builtin types,
    /// then the package's root modules, then packages by name.
    pub fn lookup(&self, from: ModId, name: &str, prelude: &HashMap<String, Builtin>) -> Option<Entity> {
        if let Some(b) = self.get(from).scope.get(name) {
            return Some(b.entity);
        }
        if let Some(&b) = prelude.get(name) {
            return Some(Entity::Builtin(b));
        }
        let root = self.root_of(from);
        if let Some(&m) = self.get(root).children.get(name) {
            return Some(Entity::Module(m));
        }
        // Packages by name, including the package itself (`std` uses `std.math`).
        if let Some(i) = self.names.iter().position(|n| n == name) {
            return Some(Entity::Module(self.roots[i]));
        }
        None
    }

    fn builtin_member(
        &self,
        key: TyId,
        name: &Ident,
        from: ModId,
        defs: &[crate::def::Def],
    ) -> Result<Entity, ResolveError> {
        if let Some(a) = self.assoc_builtin.get(&key).and_then(|m| m.get(&name.name)) {
            let adef = &defs[a.0 as usize];
            if self.visible(adef.vis, adef.module, from) {
                return Ok(Entity::Member(*a));
            }
            return Err(ResolveError::NotVisible { name: name.name.clone(), span: name.span, defined: adef.name_span });
        }
        Err(ResolveError::NotFound { name: name.name.clone(), span: name.span })
    }

    /// A member `name` of `entity`, as seen from `from`. `builtin_key` maps a
    /// generic builtin to the `TyId` its associated items are keyed by.
    pub fn member(
        &self,
        entity: Entity,
        name: &Ident,
        from: ModId,
        defs: &[crate::def::Def],
        builtin_key: &HashMap<BuiltinTy, TyId>,
    ) -> Result<Entity, ResolveError> {
        match entity {
            Entity::Module(m) => {
                let info = self.get(m);
                if let Some(b) = info.scope.get(&name.name) {
                    // Imports are re-exported only with `pub use` (§15.1).
                    let usable = if b.import { b.vis == Vis::Pub || m == from } else { self.visible(b.vis, m, from) };
                    if usable {
                        return Ok(b.entity);
                    }
                    return Err(ResolveError::NotVisible { name: name.name.clone(), span: name.span, defined: b.span });
                }
                if let Some(&c) = info.children.get(&name.name) {
                    return Ok(Entity::Module(c));
                }
                Err(ResolveError::NotFound { name: name.name.clone(), span: name.span })
            }
            Entity::Def(d) => {
                let def = &defs[d.0 as usize];
                match &def.kind {
                    DefKind::Flow(f) => {
                        if let Some((_, m)) = f.members.iter().find(|(n, _)| n == &name.name) {
                            return Ok(Entity::Member(*m));
                        }
                    }
                    DefKind::Enum(e) => {
                        if let Some(i) = e.variants.iter().position(|v| v.name == name.name) {
                            return Ok(Entity::Variant(d, i as u32));
                        }
                    }
                    DefKind::Struct(_) => {}
                    _ => return Err(ResolveError::NotANamespace { name: def.name.clone(), span: name.span }),
                }
                if let Some(a) = self.assoc.get(&d).and_then(|m| m.get(&name.name)) {
                    let adef = &defs[a.0 as usize];
                    if self.visible(adef.vis, adef.module, from) {
                        return Ok(Entity::Member(*a));
                    }
                    return Err(ResolveError::NotVisible {
                        name: name.name.clone(),
                        span: name.span,
                        defined: adef.name_span,
                    });
                }
                Err(ResolveError::NotFound { name: format!("{}.{}", def.name, name.name), span: name.span })
            }
            Entity::Member(d) => {
                // `voice.State` is a struct: it may have associated items too.
                self.member(Entity::Def(d), name, from, defs, builtin_key)
            }
            Entity::Builtin(Builtin::Scalar(t)) => self.builtin_member(t, name, from, defs),
            Entity::Builtin(Builtin::Generic(b)) => match builtin_key.get(&b) {
                Some(&t) => self.builtin_member(t, name, from, defs),
                None => Err(ResolveError::NotFound { name: name.name.clone(), span: name.span }),
            },
            Entity::Builtin(_) | Entity::Variant(..) => {
                Err(ResolveError::NotANamespace { name: name.name.clone(), span: name.span })
            }
        }
    }

    /// Resolve a full path from inside `from`.
    pub fn resolve_path(
        &self,
        from: ModId,
        path: &Path,
        prelude: &HashMap<String, Builtin>,
        defs: &[crate::def::Def],
        builtin_key: &HashMap<BuiltinTy, TyId>,
    ) -> Result<Entity, ResolveError> {
        let first = &path.segments[0];
        let mut cur = self
            .lookup(from, &first.name, prelude)
            .ok_or_else(|| ResolveError::NotFound { name: first.name.clone(), span: first.span })?;
        for seg in &path.segments[1..] {
            cur = self.member(cur, seg, from, defs, builtin_key)?;
        }
        Ok(cur)
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

    /// Detect cyclic imports (§15.1, E0310). Returns one diagnostic per cycle
    /// and the modules in dependency order (imports first) for resolution.
    pub fn check_cycles(&self) -> (Vec<Diagnostic>, Vec<ModId>) {
        let n = self.mods.len();
        let edges: Vec<Vec<(ModId, Span)>> = (0..n)
            .map(|i| {
                let m = ModId(i as u32);
                self.get(m)
                    .imports
                    .iter()
                    .filter_map(|imp| self.import_target(m, &imp.path).map(|t| (t, imp.span)))
                    .collect()
            })
            .collect();
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
                dfs(i, &edges, &mut state, &mut order, &mut diags, &mut reported, self);
            }
        }
        (diags, order)
    }
}
