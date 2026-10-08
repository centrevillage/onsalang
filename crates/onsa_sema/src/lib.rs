//! Name resolution, types, effects, rt, exclusivity, and flow checks (M2, M3).
//!
//! This crate takes parsed packages and produces an [`Analysis`]: every
//! definition with its lowered signature, interned types, module scopes, and
//! diagnostics. Bodies are checked by `check_bodies` (T2-5 .. T2-12).

pub mod body;
#[cfg(test)]
mod body_tests;
mod builtin;
mod constarg;
pub mod consteval;
pub mod def;
mod deferred;
mod effects;
#[cfg(test)]
mod effects_tests;
mod exhaust;
pub mod flow;
#[cfg(test)]
mod flow_tests;
pub mod infer;
pub mod kind;
pub mod layout;
mod modes;
#[cfg(test)]
mod modes_tests;
pub mod resolve;
mod rt;
mod sig;
#[cfg(test)]
mod tests;

/// For the unit tests: the text of the diagnostic's range in `text` after
/// applying its candidate `k` (the candidates edit inside that range).
#[cfg(test)]
pub(crate) fn fixed_region(text: &str, d: &onsa_diag::Diagnostic, k: usize) -> String {
    let fix = &d.fixes[k];
    let edits: Vec<&onsa_diag::Edit> = fix.edits().iter().collect();
    let after = onsa_diag::apply_text(text, &edits).expect("the candidate applies");
    let end = d.span.end as usize + after.len() - text.len();
    after[d.span.start as usize..end].to_string()
}
pub mod ty;

use std::collections::HashMap;

use onsa_diag::{Diagnostic, FileId};
use onsa_syntax::Parsed;

pub use body::{BodyInfo, Instance, LocalId, LocalInfo, LocalKind, Target};
/// The names of the builtin methods and associated items (for the gate, Q-14).
pub use builtin::names as builtin_member_names;
pub use consteval::ConstValue;
pub use def::{Def, DefId, DefKind, ModId};
pub use flow::{FlowInfo, FlowLet, FlowRate, InitArg, Node};
pub use kind::Kind;
pub use layout::Layout;
pub use resolve::{Builtin, Entity, ModInfo, Modules, ResolveError};
pub use ty::{Ty, TyId, Types};

/// One parsed source file (spec §15.1: one file = one module).
#[derive(Debug)]
pub struct Module {
    /// Module path from the package root: `dsp.voice`.
    pub path: String,
    pub file: FileId,
    pub text: String,
    pub parsed: Parsed,
}

/// A package: its modules and the packages it depends on (`std`).
#[derive(Debug)]
pub struct Package {
    pub name: String,
    pub modules: Vec<Module>,
    pub deps: Vec<Package>,
    /// The standard library is trusted to name effects phase 1 does not
    /// implement (D-08) and to declare `target` functions (D-07).
    pub is_std: bool,
}

/// Packages in analysis order: dependencies first (depth-first), the package
/// itself last. `ModInfo::pkg` indexes this list.
pub fn flatten(pkg: &Package) -> Vec<&Package> {
    let mut out = Vec::new();
    fn go<'a>(p: &'a Package, out: &mut Vec<&'a Package>) {
        for d in &p.deps {
            go(d, out);
        }
        out.push(p);
    }
    go(pkg, &mut out);
    out
}

/// Result of analysis (T2-1 .. T2-4). Everything the body checker needs.
#[derive(Debug, Default)]
pub struct Analysis {
    pub modules: Modules,
    pub defs: Vec<Def>,
    pub types: Types,
    /// Prelude and builtin type names (§15.1).
    pub prelude: HashMap<String, Builtin>,
    /// `TyId` keys of generic builtins in `Modules::assoc_builtin`.
    pub builtin_key: HashMap<ty::BuiltinTy, TyId>,
    /// Typed bodies of functions, tests and `const` initializers (T2-5).
    pub bodies: HashMap<DefId, BodyInfo>,
    /// Values of `const` items evaluated at check time (T2-11).
    pub const_values: HashMap<DefId, ConstValue>,
    /// Typed and rated flow bodies (T3-1), the input of flow lowering (T3-5).
    pub flows: HashMap<DefId, FlowInfo>,
    /// The defs of failed items (`onsa_syntax::ast::Item::failed`, S-59):
    /// their bodies are not checked, and a use of what was not read gets no
    /// diagnostic (R-71, S-260).
    pub failed: HashMap<DefId, onsa_syntax::ast::Failed>,
    pub diagnostics: Vec<Diagnostic>,
}

impl Analysis {
    pub fn def(&self, id: DefId) -> &Def {
        &self.defs[id.0 as usize]
    }

    pub fn defs_of_module(&self, m: ModId) -> impl Iterator<Item = (DefId, &Def)> {
        self.defs.iter().enumerate().filter(move |(_, d)| d.module == m).map(|(i, d)| (DefId(i as u32), d))
    }

    /// The parsed AST of a module, given the package that was analyzed.
    pub fn ast<'a>(&self, pkg: &'a Package, m: ModId) -> Option<&'a Module> {
        let info = self.modules.get(m);
        flatten(pkg).get(info.pkg).and_then(|p| info.module.and_then(|i| p.modules.get(i)))
    }

    /// Module of a file, if the file is one.
    pub fn module_of_file(&self, file: FileId) -> Option<ModId> {
        self.modules.mods.iter().position(|m| m.file == Some(file)).map(|i| ModId(i as u32))
    }

    /// Resolve a path from inside module `from`.
    pub fn resolve_path(&self, from: ModId, path: &onsa_syntax::ast::Path) -> Result<Entity, ResolveError> {
        self.modules.resolve_path(from, path, &self.prelude, &self.defs, &self.builtin_key)
    }

    /// Fully qualified name of a def (`dsp.voice.State`), for diagnostics.
    pub fn qualified_name(&self, id: DefId) -> String {
        let def = self.def(id);
        let mut parts = Vec::new();
        if let Some(owner) = def.owner {
            parts.push(self.qualified_name(owner));
        } else {
            let m = self.modules.get(def.module);
            if !m.path.is_empty() {
                parts.push(m.path.clone());
            }
        }
        parts.push(def.name.clone());
        parts.join(".")
    }

    /// Render a type with user types by their short names.
    pub fn display_type(&self, ty: TyId) -> String {
        self.types.display(ty, &|d| self.def(d).name.clone(), &|i| format!("<{i}>"))
    }

    /// The def is of an item whose heading a syntax error cut
    /// ([`onsa_syntax::ast::Failed::Heading`]): a function of it is an error
    /// to its users (a call of it is not checked against it).
    pub fn heading_failed(&self, id: DefId) -> bool {
        self.failed.get(&id) == Some(&onsa_syntax::ast::Failed::Heading)
    }

    /// The def is of an item a syntax error cut before its end
    /// ([`onsa_syntax::ast::Failed::Body`] or `Heading`): some of its fields,
    /// variants or value were not read, and their uses get no diagnostic
    /// (S-260). An item read whole whose unit has another syntax error
    /// (`Failed::Unit`) is not one.
    pub fn partly_read(&self, id: DefId) -> bool {
        matches!(self.failed.get(&id), Some(onsa_syntax::ast::Failed::Body | onsa_syntax::ast::Failed::Heading))
    }

    /// The longest prefix of `path` that names a def names a def a syntax
    /// error cut (S-260): the rest of the path is not known, and a path that
    /// does not resolve gets no diagnostic (R-71).
    pub fn through_partly_read(&self, from: ModId, path: &onsa_syntax::ast::Path) -> bool {
        for k in (1..path.segments.len()).rev() {
            let prefix = onsa_syntax::ast::Path { segments: path.segments[..k].to_vec(), span: path.span };
            if let Ok(Entity::Def(d)) = self.resolve_path(from, &prefix) {
                return self.partly_read(d);
            }
        }
        false
    }

    pub fn kind_of(&self, ty: TyId) -> Option<Kind> {
        kind::kind_of(self, ty)
    }

    pub fn layout_of(&self, ty: TyId) -> Option<Layout> {
        layout::layout_of(self, ty)
    }
}

/// Analyze a package and its dependencies (T2-1 .. T2-4).
pub fn analyze(pkg: &Package) -> Analysis {
    let mut analysis = sig::collect_and_lower(pkg);
    check_bodies(pkg, &mut analysis);
    analysis
}

/// Body checking (T2-5 .. T2-12): type inference per spec §4.7, generics
/// instantiation, second-class values and closures, argument modes and
/// exclusivity, `rt` rules, scopes / shadowing (E0304), `const` evaluation,
/// typed holes. It gets: `Analysis.defs` (every fn with `FnDef.body`, every
/// flow with `FlowDef.body`, tests), `Analysis.types`, the scopes in
/// `Analysis.modules` (`resolve_path` for paths in expressions; `Field`
/// chains whose head is a module / flow / type name must be read as paths),
/// `Analysis.modules.assoc` for methods and associated items, `kind_of`
/// and `layout_of`. Diagnostics are pushed to `Analysis.diagnostics`; the
/// driver keeps the first per item (P-01).
pub fn check_bodies(pkg: &Package, analysis: &mut Analysis) {
    body::check_all(pkg, analysis);
    let moved = modes::check_all(pkg, analysis);
    rt::check_all(pkg, analysis, &moved);
    effects::check_all(pkg, analysis, &moved);
}

/// The module (file) a def was declared in.
pub(crate) fn module_of_def<'p>(pkg: &'p Package, a: &Analysis, id: DefId) -> Option<&'p Module> {
    let info = a.modules.get(a.def(id).module);
    flatten(pkg).get(info.pkg).and_then(|p| info.module.and_then(|i| p.modules.get(i)))
}
