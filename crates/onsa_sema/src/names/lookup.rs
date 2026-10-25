//! The lookups of a path (spec §15.1, R-39, S-611, R-250): its head in the
//! body of a module, and each element after it in what the one before names.
//! A `use` reads the same [`Modules::member`] after its own head
//! ([`Modules::head`]).

use std::collections::HashMap;

use onsa_diag::Fix;
use onsa_syntax::ast::{Ident, Path};

use crate::def::{Def, DefKind, ModId};
use crate::resolve::{Builtin, Entity, Modules, ResolveError, UseAt};
use crate::ty::{BuiltinTy, TyId};

impl Modules {
    /// The head `name` of a path in the body of `from` (§15.1): the prelude
    /// and the builtin types, then the module's items, then the names its
    /// `use` bound. Never another module or a package: they are named
    /// through a `use` alone (R-39).
    pub fn lookup(&self, from: ModId, name: &str, prelude: &HashMap<String, Builtin>) -> Option<Entity> {
        let info = self.get(from);
        if let Some(&b) = prelude.get(name) {
            return Some(Entity::Builtin(b));
        }
        if let Some(&d) = info.items.get(name) {
            return Some(Entity::Def(d));
        }
        info.uses.get(name).and_then(|u| u.entity())
    }

    /// The head of `path` in the body of `from` that is not in its body:
    /// E0302. When the head is one of the path of a `use` (§15.1), it is the
    /// path with no `use`, and when a member follows the head (`std.math.abs`,
    /// `util.f`) its candidate adds `use head` unless the `use` closes a
    /// cycle; a module or a package alone at the place of a value or a type
    /// (`let x = util`, `x: std`) is not fixed by the `use`, and has none. Nor
    /// has a head a `use` cannot bind ([`super::clash::unbindable`]).
    fn not_in_body(&self, from: ModId, path: &Path) -> ResolveError {
        let head = &path.segments[0];
        let (name, span) = (head.name.clone(), head.span);
        // SPEC-GAP(S-673): the head of the package's own name or of the
        // module's own (`fx.util.helper()`, `main.other()`) is taken as any
        // other head: `use main` for a module under the root, none for the
        // package (not a head of a `use`); a head alone has none.
        if self.head(from, &head.name).is_none() {
            return ResolveError::NotFound { name, span };
        }
        let info = self.get(from);
        let head_path = Path { segments: vec![head.clone()], span };
        let fix = match (info.file, info.use_at) {
            _ if path.segments.len() < 2 || self.closes_cycle(from, &head_path) => None,
            // SPEC-GAP(S-674): a head that is a reserved word (`static.tick()`)
            // is this E0302, and has no candidate, as a head no `use` binds.
            _ if super::clash::unbindable(&name).is_some() => None,
            (Some(file), Some(at)) => {
                let title = format!("add `use {name}`");
                Some(match at {
                    UseAt::After(offset) => Fix::insert(title, file, offset, format!("\nuse {name}")),
                    UseAt::Before(offset) => Fix::insert(title, file, offset, format!("use {name}\n")),
                })
            }
            _ => None,
        };
        ResolveError::NeedsUse { name, span, fix }
    }

    fn builtin_member(&self, key: TyId, name: &Ident, from: ModId, defs: &[Def]) -> Result<Entity, ResolveError> {
        if let Some(a) = self.assoc_builtin.get(&key).and_then(|m| m.get(&name.name)) {
            let adef = &defs[a.0 as usize];
            if self.visible(adef.vis, adef.module, from) {
                return Ok(Entity::Member(*a));
            }
            return Err(ResolveError::NotVisible { name: name.name.clone(), span: name.span, defined: adef.name_span });
        }
        Err(ResolveError::NotFound { name: name.name.clone(), span: name.span })
    }

    /// A member `name` of `entity`, as seen from `from`. Of a module, its
    /// namespace: its items and its child modules, not the names its `use`
    /// bound (S-611, R-250). `builtin_key` maps a generic builtin to the
    /// `TyId` its associated items are keyed by.
    pub fn member(
        &self,
        entity: Entity,
        name: &Ident,
        from: ModId,
        defs: &[Def],
        builtin_key: &HashMap<BuiltinTy, TyId>,
    ) -> Result<Entity, ResolveError> {
        match entity {
            Entity::Module(m) => {
                // SPEC-GAP(S-677): a child module before an item of its name,
                // which is an E0304 (§15.1, `crate::names::clash`).
                let info = self.get(m);
                if let Some(&c) = info.children.get(&name.name) {
                    return Ok(Entity::Module(c));
                }
                if let Some(&d) = info.items.get(&name.name) {
                    let def = &defs[d.0 as usize];
                    if self.visible(def.vis, m, from) {
                        return Ok(Entity::Def(d));
                    }
                    return Err(ResolveError::NotVisible {
                        name: name.name.clone(),
                        span: name.span,
                        defined: def.name_span,
                    });
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

    /// Resolve a full path written outside a `use` in `from`.
    pub fn resolve_path(
        &self,
        from: ModId,
        path: &Path,
        prelude: &HashMap<String, Builtin>,
        defs: &[Def],
        builtin_key: &HashMap<BuiltinTy, TyId>,
    ) -> Result<Entity, ResolveError> {
        let first = &path.segments[0];
        let mut cur = self.lookup(from, &first.name, prelude).ok_or_else(|| self.not_in_body(from, path))?;
        for seg in &path.segments[1..] {
            cur = self.member(cur, seg, from, defs, builtin_key)?;
        }
        Ok(cur)
    }
}
