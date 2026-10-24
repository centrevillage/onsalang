//! Each `use` (spec §15.1, S-37, R-250, S-611): its path is absolute, and
//! it is resolved from the tables of the items and the modules alone, never
//! from what another `use` bound. So a `use` means the same wherever it is
//! written and whatever the other `use` of the package are (R-50).

use onsa_diag::{Code, Diagnostic, Stage};
use onsa_syntax::ast::{Ident, Vis};

use crate::Analysis;
use crate::def::ModId;
use crate::resolve::{Binding, Entity, Import, ResolveError};
use crate::sig::Sema;

impl<'p> Sema<'p> {
    /// Binds the names of each `use` of `m` in its scope.
    pub(crate) fn resolve_imports(&mut self, m: ModId) {
        let imports = self.a.modules.get(m).imports.clone();
        for imp in &imports {
            self.resolve_import(m, imp);
        }
    }

    fn resolve_import(&mut self, m: ModId, imp: &Import) {
        let segs = &imp.path.segments;
        // `use a.b.{c, d}` takes `c` and `d` from `a.b`; `use a.b` takes `b`
        // from `a`, and `use a` the head itself.
        let (prefix, names): (&[Ident], Vec<&Ident>) = match &imp.names {
            Some(names) => (segs, names.iter().collect()),
            None => match segs.split_last() {
                Some((last, prefix)) => (prefix, vec![last]),
                None => return,
            },
        };
        let from = match prefix.split_first() {
            None => None,
            Some((head, rest)) => {
                let mut cur = head_of(&self.a, m, head);
                for seg in rest {
                    cur = cur.and_then(|e| step(&self.a, e, seg, m));
                }
                match cur {
                    Ok(e) => Some(e),
                    Err(e) => return self.report_mod(e.into_diagnostic()),
                }
            }
        };
        for name in names {
            let entity = match from {
                None => head_of(&self.a, m, name),
                Some(e) => step(&self.a, e, name, m),
            };
            match entity {
                // SPEC-GAP(S-666): a module of a directory with no file of its
                // own (`a` of `a/b/c.onsa` alone) is taken like a module with
                // no items, as before, until it is decided.
                Ok(e) => self.bind(m, name, e, imp.vis),
                Err(e) => self.report_mod(e.into_diagnostic()),
            }
        }
    }

    /// `name` bound by a `use` in the scope of `m`: E0304 when the scope has
    /// it already (an item of the module, or the name of another `use`).
    fn bind(&mut self, m: ModId, name: &Ident, entity: Entity, vis: Vis) {
        let scope = &mut self.a.modules.get_mut(m).scope;
        match scope.get(&name.name) {
            Some(prev) => {
                let msg = format!("`{}` is already in scope; a name is bound once per module (§15.1)", name.name);
                let d = Diagnostic::new(Stage::Names, Code::E0304, name.span, msg).with_found(name.name.clone());
                let d = d.with_note(prev.span, "first bound here");
                self.report_mod(d);
            }
            None => {
                scope.insert(name.name.clone(), Binding { entity, vis, span: name.span, import: true });
            }
        }
    }
}

/// The head of the path of a `use` in `m` (§15.1, S-37): a module under the
/// package's root or a package `m`'s package depends on.
fn head_of(a: &Analysis, m: ModId, name: &Ident) -> Result<Entity, ResolveError> {
    match a.modules.head(m, &name.name) {
        Some(h) => Ok(Entity::Module(h)),
        None => Err(ResolveError::NotFound { name: name.name.clone(), span: name.span }),
    }
}

/// The element `name` after `cur` in the path of a `use` written in `from`:
/// of a module, its items and its child modules, not the names its `use`
/// bound (R-250, S-611); of anything else, its members.
fn step(a: &Analysis, cur: Entity, name: &Ident, from: ModId) -> Result<Entity, ResolveError> {
    let Entity::Module(m) = cur else {
        return a.modules.member(cur, name, from, &a.defs, &a.builtin_key);
    };
    let info = a.modules.get(m);
    if let Some(b) = info.scope.get(&name.name).filter(|b| !b.import) {
        if a.modules.visible(b.vis, m, from) {
            return Ok(b.entity);
        }
        return Err(ResolveError::NotVisible { name: name.name.clone(), span: name.span, defined: b.span });
    }
    match info.children.get(&name.name) {
        Some(&c) => Ok(Entity::Module(c)),
        None => Err(ResolveError::NotFound { name: name.name.clone(), span: name.span }),
    }
}
