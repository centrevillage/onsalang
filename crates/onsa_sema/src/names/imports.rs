//! Each `use` (spec §15.1, S-37, R-250, S-611): its path is absolute, and
//! it is resolved from the tables of the items and the modules alone, never
//! from what another `use` bound. So a `use` means the same wherever it is
//! written and whatever the other `use` of the package are (R-50).

use onsa_syntax::ast::Ident;

use crate::Analysis;
use crate::def::ModId;
use crate::resolve::{Entity, Import, ResolveError, UseBinding};
use crate::sig::Sema;

impl<'p> Sema<'p> {
    /// Binds the names of each `use` of `m` in its body.
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
                // A module of a directory with no file of its own (`a` of
                // `a/b/c.onsa` alone) is a module with no items (S-666).
                Ok(e) => self.bind(m, name, e),
                Err(e) => self.report_mod(e.into_diagnostic()),
            }
        }
    }

    /// `name` bound by a `use` in the body of `m`: the first of a name is in
    /// the table, and the clashes are E0304 after every `use`
    /// (`crate::names::clash`).
    fn bind(&mut self, m: ModId, name: &Ident, entity: Entity) {
        let info = self.a.modules.get_mut(m);
        info.bound.push((name.name.clone(), name.span));
        info.uses.entry(name.name.clone()).or_insert(UseBinding::Bound { entity, span: name.span });
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

/// The element `name` after `cur` in the path of a `use` written in `from`
/// (R-250, S-611): the same as after the head of any other path.
fn step(a: &Analysis, cur: Entity, name: &Ident, from: ModId) -> Result<Entity, ResolveError> {
    a.modules.member(cur, name, from, &a.defs, &a.builtin_key)
}
