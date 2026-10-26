//! The names of a body as a chain (§15.1, §4.5, §2.2): a chain of an
//! expression (`a.b.c`), the path of a hole of a string (§2.4), of a pattern
//! and of a struct literal. The head is a local, a parameter of the heading
//! (§4.5), a name of the body of the module (`Modules::lookup`: the prelude
//! and the builtin types, the items, the names of the `use`) or, in a flow
//! body, a builtin name of the flow (§2.2, §11.4), in that order; each
//! element after it is a member of what the one before names
//! (`Modules::member`), up to a value, whose fields and methods are the
//! types stage's.

use onsa_syntax::ast::{ExprId, ExprKind, Ident, PatId, Path};

use super::{PatRes, PathRes, StructRes, Walker};
use crate::ResolveError;
use crate::builtin;
use crate::def::{DefKind, GenericKind};
use crate::flow_names::FlowBuiltin;
use crate::resolve::{Builtin, Entity};

impl<'a> Walker<'a> {
    /// The records of the names of a path, one for each element from its
    /// head to the last one the names stage resolves (what follows is a
    /// field or a method of a value). None for a name not found and a name
    /// the names stage holds as an error (§18.1, whose diagnostics are the
    /// types stage's until W4-04 U3a), nor through an alias or `Self`, which
    /// W4-04 U6 resolves.
    pub(super) fn resolve(&mut self, segs: &[&Ident]) -> Option<Vec<PathRes>> {
        let head = &segs[0].name;
        if let Some(b) = self.lookup(head) {
            return Some(vec![PathRes::Local(b)]);
        }
        if let Some(r) = self.heading(head) {
            return Some(vec![r]);
        }
        let a = self.a;
        let mut cur = match a.modules.lookup(self.m, head, &a.prelude) {
            Some(e) => e,
            None if a.modules.held_as_error(self.m, head) => return None,
            None => {
                let builtin = FlowBuiltin::named(head).filter(|_| self.flow)?;
                return Some(vec![PathRes::FlowBuiltin(builtin)]);
            }
        };
        let mut out = Vec::new();
        for seg in &segs[1..] {
            if self.is_alias(cur) {
                return None;
            }
            match a.modules.member(cur, seg, self.m, (&a.prelude, &a.defs, &a.builtin_key)) {
                Ok(next) => {
                    out.push(PathRes::Namespace(cur));
                    cur = next;
                }
                // A value: the rest is its fields and methods.
                Err(ResolveError::NotANamespace { .. }) => break,
                Err(ResolveError::NotFound { .. }) => {
                    let assoc = self.builtin_assoc(cur, &seg.name)?;
                    out.extend([PathRes::Namespace(cur), assoc]);
                    return Some(out);
                }
                Err(_) => return None,
            }
        }
        if self.is_alias(cur) {
            return None;
        }
        out.push(PathRes::Item { entity: cur, owner: None });
        Some(out)
    }

    /// The type or const parameter `name` of the heading.
    fn heading(&self, name: &str) -> Option<PathRes> {
        let (i, g) = (0..).zip(self.generics).find(|(_, g)| g.name == name)?;
        match g.kind {
            GenericKind::Type { .. } => Some(PathRes::TypeParam(i)),
            GenericKind::Const(_) => Some(PathRes::ConstParam(i)),
            GenericKind::Effect => None,
        }
    }

    /// A path through an alias is resolved from W4-04 U6 (S-91).
    fn is_alias(&self, e: Entity) -> bool {
        matches!(e, Entity::Def(d) if matches!(self.a.def(d).kind, DefKind::Alias(_)))
    }

    /// An associated item of a builtin type in the table of the compiler's
    /// (`F32.PI`, `Buf.zeroed`, `crate::builtin`).
    fn builtin_assoc(&self, of: Entity, name: &str) -> Option<PathRes> {
        let a = self.a;
        let (scalar, generic) = match of {
            Entity::Builtin(Builtin::Scalar(t)) => (Some(t), None),
            Entity::Builtin(Builtin::Generic(g)) => (None, Some(g)),
            _ => return None,
        };
        let ty = scalar.or_else(|| generic.and_then(|g| a.builtin_key.get(&g).copied()))?;
        builtin::has_assoc(&a.types, scalar, generic, name).then(|| PathRes::BuiltinAssoc { ty, name: name.into() })
    }

    /// The chain of names `e` ends (`a.b.c` is `Field(Field(Path(a), b), c)`),
    /// from its head, with the node of each; none when its head is no name
    /// (`f().x`).
    pub(super) fn chain(&self, e: ExprId) -> Option<Vec<(ExprId, &'a Ident)>> {
        let ast = self.ast;
        let mut out = Vec::new();
        let mut cur = e;
        loop {
            match &ast.expr(cur).kind {
                ExprKind::Field { base, name } => {
                    out.push((cur, name));
                    cur = *base;
                }
                ExprKind::Path(p) if p.segments.len() == 1 => {
                    out.push((cur, &p.segments[0]));
                    out.reverse();
                    return Some(out);
                }
                _ => return None,
            }
        }
    }

    /// The records of a chain, at the nodes of the names it resolves.
    pub(super) fn name_chain(&mut self, chain: &[(ExprId, &Ident)]) {
        let names: Vec<&Ident> = chain.iter().map(|&(_, n)| n).collect();
        for (&(e, _), r) in chain.iter().zip(self.resolve(&names).unwrap_or_default()) {
            self.out.paths.insert(e, r);
        }
    }

    /// The item a path names whole: none when it ends before its last name
    /// (at a value) or at no item.
    fn item(&mut self, path: &Path) -> Option<Entity> {
        let records = self.resolve(&path.segments.iter().collect::<Vec<_>>())?;
        match records.last() {
            Some(PathRes::Item { entity, .. }) if records.len() == path.segments.len() => Some(*entity),
            _ => None,
        }
    }

    /// The item the path of the pattern `p` names (§7).
    pub(super) fn ctor(&mut self, p: PatId, path: &Path) {
        if let Some(entity) = self.item(path) {
            self.out.pats.insert(p, PatRes::Ctor { entity, owner: None });
        }
    }

    /// The def the path of the struct literal `e` names.
    pub(super) fn struct_lit(&mut self, e: ExprId, path: &Path) {
        if let Some(Entity::Def(def) | Entity::Member(def)) = self.item(path) {
            self.out.structs.insert(e, StructRes { def, owner: None });
        }
    }
}
