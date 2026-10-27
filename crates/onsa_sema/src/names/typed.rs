//! The types a path names by an alias or by `Self` (§4.4, §2.2, S-91,
//! S-595): an alias (`type P = Point`) and `Self` in the body of an `impl`
//! stand for their type, once, at the head of a path and after a module.
//! Its members are those of the type, which is the owner of what they name
//! (the type arguments of `type Samples = Buf[F32]`, of `Self` of
//! `impl[T] G[T]`). The one place of this question for a body, a constant
//! expression and a signature (D-15).

use onsa_syntax::ast::{Ident, Path};

use crate::Analysis;
use crate::def::{DefKind, ModId};
use crate::resolve::{Builtin, Entity, ResolveError};
use crate::ty::{Ty, TyId};

/// What the elements after the head of a path name, through the types its
/// aliases and `Self` stand for.
pub(crate) struct Typed {
    /// What each element names, up to the first that is no member.
    pub reached: Vec<Entity>,
    /// The error of that element.
    pub err: Option<ResolveError>,
    /// The type the last alias or `Self` passed stands for.
    pub owner: Option<TyId>,
    /// What the element after the last reached is looked up in: the last
    /// reached (or the head), or the type an alias there stands for.
    pub at: Entity,
}

impl Analysis {
    /// The namespace of the type `ty` an alias or `Self` stands for: a
    /// struct, an enum or a type a flow generates by its def, a builtin type;
    /// none for a type with no members (a tuple, an array, a function, a
    /// type parameter) and for the error type.
    fn type_namespace(&self, ty: TyId) -> Option<Entity> {
        match self.types.get(ty) {
            Ty::Named(d, _) => Some(Entity::Def(*d)),
            Ty::Builtin(b, _) => Some(Entity::Builtin(Builtin::Generic(*b))),
            Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char => Some(Entity::Builtin(Builtin::Scalar(ty))),
            _ => None,
        }
    }

    /// The type the alias `e` stands for, by its namespace: none for what is
    /// no alias, or an alias of a type with no members (`type T2 = (F32,
    /// F32)`, whose `T2.x` has none). `Err(Failed)` for an alias of the error
    /// type, whose declaration has the error (§18.1).
    pub(crate) fn alias_type(&self, e: Entity) -> Result<Option<(Entity, TyId)>, ResolveError> {
        let Entity::Def(d) = e else { return Ok(None) };
        let DefKind::Alias(t) = self.def(d).kind else { return Ok(None) };
        match self.type_namespace(t) {
            Some(ns) => Ok(Some((ns, t))),
            None if matches!(self.types.get(t), Ty::Error) => Err(ResolveError::Failed),
            None => Ok(None),
        }
    }

    /// The head of `path` outside a `use`, and the type it stands for: `Self`
    /// (§2.2, S-595) in the body of an `impl`, whose type is `self_ty` (with
    /// the `impl`'s own type parameters), by its namespace, and out of one
    /// E0302; else a name of the body of `from`. An `impl` of a type with no
    /// members has its error at its heading (held here).
    pub(crate) fn path_head(
        &self,
        from: ModId,
        path: &Path,
        self_ty: Option<TyId>,
    ) -> Result<(Entity, Option<TyId>), ResolveError> {
        let head = &path.segments[0];
        if head.name == "Self" {
            let Some(t) = self_ty else { return Err(ResolveError::SelfOutsideImpl { span: head.span }) };
            return self.type_namespace(t).map(|ns| (ns, Some(t))).ok_or(ResolveError::Failed);
        }
        match self.modules.lookup(from, &head.name, &self.prelude) {
            Some(e) => Ok((e, None)),
            None => Err(self.modules.head_error(from, path, (&self.prelude, &self.defs[..], &self.builtin_key))),
        }
    }

    /// The members of the elements `segs` after `head` (as
    /// [`crate::resolve::Modules::members`]), where an alias stands for its
    /// type; `owner` is the type `head` stands for already (`Self`,
    /// [`Self::path_head`]).
    pub(crate) fn typed_members<'i>(
        &self,
        head: Entity,
        owner: Option<TyId>,
        segs: impl IntoIterator<Item = &'i Ident>,
        from: ModId,
    ) -> Typed {
        let names = (&self.prelude, &self.defs[..], &self.builtin_key);
        let mut t = Typed { reached: Vec::new(), err: None, owner, at: head };
        for seg in segs {
            match self.alias_type(t.at) {
                Ok(Some((ns, ty))) => (t.at, t.owner) = (ns, Some(ty)),
                Ok(None) => {}
                Err(err) => {
                    t.err = Some(err);
                    return t;
                }
            }
            match self.modules.member(t.at, seg, from, names) {
                Ok(next) => {
                    t.reached.push(next);
                    t.at = next;
                }
                Err(err) => {
                    t.err = Some(err);
                    return t;
                }
            }
        }
        t
    }

    /// A path outside a `use`: its head ([`Self::path_head`]), whose error
    /// it is, then its members.
    pub(crate) fn typed_path(
        &self,
        from: ModId,
        path: &Path,
        self_ty: Option<TyId>,
    ) -> Result<(Entity, Typed), ResolveError> {
        let (head, owner) = self.path_head(from, path, self_ty)?;
        Ok((head, self.typed_members(head, owner, &path.segments[1..], from)))
    }
}
