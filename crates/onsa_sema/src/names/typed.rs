//! The types a path names by an alias or by `Self` (§4.4, §2.2, S-91,
//! S-595): an alias (`type P = Point`) and `Self` in the body of an `impl`
//! stand for their type, once, at the head of a path and after a module.
//! Its members are those of the type, which is the owner of what they name
//! (the type arguments of `type Samples = Buf[F32]`, of `Self` of
//! `impl[T] G[T]`). The one place of this question for a body, a constant
//! expression and a signature (D-15).

use onsa_syntax::ast::{Ident, Path};

use crate::def::{DefKind, ModId};
use crate::resolve::{Builtin, Entity, NameKind, ResolveError};
use crate::ty::{Ty, TyId};
use crate::{Analysis, builtin};

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

/// What a path names at its end ([`Analysis::path_end`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PathEnd {
    Entity(Entity),
    /// An associated name of the builtin type `of` the compiler's table has
    /// (`F32.PI`, `F32.from_bits`, `Str.len`).
    Builtin {
        of: Entity,
        member: BuiltinMember,
    },
}

/// What an associated name of a builtin type is in the compiler's table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BuiltinMember {
    /// `F32.PI`.
    Constant,
    /// An associated function: `F32.from_bits`, `Buf.zeroed`.
    Function,
    /// A method (`Str.len`), called with `!` or not.
    Method { bang: bool },
}

impl BuiltinMember {
    /// Its kind (§15.1): a method is a function.
    pub(crate) fn kind(self) -> NameKind {
        match self {
            BuiltinMember::Constant => NameKind::Constant,
            BuiltinMember::Function | BuiltinMember::Method { .. } => NameKind::Function,
        }
    }
}

impl PathEnd {
    /// The kind of what it names, at `span`.
    pub(crate) fn kind(self, a: &Analysis, span: onsa_diag::Span) -> NameKind {
        match self {
            PathEnd::Entity(e) => NameKind::of_named(e, &a.defs, span),
            PathEnd::Builtin { member, .. } => member.kind(),
        }
    }

    /// Whether it is a method named through its type (`P.get`, `Str.len`),
    /// and whether it is called with `!` (an `inout self`, §6.2).
    pub(crate) fn method(self, a: &Analysis) -> Option<bool> {
        match self {
            PathEnd::Entity(Entity::Member(d)) => match &a.def(d).kind {
                DefKind::Fn(f) => Some(f.self_mode? == onsa_syntax::ast::Mode::Inout),
                _ => None,
            },
            PathEnd::Builtin { member: BuiltinMember::Method { bang }, .. } => Some(bang),
            PathEnd::Entity(_) | PathEnd::Builtin { .. } => None,
        }
    }
}

/// A function declared with `self` outside an `impl` (`fn f(self)`), whose
/// E0002 is its declaration's (§6.2): what names it sees a declaration with
/// an error, a value of the error type with no diagnostic (§18.1). A method
/// is a member of an `impl`, named through its type ([`PathEnd::method`]).
pub(crate) fn self_outside_impl(a: &Analysis, entity: Entity) -> bool {
    let (Entity::Def(d) | Entity::Member(d)) = entity else { return false };
    let def = a.def(d);
    def.owner.is_none() && def.as_fn().is_some_and(|f| f.self_mode.is_some())
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

    /// What `path` outside a body names (a type, a bound, an effect row, a
    /// constant expression): [`Self::typed_path`] to its end, where an
    /// associated name of a builtin type the compiler's table has is found
    /// with what it is ([`builtin_member`]). The error of what it does not
    /// find.
    pub(crate) fn path_end(&self, from: ModId, path: &Path, self_ty: Option<TyId>) -> Result<PathEnd, ResolveError> {
        let (head, typed) = self.typed_path(from, path, self_ty)?;
        let Some(err) = typed.err else {
            return Ok(PathEnd::Entity(typed.reached.last().copied().unwrap_or(head)));
        };
        let at = typed.reached.len() + 1;
        if let ResolveError::NotFound { .. } = err {
            match builtin_member(self, typed.at, &path.segments[at].name) {
                Some(member) if at + 1 == path.segments.len() => return Ok(PathEnd::Builtin { of: typed.at, member }),
                // A member with a name after it (`Str.len.zz`, `F32.PI.x`),
                // as `P.get.zz` and `P.N.x`.
                Some(member) => {
                    let (name, span) = (path.segments[at].name.clone(), path.segments[at + 1].span);
                    return Err(ResolveError::NotANamespace { name, span, kind: Some(member.kind()) });
                }
                None => {}
            }
        }
        match err {
            // As written, when an alias or `Self` passed (`Self.nope`, not the
            // name of the type it stands for; W4-04 U6).
            ResolveError::NotFound { span, .. } if typed.owner.is_some() => {
                let names = path.segments[..=at].iter().map(|s| s.name.as_str());
                Err(ResolveError::NotFound { name: names.collect::<Vec<_>>().join("."), span })
            }
            err => Err(err),
        }
    }
}

/// The builtin type `of` names, by its key (a generic type by its own).
pub(crate) fn builtin_ty(a: &Analysis, of: Entity) -> Option<TyId> {
    match of {
        Entity::Builtin(Builtin::Scalar(t)) => Some(t),
        Entity::Builtin(Builtin::Generic(g)) => a.builtin_key.get(&g).copied(),
        _ => None,
    }
}

/// What the associated name `name` of the builtin type `of` is in the
/// compiler's table (§15.1): a method (`Str.len`), a constant (`F32.PI`) or
/// an associated function (`F32.from_bits`); none of a name it has not. The
/// one place of this question (D-15).
pub(crate) fn builtin_member(a: &Analysis, of: Entity, name: &str) -> Option<BuiltinMember> {
    let ty = builtin_ty(a, of)?;
    let (scalar, generic) = match of {
        Entity::Builtin(Builtin::Generic(g)) => (None, Some(g)),
        _ => (Some(ty), None),
    };
    if let Some(bang) = builtin::method_bang(&a.types, ty, name) {
        return Some(BuiltinMember::Method { bang });
    }
    if scalar.is_some_and(|t| builtin::has_assoc_const(&a.types, t, name)) {
        return Some(BuiltinMember::Constant);
    }
    builtin::has_assoc_fn(&a.types, scalar, generic, name).then_some(BuiltinMember::Function)
}
