//! The names of a body as a chain (§15.1, §4.5, §2.2): a chain of an
//! expression (`a.b.c`), the path of a hole of a string (§2.4), of a pattern
//! and of a struct literal. The head of a chain is a local, a parameter of
//! the heading (§4.5), a name of the body of the module (`Modules::lookup`:
//! the prelude and the builtin types, the items, the names of the `use`) or,
//! in a flow body, a builtin name of the flow (§2.2, §11.4), in that order;
//! the elements after it are members of what the one before names
//! (`Modules::members`), up to a value, whose fields and methods are the
//! types stage's. The path of a pattern or a struct literal names an item
//! of the module's names alone.
//!
//! A name that is not found, or whose kind the place does not take, is the
//! error of the names stage that stops the walk of the body (§18.1); a name
//! the names stage holds as an error stops it with no diagnostic (S-692).

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{ExprId, ExprKind, Ident, PatId, Path};

use super::kinds::Want;
use super::{Fail, PatRes, PathRes, StructRes, W, Walker};
use crate::Analysis;
use crate::def::GenericKind;
use crate::flow_names::FlowBuiltin;
use crate::names::BuiltinMember;
use crate::resolve::NameKind;
use crate::resolve::{Builtin, Entity, ResolveError};
use crate::ty::TyId;

/// What the types stage does with the end of a chain of names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Place {
    /// A value, whose fields may follow.
    Value,
    /// The callee of the call `.0` (`f(x)`, `a.m(x)`, `x.m!(y)`): its last
    /// name may be a method of the value before it, or an associated function.
    Callee(ExprId),
    /// The callee of an instance (`f~(x)`): the flow stage reads it and
    /// reports its errors (W4-12); the walk records what it finds alone.
    Instance,
    /// The `[…]` of a callee after a field (`p.m[I32](1)`): the type
    /// arguments of a method or an index, which the types stage tells apart
    /// (§4.5); the walk records what it finds, but a method named through
    /// its type, neither of them (E0308).
    TypeOrValue,
}

/// Whether the entity is a value at the place of a value: a function (of
/// an `extern` block too, a value of the error type), a constant, a variant,
/// a constructor of the prelude or `panic` ([`NameKind::is_value`]). The
/// fields and methods of a value follow it; a name after what is neither a
/// value nor a namespace has no members.
pub(crate) fn is_value(a: &Analysis, e: Entity) -> bool {
    NameKind::of(e, &a.defs).is_some_and(NameKind::is_value)
}

/// The span from the first name of `segs` to its last.
pub(super) fn span_of(segs: &[&Ident]) -> Span {
    let (first, last) = (segs[0].span, segs[segs.len() - 1].span);
    Span::new(first.file, first.start, last.end)
}

fn path_of(segs: &[&Ident]) -> Path {
    Path { segments: segs.iter().map(|&s| s.clone()).collect(), span: span_of(segs) }
}

impl<'a> Walker<'a> {
    /// The records of the chain of names `e` ends at the place `place`, at
    /// the nodes of the names it resolves; a node that is no chain walks its
    /// children.
    pub(super) fn name_at(&mut self, e: ExprId, place: Place) -> W {
        let Some(chain) = self.chain(e) else {
            return match &self.ast.expr(e).kind {
                // A field of a value that is no name (`f().x`).
                ExprKind::Path(_) | ExprKind::Field { .. } => self.exprs(self.ast.sub_exprs(e)),
                _ => self.expr(e),
            };
        };
        let names: Vec<&Ident> = chain.iter().map(|&(_, n)| n).collect();
        let (records, fail) = self.resolve(&names, place);
        for (&(e, _), r) in chain.iter().zip(records) {
            self.out.paths.insert(e, r);
        }
        match fail {
            Some(f) if place != Place::Instance => Err(self.fail(f)),
            _ => Ok(()),
        }
    }

    /// The records of the names of a chain, one for each element from its
    /// head to the last one the names stage resolves, and the error that
    /// stopped it.
    pub(super) fn resolve(&mut self, segs: &[&Ident], place: Place) -> (Vec<PathRes>, Option<Fail>) {
        let head = segs[0];
        if let Some(b) = self.lookup(head) {
            return (vec![PathRes::Local(b)], None);
        }
        if head.name == "self" {
            let d = Diagnostic::new(Stage::Names, Code::E0302, head.span, "`self` is only available inside a method");
            return (Vec::new(), Some(Fail::Report(d.with_found("self"))));
        }
        match self.heading(head) {
            Some(r @ PathRes::ConstParam(_)) => return (vec![r], None),
            // A type parameter is a type (§15.1), and no namespace of members
            // (`T.ZERO` from W4-04 U6).
            Some(r) => {
                let kind = (segs.len() == 1).then(|| self.kind_fail(NameKind::Type, segs, place)).flatten();
                return (vec![r], Some(kind.unwrap_or_else(|| self.not_found(head))));
            }
            None => {}
        }
        let a = self.a;
        if let Some(b) = self.flow_name(&head.name) {
            return self.flow_builtin(b, segs, place);
        }
        let (first, owner) = match a.path_head(self.m, &path_of(segs), self.self_ty) {
            Ok(found) => found,
            Err(ResolveError::Failed) => return (Vec::new(), Some(Fail::Held)),
            Err(ResolveError::NotFound { .. }) => return (Vec::new(), Some(self.not_found(head))),
            Err(err) => return (Vec::new(), Some(Fail::Report(err.into_diagnostic()))),
        };
        let typed = a.typed_members(first, owner, segs[1..].iter().copied(), self.m);
        let (err, owner, of) = (typed.err, typed.owner, typed.at);
        let mut out = Vec::new();
        let mut cur = first;
        for e in typed.reached {
            out.push(PathRes::Namespace(cur));
            cur = e;
        }
        // The element that is no member of `of` (the last reached, or the
        // type an alias there stands for), and whether it is the name of the
        // method of a call.
        let at = out.len() + 1;
        let method = matches!(place, Place::Callee(_) | Place::Instance) && at + 1 == segs.len();
        // `Option.None`, `Result.Ok(1)`, `O.None` (S-607); the callee of an
        // instance is the flow stage's (W4-12).
        let (variant, called) = match &err {
            Some(ResolveError::NotFound { .. }) if place != Place::Instance => {
                // A method of a builtin type with a name after it is no value
                // either (`Str.len.zz`, as `P.get.zz`).
                let place = if at + 1 == segs.len() { place } else { Place::Value };
                let called = self.builtin_called(of, &segs[..=at], place);
                (self.qualified_variant(&path_of(segs), at, of), called)
            }
            _ => (None, None),
        };
        let assoc = match &err {
            Some(ResolveError::NotFound { .. }) => self.builtin_assoc(of, segs[at], method, owner),
            _ => None,
        };
        let fail = match err {
            // An alias of the error type stands for a failed name (§18.1, S-728).
            None if a.alias_type(cur).is_err() => Some(Fail::Held),
            None => {
                out.push(PathRes::Item { entity: cur, owner });
                let kind = NameKind::of(cur, &a.defs);
                kind.and_then(|k| self.kind_fail(k, segs, place)).or_else(|| self.method_form(cur, segs, place))
            }
            // A value, or the receiver of a method (what is no value there
            // is the types stage's error, unless the check does not read it);
            // a method named through its type is no value whatever follows it.
            Some(ResolveError::NotANamespace { .. }) if is_value(a, cur) => {
                let method = self.method_form(cur, &segs[..at], Place::Value);
                if method.is_none() {
                    out.push(PathRes::Item { entity: cur, owner });
                }
                method
            }
            Some(ResolveError::NotANamespace { kind: Some(k), .. }) if !k.is_namespace() => {
                Some(Fail::Report(self.no_namespace(&segs[..=at], k)))
            }
            // What is no namespace before the method of a call (a namespace
            // with no such member is the E0302 below: `Alloc.x()`, R-300).
            Some(err @ ResolveError::NotANamespace { kind, .. })
                if method
                    && !kind.is_some_and(NameKind::is_namespace)
                    && !a.unread(self.m, &path_of(&segs[..=at]), &err) =>
            {
                out.push(PathRes::Item { entity: cur, owner });
                None
            }
            Some(ResolveError::NotFound { .. }) if variant.is_some() => variant.map(Fail::Report),
            Some(ResolveError::NotFound { .. }) if called.is_some() => called,
            Some(ResolveError::NotFound { .. }) if assoc.is_some() => {
                out.extend([PathRes::Namespace(cur)].into_iter().chain(assoc));
                None
            }
            // An associated function of a builtin type in a constant
            // expression (`[0.0; F32.from_bits]`): a value that is no
            // constant, the E0417 of the types stage, which reads the name
            // again (§4.5, W5-08).
            Some(ResolveError::NotFound { .. })
                if self.in_const
                    && at + 1 == segs.len()
                    && crate::names::builtin_member(a, of, &segs[at].name) == Some(BuiltinMember::Function) =>
            {
                out.push(PathRes::Namespace(cur));
                None
            }
            Some(err) => Some(self.member_error(&path_of(&segs[..=at]), self.written(err, &segs[..=at], owner))),
        };
        // A chain held as an error has no record, as one held at its head
        // (`BodyNames`): the types stage stops at its head.
        if matches!(fail, Some(Fail::Held)) {
            out.clear();
        }
        (out, fail)
    }

    /// The error of a path that did not resolve (`err`): none for what the
    /// check does not read ([`Analysis::unread`]), else its diagnostic.
    fn member_error(&self, path: &Path, err: ResolveError) -> Fail {
        match self.a.unread(self.m, path, &err) {
            true => Fail::Held,
            false => Fail::Report(err.into_diagnostic()),
        }
    }

    /// E0302 for the head `head` of a chain not found: one form wherever
    /// the chain is (a value, a callee, a hole, a constant expression).
    fn not_found(&self, head: &Ident) -> Fail {
        Fail::Report(ResolveError::NotFound { name: head.name.clone(), span: head.span }.into_diagnostic())
    }

    /// E0302 for the variant of the prelude `path[at]` named through its
    /// type `of` (`Option.None`, `Result.Ok(1)`, `Option.None =>`; §4.1,
    /// S-607): the variants are names of the prelude, not members of the
    /// type. The candidate takes off the qualifier, and then reads the name
    /// of the prelude (none when an item clashes with it, an E0304, and in a
    /// constant expression, where a variant is no constant); the type
    /// arguments of the qualifier go to the name from W5-10.
    fn qualified_variant(&self, path: &Path, at: usize, of: Entity) -> Option<Diagnostic> {
        let a = self.a;
        let name = &path.segments[at];
        let variant = a.prelude.get(&name.name).copied()?;
        let (Entity::Builtin(Builtin::Generic(ty)), Entity::Builtin(b)) = (of, variant) else { return None };
        if super::super::prelude::variant_of(b) != Some(ty) {
            return None;
        }
        let msg = format!("`{}` is a variant of the prelude, not a member of the type `{}`", name.name, ty.name());
        let d = Diagnostic::new(Stage::Names, Code::E0302, name.span, msg)
            .with_found(name.name.clone())
            .with_rule(format!("a variant of the prelude is written by its name alone (`{}`, §4.1)", name.name));
        if self.in_const {
            return Some(d);
        }
        let names = (&a.prelude, &a.defs[..], &a.builtin_key);
        Some(match a.modules.body_fix(self.m, path, at, Some(variant), names) {
            Ok(fix) => d.with_fix(fix),
            // An item that clashes with the name of the prelude (E0304).
            Err(_) => d,
        })
    }

    /// The builtin name of a flow `name` is, in a flow body, where no item
    /// or `use` takes it (that one is an E0304, and held as an error).
    pub(super) fn flow_name(&self, name: &str) -> Option<FlowBuiltin> {
        let a = self.a;
        let found = a.modules.lookup(self.m, name, &a.prelude).is_some() || a.modules.held_as_error(self.m, name);
        FlowBuiltin::named(name).filter(|_| self.flow && !found)
    }

    /// A builtin name of a flow body at the head of `segs` (§2.2, §11.4):
    /// the callee of a call (`prev~(x)`, `sample_rate()`; the flow stage
    /// reads it, and its marks, E0811, E0812); anywhere else E0308 (S-720,
    /// the one place of its error in a body).
    fn flow_builtin(&self, b: FlowBuiltin, segs: &[&Ident], place: Place) -> (Vec<PathRes>, Option<Fail>) {
        let called = match place {
            Place::Instance => true,
            Place::Callee(_) => segs.len() == 1,
            Place::Value | Place::TypeOrValue => false,
        };
        let fail = (!called).then(|| Fail::Report(b.misplaced(segs.iter().map(|s| s.span), self.text)));
        (vec![PathRes::FlowBuiltin(b)], fail)
    }

    /// The error `err` of the element after `segs[..len - 1]` as written,
    /// when an alias or `Self` passed (`owner`): `Q.nope`, not the name of the
    /// type it stands for (W4-04 U6).
    fn written(&self, err: ResolveError, segs: &[&Ident], owner: Option<TyId>) -> ResolveError {
        match err {
            ResolveError::NotFound { span, .. } if owner.is_some() => {
                ResolveError::NotFound { name: self.src(span_of(segs)), span }
            }
            err => err,
        }
    }

    /// The type or const parameter `name` of the heading.
    fn heading(&self, name: &Ident) -> Option<PathRes> {
        let (i, g) = (0..).zip(self.generics).find(|(_, g)| g.name == name.name)?;
        self.a.note_use(g.span, name.span);
        match g.kind {
            GenericKind::Type { .. } => Some(PathRes::TypeParam(i)),
            GenericKind::Const(_) => Some(PathRes::ConstParam(i)),
            GenericKind::Effect => None,
        }
    }

    /// An associated item `name` of the builtin type `of` in the compiler's
    /// table: a constant (`F32.PI`), or, as the name of the method of a call,
    /// a function (`Buf.zeroed`, whose call the types stage reads). A name
    /// the table has not is not found (E0302, R-249: `F32.y`, `F32.y(1.0)`).
    fn builtin_assoc(&self, of: Entity, name: &Ident, method: bool, owner: Option<TyId>) -> Option<PathRes> {
        match crate::names::builtin_member(self.a, of, &name.name)? {
            BuiltinMember::Constant => {}
            BuiltinMember::Function if method => {}
            BuiltinMember::Function | BuiltinMember::Method { .. } => return None,
        }
        let ty = crate::names::builtin_ty(self.a, of)?;
        Some(PathRes::BuiltinAssoc { ty, name: name.name.clone(), owner })
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

    /// The item a path of a pattern or a struct literal names, of the names
    /// of the module (as a type is named), and the type an alias or `Self`
    /// before it stands for; a path that ends at an alias or at `Self` names
    /// the type (`P { x }`, `Self { x }`). A name of a kind the place does
    /// not take (`want`) is E0308 (§15.1, §7): a struct literal and a struct
    /// pattern name a type, the path of any other pattern a variant or a
    /// constant (the form of each is the types stage's).
    fn item(&self, path: &Path, want: Want) -> Result<(Entity, Option<TyId>), Fail> {
        let a = self.a;
        let segs: Vec<&Ident> = path.segments.iter().collect();
        let head = segs[0];
        let error = |err| self.member_error(path, err);
        // A builtin name of a flow in a pattern (`prev(z) =>`, S-720).
        if let Some(b) = self.flow_name(&head.name) {
            return Err(Fail::Report(b.misplaced(path.segments.iter().map(|s| s.span), self.text)));
        }
        // A type or const parameter in a pattern (S-185) or at the head of
        // a struct literal (`M { x: 1 }`, R-302).
        if let ([_], Some(r)) = (&segs[..], self.heading(head)) {
            let kind = if matches!(r, PathRes::ConstParam(_)) { NameKind::ConstParam } else { NameKind::Type };
            // A type parameter is a type, and no struct (`T { x: 1 }`).
            let no_struct = || Fail::Report(crate::body::not_a_struct(head.name.clone(), head.span));
            return Err(self.want(kind, &segs, want).unwrap_or_else(no_struct));
        }
        let (first, typed) = a.typed_path(self.m, path, self.self_ty).map_err(error)?;
        let at = typed.reached.len() + 1;
        match typed.err {
            Some(err @ ResolveError::NotFound { .. }) => match self.qualified_variant(path, at, typed.at) {
                Some(d) => Err(Fail::Report(d)),
                // An associated name of a builtin type (`F32.PI { x: 1 }`, R-302).
                None => match (at + 1 == segs.len())
                    .then(|| crate::names::builtin_member(a, typed.at, &segs[at].name))
                    .flatten()
                    .and_then(|k| self.want(k.kind(), &segs, want))
                {
                    Some(f) => Err(f),
                    None => Err(error(self.written(err, &segs[..=at], typed.owner))),
                },
            },
            Some(err) => Err(error(err)),
            None => {
                let end = typed.reached.last().copied().unwrap_or(first);
                let (entity, owner) = match a.alias_type(end).map_err(error)? {
                    Some((ns, t)) => (ns, Some(t)),
                    // An alias of no struct: the types stage reads the alias.
                    None => (end, typed.owner),
                };
                match NameKind::of(entity, &a.defs).and_then(|k| self.want(k, &segs, want)) {
                    Some(f) => Err(f),
                    None => Ok((entity, owner)),
                }
            }
        }
    }

    /// The item the path of the pattern `p` names (§7).
    pub(super) fn ctor(&mut self, p: PatId, path: &Path, want: Want) -> W {
        match self.item(path, want) {
            Ok((entity, owner)) => {
                self.out.pats.insert(p, PatRes::Ctor { entity, owner });
                Ok(())
            }
            Err(f) => self.fail_at_let(f),
        }
    }

    /// The item the path of the struct literal `e` names.
    pub(super) fn struct_lit(&mut self, e: ExprId, path: &Path) -> W {
        let (entity, owner) = self.item(path, Want::Type).map_err(|f| self.fail(f))?;
        self.out.structs.insert(e, StructRes { entity, owner });
        Ok(())
    }
}
