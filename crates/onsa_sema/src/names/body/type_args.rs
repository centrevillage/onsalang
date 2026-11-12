//! The type arguments `::[…]` of a chain of names (§4.5, S-239, S-306,
//! S-978, S-979): each goes to the name before it. After a type
//! (`Buf::[F32]` of `Buf::[F32].zeroed(4)`), they make the type the next name
//! is a member of, lowered after the walk (`lower_types`) into its record's
//! `owner`; after a local, they are the E0308 of the walk; after any other
//! name that declares no type parameters (a constant, `Self`, a module,
//! `panic`, …), the E0412 of the types stage. After a function with type
//! parameters of its own (`id::[U8]`), they are its own ([`own_params`],
//! `BodyNames::own`); after a variant of the prelude (`None::[I32]`, §4.1),
//! they make the type of its enum, in the `owner` of its own record. In a
//! constant expression alike (S-329: its reader reads the `owner`,
//! `crate::constarg`). After a member of a value (`v.m::[I32]`), they are of
//! the method or the field the types stage finds (S-977): their names are
//! read here, each lowered by its form ([`Walker::const_form`], S-981).

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, Ident, Lit, Path, TypeArgList, TypeId, TypeKind};

use super::paths::{is_value, path_of};
use super::{ArgsOf, Fail, Listed, PathRes, Typed, Walker};
use crate::Analysis;
use crate::def::{DefId, DefKind, GenericKind};
use crate::names::PathEnd;
use crate::resolve::{Builtin, Entity};
use crate::sig::declared_params;

/// What type arguments go to, by the record of the name before them.
enum To {
    /// The type the next name is a member of.
    Type(Entity),
    /// The name itself: the own parameters of a function, the type of the
    /// enum of a variant of the prelude.
    Name(ArgsOf),
    /// A name that declares no type parameters: E0412.
    Nothing,
    /// A local: E0308.
    Local,
    /// A def whose heading a syntax error cut (S-59): no diagnostic.
    Unknown,
}

/// What a path is by its form ([`Walker::form_of`], [`Form::of_record`]).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    Value,
    /// A type, with what its path names (none of a type parameter).
    Type(Option<Entity>),
    Neither,
}

impl Form {
    /// What the path a walk recorded `r` at is: the form of
    /// [`Walker::form_of`], for the types stage, which has no walk (`v.m[K](x)`).
    pub(crate) fn of_record(a: &Analysis, r: &PathRes) -> Form {
        match r {
            PathRes::Local(_) | PathRes::ConstParam(_) | PathRes::BoundMember { .. } => Form::Value,
            PathRes::TypeParam(_) => Form::Type(None),
            PathRes::Item { entity: e, .. } | PathRes::Namespace(e) => Form::of_entity(a, *e),
            PathRes::FlowBuiltin(_) => Form::Neither,
        }
    }

    fn of_entity(a: &Analysis, e: Entity) -> Form {
        match e {
            _ if is_value(a, e) => Form::Value,
            _ if declared_params(a, e).is_some() => Form::Type(Some(e)),
            _ => Form::Neither,
        }
    }

    /// Whether one name of this form is an argument of the kind of the
    /// first parameter: `Some(true)` a const one, which takes a value (a
    /// local too: the E0417 of the types stage), `Some(false)` a type one,
    /// `None` no parameter (the E0412 of the types stage). The one table of
    /// the candidate `::` of a function and of a method (§4.5, S-974, D-15).
    pub(crate) fn fits(self, constant: Option<bool>) -> bool {
        match constant {
            Some(true) => self == Form::Value,
            Some(false) => matches!(self, Form::Type(_)),
            None => true,
        }
    }
}

/// Whether `e` is a chain of names with no type arguments (`K`, `m.W`): the
/// one name a candidate `::` takes in `[…]` (§4.5, S-974).
pub(crate) fn names_only(ast: &Ast, e: ExprId) -> bool {
    match &ast.expr(e).kind {
        ExprKind::Field { base, .. } => names_only(ast, *base),
        ExprKind::Path(p) => p.segments.len() == 1,
        _ => false,
    }
}

impl<'a> Walker<'a> {
    /// The type arguments `lists` of the chain of names `names` (at `nodes`;
    /// the index of the name before each, and its node), whose records are
    /// `records` and whose error is `fail`; the error that stops the walk
    /// there. Those after the name the chain stopped at, or after an error
    /// before it, are not read: that error comes first (§18.1).
    pub(super) fn lists(
        &mut self,
        (nodes, names): (&[ExprId], &[&'a Ident]),
        lists: &[(usize, ExprId)],
        records: &[PathRes],
        fail: Option<Fail>,
    ) -> Option<Fail> {
        for &(k, x) in lists {
            let ExprKind::TypeArgs { args, .. } = &self.ast.expr(x).kind else { continue };
            // A field or a method of a value; none after an error of the chain.
            let Some(r) = records.get(k) else {
                if fail.is_some() {
                    return fail;
                }
                self.member_args(x, &names[..=k], args);
                continue;
            };
            let stopped = fail.is_some() && records.len() == k + 1 && !matches!(r, PathRes::Namespace(_));
            let (of, to) = match self.goes_to(r, names[k]) {
                To::Local => {
                    let span = self.ast.expr(x).span;
                    let msg = "a local takes no type arguments: a function value is one instance of a function (§4.5)";
                    return Some(Fail::Report(
                        Diagnostic::new(Stage::Names, Code::E0308, span, msg).with_found(self.src(span)),
                    ));
                }
                _ if stopped => return fail,
                To::Type(entity) => (ArgsOf::Type(entity), k + 1),
                To::Name(of) => (of, k),
                To::Nothing => {
                    let after_type = k > 0 && matches!(self.goes_to(&records[k - 1], names[k - 1]), To::Type(_));
                    let d = self.no_params((names, k), after_type, self.ast.expr(x).span);
                    self.out.type_args.insert((x, 0), (None, Some(d)));
                    continue;
                }
                To::Unknown => continue,
            };
            let (path, to) = (path_of(&names[..=k]), nodes.get(to).copied());
            let site = self.site(Typed::Args(Box::new(Listed { key: (x, 0), of, path, args: args.clone(), to })));
            self.type_sites.push(site);
        }
        fail
    }

    /// The type arguments `args` at `x` after the member of a value that
    /// ends `names` (`v.m::[I32]`, `h.f::[I32]`, §4.5): of what the types
    /// stage finds (S-977). Their names are read now, all of them (S-981).
    pub(super) fn member_args(&mut self, x: ExprId, names: &[&Ident], args: &TypeArgList) {
        let of = ArgsOf::Member(args.args.iter().map(|&t| self.const_form(t)).collect());
        let at = Listed { key: (x, 0), of, path: path_of(names), args: args.clone(), to: None };
        let site = self.site(Typed::Args(Box::new(at)));
        self.type_sites.push(site);
    }

    /// Whether the element `t` of type arguments whose parameters are not
    /// known (after a member of a value) is a constant expression by its
    /// form, lowered as one: a form that is no type, or a path of a value
    /// ([`Self::form_of`]). The types stage judges its kind against the
    /// parameter (E0308, S-977); a name not found is a type's E0302.
    fn const_form(&self, t: TypeId) -> bool {
        match &self.ast.ty(t).kind {
            TypeKind::Path { path, .. } => self.form_of(path) == Form::Value,
            kind => matches!(kind, TypeKind::ConstArg(_)),
        }
    }

    /// What the path `path` is, read without walking it: a value (a local,
    /// a const parameter, a constant, a function, a variant, a member of a
    /// type parameter, `T.N`), a type whose parameters are known (a type
    /// parameter, with no entity), or neither (not found, a module, a flow,
    /// a trait, what the check does not read).
    pub(super) fn form_of(&self, path: &Path) -> Form {
        let head = &path.segments[0];
        if self.sees_local(head) || self.outer.contains_key(&head.name) {
            return Form::Value;
        }
        match self.heading(head) {
            Some(PathRes::ConstParam(_)) => Form::Value,
            Some(_) if path.segments.len() > 1 => Form::Value,
            Some(_) => Form::Type(None),
            None => match self.a.path_end(self.m, path, self.self_ty) {
                Ok(PathEnd::Entity(e)) => Form::of_entity(self.a, e),
                Ok(PathEnd::Builtin { .. }) => Form::Value,
                _ => Form::Neither,
            },
        }
    }

    /// Whether `::` before the `[…]` written `x` after the name `name`,
    /// whose record is `r`, leaves no error of the names stage or before
    /// (§4.5, §18.1, S-974, S-980): `x` is one name (a path of modules too,
    /// `m.W`) or an integer literal, that [`Form::fits`] the first parameter
    /// the arguments go to.
    pub(super) fn fits_square(&self, r: &PathRes, name: &Ident, x: ExprId) -> bool {
        let form = match (&self.ast.expr(x).kind, self.ast.chain(x)) {
            (ExprKind::Lit(Lit::Int { .. }), _) => Form::Value,
            (_, Some(c)) if c.lists.is_empty() => {
                let path = c.path(c.names.len());
                if path.segments.len() > 1 && !self.reads_to_item(&path) {
                    return false;
                }
                self.form_of(&path)
            }
            _ => return false,
        };
        let a = self.a;
        let constant = match self.goes_to(r, name) {
            To::Type(e) | To::Name(ArgsOf::Type(e)) => match declared_params(a, e) {
                Some(kinds) => kinds.first().map(|k| *k == Some(true)),
                None => return false,
            },
            To::Name(ArgsOf::Own(d)) => {
                own_params(a, d).first().map(|&k| matches!(a.def(d).generics()[k].kind, GenericKind::Const(_)))
            }
            To::Nothing => None,
            _ => return false,
        };
        form.fits(constant)
    }

    /// Whether the path of more names than one `path` reads to an item that
    /// is no method (`m.W`, `m.K`, `V.C`): no other is one name of a candidate
    /// `::` in `[…]` (§4.5). A member of a local or of a parameter, a method
    /// (`V.meth`, `Str.len`) and a name after a type parameter (`T.N`) leave
    /// an error of the names stage, or are not read before the types stage.
    fn reads_to_item(&self, path: &Path) -> bool {
        let head = &path.segments[0];
        if self.sees_local(head) || self.outer.contains_key(&head.name) || self.heading(head).is_some() {
            return false;
        }
        match self.a.path_end(self.m, path, self.self_ty) {
            Ok(end @ PathEnd::Entity(_)) => end.method(self.a).is_none(),
            _ => false,
        }
    }

    /// The type arguments `lists` of the path of the struct literal `e`,
    /// which names `end` (§4.5): after its last name, to the literal as those
    /// of a chain go ([`Self::goes_to`], R-424); after another name, E0412.
    pub(super) fn struct_args(&mut self, e: ExprId, path: &Path, lists: &[(usize, TypeArgList)], end: Entity) {
        let segs: Vec<&Ident> = path.segments.iter().collect();
        let last = PathRes::Item { entity: end, owner: None };
        for (k, args) in lists {
            let key = (e, *k as u32);
            match (*k + 1 == segs.len()).then(|| self.goes_to(&last, segs[*k])) {
                Some(To::Type(entity)) => {
                    let of = ArgsOf::Type(entity);
                    let at = Listed { key, of, path: path.clone(), args: args.clone(), to: Some(e) };
                    let site = self.site(Typed::Args(Box::new(at)));
                    self.type_sites.push(site);
                }
                Some(To::Unknown) => {}
                _ => {
                    let d = self.no_params((&segs, *k), false, Span { start: segs[0].span.start, ..args.span });
                    self.out.type_args.insert(key, (None, Some(d)));
                }
            }
        }
    }

    /// Whether the name `name`, whose record is `r`, is a def whose heading
    /// a syntax error cut ([`To::Unknown`]).
    pub(super) fn cut(&self, r: &PathRes, name: &Ident) -> bool {
        matches!(self.goes_to(r, name), To::Unknown)
    }

    /// What the type arguments after the name `name`, whose record is `r`, go to.
    fn goes_to(&self, r: &PathRes, name: &Ident) -> To {
        let a = self.a;
        let e = match r {
            PathRes::Local(_) => return To::Local,
            PathRes::TypeParam(_) | PathRes::FlowBuiltin(_) | PathRes::ConstParam(_) => return To::Nothing,
            // As the member of the representative type (`T.round_from`).
            PathRes::BoundMember { member, .. } => Entity::Member(*member),
            PathRes::Namespace(e) | PathRes::Item { entity: e, .. } => *e,
        };
        if crate::names::is_self_type(&name.name) {
            return To::Nothing;
        }
        match e {
            Entity::Builtin(Builtin::Scalar(_) | Builtin::Generic(_)) => To::Type(e),
            Entity::Variant(d, _) if a.modules.lang.of(d).is_some() => To::Name(ArgsOf::Type(Entity::Def(d))),
            Entity::Module(_) | Entity::Builtin(_) | Entity::Variant(..) => To::Nothing,
            Entity::Def(d) | Entity::Member(d) if a.heading_failed(d) => To::Unknown,
            Entity::Def(d) | Entity::Member(d) => match &a.def(d).kind {
                DefKind::Struct(_) | DefKind::Enum(_) | DefKind::Alias(_) => To::Type(e),
                DefKind::Flow(_) => To::Nothing,
                DefKind::Fn(_) if !own_params(a, d).is_empty() => To::Name(ArgsOf::Own(d)),
                _ => To::Nothing,
            },
        }
    }

    /// The E0412 of the type arguments at `span` after the name `names[k]`,
    /// which declares no type parameters (§4.5, S-306): no candidate, and a
    /// note of the item that takes them, the type before it (`after_type`).
    pub(super) fn no_params(&self, (names, k): (&[&Ident], usize), after_type: bool, span: Span) -> Diagnostic {
        let name = &names[k].name;
        let rule = after_type.then(|| {
            format!(
                "the type arguments of `{0}` are written after it, `{0}::[…].{name}`",
                path_of(&names[..k]).dotted()
            )
        });
        count_error(name, (&[], 0), (span, self.src(span)), rule)
    }
}

/// The E0412 of the `n` type arguments at `span` (written `found`) after
/// `name`, whose own parameters are `params` (§4.5, S-306): no candidate,
/// and a note of the parameters, or of the item that takes them (`rule`).
pub(crate) fn count_error(
    name: &str,
    (params, n): (&[String], usize),
    (span, found): (Span, String),
    rule: Option<String>,
) -> Diagnostic {
    let (msg, rule) = match params {
        [] => (
            format!("`{name}` declares no type parameters to take type arguments (§4.5)"),
            rule.unwrap_or_else(|| {
                "type arguments are written after the item that declares the type parameters".into()
            }),
        ),
        _ => (
            format!("`{name}` takes {} type argument(s), {n} given", params.len()),
            format!("`{name}` declares the type parameters {} (§4.5)", params.join(", ")),
        ),
    };
    Diagnostic::new(Stage::Types, Code::E0412, span, msg).with_found(found).with_rule(rule)
}

/// The own type and const parameters of the function `d` (§4.5), at their
/// index in its generics: those after its `impl`'s, with no effect-row
/// variable (S-982, `fn apply[T, e]` has one).
pub(crate) fn own_params(a: &Analysis, d: DefId) -> Vec<usize> {
    let def = a.def(d);
    let of_impl = def.owner.filter(|&o| matches!(a.def(o).kind, DefKind::Impl(_)) && o != d);
    let from = of_impl.map_or(0, |o| a.def(o).generics().len());
    (from..def.generics().len()).filter(|&k| !matches!(def.generics()[k].kind, GenericKind::Effect)).collect()
}
