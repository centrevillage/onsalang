//! The type arguments `::[…]` of a chain of names (§4.5, S-239, S-306,
//! S-978, S-979): each goes to the name before it. After a type
//! (`Buf::[F32]` of `Buf::[F32].zeroed(4)`), they make the type the next name
//! is a member of, lowered after the walk (`lower_types`) into its record's
//! `owner`; after a local, they are the E0308 of the walk; after any other
//! name that declares no type parameters (a constant, `Self`, a module,
//! `panic`, …), the E0412 of the types stage. In a constant expression
//! alike (S-329: its reader reads the `owner`, `crate::constarg`). Those of a
//! function or a method and of a variant of the prelude are E0200 until the
//! units that read them (W5-10 U2a, U2b), before the marks of the call
//! (`flow.rs`).

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{ExprId, ExprKind, Ident};

use super::paths::path_of;
use super::{Fail, Listed, PathRes, Typed, Walker};
use crate::def::DefKind;
use crate::resolve::{Builtin, Entity};

/// What type arguments go to, by the record of the name before them.
enum To {
    Type(Entity),
    /// A name that declares no type parameters: E0412.
    Nothing,
    /// A local: E0308.
    Local,
    /// Not read yet: E0200.
    Later,
    /// A def whose heading a syntax error cut (S-59): no diagnostic.
    Unknown,
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
            // A field or a method of a value (U2b).
            let Some(r) = records.get(k) else { return fail.or_else(|| Some(self.type_args(args.span))) };
            let stopped = fail.is_some() && records.len() == k + 1 && !matches!(r, PathRes::Namespace(_));
            match self.goes_to(r, names[k]) {
                To::Local => {
                    let span = self.ast.expr(x).span;
                    let msg = "a local takes no type arguments: a function value is one instance of a function (§4.5)";
                    return Some(Fail::Report(
                        Diagnostic::new(Stage::Names, Code::E0308, span, msg).with_found(self.src(span)),
                    ));
                }
                To::Later => return Some(self.type_args(args.span)),
                _ if stopped => return fail,
                To::Type(entity) => {
                    let (path, to) = (path_of(&names[..=k]), nodes.get(k + 1).copied());
                    let at = Listed { key: (x, 0), entity, path, args: args.clone(), to };
                    let site = self.site(Typed::Args(Box::new(at)));
                    self.type_sites.push(site);
                }
                To::Nothing => {
                    let after_type = k > 0 && matches!(self.goes_to(&records[k - 1], names[k - 1]), To::Type(_));
                    let d = self.no_params((names, k), after_type, self.ast.expr(x).span);
                    self.out.type_args.insert((x, 0), (None, Some(d)));
                }
                To::Unknown => {}
            }
        }
        fail
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
            Entity::Variant(d, _) if a.modules.lang.of(d).is_some() => To::Later,
            Entity::Module(_) | Entity::Builtin(_) | Entity::Variant(..) => To::Nothing,
            Entity::Def(d) | Entity::Member(d) if a.heading_failed(d) => To::Unknown,
            Entity::Def(d) | Entity::Member(d) => match &a.def(d).kind {
                DefKind::Struct(_) | DefKind::Enum(_) | DefKind::Alias(_) => To::Type(e),
                DefKind::Flow(_) => To::Nothing,
                // Its own parameters, after those of its `impl`.
                DefKind::Fn(f) => {
                    let of_impl = a.def(d).owner.filter(|&o| matches!(a.def(o).kind, DefKind::Impl(_)));
                    match f.generics.len() > of_impl.map_or(0, |o| a.def(o).generics().len()) {
                        true => To::Later,
                        false => To::Nothing,
                    }
                }
                _ => To::Nothing,
            },
        }
    }

    /// The E0412 of the type arguments at `span` after the name `names[k]`,
    /// which declares no type parameters (§4.5, S-306): no candidate, and a
    /// note of the item that takes them, the type before it (`after_type`).
    pub(super) fn no_params(&self, (names, k): (&[&Ident], usize), after_type: bool, span: Span) -> Diagnostic {
        let name = &names[k].name;
        let msg = format!("`{name}` declares no type parameters to take type arguments (§4.5)");
        let rule = match after_type {
            true => format!(
                "the type arguments of `{0}` are written after it, `{0}::[…].{name}`",
                path_of(&names[..k]).dotted()
            ),
            false => "type arguments are written after the item that declares the type parameters".to_string(),
        };
        Diagnostic::new(Stage::Types, Code::E0412, span, msg).with_found(self.src(span)).with_rule(rule)
    }
}
