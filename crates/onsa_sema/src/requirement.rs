//! The requirements of a type parameter on its argument (§4.5): the implicit
//! `Escape`, the implicit `Dup` and the bounds, in the order they are judged
//! ([`requirements`]), the type a requirement is on ([`Required`]) and the
//! words of their errors (E0710, E0416, E0406). Of no stage: the checks of a
//! body that wait ([`crate::deferred`]), the constant expressions
//! ([`crate::constarg`]) and the types written (`sig::wellformed`) read them.

use crate::Analysis;
use crate::def::{Bound, GenericDef, GenericKind};
use crate::ty::{BuiltinTy, Ty, TyId};

/// A requirement of a type parameter on its argument (§4.5), of [`requirements`].
#[derive(Clone, Copy)]
pub(crate) enum Requirement {
    /// The implicit `Escape` (E0710 of the rule `rule`); `lifted`: the parameter is `?Escape`.
    Escape { rule: &'static str, lifted: bool },
    /// The implicit `Dup` or a bound (E0416).
    Bound(Bound),
}

/// What the type parameter `g` requires of its argument, in the order it is
/// judged (§4.5, S-862): its implicit `Escape`, then the implicit `Dup` and
/// its bounds. The first one an argument does not meet is its error, and the
/// others are not judged (a second-class argument is E0710 alone): a use of a
/// value makes them items in this order (the first one to fail is reported,
/// [`crate::body::Checker::check_deferred_now`]), a constant expression judges them at once
/// ([`crate::constarg`]). None of a const parameter, nor of one with an
/// unknown bound, which requires nothing of its users (§18.1, S-768).
/// `of_seq`: of the element of a method of an array.
pub(crate) fn requirements(g: &GenericDef, of_seq: bool) -> Option<impl Iterator<Item = Requirement> + '_> {
    let GenericKind::Type { bounds, dup, unknown: false, .. } = &g.kind else { return None };
    let lifted = g.lifts_escape();
    let rule = match (lifted, of_seq) {
        (true, _) => LIFTED_VIEW,
        (false, true) => VIEW_OF_ARRAY,
        (false, false) => GENERIC_VIEW,
    };
    let wants = dup.then_some(Bound::Dup).into_iter().chain(bounds.iter().copied());
    Some(std::iter::once(Requirement::Escape { rule, lifted }).chain(wants.map(Requirement::Bound)))
}

/// The name of the type `t` with no type argument (`Rg` of `Rg[T, N]`,
/// `Buf` of `Buf[T]`); none of another form.
pub(crate) fn head_of(a: &Analysis, t: TyId) -> Option<String> {
    match a.types.get(t) {
        Ty::Named(d, _) => Some(a.def(*d).name.clone()),
        Ty::Builtin(b, _) => Some(b.name().to_string()),
        _ => None,
    }
}

/// The generic parameter `g` of `owner` (``the `impl` of `Rg` ``) as a
/// message names it.
pub(crate) fn parameter(g: &GenericDef, owner: &str) -> String {
    let kind = if matches!(g.kind, GenericKind::Const(_)) { "const" } else { "type" };
    format!("the {kind} parameter `{}` of {owner}", g.name)
}

/// The note of an E0406 of the constant `name` of the `impl` of the type
/// `head` (S-304): how its arguments are given, after its name or by an
/// alias.
pub(crate) fn alias_way(head: &str, name: &str) -> String {
    format!("give the type its arguments: `{head}::[…].{name}`, or by an alias, `type R = {head}[…]`, then `R.{name}`")
}

/// The message of the E0710 of the type argument `shown` of `what`, a
/// second-class type (§4.5, §5.3).
pub(crate) fn second_class_argument(shown: &str, what: &str) -> String {
    format!("`{shown}` is second-class: {what} cannot take it (§4.5, §5.3)")
}

/// The rule of the E0710 of a type argument with no kind (§5.3, S-862).
pub(crate) const GENERIC_VIEW: &str = "to take a view generically, declare the parameter `xs: Span[T]` or `xs: [Span[T]; N]` (§5.3), or give the type parameter `?Escape` (§4.5)";

/// The rule of that E0710 of a `?Escape` parameter (S-927).
pub(crate) const LIFTED_VIEW: &str =
    "a `?Escape` type parameter takes a `Span` and a planar array, no other second-class type (§4.5)";

/// The rule of that E0710 of the element of a method of an array.
pub(crate) const VIEW_OF_ARRAY: &str = "call the method on one view of the array (`xs[k].get(i)`, §5.3)";

/// The type a requirement is on.
#[derive(Debug, Clone)]
pub(crate) enum Required {
    /// A type parameter `param` of `owner` (`` `need_f` ``, ``the `impl` of `Wrap` ``):
    /// its bounds and the implicit `Dup`. `std`: `owner` is std's, whose
    /// declaration the user does not change.
    Param { param: String, owner: String, std: bool },
    /// The element of `[e; N]` (`Dup`, §2.4).
    RepeatElement,
    /// The element of `Buf` / `Span` (`Copy`, §4.5), named as written (R-351).
    BufElement(BuiltinTy),
    /// The element of `Array` / `Set`, the key and the value of `Map`
    /// (`Dup`, §4.5, S-767).
    SharedElement,
    /// The element of the receiver of the type `recv` of the method `method`
    /// of std's `impl` of a sequence: its bounds (§5.3, S-853).
    SeqElement { recv: TyId, method: String },
    /// The value of a hole of a string (`Show`, §2.4, R-292).
    HoleValue,
}

/// What the message of a type argument calls it.
#[derive(Debug, Clone)]
pub(crate) enum ArgumentName {
    Text(String),
    /// The element of the receiver of the type `recv` of the method `method`,
    /// shown when the error is reported, as [`Required::SeqElement`] is.
    SeqElement {
        recv: TyId,
        method: String,
    },
}

impl ArgumentName {
    pub(crate) fn text(&self, show: impl FnOnce(TyId) -> String) -> String {
        match self {
            ArgumentName::Text(t) => t.clone(),
            ArgumentName::SeqElement { recv, method } => {
                format!("the element type of `{method}` of `{}`", show(*recv))
            }
        }
    }
}

impl Required {
    /// The message of the E0416 of the type `shown` that does not meet `bound`
    /// as this requirement: of a body, and of a type written (`sig::wellformed`).
    /// `show` shows another type, when the error is reported.
    pub(crate) fn unmet(&self, shown: &str, bound: Bound, show: &mut dyn FnMut(TyId) -> String) -> String {
        match self {
            Required::HoleValue => {
                format!("a hole of a string takes a value that implements `Show`; `{shown}` does not (§2.4)")
            }
            Required::RepeatElement => format!(
                "`[e; N]` repeats the value of `e`, so its type must be Copy or Shared (`Dup`); `{shown}` is not; make an Affine array with `array.from_fn` (§2.4)"
            ),
            Required::BufElement(b) => {
                format!("the element type of `{}` must be Copy; `{shown}` is not (§4.5)", b.name())
            }
            Required::SharedElement => format!(
                "the elements of `Array`, `Set` and `Map` are Copy or Shared (`Dup`); `{shown}` is Affine (§4.5)"
            ),
            Required::Param { param, owner, std: true } if bound == Bound::Dup => {
                format!("`{shown}` is not Copy or Shared, so it does not satisfy `{param}: Dup` of {owner} (§4.5)")
            }
            Required::Param { param, owner, .. } if bound == Bound::Dup => format!(
                "`{shown}` is not Copy or Shared, so it does not satisfy `{param}: Dup` of {owner}; a type parameter takes only Copy or Shared types unless it is declared `{param}: ?Dup` (§4.5)"
            ),
            Required::Param { param, owner, .. } => {
                format!("`{shown}` does not satisfy the bound `{param}: {}` of {owner} (§4.5)", bound.name())
            }
            Required::SeqElement { recv, method } => {
                let need = match bound {
                    Bound::Dup => "a Copy or Shared (`Dup`) element".to_string(),
                    Bound::Copy => "a Copy element".to_string(),
                    b => format!("an element that meets `{}`", b.name()),
                };
                format!("`{}` has `{method}` only with {need}; its element `{shown}` is not (§5.3)", show(*recv))
            }
        }
    }
}
