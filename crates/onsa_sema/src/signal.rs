//! The value type of a signal (§11.3): Copy, and holding no function type
//! (S-372) by its structure, the one judgment of the value types of the
//! inputs and the output of a flow and of the types of the expressions of
//! its body.

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Span, Stage};

use crate::ty::{Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

/// The E0810 at `span` of the value type `ty` of a signal that is not
/// Copy, the one judgment of the inputs and the output
/// ([`signal_type_error`]), of the `let`s of a flow body and of the elements
/// of a `par~` (S-1047).
pub(crate) fn not_copy_signal(a: &Analysis, ty: TyId, span: Span) -> Option<Diagnostic> {
    let k = not_copy(a, ty)?;
    let msg = format!("the value type of a signal must be Copy; `{}` is {k} (§11.3)", a.display_type(ty));
    Some(Diagnostic::new(Stage::Flow, Code::E0810, span, msg))
}

/// The kind of `ty` when it is not Copy: the predicate of the value type
/// of a signal and of a hoisted field (§11.3, S-1046 (a)).
pub(crate) fn not_copy(a: &Analysis, ty: TyId) -> Option<&'static str> {
    crate::kind::facts_of(a, ty, &[]).not_copy()
}

/// The E0816 at `span` of the value type `ty` of a signal that does not
/// satisfy `Default`, where the value of `what` is not written and is
/// `T.default()` (§11.4: the omitted `init` of a delay, an arm `match~` did
/// not take (§11.5), the first values of `when~` and of a gathered rate, an
/// event before its first), of the section `at`. The predicate is the
/// bound's (§6.3, as of E0416): of the types of the elements whatever the
/// length (S-1104), quiet of a type not known (§18.1). No candidate: the
/// value is the writer's.
pub(crate) fn no_default_signal(a: &Analysis, ty: TyId, span: Span, what: &str, at: &str) -> Option<Diagnostic> {
    if (crate::bounds::Bounds { a, generics: &[] }).satisfies(ty, crate::def::Bound::Default) {
        return None;
    }
    let shown = a.display_type(ty);
    let msg = format!("{what} is the default of its type, and `{shown}` does not satisfy `Default` ({at})");
    Some(Diagnostic::new(Stage::Flow, Code::E0816, span, msg))
}

/// The E0810 at `span` of the value type `ty` of a signal, in this order:
/// not Copy, holding a function type.
pub(crate) fn signal_type_error(a: &Analysis, ty: TyId, span: Span) -> Option<Diagnostic> {
    let what = "the value type of a signal";
    not_copy_signal(a, ty, span).or_else(|| holds_fn(a, ty).then(|| fn_type_error(a, ty, span, what)))
}

/// A step from a type into a part of it, on the way to a function type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Part {
    /// The element of an array (of length 0 too: the type is there).
    Elem,
    /// The item of a tuple, from 0.
    Item(usize),
    /// The argument of a type, from 0.
    Arg(usize),
    /// The field of a struct (`priv` too).
    Field(DefId, String),
    /// An item of the variant of an enum.
    Variant(DefId, String),
    /// What an alias names.
    Alias(DefId),
}

/// A function type in a type: the steps to it from the type, and it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FnIn {
    pub(crate) parts: Vec<Part>,
    pub(crate) found: TyId,
}

/// The steps a note shows ([`FnIn::path`]): a chain of declarations of
/// any depth has a note of a few lines.
const SHOWN: usize = 8;

/// Whether `ty` holds a function type, as [`fn_in`] finds one, kept for
/// the package from when the declarations are lowered ([`Summaries::fns`]):
/// each type of the body of a flow is a question, answered once.
///
/// A question walks the parts as [`fn_in`] does ([`Search`]). Of a
/// question that finds none, the types reached are kept, all holding none:
/// what they reach the question reaches. Of one that finds one, only those
/// found to hold one are: a type found to hold none may hold one through a
/// declaration the question was entering, which it did not enter again.
///
/// [`Summaries::fns`]: crate::summary::Summaries::fns
pub(crate) fn holds_fn(a: &Analysis, ty: TyId) -> bool {
    let mut ask = Search::new(a, None);
    let k = ask.of(ty, 0);
    if a.known.ready {
        a.known.summaries.borrow_mut().fns.extend(ask.found.into_iter().filter(|&(_, f)| f || !k));
    }
    k
}

/// The E0810 at `span` of `ty`, the type of `what`, which holds a function
/// type ([`holds_fn`], §11.3, S-372): with the steps to it ([`FnIn::path`])
/// and the rule.
pub(crate) fn fn_type_error(a: &Analysis, ty: TyId, span: Span, what: &str) -> Diagnostic {
    let held = fn_in(a, ty).filter(|h| !h.parts.is_empty());
    let shown = match &held {
        Some(h) => format!("holds the function type `{}`", a.display_type(h.found)),
        None => "is a function type".to_string(),
    };
    let msg = format!("{what} holds no function type; `{}` {shown} (§11.3)", a.display_type(ty));
    let d = Diagnostic::new(Stage::Flow, Code::E0810, span, msg);
    let d = match held {
        Some(h) => d.with_rule(format!("`{}` is in {}", a.display_type(h.found), h.path(a))),
        None => d,
    };
    d.with_rule(
        "a flow takes, gives and keeps no function value; to choose among functions, take an enum and `match` on it",
    )
}

/// The first function type in `ty`, if one is: the type itself, an element
/// of an array or a tuple, a type argument, a field of a struct, an item of
/// a variant, what an alias names, in that order, the arguments of a type
/// before its declaration. A declaration is entered once a question (its
/// fields hold no parameter of a function type: its arguments are read
/// where it is used), so a type that holds itself ends, and the work is in
/// proportion to the types reached. Made for the note of a diagnostic, of a
/// type [`holds_fn`] finds one in.
pub(crate) fn fn_in(a: &Analysis, ty: TyId) -> Option<FnIn> {
    let mut find = Search::new(a, Some(Vec::new()));
    find.of(ty, 0).then_some(())?;
    let mut parts = find.path?;
    parts.reverse();
    Some(FnIn { parts, found: find.found_fn? })
}

impl FnIn {
    /// The steps, for a note: "the field `inner` of `Wrapper`, then the
    /// field `cb` of `Pt`", the first [`SHOWN`] of them and how many more.
    pub(crate) fn path(&self, a: &Analysis) -> String {
        let step = |p: &Part| match p {
            Part::Elem => "an element".to_string(),
            Part::Item(i) => format!("the item {i} of the tuple"),
            Part::Arg(i) => format!("the type argument {}", i + 1),
            Part::Field(d, f) => format!("the field `{f}` of `{}`", a.shown_name(*d)),
            Part::Variant(d, v) => format!("the variant `{v}` of `{}`", a.shown_name(*d)),
            Part::Alias(d) => format!("the alias `{}`", a.shown_name(*d)),
        };
        let mut steps: Vec<String> = self.parts.iter().take(SHOWN).map(step).collect();
        if let Some(more) = self.parts.len().checked_sub(SHOWN).filter(|&n| n > 0) {
            steps.push(format!("{more} more steps"));
        }
        steps.join(", then ")
    }
}

/// Types to look in, each with the step to it.
type Parts = Vec<(Part, TyId)>;

/// The parts of `ty` a function type is looked for in, each with the step
/// to it, and the declaration it names, entered after them; none of a
/// function type.
fn parts(a: &Analysis, ty: TyId) -> Option<(Parts, Option<DefId>)> {
    let each = |ts: &[TyId], part: fn(usize) -> Part| ts.iter().enumerate().map(|(i, &t)| (part(i), t)).collect();
    Some(match a.types.get(ty) {
        Ty::Fn(_) => return None,
        Ty::Array(e, _) => (vec![(Part::Elem, *e)], None),
        Ty::Tuple(ts) => (each(ts, Part::Item), None),
        Ty::Builtin(_, ts) => (each(ts, Part::Arg), None),
        Ty::Named(d, args) => (each(args, Part::Arg), Some(*d)),
        _ => (Vec::new(), None),
    })
}

/// What `d` holds, each with the step to it, and the depth to read it at.
fn held(w: &Walk, d: DefId, depth: u32) -> (Parts, u32) {
    let Some((holds, _, depth)) = w.enter(d, &[], None, (depth, None)) else {
        // Each declaration once a question: no deeper than there are.
        onsa_diag::internal::bug(None, "the walk of a function type entered declarations past the limit")
    };
    let parts = match holds {
        Holds::Fields(fs, _) => fs.iter().map(|f| (Part::Field(d, f.name.clone()), f.ty)).collect(),
        Holds::Variants(vs) => {
            vs.iter().flat_map(|v| v.fields.iter().map(|&t| (Part::Variant(d, v.name.clone()), t))).collect()
        }
        Holds::Alias(t) => vec![(Part::Alias(d), t)],
        Holds::Opaque(_) | Holds::Nothing => Vec::new(),
    };
    (parts, depth)
}

/// The walk of [`holds_fn`] and of [`fn_in`] (with `path`): whether a type
/// holds a function type. A "yes" ends the question, so a function type
/// reached by any step is told to the type asked.
struct Search<'a> {
    w: Walk<'a>,
    /// The declarations entered, once a question.
    seen: HashSet<DefId>,
    /// The answer of each type reached in the question (not of a note's).
    found: HashMap<TyId, bool>,
    /// Of [`fn_in`]: the steps from the function type out, and it.
    path: Option<Vec<Part>>,
    found_fn: Option<TyId>,
}

impl<'a> Search<'a> {
    fn new(a: &'a Analysis, path: Option<Vec<Part>>) -> Self {
        let (seen, found) = (HashSet::default(), HashMap::default());
        Search { w: Walk::new(a), seen, found, path, found_fn: None }
    }

    fn of(&mut self, ty: TyId, depth: u32) -> bool {
        let known = &self.w.a.known;
        let kept = known.ready.then(|| known.summaries.borrow().fns.get(&ty).copied()).flatten();
        // The steps of a "yes" are walked.
        if let Some(k) = kept.or_else(|| self.found.get(&ty).copied()).filter(|&k| !k || self.path.is_none()) {
            return k;
        }
        let k = match parts(self.w.a, ty) {
            None => {
                self.found_fn = Some(ty);
                true
            }
            Some((parts, decl)) => self.any(parts, depth) || decl.is_some_and(|d| self.decl(d, depth)),
        };
        // A note's walk keeps none: made once, of a type found to hold one,
        // it ends at the first function type.
        if self.path.is_none() {
            self.found.insert(ty, k);
        }
        k
    }

    fn any(&mut self, parts: Parts, depth: u32) -> bool {
        for (part, t) in parts {
            if self.of(t, depth) {
                if let Some(p) = &mut self.path {
                    p.push(part);
                }
                return true;
            }
        }
        false
    }

    /// `d`, entered once a question (its fields hold no parameter of a
    /// function type: its arguments are read where it is used).
    fn decl(&mut self, d: DefId, depth: u32) -> bool {
        if !self.seen.insert(d) {
            return false;
        }
        let (parts, depth) = held(&self.w, d, depth);
        self.any(parts, depth)
    }
}

#[cfg(test)]
mod tests;
