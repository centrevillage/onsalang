//! Whether a type holds a function type (§11.3, S-372): by its structure,
//! the one judgment of the value types of the inputs and the output of a
//! flow and of the types of the expressions of its body.

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Span, Stage};

use crate::ty::{Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

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
/// A question walks the parts as [`fn_in`] does. A type reached in one
/// that finds none has none: what it reaches, its question reaches. Of one
/// that finds one, only those found to hold one are kept: one walked past
/// a declaration being entered may have one through it.
///
/// [`Summaries::fns`]: crate::summary::Summaries::fns
pub(crate) fn holds_fn(a: &Analysis, ty: TyId) -> bool {
    let mut ask = Ask { w: Walk::new(a), seen: HashSet::default(), found: HashMap::default() };
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
    let mut find = Find { w: Walk::new(a), seen: HashSet::default(), parts: Vec::new() };
    let found = find.of(ty, 0)?;
    find.parts.reverse();
    Some(FnIn { parts: find.parts, found })
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

/// What `d` holds, each with the step to it, and the depth to read it at,
/// if a question has not entered it (`seen`).
fn held(w: &Walk, seen: &mut HashSet<DefId>, d: DefId, depth: u32) -> Option<(Parts, u32)> {
    if !seen.insert(d) {
        return None;
    }
    let Some((holds, _, depth)) = w.enter(d, &[], None, (depth, None)) else {
        // Each declaration once: no deeper than there are, under the limit.
        debug_assert!(false, "the walk of a function type entered declarations past the limit");
        return None;
    };
    let parts = match holds {
        Holds::Fields(fs, _) => fs.iter().map(|f| (Part::Field(d, f.name.clone()), f.ty)).collect(),
        Holds::Variants(vs) => {
            vs.iter().flat_map(|v| v.fields.iter().map(|&t| (Part::Variant(d, v.name.clone()), t))).collect()
        }
        Holds::Alias(t) => vec![(Part::Alias(d), t)],
        Holds::Opaque(_) | Holds::Nothing => Vec::new(),
    };
    Some((parts, depth))
}

struct Find<'a> {
    w: Walk<'a>,
    seen: HashSet<DefId>,
    /// The steps from the function type out, as the walk returns.
    parts: Vec<Part>,
}

impl Find<'_> {
    fn of(&mut self, ty: TyId, depth: u32) -> Option<TyId> {
        let Some((parts, decl)) = parts(self.w.a, ty) else { return Some(ty) };
        if let Some(found) = self.first(parts, depth) {
            return Some(found);
        }
        let (parts, depth) = held(&self.w, &mut self.seen, decl?, depth)?;
        self.first(parts, depth)
    }

    fn first(&mut self, parts: Parts, depth: u32) -> Option<TyId> {
        parts.into_iter().find_map(|(part, t)| {
            let found = self.of(t, depth)?;
            self.parts.push(part);
            Some(found)
        })
    }
}

/// A question of [`holds_fn`]: the answer of each type reached.
struct Ask<'a> {
    w: Walk<'a>,
    seen: HashSet<DefId>,
    found: HashMap<TyId, bool>,
}

impl Ask<'_> {
    fn of(&mut self, ty: TyId, depth: u32) -> bool {
        let known = &self.w.a.known;
        let kept = known.ready.then(|| known.summaries.borrow().fns.get(&ty).copied()).flatten();
        if let Some(k) = kept.or_else(|| self.found.get(&ty).copied()) {
            return k;
        }
        let k = match parts(self.w.a, ty) {
            None => true,
            Some((parts, decl)) => {
                parts.iter().any(|&(_, t)| self.of(t, depth))
                    || decl
                        .and_then(|d| held(&self.w, &mut self.seen, d, depth))
                        .is_some_and(|(parts, depth)| parts.iter().any(|&(_, t)| self.of(t, depth)))
            }
        };
        self.found.insert(ty, k);
        k
    }
}

#[cfg(test)]
mod tests;
