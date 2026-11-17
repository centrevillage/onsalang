//! Whether a type holds a function type (§11.3, S-372): by its structure,
//! the one judgment of the value types of the inputs and the output of a
//! flow and of the types of the expressions of its body.

use onsa_diag::hash::HashSet;

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

/// The first function type in `ty`, if one is: the type itself, an element
/// of an array or a tuple, a type argument, a field of a struct, an item of
/// a variant, what an alias names, in that order, the arguments of a type
/// before its declaration. A declaration is entered once a question (its
/// fields hold no parameter of a function type: its arguments are read
/// where it is used), so a type that holds itself ends, and the work is in
/// proportion to the types reached; past the limits of [`Walk`], none.
pub(crate) fn fn_in(a: &Analysis, ty: TyId) -> Option<FnIn> {
    let mut find = Find { w: Walk::new(a), seen: HashSet::default(), parts: Vec::new() };
    let found = find.of(ty, 0)?;
    find.parts.reverse();
    Some(FnIn { parts: find.parts, found })
}

impl FnIn {
    /// The steps, for a note: "the field `inner` of `Wrapper`, then the field `cb` of `Pt`".
    pub(crate) fn path(&self, a: &Analysis) -> String {
        let step = |p: &Part| match p {
            Part::Elem => "an element".to_string(),
            Part::Item(i) => format!("the item {i} of the tuple"),
            Part::Arg(i) => format!("the type argument {}", i + 1),
            Part::Field(d, f) => format!("the field `{f}` of `{}`", a.shown_name(*d)),
            Part::Variant(d, v) => format!("the variant `{v}` of `{}`", a.shown_name(*d)),
            Part::Alias(d) => format!("the alias `{}`", a.shown_name(*d)),
        };
        self.parts.iter().map(step).collect::<Vec<_>>().join(", then ")
    }
}

struct Find<'a> {
    w: Walk<'a>,
    seen: HashSet<DefId>,
    /// The steps from the function type out, as the walk returns.
    parts: Vec<Part>,
}

impl Find<'_> {
    fn of(&mut self, ty: TyId, depth: u32) -> Option<TyId> {
        let a = self.w.a;
        match a.types.get(ty) {
            Ty::Fn(_) => Some(ty),
            Ty::Array(e, _) => self.each(&[*e], depth, |_| Part::Elem),
            Ty::Tuple(ts) => self.each(ts, depth, Part::Item),
            Ty::Builtin(_, ts) => self.each(ts, depth, Part::Arg),
            Ty::Named(d, args) => {
                let d = *d;
                if let Some(found) = self.each(args, depth, Part::Arg) {
                    return Some(found);
                }
                if !self.seen.insert(d) {
                    return None;
                }
                let (holds, _, depth) = self.w.enter(d, &[], None, (depth, None))?;
                match holds {
                    Holds::Fields(fs, _) => fs.iter().find_map(|f| {
                        let found = self.of(f.ty, depth)?;
                        self.parts.push(Part::Field(d, f.name.clone()));
                        Some(found)
                    }),
                    Holds::Variants(vs) => vs.iter().find_map(|v| {
                        let found = v.fields.iter().find_map(|&t| self.of(t, depth))?;
                        self.parts.push(Part::Variant(d, v.name.clone()));
                        Some(found)
                    }),
                    Holds::Alias(t) => self.each(&[t], depth, |_| Part::Alias(d)),
                    Holds::Opaque(_) | Holds::Nothing => None,
                }
            }
            _ => None,
        }
    }

    /// The first function type in `ts`, the step to the one it is in made by `part` of its index.
    fn each(&mut self, ts: &[TyId], depth: u32, part: impl Fn(usize) -> Part) -> Option<TyId> {
        ts.iter().enumerate().find_map(|(i, &t)| {
            let found = self.of(t, depth)?;
            self.parts.push(part(i));
            Some(found)
        })
    }
}
