//! Kinds (spec §4.6): Copy / Shared / Affine, from the structure of a type.

use std::collections::HashSet;

use crate::def::{DefKind, Fields, FlowTy};
use crate::ty::{BuiltinTy, Ty, TyId};
use crate::{Analysis, DefId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Copy,
    Shared,
    Affine,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Copy => "Copy",
            Kind::Shared => "Shared",
            Kind::Affine => "Affine",
        }
    }
}

/// Kind of a type; `None` when it depends on a generic parameter, or for
/// second-class types (`Span`). Recursive types stop with `None`.
pub fn kind_of(a: &Analysis, ty: TyId) -> Option<Kind> {
    let mut visiting = HashSet::new();
    kind_rec(a, ty, &mut visiting)
}

fn kind_rec(a: &Analysis, ty: TyId, visiting: &mut HashSet<DefId>) -> Option<Kind> {
    match a.types.get(ty) {
        Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Unit | Ty::Fn(_) | Ty::ConstVal(_) => Some(Kind::Copy),
        Ty::Array(t, _) => kind_rec(a, *t, visiting),
        Ty::Tuple(ts) => ts.iter().try_fold(Kind::Copy, |k, &t| Some(k.max(kind_rec(a, t, visiting)?))),
        Ty::Builtin(b, args) => match b {
            BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set => {
                Some(Kind::Shared)
            }
            BuiltinTy::Buf => Some(Kind::Affine),
            BuiltinTy::Ptr => Some(Kind::Copy),
            BuiltinTy::Span => None,
            BuiltinTy::Option | BuiltinTy::Result => {
                args.iter().try_fold(Kind::Copy, |k, &t| Some(k.max(kind_rec(a, t, visiting)?)))
            }
        },
        Ty::Named(d, args) => {
            if !visiting.insert(*d) {
                return None;
            }
            let r = kind_of_def(a, *d, args, visiting);
            visiting.remove(d);
            r
        }
        Ty::Rate(_, t) => kind_rec(a, *t, visiting),
        Ty::Param(_) | Ty::Var(_) | Ty::Error => None,
    }
}

fn kind_of_def(a: &Analysis, d: DefId, args: &[TyId], visiting: &mut HashSet<DefId>) -> Option<Kind> {
    let def = a.def(d);
    let field_kind = |t: TyId, visiting: &mut HashSet<DefId>| {
        let t = crate::layout::subst(a, t, args);
        kind_rec(a, t, visiting)
    };
    match &def.kind {
        DefKind::Struct(s) => {
            if s.flow_ty == Some(FlowTy::State) {
                return Some(Kind::Affine); // §4.6: flow state is Affine
            }
            match &s.fields {
                Fields::Named(fs) => fs.iter().try_fold(Kind::Copy, |k, f| Some(k.max(field_kind(f.ty, visiting)?))),
                Fields::Tuple(t) => field_kind(*t, visiting),
                Fields::Opaque => Some(Kind::Copy),
            }
        }
        DefKind::Enum(e) => e
            .variants
            .iter()
            .flat_map(|v| v.fields.iter())
            .try_fold(Kind::Copy, |k, &t| Some(k.max(field_kind(t, visiting)?))),
        DefKind::Alias(t) => kind_rec(a, *t, visiting),
        _ => None,
    }
}
