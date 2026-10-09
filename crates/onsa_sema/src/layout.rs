//! Layout (spec §12.4): declaration order, natural alignment, no reordering.
//! Enums: the smallest tag of `U8` / `U16` / `U32`, then the largest variant.

use crate::def::{DefKind, Fields};
use crate::ty::{BuiltinTy, FloatKind, IntKind, Len, Ty, TyId};
use crate::{Analysis, DefId};

/// Pointer width of the reference host, for `Ptr` and function values.
pub const PTR_SIZE: u32 = 8;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Layout {
    pub size: u32,
    pub align: u32,
    /// Named fields with offsets (structs, flow state, tuples as `0`, `1`, ...).
    pub fields: Vec<(String, u32)>,
}

impl Layout {
    fn scalar(size: u32) -> Layout {
        Layout { size, align: size, fields: Vec::new() }
    }
}

fn round_up(x: u32, align: u32) -> u32 {
    if align == 0 { x } else { x.div_ceil(align) * align }
}

/// Lay out a sequence of types as a struct.
fn record(a: &Analysis, names: impl Iterator<Item = String>, tys: &[TyId]) -> Option<Layout> {
    let mut size = 0u32;
    let mut align = 1u32;
    let mut fields = Vec::new();
    for (name, &t) in names.zip(tys) {
        let l = layout_of(a, t)?;
        size = round_up(size, l.align);
        fields.push((name, size));
        size = size.checked_add(l.size)?;
        align = align.max(l.align);
    }
    Some(Layout { size: round_up(size, align), align, fields })
}

fn enum_layout(a: &Analysis, variants: &[Vec<TyId>]) -> Option<Layout> {
    let tag = match variants.len() {
        0..=256 => 1,
        257..=65536 => 2,
        _ => 4,
    };
    let mut payload_size = 0;
    let mut payload_align = 1;
    for v in variants {
        let l = record(a, (0..).map(|i| i.to_string()), v)?;
        payload_size = payload_size.max(l.size);
        payload_align = payload_align.max(l.align);
    }
    let align = tag.max(payload_align);
    let payload_at = round_up(tag, payload_align);
    let size = round_up(payload_at + payload_size, align);
    Some(Layout { size, align, fields: vec![("tag".into(), 0), ("payload".into(), payload_at)] })
}

/// Substitute generic arguments (`Ty::Param(i)` → `args[i]`, `Len::Param(i)`
/// → the `ConstVal` in `args[i]`).
pub fn subst(a: &Analysis, ty: TyId, args: &[TyId]) -> TyId {
    if args.is_empty() {
        return ty;
    }
    // The interner is behind `&Analysis`; substitution needs `&mut`. Types
    // whose structure does not change are returned as is; otherwise we look
    // the substituted structure up and fall back to `ty` when it was never
    // interned (callers interning concrete instantiations do so in `sig`).
    match a.types.get(ty) {
        Ty::Param(i) => args.get(*i as usize).copied().unwrap_or(ty),
        Ty::Array(t, Len::Param(i)) => {
            let n = match args.get(*i as usize).map(|&c| a.types.get(c)) {
                Some(Ty::ConstVal(n)) => *n,
                _ => return ty,
            };
            let elem = subst(a, *t, args);
            a.types.find(&Ty::Array(elem, Len::Const(n))).unwrap_or(ty)
        }
        Ty::Array(t, len) => {
            let elem = subst(a, *t, args);
            if elem == *t { ty } else { a.types.find(&Ty::Array(elem, *len)).unwrap_or(ty) }
        }
        Ty::Tuple(ts) => {
            let ns: Vec<TyId> = ts.iter().map(|&t| subst(a, t, args)).collect();
            if ns == *ts { ty } else { a.types.find(&Ty::Tuple(ns)).unwrap_or(ty) }
        }
        Ty::Named(d, ts) => {
            let ns: Vec<TyId> = ts.iter().map(|&t| subst(a, t, args)).collect();
            if ns == *ts { ty } else { a.types.find(&Ty::Named(*d, ns)).unwrap_or(ty) }
        }
        Ty::Builtin(b, ts) => {
            let ns: Vec<TyId> = ts.iter().map(|&t| subst(a, t, args)).collect();
            if ns == *ts { ty } else { a.types.find(&Ty::Builtin(*b, ns)).unwrap_or(ty) }
        }
        _ => ty,
    }
}

/// Size and alignment of a value type (§12.1); `None` for heap, second-class,
/// generic, or not-yet-computed (flow `State` before M3) types.
pub fn layout_of(a: &Analysis, ty: TyId) -> Option<Layout> {
    match a.types.get(ty) {
        Ty::Int(k) => Some(Layout::scalar(k.bits() / 8)),
        Ty::Float(FloatKind::F32) => Some(Layout::scalar(4)),
        Ty::Float(FloatKind::F64) => Some(Layout::scalar(8)),
        Ty::Bool => Some(Layout::scalar(1)),
        Ty::Char => Some(Layout::scalar(4)),
        Ty::Unit => Some(Layout { size: 0, align: 1, fields: Vec::new() }),
        Ty::Array(t, Len::Const(n)) => {
            let l = layout_of(a, *t)?;
            Some(Layout { size: l.size.checked_mul(*n)?, align: l.align, fields: Vec::new() })
        }
        Ty::Array(_, Len::Param(_) | Len::Var(_)) => None,
        Ty::Tuple(ts) => record(a, (0..).map(|i| i.to_string()), ts),
        Ty::Builtin(b, args) => match b {
            BuiltinTy::Ptr => Some(Layout::scalar(PTR_SIZE)),
            BuiltinTy::Option => enum_layout(a, &[vec![], vec![args[0]]]),
            BuiltinTy::Result => enum_layout(a, &[vec![args[0]], vec![args[1]]]),
            _ => None,
        },
        Ty::Fn(_) => Some(Layout::scalar(PTR_SIZE)),
        Ty::Named(d, args) => layout_of_def(a, *d, args),
        Ty::ConstVal(_) | Ty::Param(_) | Ty::Var(_) | Ty::Error => None,
    }
}

/// Layout of a user type by its def (`onsa interface`), without interning its `TyId`.
pub fn layout_of_def(a: &Analysis, d: DefId, args: &[TyId]) -> Option<Layout> {
    match &a.def(d).kind {
        DefKind::Struct(s) => match &s.fields {
            Fields::Named(fs) => {
                let tys: Vec<TyId> = fs.iter().map(|f| subst(a, f.ty, args)).collect();
                record(a, fs.iter().map(|f| f.name.clone()), &tys)
            }
            Fields::Tuple(t) => {
                let l = layout_of(a, subst(a, *t, args))?;
                Some(Layout { size: l.size, align: l.align, fields: vec![("0".into(), 0)] })
            }
            Fields::Opaque => None,
        },
        DefKind::Enum(e) => {
            let vs: Vec<Vec<TyId>> =
                e.variants.iter().map(|v| v.fields.iter().map(|&t| subst(a, t, args)).collect()).collect();
            enum_layout(a, &vs)
        }
        DefKind::Alias(t) => layout_of(a, *t),
        _ => None,
    }
}

/// `IntKind` of the enum tag for `n` variants.
pub fn tag_kind(n: usize) -> IntKind {
    match n {
        0..=256 => IntKind::U8,
        257..=65536 => IntKind::U16,
        _ => IntKind::U32,
    }
}
