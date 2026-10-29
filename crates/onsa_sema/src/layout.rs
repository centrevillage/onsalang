//! Layout (spec §12.4): declaration order, natural alignment, no reordering.
//! Enums: the smallest tag of `U8` / `U16` / `U32`, then the largest variant.

use crate::ty::{BuiltinTy, Env, FloatKind, IntKind, Len, Ty, TyId};
use crate::walk::{Holds, Walk};
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

/// Where a walk is: the arguments its types are read under (R-30), and the
/// named types entered on its way ([`Walk::enter`]).
type At<'e> = (Option<&'e Env<'e>>, u32);

/// Lay out a sequence of types as a struct.
fn record(w: &Walk, names: impl Iterator<Item = String>, tys: &[TyId], at: At) -> Option<Layout> {
    let mut size = 0u32;
    let mut align = 1u32;
    let mut fields = Vec::new();
    for (name, &t) in names.zip(tys) {
        let l = walk(w, t, at)?;
        size = round_up(size, l.align);
        fields.push((name, size));
        size = size.checked_add(l.size)?;
        align = align.max(l.align);
    }
    Some(Layout { size: round_up(size, align), align, fields })
}

fn enum_layout(w: &Walk, variants: &[&[TyId]], at: At) -> Option<Layout> {
    let tag = match variants.len() {
        0..=256 => 1,
        257..=65536 => 2,
        _ => 4,
    };
    let mut payload_size = 0;
    let mut payload_align = 1;
    for v in variants {
        let l = record(w, (0..).map(|i| i.to_string()), v, at)?;
        payload_size = payload_size.max(l.size);
        payload_align = payload_align.max(l.align);
    }
    let align = tag.max(payload_align);
    let payload_at = round_up(tag, payload_align);
    let size = round_up(payload_at + payload_size, align);
    Some(Layout { size, align, fields: vec![("tag".into(), 0), ("payload".into(), payload_at)] })
}

/// Size and alignment of a value type (§12.1); `None` for heap, second-class,
/// generic, or not-yet-computed (flow `State` before M3) types.
pub fn layout_of(a: &Analysis, ty: TyId) -> Option<Layout> {
    layout_in(a, ty, None)
}

/// [`layout_of`] of `ty` read under the arguments `env` (R-30).
pub fn layout_in(a: &Analysis, ty: TyId, env: Option<&Env>) -> Option<Layout> {
    walk(&Walk::new(a), ty, (env, 0))
}

fn walk(w: &Walk, ty: TyId, (env, depth): At) -> Option<Layout> {
    let (ty, env) = w.at(ty, env)?;
    let at = (env, depth);
    match ty {
        Ty::Int(k) => Some(Layout::scalar(k.bits() / 8)),
        Ty::Float(FloatKind::F32) => Some(Layout::scalar(4)),
        Ty::Float(FloatKind::F64) => Some(Layout::scalar(8)),
        Ty::Bool => Some(Layout::scalar(1)),
        Ty::Char => Some(Layout::scalar(4)),
        Ty::Unit => Some(Layout { size: 0, align: 1, fields: Vec::new() }),
        Ty::Array(t, len) => match w.a.types.len_in(*len, env) {
            Len::Const(n) => {
                let l = walk(w, *t, at)?;
                Some(Layout { size: l.size.checked_mul(n)?, align: l.align, fields: Vec::new() })
            }
            Len::Param(_) | Len::Var(_) => None,
        },
        Ty::Tuple(ts) => record(w, (0..).map(|i| i.to_string()), ts, at),
        Ty::Builtin(b, args) => match b {
            BuiltinTy::Ptr => Some(Layout::scalar(PTR_SIZE)),
            BuiltinTy::Option => enum_layout(w, &[&[], &args[..1]], at),
            BuiltinTy::Result => enum_layout(w, &[&args[..1], &args[1..2]], at),
            _ => None,
        },
        Ty::Fn(_) => Some(Layout::scalar(PTR_SIZE)),
        Ty::Named(d, args) => named(w, *d, args, at),
        Ty::ConstVal(_) | Ty::Param(_) | Ty::Var(_) | Ty::Error => None,
    }
}

/// Layout of a user type by its def (`onsa interface`), without interning its `TyId`.
pub fn layout_of_def(a: &Analysis, d: DefId, args: &[TyId]) -> Option<Layout> {
    named(&Walk::new(a), d, args, (None, 0))
}

fn named(w: &Walk, d: DefId, args: &[TyId], (env, depth): At) -> Option<Layout> {
    w.remember(&w.a.known.layouts, (d, args, env, depth), |depth, key| {
        let (holds, env, depth) = w.enter(d, args, env, (depth, key))?;
        let at = (env.as_ref(), depth);
        match holds {
            Holds::Fields(fs, _) => {
                let tys: Vec<TyId> = fs.iter().map(|f| f.ty).collect();
                record(w, fs.iter().map(|f| f.name.clone()), &tys, at)
            }
            Holds::Variants(vs) => enum_layout(w, &vs.iter().map(|v| &v.fields[..]).collect::<Vec<_>>(), at),
            Holds::Alias(t) => walk(w, t, at),
            Holds::Opaque(_) | Holds::Nothing => None,
        }
    })
}

/// `IntKind` of the enum tag for `n` variants.
pub fn tag_kind(n: usize) -> IntKind {
    match n {
        0..=256 => IntKind::U8,
        257..=65536 => IntKind::U16,
        _ => IntKind::U32,
    }
}
