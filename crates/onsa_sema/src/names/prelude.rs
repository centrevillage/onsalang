//! The names in scope in every module (spec §15.1, §4.1, S-107, S-659): the
//! compiler's (the builtin types, the variants of `Option` and `Result`,
//! `panic`, the traits of §6.3 and the kind constraints), and the items of
//! `std.core` (`Alloc`, `Block`).

use crate::Analysis;
use crate::def::{Bound, TRAITS};
use crate::resolve::{Builtin, Entity};
use crate::ty::BuiltinTy;

/// The scalar types (§4.1), in the order of their `TyId`s.
const SCALARS: [&str; 12] = ["I8", "I16", "I32", "I64", "U8", "U16", "U32", "U64", "F32", "F64", "Bool", "Char"];

/// The generic builtin types (§4.1).
const GENERICS: [BuiltinTy; 10] = [
    BuiltinTy::Str,
    BuiltinTy::Bytes,
    BuiltinTy::Array,
    BuiltinTy::Map,
    BuiltinTy::Set,
    BuiltinTy::Buf,
    BuiltinTy::Span,
    BuiltinTy::Ptr,
    BuiltinTy::Option,
    BuiltinTy::Result,
];

/// The variants of the prelude, and `panic`.
const VALUES: [(&str, Builtin); 5] = [
    ("Some", Builtin::Some),
    ("None", Builtin::None),
    ("Ok", Builtin::Ok),
    ("Err", Builtin::Err),
    ("panic", Builtin::Panic),
];

/// The module of std whose `pub` items are in the prelude (§15.1, S-659).
const CORE: &str = "core";

/// The lang item of the effect of the heap (D-08), an item of `std.core`.
const ALLOC: &str = "Alloc";

/// Fills `a.prelude` with the compiler's names, and `a.builtin_key` with the
/// key of each generic builtin (the type with no arguments) its associated
/// items are under. Before the items are collected.
pub(super) fn build(a: &mut Analysis) {
    let mut put = |name: &str, b: Builtin| a.prelude.insert(name.to_string(), Entity::Builtin(b));
    for (i, (name, _)) in TRAITS.iter().enumerate() {
        put(name, Builtin::Trait(i as u8));
    }
    for (name, b) in VALUES {
        put(name, b);
    }
    put(onsa_syntax::foreign::COPY, Builtin::Kind(Bound::Copy));
    put(onsa_syntax::foreign::DUP, Builtin::Kind(Bound::Dup));
    for name in SCALARS {
        let Some(t) = a.types.scalar(name) else {
            onsa_diag::internal::bug(None, format!("`{name}` is not a scalar type"))
        };
        a.prelude.insert(name.to_string(), Entity::Builtin(Builtin::Scalar(t)));
    }
    for b in GENERICS {
        let key = a.types.builtin(b, Vec::new());
        a.builtin_key.insert(b, key);
        a.prelude.insert(b.name().to_string(), Entity::Builtin(Builtin::Generic(b)));
    }
}

/// The items of `std.core` in the prelude, once the items are collected and
/// before their clashes (§15.1): its `pub` items, of which `Alloc` is the
/// lang item. The embedded std has them, so a `std.core` with no `Alloc` is
/// a bug; a package analyzed with no std or an empty one (unit tests of this
/// crate) has neither.
pub(super) fn declared(a: &mut Analysis) {
    let std = a.modules.roots.iter().copied().find(|&r| a.modules.is_std(r));
    let Some(core) = std.and_then(|r| a.modules.get(r).children.get(CORE).copied()) else { return };
    a.modules.core = Some(core);
    let mut items: Vec<(String, crate::def::DefId)> =
        a.modules.get(core).items.iter().map(|(n, &d)| (n.clone(), d)).collect();
    items.sort();
    for (name, d) in items {
        if a.def(d).vis == onsa_syntax::ast::Vis::Pub {
            a.prelude.insert(name, Entity::Def(d));
        }
    }
    match a.prelude.get(ALLOC) {
        Some(&Entity::Def(d)) => a.alloc = Some(d),
        _ => onsa_diag::internal::bug(None, "`std.core` declares no `Alloc`"),
    }
}
