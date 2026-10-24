//! The names in scope in every module that the compiler gives (spec §15.1,
//! §4.1): the builtin types and the variants of `Option` and `Result`.

use crate::Analysis;
use crate::resolve::Builtin;
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

/// The variants of the prelude.
const VARIANTS: [(&str, Builtin); 4] =
    [("Some", Builtin::Some), ("None", Builtin::None), ("Ok", Builtin::Ok), ("Err", Builtin::Err)];

/// Fills `a.prelude`, and `a.builtin_key` with the key of each generic
/// builtin (the type with no arguments) its associated items are under.
pub(super) fn build(a: &mut Analysis) {
    for name in SCALARS {
        let Some(t) = a.types.scalar(name) else {
            onsa_diag::internal::bug(None, format!("`{name}` is not a scalar type"))
        };
        a.prelude.insert(name.to_string(), Builtin::Scalar(t));
    }
    for b in GENERICS {
        let key = a.types.builtin(b, Vec::new());
        a.builtin_key.insert(b, key);
        a.prelude.insert(b.name().to_string(), Builtin::Generic(b));
    }
    for (name, b) in VARIANTS {
        a.prelude.insert(name.to_string(), b);
    }
}
