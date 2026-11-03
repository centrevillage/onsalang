//! The primitives (`onsa_sema::prim`): the table is sema's, so that the
//! analysis resolves a `std` `target` declaration to its row (S-69 (2)); the
//! backends read it here, as they depend on `onsa_core` alone.

pub use onsa_sema::prim::*;
