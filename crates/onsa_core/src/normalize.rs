//! The normal form of the evaluation order (W8-03, R1 to R4): a stage of
//! [`crate::lower`] after the bounds and before the storage of the locals,
//! on each function. It reads the types and makes none (`&Types`).
//! This version changes nothing (U7a writes it).

use crate::ir::{FnDef, Types};

/// Put the body of `f` in the normal form.
pub fn normalize(_tys: &Types, _f: &mut FnDef) {}
