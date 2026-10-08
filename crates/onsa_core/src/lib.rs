//! Onsa Core IR: definitions, verifier, lowering from the typed AST,
//! monomorphization and flow lowering (M3: T3-2 to T3-6).
//!
//! See `docs/implementation-tasks.md` §3.4 for the IR shape and §1 D-03 for
//! how flows become `init` / `reset` / `ctl` / `tick` / `process`.

pub mod dump;
pub mod ir;
pub mod layout;
pub mod lower;
pub mod prim;
pub mod reach;
pub mod verify;
pub mod walk;

#[cfg(test)]
mod tests;

pub use dump::{dump, dump_item};
pub use ir::*;
pub use layout::{FieldLayout, FlowLayout, RecordLayout, flow_layout, flow_layout_for, size_align, size_align_for};
pub use lower::flow::{FlowFns, FlowMeta};
pub use lower::{GenericArg, LowerFailure, LowerOptions, lower, lower_with};
pub use reach::{Reach, reach};
pub use verify::{VerifyError, verify};
