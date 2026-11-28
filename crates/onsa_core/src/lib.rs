//! Onsa Core IR: definitions, verifier, lowering from the typed AST,
//! monomorphization and flow lowering (M3: T3-2 to T3-6).
//!
//! See `design/04-core.md` for the IR shape and D-03 for
//! how flows become `init` / `reset` / `ctl` / `tick` / `process`.

pub mod dump;
pub mod effects;
pub mod ir;
pub mod layout;
pub mod lower;
pub mod prim;
pub mod reach;
mod rt_cycles;
pub mod verify;
pub mod walk;

#[cfg(test)]
mod tests;

pub use dump::{dump, dump_item};
pub use ir::*;
pub use layout::{FieldLayout, FlowLayout, RecordLayout, TyFacts, flow_layout, size_align};
pub use lower::flow::{FlowFns, FlowMeta};
pub use lower::{GenericArg, LowerFailure, LowerOptions, lower, lower_with};
pub use onsa_sema::def::{ParamInfo, ParamKey, ParamKind, ParamNumber};
pub use onsa_sema::flow_names::FixedField;
pub use reach::{Reach, reach};
pub use verify::depth::CORE_DEPTH_LIMIT;
pub use verify::{Rule, VerifyError, verify};
