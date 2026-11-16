//! The reference evaluator of a flow (W7-01, Q-02 (b), K-04): a small evaluator
//! that reads the syntax tree and the tables of names and types of `onsa_sema`
//! and evaluates a flow one sample at a time, from the spec alone. It shares
//! nothing with the interpreter, so that the two are independent sources.
//!
//! - [`value`]: the values of the evaluator, their defaults (§6.4) and their
//!   equality (§13.4).
//! - [`scalar`]: the operators of §3.4 and `as` of §3.3 on the scalars, with the
//!   panics of §9.2 as values.

pub mod scalar;
pub mod value;

#[cfg(test)]
mod probe_tests;
#[cfg(test)]
mod tests;
