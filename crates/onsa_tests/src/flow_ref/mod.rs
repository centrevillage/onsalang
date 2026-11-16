//! The reference evaluator of a flow (W7-01, Q-02 (b), K-04): a small evaluator
//! that reads the syntax tree and the tables of names and types of `onsa_sema`
//! and evaluates a flow one sample at a time, from the spec alone. It shares the syntax tree (the parser, whose
//! precedence and associativity are not an independent source), `float_value`, the tables of `onsa_sema` and
//! `IntKind` with the interpreter, and has its own operators and rules of evaluation: those are the two sources.
//!
//! Call it in a thread of a large stack (`onsa_diag::stack::run`), not in a default 2 MiB one: a level of nesting
//! of an expression takes about 2 KB of a debug build (a constant that reads a constant about 5 KB), and a body
//! may nest 256 levels (§2.5): 0.6 MB, and 1.4 MB for a chain of 256 constants.
//!
//! - [`value`]: the values of the evaluator, their defaults (§6.4) and their
//!   equality (§13.4).
//! - [`scalar`]: the operators of §3.4 and `as` of §3.3 on the scalars, with the
//!   panics of §9.2 as values.
//! - [`expr`]: the expressions: names, literals, operators, `as`, `at`, `if`.
//! - [`sema_view`]: the tables of the checker the evaluator reads, in one file.

pub mod expr;
pub mod scalar;
pub mod sema_view;
pub mod value;

#[cfg(test)]
mod expr_tests;
#[cfg(test)]
mod probe_tests;
#[cfg(test)]
mod tests;
