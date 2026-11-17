//! The reference evaluator of a flow (W7-01, Q-02 (b), K-04): a small evaluator
//! that reads the syntax tree and the tables of names and types of `onsa_sema`
//! and evaluates a flow one sample at a time, from the spec alone. It shares the syntax tree (the parser, whose
//! precedence and associativity are not an independent source), `float_value`, the tables of `onsa_sema` and
//! `IntKind` with the interpreter, and has its own operators and rules of evaluation: those are the two sources.
//!
//! Call it in a thread of a large stack (`onsa_diag::stack::run`), not in a default 2 MiB one. A level of nesting takes
//! in a debug build (2026-11-16, the least stack that lets an input through): 2.4 KB for a `match` arm, 3.5 KB for
//! `Some(..)` in a value and in a pattern, 4.0 KB for a struct pattern, 6.1 KB for an array literal and its index, 6.9 KB
//! for a struct literal and its field, 8.0 KB for a chain of defaults of structs, 12.7 KB for a level of calls of
//! `if n == 0 { 0 } else { 1 + rec(n - 1) }` (the 128 of §12.5 are 1.6 MB); a body may nest 256 levels (§2.5), so
//! 0.6 to 2 MB. The chain of constants that read constants, with an initializer 256 levels deep each, is more than the
//! stack of the thread: [`expr::Limits`] keeps 4 MiB of it back, and an `eval` that finds less left stops with
//! `Unavailable`, whatever the input (a thread that is not one of `onsa_diag::stack` has no such guard).
//! A level of a `vdelay~` in the `d` of a `vdelay~` takes 3.7 KB (2026-11-17).
//!
//! - [`value`]: the values of the evaluator, their defaults (§6.4) and their
//!   equality (§13.4).
//! - [`scalar`]: the operators of §3.4 and `as` of §3.3 on the scalars, with the
//!   panics of §9.2 as values.
//! - [`expr`]: the expressions: names, literals, operators, `as`, `at`, `if`, blocks and `let`, and the limits.
//! - [`aggregate`]: the literals of tuples, arrays and structs, the fields, the elements and the indexes, and the
//!   variants an enum is built with.
//! - [`call`]: the calls of functions and methods, the ones with a body of expressions only evaluated here, the others
//!   handed to the [`host`] (§6.1, §11.5), and the limit of 128 nested calls (§12.5).
//! - [`host`]: the door of the functions the evaluator does not evaluate, and the two hosts it has of its own.
//! - [`pattern`]: `match` and the `let` that takes a value apart, and the patterns they use (a guard is tried for
//!   each way a `|` lets a pattern match).
//! - [`flow`]: one instance of a flow: the clock of each `let` and the stages `init` and `process` run them in.
//! - [`state`]: the state of an instance, a tree of cells made for each place a delay is called, and the delays
//!   (`prev~`, `delay~`, `vdelay~`) with the two phases of a tick that `^` needs.
//! - [`sema_view`]: the tables of the checker the evaluator reads, in one file.

pub mod aggregate;
pub mod call;
pub mod expr;
pub mod flow;
pub mod host;
pub mod pattern;
pub mod scalar;
pub mod sema_view;
pub mod state;
pub mod value;

#[cfg(test)]
mod aggregate_tests;
#[cfg(test)]
mod call_tests;
#[cfg(test)]
mod expr_tests;
#[cfg(test)]
mod flow_tests;
#[cfg(test)]
mod limits_tests;
#[cfg(test)]
mod pattern_tests;
#[cfg(test)]
mod probe_tests;
#[cfg(test)]
mod state_tests;
#[cfg(test)]
mod tests;
