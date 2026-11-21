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
//! A level of a `vdelay~` in the `d` of a `vdelay~` takes 3.7 KB, one of `id~(id~(..))` 6.0 KB and a flow that calls a flow
//! 9.4 KB in a frame and 8.4 KB at `init` (64 MiB hold some 6700 and 7450 of them; `Frame::low_stack` stops it,
//! 2026-11-18; the `Frame::form` frame is 816 B, `in_child` 4.5 KB).
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
//! - [`interp_host`]: the host that runs the functions of the user's package in the interpreter (W7-19).
//! - [`pattern`]: `match` and the `let` that takes a value apart, and the patterns they use (a guard is tried for
//!   each way a `|` lets a pattern match).
//! - [`flow`]: an instance of a flow: the clock of each `let`, the stages `init`, `block` and the ticks (`sample / N`, `sample`) of `process` run them in, `reset`,
//!   and `render` and `Outcome` (a panic with the stage it is at: `init`, `block`, the frame `n`).
//! - [`branch`]: `par~` (a replica of its body for each value of its index, a state for each) and `if~` and `match~`
//!   (every branch is evaluated, one is taken, an arm not taken has the default of its bindings).
//! - [`boundary`]: an exported flow as the C API has it (§9.2, §14.2): `init`, `process` and `reset` with the status, a panic that
//!   zeroes the outputs of a call and poisons the instance, and one that leaves it uninitialized.
//! - [`rate`]: the rates (W7-09): the chain of `.down~(N)` and `.up~(N)` and its ratio, the ticks slower than `sample` a flow has stages for, and the time
//!   an instance of a chain runs in (§11.4, §11.9).
//! - [`state`]: the state of an instance, a tree of cells and instances made for each place a delay or a flow is called,
//!   the delays (`prev~`, `delay~`, `vdelay~`) with the two phases of a tick that `^` needs, the time (`sample_rate()`, `sample_tick()`).
//! - [`walk`]: the `test` blocks of a case taken apart and run on the evaluator: the calls of `render` and the asserts (W7-19).
//! - [`walk_model`], `reads`: the data a walk gives (the verdicts, the events), and what an assert reads of the outputs.
//! - [`sema_view`]: the tables of the checker the evaluator reads, in one file.

pub mod aggregate;
pub mod boundary;
pub mod branch;
pub mod call;
pub mod data;
pub mod expr;
pub mod flow;
mod hoist;
pub mod host;
pub mod interp_host;
pub mod pattern;
mod rate;
mod reads;
pub mod scalar;
pub mod sema_view;
pub mod state;
pub mod value;
pub mod walk;
pub mod walk_model;

#[cfg(test)]
mod aggregate_tests;
#[cfg(test)]
mod boundary_tests;
#[cfg(test)]
mod branch_tests;
#[cfg(test)]
mod call_tests;
#[cfg(test)]
mod data_tests;
#[cfg(test)]
mod expr_tests;
#[cfg(test)]
mod flow_tests;
#[cfg(test)]
mod hoist_tests;
#[cfg(test)]
mod instance_tests;
#[cfg(test)]
mod limits_tests;
#[cfg(test)]
mod multirate_tests;
#[cfg(test)]
mod pattern_tests;
#[cfg(test)]
mod probe_tests;
#[cfg(test)]
mod render_tests;
#[cfg(test)]
mod sequence_tests;
#[cfg(test)]
mod state_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod walk_tests;
