//! The test vectors of the numeric rules (plan D-16 2, Q-02 (a), R-113 2,
//! W2-02): the interpreter and the generated C, each against the data of
//! `tests/vectors/` (`FORMAT.md`). The two are never compared with each
//! other: the data is the reference.
//!
//! ```text
//! onsa_cases --vectors interp    gate item `vectors-interp`  ([`interp`])
//! onsa_cases --vectors c         gate item `vectors-c`       ([`c`]: every C toolchain)
//! ```
//!
//! The flow, for each package of `tests/vectors/fixture/` (`OPS.tsv`'s `pkg`):
//!
//! 1. [`data`]: the registry `OPS.tsv` (the one list of the operations, D-15:
//!    Rust holds no table of them and never branches on an operation's name)
//!    and the rows of its data files, read strictly by `FORMAT.md`; every row
//!    is typed by the types `OPS.tsv` writes, whether its operation runs or not.
//! 2. [`bind`]: each operation to the functions the fixture exports, checked
//!    against the Core of the build. An operation returning `Option` is the
//!    pair `<fn>_some` / `<fn>_val` (`FORMAT.md`; `_val` is called only when
//!    `_some` gives `true`). Its rows become calls ([`bind::plan`]).
//! 3. The implementation makes the calls ([`judge::Got`] for each).
//! 4. [`judge`]: each row by spec §13.4 ([`crate::scalar::same`]: bit for bit,
//!    `0.0` and `-0.0` differ; an expected `nan` is any NaN). `panic:<kind>`
//!    compares only that the call panics. A `held-*` row only runs: it fails
//!    on an internal error or a run that ends, never on its value.
//! 5. [`item`]: a case per operation (and per toolchain for C), applied to
//!    the list (`tests/pending.toml`, kind `gate`, `<item>/<case>`,
//!    [`crate::ccheck::reconcile_cases`]), and the report.
//!
//! What the list may hold: an operation's failing rows (a value, a panic or
//! not, the boundary's report, a C run that ended inside the operation and the
//! rows it did not make), exactly as many as its entry's `rows`. An internal
//! error of the interpreter only with `expect = "internal"`. Never: an error
//! of the data, of the fixture's build, of the harness, or a time budget
//! exceeded (errors of the item, exit 2).
//!
//! A package that the list holds as a whole test case (`test-case`
//! `tests/vectors/fixture/<pkg>`: it does not check yet) is not run; its
//! operations are counted and shown. Another package that does not build
//! is an error of the item.

pub mod bind;
pub mod c;
pub mod data;
pub mod interp;
pub mod item;
pub mod judge;
#[cfg(test)]
mod tests;

pub use item::{run_item, run_item_with, text};

/// The data, from the repository root.
pub const DIR: &str = "tests/vectors";
/// The registry of the operations, in [`DIR`].
pub const REGISTRY: &str = "OPS.tsv";
/// The record of the files, in [`DIR`]; its first line is the format.
pub const MANIFEST: &str = "MANIFEST";
/// The fixture packages, in [`DIR`].
pub const FIXTURE: &str = "fixture";
/// The format this reader reads (`FORMAT.md`: the first line of `MANIFEST`).
pub const FORMAT: &str = "format 1";
/// The arguments of an operation without any (`FORMAT.md`).
pub const NO_ARGS: &str = "()";
/// The suffixes of the two functions of an operation that returns `Option` (`FORMAT.md`).
pub const SOME: &str = "_some";
pub const VAL: &str = "_val";

/// An implementation the data is compared with: a gate item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Impl {
    Interp,
    C,
}

impl Impl {
    pub fn parse(s: &str) -> Option<Impl> {
        match s {
            "interp" => Some(Impl::Interp),
            "c" => Some(Impl::C),
            _ => None,
        }
    }

    /// The gate item (`tools/gate_steps.py`).
    pub fn item(self) -> &'static str {
        match self {
            Impl::Interp => "vectors-interp",
            Impl::C => "vectors-c",
        }
    }

    /// The form of the item's cases, for messages.
    fn form(self) -> &'static str {
        match self {
            Impl::Interp => "`<operation>` (`u64.mul`)",
            Impl::C => "`<operation>[<toolchain>]` (`u32.mul[c-gcc]`)",
        }
    }
}
