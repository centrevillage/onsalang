//! Argument modes, exclusivity, second-class values, borrow bindings and
//! Affine moves (spec §5.2, §5.3, §5.4, §7, §12.2; W4-07 memo 1.1). Runs over
//! the typed tables of [`crate::body::BodyInfo`] and the states of the
//! bindings, for the bodies whose units did not fail before (§18.1), and
//! reports the first diagnostic of each body (P-01).

use std::collections::{HashMap, HashSet};

use crate::DefId;
use crate::body::LocalId;

mod calls;
mod capture;
mod check;
mod consume;
mod exclusive;
mod flow;
mod frozen;
mod marks;
mod place;
mod state;
#[cfg(test)]
mod tests;
mod walk;
mod write;

pub(crate) use check::check_all;

/// Locals moved somewhere in each body (the `rt` pass uses it for drops).
pub(crate) type MovedLocals = HashMap<DefId, HashSet<LocalId>>;
