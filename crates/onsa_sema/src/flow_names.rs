//! The names of the flow language that every stage reads: the clock after
//! `at` (§11.3, S-359; the names are [`Rate::clock`]) and the built-in delays
//! `prev~` / `delay~` / `vdelay~` and the other builtin names of a flow
//! (§11.4, §2.2). The one table of each (plan
//! D-15): the names stage, the flow checks, the gate of the flow syntax
//! outside a flow (`crate::flow_syntax`), `onsa graph` and `onsa interface`
//! read them from here.

use onsa_diag::{Code, Diagnostic, Stage};
use onsa_syntax::ast::Clock;

use crate::ty::Rate;

/// The clock after `at` (§11.3, S-359): a name of the clock namespace, or
/// E0302 at the name, whatever value or type has that name.
pub(crate) fn clock_rate(c: &Clock) -> Result<Rate, Diagnostic> {
    if let Some(r) = Rate::of_clock(&c.name.name) {
        return Ok(r);
    }
    let names = Rate::ALL.iter().map(|r| format!("`{}`", r.clock())).collect::<Vec<_>>().join(", ");
    Err(Diagnostic::new(
        Stage::Names,
        Code::E0302,
        c.name.span,
        format!("cannot find the clock `{}`; a clock after `at` is a name of the clocks (§11.3)", c.name.name),
    )
    .with_found(c.name.name.clone())
    .with_rule(format!("the clocks of this version are {names}")))
}

/// The builtin of a flow that is no delay and is checked (§11.4).
pub(crate) const SAMPLE_RATE: &str = "sample_rate";

/// The builtin names of a flow that are no delay (§11.4): `sample_tick` is
/// not checked yet, but its name is reserved as the others.
const OTHER_BUILTINS: [&str; 2] = [SAMPLE_RATE, "sample_tick"];

/// `name` is a builtin name of a flow (§2.2): no binding a flow body sees
/// (an item of a module, a name a `use` binds) takes it (E0304, S-542).
pub(crate) fn is_builtin(name: &str) -> bool {
    Delay::named(name).is_some() || OTHER_BUILTINS.contains(&name)
}

/// A built-in delay (§11.4): the one table of their names and arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delay {
    /// `prev~`
    Prev,
    /// `delay~`
    Fixed,
    /// `vdelay~`
    Variable,
}

impl Delay {
    const ALL: [Delay; 3] = [Delay::Prev, Delay::Fixed, Delay::Variable];

    /// The name (`prev`); a call writes `~` after it (`prev~(…)`).
    pub fn name(self) -> &'static str {
        match self {
            Delay::Prev => "prev",
            Delay::Fixed => "delay",
            Delay::Variable => "vdelay",
        }
    }

    pub fn named(name: &str) -> Option<Delay> {
        Delay::ALL.into_iter().find(|d| d.name() == name)
    }

    /// The position of the optional `init`, which is the last argument
    /// (`prev~(e, init)`, `delay~(e, N, init)`, `vdelay~(e, d, MAX, init)`).
    pub fn init_index(self) -> usize {
        match self {
            Delay::Prev => 1,
            Delay::Fixed => 2,
            Delay::Variable => 3,
        }
    }
}
