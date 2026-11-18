//! The clocks of a flow (§11.3) in two layers (W7-02 U1):
//!
//! - [`ClockName`]: the names stage's layer, the base clocks a name after
//!   `at` and the heading of a flow write (`init`, `block`, `sample`). The
//!   one table of the names (D-15); [`resolve_name`] looks one up (E0302).
//! - [`Clock`]: the layer of the values, the clock of an expression, a local,
//!   an input or the output, which the tables of a flow hold
//!   ([`crate::flow::FlowInfo::clocks`], [`crate::def::FlowInput::clock`]).
//!   Its stage of evaluation is a [`ClockStage`] ([`Clock::stage`]).
//!
//! The comparisons of clocks are not here yet (W7-02 U2a): the rate pass
//! keeps its own order (`flow::FlowRate`) and maps its results here.

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast;
use serde::{Deserialize, Serialize};

/// A base clock a name writes (§11.3): after `at`, after the type of an input
/// or of the output of a flow. `event` is not one in this version (E0302).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ClockName {
    Init,
    Block,
    Sample,
}

impl ClockName {
    /// Every name, slowest first.
    pub const ALL: [ClockName; 3] = [ClockName::Init, ClockName::Block, ClockName::Sample];

    /// The name of the clock (§11.3): the one table of the clock names.
    pub fn name(self) -> &'static str {
        match self {
            ClockName::Init => "init",
            ClockName::Block => "block",
            ClockName::Sample => "sample",
        }
    }

    /// The clock of the name `name`, if it is one.
    pub fn of_name(name: &str) -> Option<ClockName> {
        ClockName::ALL.into_iter().find(|c| c.name() == name)
    }

    /// The clock the name `name` of a rate written as a type names (`Sig`,
    /// [`onsa_syntax::foreign::RATE_TYPES`], S-120), if it is one: the names
    /// of that list are in the order of [`ClockName::ALL`].
    pub fn of_type_name(name: &str) -> Option<ClockName> {
        ClockName::ALL.into_iter().zip(onsa_syntax::foreign::RATE_TYPES).find(|&(_, n)| n == name).map(|(c, _)| c)
    }

    /// The clock of the values the name gives.
    pub fn clock(self) -> Clock {
        match self {
            ClockName::Init => Clock::Init,
            ClockName::Block => Clock::Block,
            ClockName::Sample => Clock::SAMPLE,
        }
    }
}

/// The clock after `at` (§11.3, S-359): a name of the clock namespace, or
/// E0302 at the name, whatever value or type has that name.
pub(crate) fn resolve_name(c: &ast::Clock) -> Result<ClockName, Diagnostic> {
    if let Some(r) = ClockName::of_name(&c.name.name) {
        return Ok(r);
    }
    let names = ClockName::ALL.iter().map(|r| format!("`{}`", r.name())).collect::<Vec<_>>().join(", ");
    Err(Diagnostic::new(
        Stage::Names,
        Code::E0302,
        c.name.span,
        format!("cannot find the clock `{}`; a clock after `at` is a name of the clocks (§11.3)", c.name.name),
    )
    .with_found(c.name.name.clone())
    .with_rule(format!("the clocks of this version are {names}")))
}

/// The clock of a value of a flow (§11.3). No order: two clocks are compared
/// by the rules of the clocks, not by the place of their variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Clock {
    /// A compile-time constant.
    Const,
    Init,
    Block,
    /// The clock of an event input (W7-11); none is made in this version.
    Event(EventSrc),
    /// The `sample` of the body times 2 to the power of the ratio (S-1077).
    Tick(Ratio),
    /// The clock of `sample_tick()` (W7-09); none is made in this version.
    Ambient,
    /// A clock in error (an input whose clock has a diagnostic).
    Error,
}

/// The power of 2 of a tick clock over the `sample` of the body (S-1077).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Ratio(pub i32);

/// The source of an event clock: a provisional form (W7-11 decides it).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EventSrc(pub u32);

/// A stage of evaluation, slowest first (`Tick` by its ratio). The name is
/// not `Stage`, which is the stage of the compiler (`onsa_diag::Stage`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ClockStage {
    Init,
    Block,
    Tick(Ratio),
}

impl ClockStage {
    /// The stage of the `sample` of the body ([`Clock::SAMPLE`]): the one
    /// spelling of it (D-15).
    pub const SAMPLE: ClockStage = ClockStage::Tick(Ratio(0));
}

impl Clock {
    /// The `sample` of the body.
    pub const SAMPLE: Clock = Clock::Tick(Ratio(0));

    /// The stage the values of the clock are evaluated at. `None` of a
    /// constant, `sample_tick()` and a clock in error, whose stage is the
    /// stage of the place that reads them.
    pub fn stage(self) -> Option<ClockStage> {
        match self {
            Clock::Init => Some(ClockStage::Init),
            Clock::Block => Some(ClockStage::Block),
            Clock::Tick(k) => Some(ClockStage::Tick(k)),
            Clock::Const | Clock::Ambient | Clock::Error => None,
            Clock::Event(_) => onsa_diag::internal::bug(None, "the stage of an event clock, which W7-11 makes"),
        }
    }

    /// The clock as `onsa interface` and `onsa graph` write it (§11.3):
    /// `constant`, `init`, `block`, `sample`, `sample / 4`, `sample * 2`.
    /// A clock no text names (in error, of `sample_tick()`, of an event) is
    /// an internal error at `at`.
    pub fn shown(self, at: Span) -> String {
        let k = match self {
            Clock::Const => return "constant".into(),
            Clock::Init => return ClockName::Init.name().into(),
            Clock::Block => return ClockName::Block.name().into(),
            Clock::Tick(Ratio(k)) => k,
            Clock::Event(_) | Clock::Ambient | Clock::Error => {
                onsa_diag::internal::bug(Some(at), format!("the clock {self:?} has no text"))
            }
        };
        let sample = ClockName::Sample.name();
        let Some(n) = 2u64.checked_pow(k.unsigned_abs()) else {
            onsa_diag::internal::bug(Some(at), format!("the ratio of the clock {self:?} out of the text"))
        };
        match k {
            0 => sample.into(),
            1.. => format!("{sample} * {n}"),
            _ => format!("{sample} / {n}"),
        }
    }
}
