//! The builtin names of the flow language that every stage reads: the
//! built-in delays `prev~` / `delay~` / `vdelay~` and the other builtin names
//! of a flow (§11.4, §2.2). The one table of them (plan D-15): the names
//! stage, the flow checks, `onsa graph` and `onsa interface` read them from
//! here. The names of the clocks after `at` (§11.3, S-359) are
//! [`crate::clock::ClockName`]'s.

use onsa_diag::{Code, Diagnostic, Span, Stage};
use serde::{Deserialize, Serialize};

/// The builtins of a flow that are no delay (§11.4): the rate and the
/// time since `reset` in ticks, whose counter the Core of W7-16 lowers.
pub(crate) const SAMPLE_RATE: &str = "sample_rate";
const SAMPLE_TICK: &str = "sample_tick";

/// The names the processor gives the state of a flow (§11.6, S-1138), all
/// of a form no user writes (`_` first or a `.` in it, §2.3): the scope of
/// the nodes of the output, the kinds of a `par~` and of a hoisted field
/// (§11.3), and the fixed fields. The one table of them: the names of the
/// plan (`flow::plan`) and the lowering and the C backend that look a
/// fixed field up read them from here.
pub const OUTPUT_SCOPE: &str = "_out";
pub(crate) const PAR: &str = "par";
pub const HOIST: &str = "_hoist";

/// `<scope>.<name>` (`a.prev_0`, §11.6): the one join of a scope and a name.
pub fn qualify(scope: &str, name: &str) -> String {
    format!("{scope}.{name}")
}

/// A fixed field of the state of a flow (§11.6, §12.4, S-1138).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixedField {
    SampleRate,
    /// The counter of the phase (§11.9, S-1137).
    Tick,
    /// The upper word of the time (§11.4, §12.4, S-1211).
    TickHi,
    Poisoned,
    Initialized,
    /// The pointer to the bulk region (§12.4).
    Bulk,
}

impl FixedField {
    pub fn name(self) -> &'static str {
        match self {
            FixedField::SampleRate => "_sample_rate",
            FixedField::Tick => "_tick",
            FixedField::TickHi => "_tick_hi",
            FixedField::Poisoned => "_poisoned",
            FixedField::Initialized => "_initialized",
            FixedField::Bulk => "_bulk",
        }
    }
}

/// A builtin name of a flow (§2.2, §11.4), as the names stage records a
/// flow body naming one (`prev~(x)`, `sample_rate()`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FlowBuiltin {
    Delay(Delay),
    SampleRate,
    SampleTick,
}

impl FlowBuiltin {
    pub fn named(name: &str) -> Option<FlowBuiltin> {
        match name {
            SAMPLE_RATE => Some(FlowBuiltin::SampleRate),
            SAMPLE_TICK => Some(FlowBuiltin::SampleTick),
            _ => Delay::named(name).map(FlowBuiltin::Delay),
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            FlowBuiltin::Delay(d) => d.name(),
            FlowBuiltin::SampleRate => SAMPLE_RATE,
            FlowBuiltin::SampleTick => SAMPLE_TICK,
        }
    }

    /// E0308 for the builtin name written where it is not the callee of its
    /// call (§11.4, §15.1, S-720), with no candidate: the note shows the
    /// call. `names` are the spans of the names of the path from the builtin
    /// one; the error is at it and the name after its `.` (`prev.y`), in
    /// the source `text`.
    pub(crate) fn misplaced(self, mut names: impl Iterator<Item = Span>, text: &str) -> Diagnostic {
        let name = names.next().expect("the builtin name");
        let end = names.next().unwrap_or(name);
        let span = Span::new(name.file, name.start, end.end);
        let found = span.text_in(text);
        let call = match self {
            FlowBuiltin::Delay(d) => format!("{}~(…)", d.name()),
            _ => format!("{}()", self.name()),
        };
        let msg =
            format!("`{}` is a builtin name of a flow, written only as the callee of its call (§11.4)", self.name());
        Diagnostic::new(Stage::Names, Code::E0308, span, msg)
            .with_found(found)
            .with_note(name, format!("its call is `{call}`"))
    }
}

/// `name` is a builtin name of a flow (§2.2): no binding a flow body sees
/// (an item of a module, a name a `use` binds) takes it (E0304, S-542).
pub(crate) fn is_builtin(name: &str) -> bool {
    FlowBuiltin::named(name).is_some()
}

/// A modifier of an instance (§11.9, §11.10): the closed list of their
/// names, which the names stage looks up only after the call of an instance
/// (S-556). The one table of them (D-15).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Modifier {
    Down,
    Up,
    When,
    ResetIf,
}

impl Modifier {
    pub const ALL: [Modifier; 4] = [Modifier::Down, Modifier::Up, Modifier::When, Modifier::ResetIf];

    /// The name (`down`); a call writes `~` after it (`.down~(…)`).
    pub fn name(self) -> &'static str {
        match self {
            Modifier::Down => "down",
            Modifier::Up => "up",
            Modifier::When => "when",
            Modifier::ResetIf => "reset_if",
        }
    }

    pub fn named(name: &str) -> Option<Modifier> {
        Modifier::ALL.into_iter().find(|m| m.name() == name)
    }

    /// The rate it gives (§11.9): `.down~(N)` the `sample / N` of the
    /// caller, `.up~(N)` the `sample * N`; none of `when~` and `reset_if~`,
    /// which keep it. Its one argument is then the N, a constant expression.
    pub fn ratio_op(self) -> Option<onsa_syntax::ast::RatioOp> {
        match self {
            Modifier::Down => Some(onsa_syntax::ast::RatioOp::Div),
            Modifier::Up => Some(onsa_syntax::ast::RatioOp::Mul),
            Modifier::When | Modifier::ResetIf => None,
        }
    }
}

/// A built-in delay (§11.4): the one table of their names and arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
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

    /// The position of the value it saves, whose clock is the clock of the
    /// delay (§11.4): the first.
    pub const SAVED: usize = 0;

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

    /// The position of the constant expression that fixes the state size
    /// (`delay~(e, N)`, `vdelay~(e, d, MAX)`, §11.4), if any.
    pub fn const_index(self) -> Option<usize> {
        match self {
            Delay::Prev => None,
            Delay::Fixed => Some(1),
            Delay::Variable => Some(2),
        }
    }

    /// The position of the `d` of `vdelay~(e, d, MAX)` (§11.4), if any.
    pub fn d_index(self) -> Option<usize> {
        match self {
            Delay::Variable => Some(1),
            Delay::Prev | Delay::Fixed => None,
        }
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
