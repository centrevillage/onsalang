//! The clocks of a flow (§11.3) in two layers (W7-02 U1):
//!
//! - [`ClockName`]: the names stage's layer, the base clocks a name after
//!   `at` and the heading of a flow write (`init`, `block`, `sample`). The
//!   one table of the names (D-15); [`resolve_at`] looks one up (E0302).
//! - [`Clock`]: the layer of the values, the clock of an expression, a local,
//!   an input or the output, which the tables of a flow hold
//!   ([`crate::flow::FlowInfo::clocks`], [`crate::def::FlowInput::caller_clock`]).
//!   Its stage of evaluation is a [`ClockStage`] ([`Clock::stage`]).
//!
//! The comparisons of clocks ([`join`], [`readable_at`], [`promote`],
//! [`keeps_delay_state`], [`delay_out`], [`rebase`], [`loop_clock`], W7-02 U2a)
//! are the one table of the rules (D-15). The walk of the clocks
//! (`flow::clocks`) and its checks read them. Each passes a clock in error with
//! no clash and gives a clock in error. The rows of an event clock are
//! W7-11's (S-1095, S-1096): an event clock where its row is not written is
//! an internal error, with a clock in error too.

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

/// The name of the clock of an event input (§11.11), which this version
/// does not look up as a clock (E0302 until W7-11): the base of a derived
/// clock of an expression that is not `sample` (E0815, S-1078).
const EVENT: &str = "event";

/// The clock after `at` of an expression of a flow body, as the names
/// stage looked it up (§11.3, S-359, S-1078): a name of the clocks, or a
/// derived clock `(base / N)`, `(base * N)`, whose N the types stage
/// evaluates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ClockRef {
    Name(ClockName),
    Derived(Base, ast::RatioOp, ast::ExprId),
}

/// The base of a derived clock (S-1078): a name of the clocks, or `event`,
/// looked up by its text until W7-11 puts it in the clock namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Base {
    Clock(ClockName),
    Event,
}

impl ClockRef {
    /// The clock of the host a port written at it is at: a name with no
    /// ratio (§11.6), none of a derived clock, which no port of the host has
    /// (§11.9). The one test of the ports of the generated API (D-15): the
    /// items a flow generates by its inputs ([`crate::def::FlowInput::host`]).
    pub fn host(self) -> Option<ClockName> {
        match self {
            ClockRef::Name(n) => Some(n),
            ClockRef::Derived(..) => None,
        }
    }
}

impl Base {
    /// The name the base is written as.
    pub fn name(self) -> &'static str {
        if let Base::Clock(c) = self { c.name() } else { EVENT }
    }
}

/// The clock after `at` of an expression of a flow body, of an input and
/// of the output of a flow (§11.3, S-359, S-1078): a name of the clock
/// namespace, or a derived clock whose base is one (`event` too), else E0302
/// at the name, whatever value or type has that name.
pub(crate) fn resolve_at(c: &ast::Clock) -> Result<ClockRef, Diagnostic> {
    let name = ClockName::of_name(&c.name.name);
    let base = name.map(Base::Clock).or_else(|| (c.name.name == EVENT).then_some(Base::Event));
    match (&c.ratio, base) {
        (None, _) => name.map(ClockRef::Name).ok_or_else(|| not_found(c)),
        (Some(r), Some(base)) => Ok(ClockRef::Derived(base, r.op, r.n)),
        (Some(_), None) => Err(not_found(c)),
    }
}

/// The E0302 of the name of the clock `c`, which is none (§11.3).
fn not_found(c: &ast::Clock) -> Diagnostic {
    let names = ClockName::ALL.iter().map(|r| format!("`{}`", r.name())).collect::<Vec<_>>().join(", ");
    Diagnostic::new(
        Stage::Names,
        Code::E0302,
        c.name.span,
        format!("cannot find the clock `{}`; a clock after `at` is a name of the clocks (§11.3)", c.name.name),
    )
    .with_found(c.name.name.clone())
    .with_rule(format!("the clocks of this version are {names}"))
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
    /// The clock of `sample_tick()` (§11.4, S-567 K6): of the place that
    /// reads it ([`rooted`]).
    Ambient,
    /// A clock in error (an input whose clock has a diagnostic).
    Error,
}

/// The power of 2 of a tick clock over the `sample` of the body (S-1077).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Ratio(pub i32);

impl Ratio {
    /// Faster than the `sample` of the body: the `sample * N` of the caller
    /// (§11.9), which a join, `at` and a delay take apart from the other
    /// ticks. The one test of it (D-15).
    pub fn faster_than_body(self) -> bool {
        self.0 > 0
    }

    /// Slower than the `sample` of the body: `sample / N`, and the ratio of
    /// a `.down~(N)` (§11.9). The one test of it (D-15).
    pub fn slower_than_body(self) -> bool {
        self.0 < 0
    }

    /// The N of the ratio (`sample / N`, `.down~(N)`), none past `u64`.
    pub fn n(self) -> Option<u64> {
        2u64.checked_pow(self.0.unsigned_abs())
    }

    /// The N of a clock, `U32` (2^31 at most) of `sample * N` and `sample /
    /// N` alike, none past it (§11.9, S-1216): of `sample * N` the length of
    /// an array, of `sample / N` the period of a counter of one `U32` word.
    /// The one test of it (D-15): the check of the composed clocks of a
    /// chain (E0808 of the flow stage) and the Core read it.
    pub fn made_n(self) -> Option<u64> {
        self.n().filter(|_| (-31..32).contains(&self.0))
    }

    /// The ratio of `(sample / n)` (`op` `/`) or `(sample * n)` (`*`), and
    /// of `.down~(n)` and `.up~(n)` (S-1077): `n` a power of 2 that is 2 or
    /// more, else none (E0808). The one test of an N (D-15).
    pub fn of_n(op: ast::RatioOp, n: u32) -> Option<Ratio> {
        let k = (n >= 2 && n.is_power_of_two()).then(|| n.trailing_zeros() as i32)?;
        Some(Ratio(match op {
            ast::RatioOp::Div => -k,
            ast::RatioOp::Mul => k,
        }))
    }
}

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

    /// The stage as the text of a diagnostic writes it: the name of its
    /// clock ([`Clock::shown`]), `sample / 4` of a tick.
    pub fn shown(self, at: Span) -> String {
        match self {
            ClockStage::Init => Clock::Init,
            ClockStage::Block => Clock::Block,
            ClockStage::Tick(k) => Clock::Tick(k),
        }
        .shown(at)
    }

    /// A tick slower than the stage `at` that reads what is of it: that is
    /// kept in a field written at the tick, which starts at `T.default()`
    /// (§11.3, S-1158 (c), S-1186). The one test of it (D-15).
    pub fn tick_slower_than(self, at: ClockStage) -> bool {
        match self {
            ClockStage::Tick(_) => self < at,
            ClockStage::Init | ClockStage::Block => false,
        }
    }
}

impl Clock {
    /// The `sample` of the body.
    pub const SAMPLE: Clock = Clock::Tick(Ratio(0));

    /// A periodic tick of a ratio (§11.3): `sample / N`, `sample * N`.
    pub fn of_ratio(self) -> bool {
        matches!(self, Clock::Tick(k) if k != Ratio(0))
    }

    /// A burst: a tick faster than the `sample` of the body (`sample * N`,
    /// §11.9), whose values the body sees as `[T; N]`. The one test of a
    /// clock of a burst (D-15), of any N (a chain with an `.up~(N)` makes one
    /// past `U32` at the call side); a join, `at` and a delay test the ratio
    /// ([`Ratio::faster_than_body`]).
    pub fn burst(self) -> bool {
        matches!(self, Clock::Tick(k) if k.faster_than_body())
    }

    /// The N of a [`Clock::burst`], none of another clock: the view of the
    /// ports of a body and the Core's type of the values of the caller read
    /// it. An N the Core does not make ([`Ratio::made_n`]) is an internal error.
    pub fn burst_len(self) -> Option<u32> {
        let Clock::Tick(k) = self else { return None };
        let n = self.burst().then(|| k.made_n().and_then(|n| u32::try_from(n).ok()))?;
        Some(n.unwrap_or_else(|| onsa_diag::internal::bug(None, format!("a burst at {self:?}, past `U32`"))))
    }

    /// The stage the values of the clock are evaluated at. `None` of a
    /// constant, `sample_tick()` and a clock in error, whose stage is the
    /// stage of the place that reads them.
    pub fn stage(self) -> Option<ClockStage> {
        match self {
            Clock::Init => Some(ClockStage::Init),
            Clock::Block => Some(ClockStage::Block),
            Clock::Tick(k) => Some(ClockStage::Tick(k)),
            Clock::Const | Clock::Ambient | Clock::Error => None,
            Clock::Event(_) => event_bug("the stage"),
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
        let Some(n) = Ratio(k).n() else {
            onsa_diag::internal::bug(Some(at), format!("the ratio of the clock {self:?} out of the text"))
        };
        match k {
            0 => sample.into(),
            1.. => format!("{sample} * {n}"),
            _ => format!("{sample} / {n}"),
        }
    }
}

impl Clock {
    /// The clock as a declaration writes it after `at` (§11.3): of a ratio
    /// in parentheses, `(sample / 4)`, else [`Clock::shown`]. The one text of
    /// the clocks `onsa graph` and `onsa interface` write (S-1084), which the
    /// diagnostics do not (their text is [`Clock::shown`]).
    // SPEC-GAP(S-1084): the parentheses of the declaration in the labels and
    // the heading (provisional (2)).
    pub fn written(self, at: Span) -> String {
        let shown = self.shown(at);
        if self.of_ratio() { format!("({shown})") } else { shown }
    }
}

/// The frame a declared clock of a callee is read in ([`rebase`]): the ratio
/// of the place of the call over the `sample` of the body (§11.9). Always
/// `Ratio(0)` in W7-02; W7-10 marks the things that make time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClockFrame {
    pub ratio: Ratio,
}

impl ClockFrame {
    pub const BODY: ClockFrame = ClockFrame { ratio: Ratio(0) };
    /// The tick of the frame, a callee's `sample` [`rebase`]d as the walk of
    /// an instance does, which E0813 and the lift of a chain read (D-15).
    pub fn tick(self) -> Clock {
        rebase(Clock::SAMPLE, self)
    }
}

/// Two operands whose clocks do not meet (E0815; a loop of W7-09 too): each
/// by its index in the operands of the comparison and its clock. `first` is
/// the operand whose clock the scan held when `second` met it (in a [`join`],
/// the one the result so far came from, not always the lowest index), so
/// the lower index is first. The caller puts the places (`ExprId`) on them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Clash {
    pub first: (usize, Clock),
    pub second: (usize, Clock),
}

fn clash(first: (usize, Clock), second: (usize, Clock)) -> Clash {
    Clash { first, second }
}

fn event_bug(what: &str) -> ! {
    onsa_diag::internal::bug(None, format!("{what} of an event clock, which W7-11 makes"))
}

/// The order of the parameter kinds (constant < `init` < `block`, §11.3).
fn param_rank(c: Clock) -> u8 {
    match c {
        Clock::Const => 0,
        Clock::Init => 1,
        Clock::Block => 2,
        _ => onsa_diag::internal::bug(None, format!("the clock {c:?} is not a parameter kind")),
    }
}

/// The clock of the operands of an expression (§11.3 "式のクロックは三つで
/// 決まる"): the largest parameter kind; tick clocks of one ratio, which is the
/// result (two ratios clash, E0815); `sample_tick()` follows a tick and is
/// itself with parameter kinds alone (S-567 K6); `sample * N` with another
/// operand clashes for now (§11.9). `None` (⊥, a `^name` in the loop being
/// solved) is the unit, and the result of no other operand. The clash holds
/// indices of `ops`. Linear in the operands.
pub fn join(ops: &[Option<Clock>]) -> Result<Option<Clock>, Clash> {
    join_by(ops, |&c| c)
}

/// [`join`] of the clocks `clock` gives of the operands `ops`, whose indices
/// the clash holds.
pub fn join_by<T>(ops: &[T], clock: impl Fn(&T) -> Option<Clock>) -> Result<Option<Clock>, Clash> {
    let given = || ops.iter().enumerate().filter_map(|(i, c)| clock(c).map(|c| (i, c)));
    if given().any(|(_, c)| matches!(c, Clock::Event(_))) {
        event_bug("a join");
    }
    if given().any(|(_, c)| c == Clock::Error) {
        return Ok(Some(Clock::Error));
    }
    let mut out: Option<(usize, Clock)> = None;
    for (i, c) in given() {
        let Some(acc) = out else {
            out = Some((i, c));
            continue;
        };
        out = Some(match (acc.1, c) {
            (Clock::Tick(k), _) | (_, Clock::Tick(k)) if k.faster_than_body() => return Err(clash(acc, (i, c))),
            (Clock::Tick(a), Clock::Tick(b)) if a != b => return Err(clash(acc, (i, c))),
            (Clock::Tick(_), _) | (Clock::Ambient, Clock::Ambient) => acc,
            (_, Clock::Tick(_)) | (_, Clock::Ambient) => (i, c),
            (Clock::Ambient, _) => acc,
            (a, b) if param_rank(b) > param_rank(a) => (i, c),
            _ => acc,
        });
    }
    Ok(out.map(|(_, c)| c))
}

/// Whether a value of the clock `value` is read at a place of the clock
/// `place` (§11.3 "読み方"): a parameter kind at a place of its kind or larger
/// and at every tick place; a tick at the same tick only; `sample_tick()` at
/// a tick place (S-567 K6). The clash is the value (0) and the place (1).
pub fn readable_at(value: Clock, place: Clock) -> Result<(), Clash> {
    let ok = match (value, place) {
        (Clock::Event(_), _) | (_, Clock::Event(_)) => event_bug("a read"),
        (Clock::Error, _) | (_, Clock::Error) => true,
        (_, Clock::Ambient) => onsa_diag::internal::bug(None, "a place at the clock of `sample_tick()`"),
        (Clock::Tick(a), Clock::Tick(b)) => a == b,
        (_, Clock::Tick(_)) => true,
        (Clock::Tick(_) | Clock::Ambient, _) => false,
        (v, p) => param_rank(v) <= param_rank(p),
    };
    if ok { Ok(()) } else { Err(clash((0, value), (1, place))) }
}

/// The clock of `e at k` (§11.3): `k`, when `e` is as slow as `k` or slower
/// and `k` is the `sample` of the body or slower; `sample_tick()` goes to a
/// tick only (S-567 K6). The clash is the value (0) and the clock `k` (1).
pub fn promote(value: Clock, to: Clock) -> Result<Clock, Clash> {
    let ok = match (value, to) {
        (Clock::Event(_), _) | (_, Clock::Event(_)) => event_bug("`at`"),
        (Clock::Error, _) | (_, Clock::Error) => return Ok(Clock::Error),
        (_, Clock::Const | Clock::Ambient) => onsa_diag::internal::bug(None, format!("`at` to {to:?}, no name")),
        (_, Clock::Tick(j)) if j.faster_than_body() => false,
        (Clock::Tick(Ratio(k)), Clock::Tick(Ratio(j))) => k <= j,
        (_, Clock::Tick(_)) => true,
        (Clock::Tick(_) | Clock::Ambient, _) => false,
        (v, t) => param_rank(v) <= param_rank(t),
    };
    if ok { Ok(to) } else { Err(clash((0, value), (1, to))) }
}

/// Whether a delay keeps its state at the clock of its first argument
/// (§11.4, E0813): a tick of the body (`sample`, `sample / N`) and
/// `sample_tick()` (S-567 K6), not a parameter kind nor the `sample * N` of
/// the caller. A clock in error holds (no second diagnostic).
// SPEC-GAP(S-1097): the `sample * N` of the caller is this E0813, with no
// candidate (provisional).
pub fn keeps_delay_state(c: Clock) -> bool {
    match c {
        Clock::Tick(k) => !k.faster_than_body(),
        Clock::Ambient | Clock::Error => true,
        Clock::Const | Clock::Init | Clock::Block => false,
        Clock::Event(_) => event_bug("the state"),
    }
}

/// The clock of a delay by the clock of its first argument (§11.3, §11.4):
/// a tick or an event itself, `sample_tick()` [`grounded`] (S-567 K6). A
/// parameter kind, which E0813 rejects at the check, is ⊥ when it reads a ⊥
/// (`partial`, in a loop being solved) and else the `sample` of the body to
/// go on with. ⊥ gives ⊥.
pub fn delay_out(first: Option<Clock>, partial: bool) -> Option<Clock> {
    match first? {
        c @ (Clock::Tick(_) | Clock::Event(_) | Clock::Error | Clock::Ambient) => Some(grounded(c)),
        Clock::Const | Clock::Init | Clock::Block => (!partial).then_some(Clock::SAMPLE),
    }
}

/// A declared clock of a callee read in the frame of its call (§11.3, §11.9):
/// a tick moved by the ratio of the frame (S-1077), `init`, `block` and a
/// clock in error as they are. A ratio past `i32` is an internal error (M1).
pub fn rebase(decl: Clock, frame: ClockFrame) -> Clock {
    match decl {
        Clock::Init | Clock::Block | Clock::Error => decl,
        Clock::Tick(Ratio(k)) => match k.checked_add(frame.ratio.0) {
            Some(k) => Clock::Tick(Ratio(k)),
            None => onsa_diag::internal::bug(None, format!("the ratio of {decl:?} in the frame {frame:?}")),
        },
        Clock::Event(_) => event_bug("the frame"),
        Clock::Const | Clock::Ambient => onsa_diag::internal::bug(None, format!("{decl:?} is no declared clock")),
    }
}

/// The clock of a value at `c` used at a place of the clock `root` (§11.4):
/// `sample_tick()` with no tick beside it takes the clock of the place it
/// is used at; any other clock is its own. The one place of the rule
/// (D-15).
pub fn rooted(c: Clock, root: Clock) -> Clock {
    if c == Clock::Ambient { root } else { c }
}

/// [`rooted`] at a place of no tick of its own (a `let`, a loop, a delay, the
/// text of a diagnostic): the lowest clock `sample_tick()` takes, the
/// `sample` of the body (§11.4). The one place of that clock (D-15).
// SPEC-GAP(S-1180): a `let` of `sample_tick()` alone is the `sample` of the
// body (provisional (1)).
pub fn grounded(c: Clock) -> Clock {
    rooted(c, Clock::SAMPLE)
}

/// The clock of every `let` of a loop by the join `t` of its operands (§11.3
/// "読み方", S-567 P3): a tick, an event or a clock in error itself,
/// `sample_tick()` [`grounded`], else (a parameter kind, ⊥) the `sample` of
/// the body.
pub fn loop_clock(t: Option<Clock>) -> Clock {
    match t.map(grounded) {
        Some(c @ (Clock::Tick(_) | Clock::Event(_) | Clock::Error)) => c,
        Some(Clock::Const | Clock::Init | Clock::Block | Clock::Ambient) | None => Clock::SAMPLE,
    }
}
