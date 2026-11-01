//! The wall-clock time of each phase of the compiler, for the measurements
//! of the test binary (`onsa_cases --phases`, X-20). No command reads it.
//! A thread records only inside [`record`]; elsewhere a phase costs one read
//! of a thread-local.
//!
//! The phases are the one list [`Phase::ALL`] (D-15). A phase entered inside
//! another is not counted in the outer one (the flow checks of a flow body
//! run inside the types stage), so the phases of a run add up to at most its
//! time; what no phase holds is the rest.

use std::cell::RefCell;
use std::time::{Duration, Instant};

/// The phases (D-15: the enum, [`Phase::ALL`] and [`Phase::name`] are made
/// from this one list), in the order they run.
macro_rules! phases {
    ($($(#[doc = $doc:literal])* $phase:ident $name:literal,)*) => {
        /// A phase of the compiler.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum Phase { $($(#[doc = $doc])* $phase,)* }

        impl Phase {
            pub const ALL: &'static [Phase] = &[$(Phase::$phase,)*];

            pub fn name(self) -> &'static str {
                match self { $(Phase::$phase => $name,)* }
            }
        }
    };
}

phases! {
    /// The lexer and the parser (CST and AST), of the user's files and std.
    Syntax "syntax",
    /// The names of the modules and of the bodies.
    Names "names",
    /// The signatures and the generated items.
    Signatures "signatures",
    /// The types of the bodies (and of a flow body's walk).
    Types "types",
    /// The flow checks after a flow body is typed (the rate pass, §11.3).
    Flow "flow",
    /// The states of the bindings.
    Bindings "bindings",
    Modes "modes",
    Rt "rt",
    Effects "effects",
    /// The choice of the diagnostics and their candidates, after the analysis.
    Report "report",
    /// The lowering to Core.
    Lower "lower",
    /// The verifier of Core.
    Verify "verify",
}

/// What [`record`] measured: by phase (in the order of [`Phase::ALL`]) the
/// time and the times it was entered, and the time of the whole run.
#[derive(Debug, Clone, Default)]
pub struct Times {
    pub phases: Vec<(Phase, Duration, u32)>,
    pub total: Duration,
}

#[derive(Default)]
struct Recorder {
    spent: Vec<(Duration, u32)>,
    /// The phases entered and not left, each with the instant its own time
    /// last started.
    open: Vec<(Phase, Instant)>,
}

thread_local! {
    static RECORDER: RefCell<Option<Recorder>> = const { RefCell::new(None) };
}

/// Ends the phase it was made for when dropped (also by a panic).
#[must_use]
pub struct Entered(bool);

/// Enter `phase` until the returned value is dropped.
pub fn phase(phase: Phase) -> Entered {
    Entered(with_recorder(|r| {
        let now = Instant::now();
        if let Some((outer, since)) = r.open.last() {
            r.spent[*outer as usize].0 += now - *since;
        }
        r.spent[phase as usize].1 += 1;
        r.open.push((phase, now));
    }))
}

impl Drop for Entered {
    fn drop(&mut self) {
        if self.0 {
            with_recorder(|r| {
                let now = Instant::now();
                if let Some((left, since)) = r.open.pop() {
                    r.spent[left as usize].0 += now - since;
                }
                if let Some((_, since)) = r.open.last_mut() {
                    *since = now;
                }
            });
        }
    }
}

/// Run `f` on this thread with the phases recorded. Not nested in itself.
pub fn record<T>(f: impl FnOnce() -> T) -> (T, Times) {
    let fresh = Recorder { spent: vec![Default::default(); Phase::ALL.len()], open: Vec::new() };
    RECORDER.with(|r| *r.borrow_mut() = Some(fresh));
    let start = Instant::now();
    let out = f();
    let total = start.elapsed();
    let spent = RECORDER.with(|r| r.borrow_mut().take()).map(|r| r.spent).unwrap_or_default();
    let phases = Phase::ALL.iter().zip(spent).map(|(&p, (d, n))| (p, d, n)).collect();
    (out, Times { phases, total })
}

/// Whether a recorder was there to take `f`.
fn with_recorder(f: impl FnOnce(&mut Recorder)) -> bool {
    RECORDER.with(|r| r.borrow_mut().as_mut().map(f).is_some())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The list is in the order of the discriminants that index it.
    #[test]
    fn the_list_is_in_the_order_of_the_phases() {
        for (i, p) in Phase::ALL.iter().enumerate() {
            assert_eq!(*p as usize, i, "{}", p.name());
        }
    }

    /// An inner phase is not counted in the outer one, and outside
    /// [`record`] nothing is recorded.
    #[test]
    fn an_inner_phase_is_taken_out_of_the_outer() {
        drop(phase(Phase::Syntax));
        let ((), t) = record(|| {
            let _types = phase(Phase::Types);
            std::thread::sleep(Duration::from_millis(2));
            let _flow = phase(Phase::Flow);
            std::thread::sleep(Duration::from_millis(20));
        });
        let of = |p: Phase| t.phases[p as usize];
        assert!(of(Phase::Types).1 < Duration::from_millis(20), "{t:?}");
        assert!(of(Phase::Flow).1 >= Duration::from_millis(20), "{t:?}");
        assert_eq!((of(Phase::Types).2, of(Phase::Flow).2, of(Phase::Syntax).2), (1, 1, 0));
        assert!(t.phases.iter().map(|p| p.1).sum::<Duration>() <= t.total, "{t:?}");
        assert!(RECORDER.with(|r| r.borrow().is_none()));
    }
}
