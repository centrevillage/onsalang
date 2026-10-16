//! The convergence of the fix candidates (`onsa_cases --fix-loop`; S-236,
//! `rules/criteria.md` 7.27; W3-22): a candidate of a reported
//! diagnostic applied, the file checked again, and again, as a repair loop
//! does, until the loop stops.
//!
//! A file is checked as `onsa check` checks it (a single-file package; the
//! entry of `--fix-same-place`). Each step takes one of the diagnostics the
//! driver reported (one per unit, §18.1; never chosen again here, D-15) that
//! has candidates: the first in the order the diagnostics are printed, or
//! the last ([`Pick`]: the order a loop takes them in is its own, and the
//! rule 27 asks for any), and applies its first candidate alone
//! ([`crate::fix_contract::apply_alone`], [`crate::fix_contract::check_text`],
//! shared with the contract). A walk stops ([`Stop`]):
//!
//! - `clean`: no diagnostic is left;
//! - `no-candidate`: diagnostics are left, none with a candidate;
//! - `cycle`: the text after a step is the text of an earlier point of the
//!   walk ([`How::State`]; texts are compared byte for byte: a candidate is
//!   a minimal edit, and blanks mean something in Onsa, `f (x)`), or every
//!   edit of the step restores what an edit of one earlier step replaced
//!   ([`How::Undo`]: a round trip across stages, as the `~` of S-435, where
//!   the text is not the same). A step that restores some of the edits of an
//!   earlier step is an undo too. The places of the earlier edits are moved
//!   by the rule of the contract (`fix_contract::shift`: an insertion at an
//!   end of a range is outside it); a deletion is a point that an insertion
//!   at it does not move past, so the deleted text written again on either
//!   side of the insertion is an undo, and that an edit replacing text on
//!   both sides of it ends (nothing restores it after that);
//! - `limit`: the steps reached the limit, `--steps N`, by default
//!   [`step_limit`] of the input: twice its tokens (comments included, but
//!   blanks), and 8. §18.1 shows the first error of each unit only, so the
//!   errors at the start do not bound the steps (150 `let mut` in one
//!   function are one error at the start and 150 steps); every error lies at
//!   a token, a comment too (a block comment, E0020; `///`, E0004), and a
//!   token may hold errors of two stages (a form, then its type);
//! - `diverge`: the errors (the reported diagnostics) rose in `--diverge N`
//!   steps in a row, by default [`DIVERGE`] = 4. No walk of the cases and the
//!   saved inputs of 2026-10-13 rises in two steps in a row for a sound
//!   reason (`tests/spec/fixes/e0320_rename.onsa` rises in two for a known
//!   defect, R-87 (5), until W4-04); 4 leaves room for candidates that let
//!   the check reach errors of other units, and a growth that goes on stops
//!   in 4 steps;
//! - `internal`: the check after a step ends in an internal error (with the
//!   position of the panic);
//! - `cannot-apply`: a candidate does not apply ([`crate::fix_contract::Unapplied`]).
//!
//! **Branches** (`--branches`): every candidate is a branch. The walks are
//! taken in the order of how many times they take a candidate other than the
//! first (a limited discrepancy search): every walk that takes none, then
//! every one that takes one, then two, and so on, each round depth first, so
//! a later candidate of the first diagnostic is walked before the
//! combinations of the candidates of the units after it. A text is checked
//! once per file (the results are kept); in a round, a point is not walked
//! again from a text already walked from with as many other candidates left
//! and in as few steps (it is counted as joined). An undo and a divergence
//! are properties of the steps of one walk, so one past a join may not be
//! seen. The first round (the walk that takes no other candidate) always
//! ends, as a walk without branches does (by the limit of the steps); after
//! it, the texts checked are at most `--states N`, by default [`STATES`] =
//! 256 per file; past it the walk stops, says it is truncated, and how many
//! other candidates every walk it finished took at most (`discrepancies`).
//! The stops are counted by walk, not by text: walks to one text that take
//! other candidates a different number of times are each counted.
//!
//! The gate item `fix-loop` ([`gate`]) walks the single-file cases of
//! `tests/spec/fixes` and the saved inputs of the fuzzing `tests/fuzz` with
//! branches, in both orders, within [`GATE_BUDGET`] = 300 s, and reports the
//! cycles, the divergences and the limits without failing on them (until
//! the known ones are sorted out).

mod gate;
mod text;
mod walk;

// The self-tests (a file named `_tests.rs`, as the tests of the crates that the search for
// spelled codes skips, `onsa_syntax::foreign_tests`).
#[cfg(test)]
mod fix_loop_tests;

use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use onsa_diag::{Diagnostic, FileId, SourceMap};

use crate::fix_contract;
use crate::single_files::{on_stacks, read_input};

pub use gate::{Gate, gate};
pub use text::text;
pub use walk::walk;

/// The texts checked per file with branches after the first round, by default.
pub const STATES: usize = 256;
/// The steps in a row whose errors rose that make a divergence, by default.
pub const DIVERGE: usize = 4;
/// The time of the gate item.
pub const GATE_BUDGET: Duration = Duration::from_secs(300);
/// The walks of a file kept in its report: the first, then those of a kept stop ([`Stop::kept`]),
/// the heaviest ([`Stop::weight`]) when there are more.
const WALKS: usize = 20;

/// The limit of the steps of a walk from `text` by default (the module's documentation, `limit`).
pub fn step_limit(text: &str) -> usize {
    let tokens = onsa_syntax::lex(FileId(0), text)
        .tokens
        .iter()
        .filter(|t| {
            !matches!(
                t.kind,
                onsa_syntax::TokenKind::Whitespace | onsa_syntax::TokenKind::Newline | onsa_syntax::TokenKind::Eof
            )
        })
        .count();
    2 * tokens + 8
}

/// Which reported diagnostic with candidates a step takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pick {
    First,
    Last,
}

impl Pick {
    pub fn parse(s: &str) -> Option<Pick> {
        [Pick::First, Pick::Last].into_iter().find(|p| p.name() == s)
    }

    pub fn name(self) -> &'static str {
        match self {
            Pick::First => "first",
            Pick::Last => "last",
        }
    }
}

/// The options of a walk; the defaults are the module's documentation's.
#[derive(Debug, Clone)]
pub struct Options {
    pub pick: Pick,
    /// Every candidate is a branch (else the first only).
    pub branches: bool,
    /// The limit of the steps (`None`: [`step_limit`]).
    pub steps: Option<usize>,
    /// The texts checked per file, with branches, after the first round.
    pub states: usize,
    /// The steps in a row whose errors rose that make a divergence.
    pub diverge: usize,
    /// When the walk gives up (the gate's budget).
    pub deadline: Option<Instant>,
}

impl Default for Options {
    fn default() -> Options {
        Options { pick: Pick::First, branches: false, steps: None, states: STATES, diverge: DIVERGE, deadline: None }
    }
}

/// What a check of a text gives a walk: the sources (for applying a
/// candidate and placing a diagnostic) and the reported diagnostics.
pub struct Checked {
    pub sources: SourceMap,
    pub diagnostics: Vec<Diagnostic>,
}

/// The check of a text as `onsa check` checks it ([`fix_contract::check_text`]);
/// a panic outside the driver's stages is an internal error too, rendered
/// with its position.
pub fn check(text: &str) -> Result<Checked, String> {
    let run = onsa_driver::guard(|| fix_contract::check_text(text)).map_err(|e| {
        let mut sources = SourceMap::default();
        sources.add("m.onsa", text);
        e.render(&sources)
    })??;
    Ok(Checked { sources: run.loaded.sources, diagnostics: run.analyzed.diagnostics })
}

/// How a walk stopped (the module's documentation).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Stop {
    Clean,
    NoCandidate,
    Cycle,
    Limit,
    Diverge,
    Internal,
    CannotApply,
}

impl Stop {
    pub const ALL: [Stop; 7] =
        [Stop::Clean, Stop::NoCandidate, Stop::Cycle, Stop::Limit, Stop::Diverge, Stop::Internal, Stop::CannotApply];

    /// Its name, in the text and in the JSON (the one place of it).
    pub fn name(self) -> &'static str {
        match self {
            Stop::Clean => "clean",
            Stop::NoCandidate => "no-candidate",
            Stop::Cycle => "cycle",
            Stop::Limit => "limit",
            Stop::Diverge => "diverge",
            Stop::Internal => "internal",
            Stop::CannotApply => "cannot-apply",
        }
    }

    /// The stops a report keeps the walk of, after the first.
    fn kept(self) -> bool {
        !matches!(self, Stop::Clean | Stop::NoCandidate)
    }

    /// The order in which the kept walks fill a report, the heaviest (0) first.
    fn weight(self) -> u8 {
        match self {
            Stop::Cycle => 0,
            Stop::Diverge => 1,
            Stop::Internal => 2,
            Stop::CannotApply => 3,
            Stop::Limit => 4,
            Stop::Clean | Stop::NoCandidate => 5,
        }
    }
}

impl serde::Serialize for Stop {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(self.name())
    }
}

/// What a cycle came back to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum How {
    /// The text of an earlier point.
    State,
    /// The edits of an earlier step, undone.
    Undo,
}

impl How {
    pub const ALL: [How; 2] = [How::State, How::Undo];

    /// Its name, in the JSON (the one place of it).
    pub fn name(self) -> &'static str {
        match self {
            How::State => "state",
            How::Undo => "undo",
        }
    }
}

impl serde::Serialize for How {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(self.name())
    }
}

/// One step: the diagnostic (its place in the text before the step), the
/// candidate, and the errors after it (`None`: not checked).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Step {
    pub code: String,
    pub line: u32,
    pub col: u32,
    pub candidate: usize,
    pub of: usize,
    pub title: String,
    pub errors: Option<usize>,
}

/// One walk, to where it stopped.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Walk {
    pub stop: Stop,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub how: Option<How>,
    /// A cycle: the step whose text came back (`state`, 0 for the input), or
    /// whose edits were undone (`undo`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub back_to: Option<usize>,
    /// An internal error, a candidate that does not apply.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    pub steps: Vec<Step>,
}

impl Walk {
    fn new(stop: Stop, steps: Vec<Step>) -> Walk {
        Walk { stop, how: None, back_to: None, message: None, steps }
    }

    fn cycle(how: How, back_to: usize, steps: Vec<Step>) -> Walk {
        Walk { how: Some(how), back_to: Some(back_to), ..Walk::new(Stop::Cycle, steps) }
    }

    fn failed(stop: Stop, message: String, steps: Vec<Step>) -> Walk {
        Walk { message: Some(message), ..Walk::new(stop, steps) }
    }
}

/// What the walks of one file found.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Report {
    pub file: String,
    /// The errors at the start.
    pub errors: usize,
    #[serde(serialize_with = "pick_name")]
    pub pick: Pick,
    pub branches: bool,
    /// The walks that stopped, by how (walks, not texts: the module's documentation, branches).
    pub stops: BTreeMap<Stop, usize>,
    /// Of the cycles, those of [`How::Undo`].
    pub undos: usize,
    /// The most steps of a walk.
    pub longest: usize,
    /// The texts checked, the input included.
    pub explored: usize,
    /// The points not walked again (the module's documentation, branches).
    pub joined: usize,
    /// The walk stopped at `states` texts.
    pub truncated: bool,
    /// With branches: every walk that takes another candidate than the
    /// first at most this many times was walked.
    pub discrepancies: Option<usize>,
    /// The first walk, then those of a kept stop (at most [`WALKS`], the heaviest).
    pub walks: Vec<Walk>,
    /// The check of the file itself ended in an internal error.
    pub internal: Option<String>,
    /// The file cannot be read (or is not UTF-8).
    pub unreadable: Option<String>,
    /// The deadline passed before the walk ended.
    #[serde(skip)]
    pub timed_out: bool,
}

fn pick_name<S: serde::Serializer>(p: &Pick, s: S) -> Result<S::Ok, S::Error> {
    s.serialize_str(p.name())
}

impl Report {
    fn new(file: &str, options: &Options) -> Report {
        Report {
            file: file.to_string(),
            errors: 0,
            pick: options.pick,
            branches: options.branches,
            stops: BTreeMap::new(),
            undos: 0,
            longest: 0,
            explored: 0,
            joined: 0,
            truncated: false,
            discrepancies: None,
            walks: Vec::new(),
            internal: None,
            unreadable: None,
            timed_out: false,
        }
    }

    /// A walk that stopped: counted, and kept when it is the first or of a
    /// kept stop; past [`WALKS`], the last of the lightest after the first goes.
    fn leaf(&mut self, walk: Walk) {
        *self.stops.entry(walk.stop).or_default() += 1;
        self.undos += usize::from(walk.how == Some(How::Undo));
        self.longest = self.longest.max(walk.steps.len());
        if self.walks.is_empty() || walk.stop.kept() {
            self.walks.push(walk);
        }
        if self.walks.len() > WALKS {
            let lightest = (1..self.walks.len()).max_by_key(|&i| (self.walks[i].stop.weight(), i));
            self.walks.remove(lightest.expect("more than one walk"));
        }
    }

    /// The walks that stopped on `stop`.
    pub fn count(&self, stop: Stop) -> usize {
        self.stops.get(&stop).copied().unwrap_or(0)
    }
}

/// Walk each file (named as given) with the compiler's check, in parallel.
pub fn walk_files(files: &[String], options: &Options) -> Vec<Report> {
    on_stacks(files.len(), |i| match read_input(&files[i]) {
        Err(e) => Report { unreadable: Some(e), ..Report::new(&files[i], options) },
        Ok(text) => walk(&files[i], &text, options, &check),
    })
}

/// Walk each text (with its name) with the compiler's check, in parallel.
pub fn walk_texts(inputs: &[(String, String)], options: &Options) -> Vec<Report> {
    on_stacks(inputs.len(), |i| walk(&inputs[i].0, &inputs[i].1, options, &check))
}
