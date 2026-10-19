//! The walk of the fixes of one text (the module's documentation of
//! [`super`]).

use std::collections::HashMap;
use std::rc::Rc;
use std::time::Instant;

use onsa_diag::{Edit, FileId, Fix};

use super::{Checked, How, Options, Pick, Report, Step, Stop, Walk, step_limit};
use crate::fix_contract::{self, Moved, shift};

/// What a step replaced, at the place its replacement is in the text of the
/// walk now (moved by the steps after it): what an undo restores. For a
/// deletion, the place is a point that may have moved apart into the range
/// `start..=end`, by insertions at it; a later edit that replaces text on
/// both sides of it ends the mark (no step restores it then).
#[derive(Debug, Clone)]
pub(super) struct Mark {
    pub start: u32,
    pub end: u32,
    pub old: String,
    pub new: String,
}

impl Mark {
    /// The mark moved by the edits of a step (`fix_contract::shift`: an
    /// insertion at an end of a range is outside it; one at a deletion's
    /// point widens the point).
    fn moved(&self, edits: &[Moved]) -> Mark {
        let file = FileId(0);
        let point = self.new.is_empty();
        let start = shift(edits, file, self.start, !point);
        let end = shift(edits, file, self.end, point);
        Mark { start, end, ..self.clone() }
    }

    /// Whether an edit of `fix` replaces text on both sides of this deletion's point.
    fn swallowed_by(&self, fix: &Fix) -> bool {
        self.new.is_empty() && fix.edits().iter().any(|e| e.span.start < self.start && self.end < e.span.end)
    }

    /// Whether `e`, an edit of the text `text`, restores what this mark replaced.
    fn undone_by(&self, text: &str, e: &Edit) -> bool {
        if e.replace != self.old || self.old == self.new {
            return false;
        }
        if self.new.is_empty() {
            e.span.is_empty() && self.start <= e.span.start && e.span.start <= self.end
        } else {
            (e.span.start, e.span.end) == (self.start, self.end)
                && text.get(self.start as usize..self.end as usize) == Some(self.new.as_str())
        }
    }
}

/// The earlier step (an index of `marks`) whose edits `fix` undoes: each of
/// its edits restores a mark of that step.
pub(super) fn undoes(marks: &[Vec<Mark>], text: &str, fix: &Fix) -> Option<usize> {
    let edits = fix.edits();
    if edits.is_empty() {
        return None;
    }
    marks.iter().position(|ms| edits.iter().all(|e| ms.iter().any(|m| m.undone_by(text, e))))
}

/// The marks after `fix` (applied to `text`, its edits placed as `moved`):
/// those before moved, and the step's own.
fn moved_marks(
    marks: &[Vec<Mark>],
    text: &str,
    fix: &Fix,
    moved: &[Moved],
    ranges: &[onsa_diag::Span],
) -> Vec<Vec<Mark>> {
    let mut out: Vec<Vec<Mark>> =
        marks.iter().map(|ms| ms.iter().filter(|m| !m.swallowed_by(fix)).map(|m| m.moved(moved)).collect()).collect();
    let own = fix.edits().iter().zip(ranges).map(|(e, r)| Mark {
        start: r.start,
        end: r.end,
        old: text.get(e.span.start as usize..e.span.end as usize).unwrap_or_default().to_string(),
        new: e.replace.clone(),
    });
    out.push(own.collect());
    out
}

/// A point of a walk: a text, its check, and what the steps to it did.
struct Frame {
    text: String,
    checked: Rc<Checked>,
    /// The marks of each step before it, moved to its text.
    marks: Vec<Vec<Mark>>,
    /// The steps in a row whose errors rose, to it.
    rise: usize,
    /// The diagnostic its steps take (an index of `checked.diagnostics`).
    pick: usize,
    /// The next candidate to walk.
    next: usize,
    /// The candidates other than the first the walk took to it.
    used: usize,
}

/// How a round ended.
enum Round {
    /// Walked; `more`: a walk was left that takes more other candidates.
    Done {
        more: bool,
    },
    Truncated,
    TimedOut,
}

struct Walker<'a> {
    options: &'a Options,
    check: &'a dyn Fn(&str) -> Result<Checked, String>,
    limit: usize,
    /// Every text checked, and what its check gave.
    checks: HashMap<String, Result<Rc<Checked>, String>>,
    /// The texts checked in the rounds after the first (those `states` bounds).
    counted: usize,
    report: Report,
}

/// The diagnostic the steps from `checked` take: of those with candidates,
/// the first or the last in the order the diagnostics are printed
/// ([`onsa_diag::printed_order`], §18.1).
fn pick(checked: &Checked, pick: Pick) -> Option<usize> {
    let ds = &checked.diagnostics;
    let order: Vec<usize> =
        onsa_diag::printed_order(&checked.sources, ds).into_iter().filter(|&i| !ds[i].fixes.is_empty()).collect();
    match pick {
        Pick::First => order.first().copied(),
        Pick::Last => order.last().copied(),
    }
}

/// Walk the fixes of `text` (the module's documentation of [`super`]),
/// checking each text with `check` ([`super::check`]; the self-tests give
/// one of their own).
pub fn walk(file: &str, text: &str, options: &Options, check: &dyn Fn(&str) -> Result<Checked, String>) -> Report {
    let mut report = Report::new(file, options);
    let root = match check(text) {
        Ok(c) => Rc::new(c),
        Err(e) => {
            report.internal = Some(e);
            return report;
        }
    };
    report.errors = root.diagnostics.len();
    let limit = options.steps.unwrap_or_else(|| step_limit(text));
    let checks = HashMap::from([(text.to_string(), Ok(root.clone()))]);
    let mut w = Walker { options, check, limit, checks, counted: 0, report };
    match w.at_point(&root, 0) {
        Some(stop) => w.report.leaf(Walk::new(stop, Vec::new())),
        None => {
            for d in 0.. {
                match w.round(text, &root, d) {
                    Round::Done { more } => {
                        w.report.discrepancies = options.branches.then_some(d);
                        if !more || !options.branches {
                            break;
                        }
                    }
                    Round::Truncated => {
                        w.report.truncated = true;
                        break;
                    }
                    Round::TimedOut => {
                        w.report.timed_out = true;
                        break;
                    }
                }
            }
        }
    }
    w.report.explored = w.checks.len();
    w.report
}

impl Walker<'_> {
    /// The stop at a point that the steps do not go past: no diagnostic,
    /// none with a candidate, the limit.
    fn at_point(&self, checked: &Checked, depth: usize) -> Option<Stop> {
        if checked.diagnostics.is_empty() {
            Some(Stop::Clean)
        } else if pick(checked, self.options.pick).is_none() {
            Some(Stop::NoCandidate)
        } else if depth >= self.limit {
            Some(Stop::Limit)
        } else {
            None
        }
    }

    /// The check of `text`, once per file. `None`: no more texts may be
    /// checked (`states`, with branches, counted after the first round).
    fn checked(&mut self, text: &str, counted: bool) -> Option<Result<Rc<Checked>, String>> {
        if let Some(c) = self.checks.get(text) {
            return Some(c.clone());
        }
        if counted && self.options.branches && self.counted >= self.options.states {
            return None;
        }
        self.counted += usize::from(counted);
        let c = (self.check)(text).map(Rc::new);
        self.checks.insert(text.to_string(), c.clone());
        Some(c)
    }

    /// One round: every walk that takes another candidate than the first at
    /// most `d` times, depth first; the walks that take it exactly `d` times
    /// are reported (the others were, in the rounds before).
    fn round(&mut self, text: &str, root: &Rc<Checked>, d: usize) -> Round {
        let options = self.options;
        let mut more = false;
        let mut steps: Vec<Step> = Vec::new();
        let mut on_path: HashMap<String, usize> = HashMap::from([(text.to_string(), 0)]);
        // The points walked from in the round: the other candidates left and the steps to it.
        let mut walked: HashMap<String, Vec<(usize, usize)>> = HashMap::from([(text.to_string(), vec![(d, 0)])]);
        let first = pick(root, options.pick).expect("a point with a pick");
        let mut frames = vec![Frame {
            text: text.to_string(),
            checked: root.clone(),
            marks: Vec::new(),
            rise: 0,
            pick: first,
            next: 0,
            used: 0,
        }];
        while let Some(top) = frames.last_mut() {
            let n = if options.branches { top.checked.diagnostics[top.pick].fixes.len() } else { 1 };
            let open = if top.used < d { n } else { 1 };
            more |= n > open;
            if top.next >= open {
                on_path.remove(&top.text);
                frames.pop();
                steps.pop();
                continue;
            }
            let k = top.next;
            top.next += 1;
            if options.deadline.is_some_and(|t| Instant::now() >= t) {
                return Round::TimedOut;
            }
            let top = frames.last().expect("a point");
            let used = top.used + usize::from(k > 0);
            let report = used == d;
            let dg = &top.checked.diagnostics[top.pick];
            let fix = &dg.fixes[k];
            let lc = top.checked.sources.file(dg.span.file).line_col(dg.span.start);
            let mut step = Step {
                code: dg.code.as_str().to_string(),
                line: lc.line,
                col: lc.col,
                candidate: k + 1,
                of: dg.fixes.len(),
                title: fix.title().to_string(),
                errors: None,
            };
            let path = |step: Step| steps.iter().cloned().chain([step]).collect::<Vec<_>>();
            let (new_text, applied) = match fix_contract::apply_alone(&top.checked.sources, fix) {
                Ok(a) => a,
                Err(e) => {
                    if report {
                        self.report.leaf(Walk::failed(Stop::CannotApply, e.to_string(), path(step)));
                    }
                    continue;
                }
            };
            if let Some(&back) = on_path.get(&new_text) {
                if report {
                    step.errors = Some(frames[back].checked.diagnostics.len());
                    self.report.leaf(Walk::cycle(How::State, back, path(step)));
                }
                continue;
            }
            let checked = match self.checked(&new_text, d > 0) {
                None => return Round::Truncated,
                Some(Err(e)) => {
                    if report {
                        self.report.leaf(Walk::failed(Stop::Internal, e, path(step)));
                    }
                    continue;
                }
                Some(Ok(c)) => c,
            };
            let errors = checked.diagnostics.len();
            step.errors = Some(errors);
            if let Some(j) = undoes(&top.marks, &top.text, fix) {
                if report {
                    self.report.leaf(Walk::cycle(How::Undo, j + 1, path(step)));
                }
                continue;
            }
            let rise = if errors > top.checked.diagnostics.len() { top.rise + 1 } else { 0 };
            if rise >= options.diverge {
                if report {
                    self.report.leaf(Walk::new(Stop::Diverge, path(step)));
                }
                continue;
            }
            let (left, depth) = (d - used, steps.len() + 1);
            let seen = walked.entry(new_text.clone()).or_default();
            if seen.iter().any(|&(l, s)| l >= left && s <= depth) {
                self.report.joined += usize::from(report);
                continue;
            }
            seen.push((left, depth));
            if let Some(stop) = self.at_point(&checked, depth) {
                if report {
                    self.report.leaf(Walk::new(stop, path(step)));
                }
                continue;
            }
            let moved = fix_contract::moved(fix, &applied);
            let marks = moved_marks(&top.marks, &top.text, fix, &moved, &applied.ranges);
            let next = Frame {
                pick: pick(&checked, options.pick).expect("a point with a pick"),
                text: new_text.clone(),
                checked,
                marks,
                rise,
                next: 0,
                used,
            };
            steps.push(step);
            on_path.insert(new_text, frames.len());
            frames.push(next);
        }
        Round::Done { more }
    }
}
