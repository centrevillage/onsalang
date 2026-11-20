//! The shrinking of a program that fails (W7-20 U3, for the twins of `if~` and `match~` and for the panics by stage): a greedy
//! run of smaller candidates, of which one is taken when it fails in the same class (a program that is no longer read, or that
//! fails in another way, is not taken). The run is bounded by a number of tries and a time. It runs only on a failure, so a run
//! that passes does not pay for it. The candidates are the plan of a family when it has one (`twin_pan.rs`), and else the
//! text of the program without a line.

use std::time::{Duration, Instant};

/// The most candidates tried, and the longest the run lasts.
pub const LIMITS: (usize, Duration) = (200, Duration::from_secs(20));

/// The kinds of failure that the panics by stage tell (`twin_pan.rs` writes them, `class_of` reads them), and the two that the
/// driver and the interpreter tell: a broken Core, and a division of the program that divides by zero when it runs.
pub const UNEXPECTED_PANIC: &str = "unexpected panic";
pub const MISSING_PANIC: &str = "missing panic";
pub const OUT_OF_STAGES: &str = "panic out of its stages";
pub const INTERNAL: &str = "internal error";
pub const DIVISION: &str = "division by zero";

/// What kind of failure a message tells, by what it says (the words of a text and its position are not the kind).
pub fn class_of(msg: &str) -> &'static str {
    const KINDS: [&str; 12] = [
        "does not hold",
        "it panicked at",
        "did not panic",
        UNEXPECTED_PANIC,
        MISSING_PANIC,
        OUT_OF_STAGES,
        "not read",
        "not printed",
        "not evaluated",
        "not compared",
        INTERNAL,
        DIVISION,
    ];
    KINDS.iter().copied().find(|k| msg.contains(k)).unwrap_or("other")
}

/// The smallest of what `smaller` gives that `fails` in the class `class`, from `start` (which fails in it), and how many
/// candidates were tried. Each step takes the first candidate that keeps the class, so the run ends when none does, or at a limit.
pub fn shrink<T>(
    start: T,
    class: &str,
    (tries, time): (usize, Duration),
    smaller: impl Fn(&T) -> Vec<T>,
    fails: impl Fn(&T) -> Option<&'static str>,
) -> (T, usize) {
    let (t0, mut n, mut best) = (Instant::now(), 0, start);
    'steps: loop {
        for c in smaller(&best) {
            if n >= tries || t0.elapsed() > time {
                break 'steps;
            }
            n += 1;
            if fails(&c) == Some(class) {
                best = c;
                continue 'steps;
            }
        }
        break;
    }
    (best, n)
}

/// The texts of `src` without one line, the last line first (the tests are at the end of a program).
pub fn without_a_line(src: &str) -> Vec<String> {
    let lines: Vec<&str> = src.lines().collect();
    (0..lines.len())
        .rev()
        .map(|i| lines.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, l)| *l).collect::<Vec<_>>().join("\n"))
        .collect()
}
