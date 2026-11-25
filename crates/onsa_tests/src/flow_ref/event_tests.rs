//! The event stages of the evaluator on the table of values of W7-11 stage 1 (`event_values.md`; §11.11, §11.3, §11.9, §11.4): each case is a flow with its source, its inputs (the columns of `sample`, the values of
//! `block`, the events the boundary gives as `(position, input, value)` in the order it gives them) and the output, written by hand from the text before any model was run. A case marked `【字で決まらない】` is not
//! run (counted). A case of a form the evaluator has not yet (a modifier with an event condition, `par~`, an arm, a part under a boundary with an event inside) stops with `Unavailable` and is counted, never dropped.

use super::event_table_tests::{Report, run_cases};

const VALUES: &str = include_str!("event_values.md");
const READS: &str = include_str!("event_reads_values.md");

/// The sections of the table in the straight line (U2): a producer and a receiver, a chain of them, two inputs, the reads of an event, `sample_tick()`, and the flows that wrap them.
fn straight(id: &str) -> bool {
    matches!(id.chars().next(), Some('a' | 'b' | 'c' | 'h' | 'i')) || matches!(id, "k-a1" | "k-b1")
}

fn show(r: &Report) -> String {
    format!("passed {:?}\nunavailable {:?}\nnot settled by the text {:?}", r.passed, r.unavailable, r.gap)
}

#[test]
fn the_straight_cases_of_the_table_pass_with_the_values_written_by_hand() {
    let r = run_cases(VALUES, &straight);
    assert!(r.failed.is_empty(), "{:#?}", r.failed);
    // A `when~` with an event runs from U3 (h5, h10, i2a). The cases whose chain has a rate (h7) or whose flow takes events and has a `when~` (i4) stop with `Unavailable` (W7-17), and no other does.
    let later: Vec<&str> = r.unavailable.iter().map(|(id, _)| id.as_str()).collect();
    assert_eq!(later, ["h7", "i4"], "{}", show(&r));
    assert_eq!(r.passed.len() + r.unavailable.len() + r.gap.len(), r.count, "{}", show(&r));
    // a1 .. a6, b1 .. b3, c1 .. c5b, h1 .. h6, h8 .. h11, i1, i2a, i2b, i3, i5a, i5b, k-a1, k-b1; b4 is not settled by the text.
    assert_eq!(r.passed.len(), 33, "{}", show(&r));
    assert_eq!(r.gap, ["b4"]);
}

#[test]
fn the_other_cases_are_counted_and_whatever_passes_passes() {
    let r = run_cases(VALUES, &|id| !straight(id));
    assert!(r.failed.is_empty(), "{:#?}", r.failed);
    assert_eq!(r.passed.len() + r.unavailable.len() + r.gap.len(), r.count, "{}", show(&r));
    println!("{}", show(&r));
}

#[test]
fn an_event_read_without_a_caret_is_the_value_where_it_is_written_whatever_condition_with_a_caret_chooses_it() {
    let r = run_cases(READS, &|_| true);
    assert!(r.failed.is_empty() && r.unavailable.is_empty(), "{:#?} {}", r.failed, show(&r));
    assert_eq!(r.passed, ["r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8"], "{}", show(&r));
}
