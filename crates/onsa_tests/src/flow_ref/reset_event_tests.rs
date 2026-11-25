//! A `reset_if~` of an event on the evaluator (W7-11 U2r/e; §11.10, §11.11, §11.3, S-1236, S-1250 (B)): the table of values worked out by hand (`reset_event_values.md`), run as the table of `event_values.md` is.

use super::event_table_tests::run_cases;

const VALUES: &str = include_str!("reset_event_values.md");

#[test]
fn the_values_of_a_reset_by_an_event_are_those_written_by_hand() {
    let r = run_cases(VALUES, &|_| true);
    assert!(
        r.failed.is_empty() && r.unavailable.is_empty() && r.gap.is_empty(),
        "{:#?} {:?} {:?}",
        r.failed,
        r.unavailable,
        r.gap
    );
    assert_eq!(r.passed, ["s1", "s2", "s3", "s4", "s5", "t1", "t2", "t3", "u1", "u2", "u3", "v1"]);
}
