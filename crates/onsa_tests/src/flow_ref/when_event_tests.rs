//! A `when~` of an event on the evaluator (W7-11 U3/e; §11.10, §11.11, §11.3, S-563, S-1209): the table of values worked out by hand (`when_event_values.md`), run as the table of `event_values.md` is. The form of W7-17 (a `when~`
//! with the `reset_if~` of an event in one chain) is in it (the section `u1`) and runs from W7-17 U4.

use super::event_table_tests::run_cases;

const VALUES: &str = include_str!("when_event_values.md");

#[test]
fn the_values_of_a_when_of_an_event_are_those_written_by_hand() {
    let r = run_cases(VALUES, &|id| id.starts_with(['w', 'f']));
    let (f, u, g) = (&r.failed, &r.unavailable, &r.gap);
    assert!(f.is_empty() && u.is_empty() && g.is_empty(), "{f:#?} {u:?} {g:?}");
    assert_eq!(r.passed, ["w1", "w2", "w3", "w4", "w5", "w6", "f1"]);
}

#[test]
fn a_when_with_the_reset_of_an_event_in_one_chain_runs_with_the_values_written_by_hand() {
    let r = run_cases(VALUES, &|id| id.starts_with('u'));
    let (f, u, g) = (&r.failed, &r.unavailable, &r.gap);
    assert!(f.is_empty() && u.is_empty() && g.is_empty(), "{f:#?} {u:?} {g:?}");
    assert_eq!(r.passed, ["u1"]);
}
