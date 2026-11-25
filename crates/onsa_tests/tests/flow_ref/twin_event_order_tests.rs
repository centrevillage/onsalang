//! The places that stop the run when events tick inside one position (`twin_event_order.rs`, W7-11 U2-e2, S-1233 .. S-1236, S-1240).

use super::twin_event_order::{GROUPS, run, saved_cases};

#[test]
fn the_first_division_is_where_the_order_of_the_stages_of_events_says() {
    let (stopped, bad) = run(false);
    let runs: usize = GROUPS.iter().map(|g| g.order.len()).sum();
    assert!(bad.is_empty(), "{}", bad.join("\n\n"));
    // Every program of a group stops (the places are made safe one after the other), and so do the cases that follow, but one.
    assert_eq!(stopped, runs + saved_cases().len() - 1, "{stopped} runs stopped");
}

#[test]
fn the_places_of_the_groups_are_each_the_first_of_a_run_and_no_place_is_named_twice() {
    for g in GROUPS {
        let letters: std::collections::BTreeSet<char> = g.order.chars().collect();
        assert_eq!(letters.len(), g.order.len(), "{}: a place twice in {}", g.name, g.order);
        let text = [g.parts.concat(), g.body.to_string()].concat();
        for l in g.order.chars() {
            assert_eq!(text.matches(&format!("@{l}")).count(), 1, "{}: the place {l} is not once", g.name);
        }
    }
}

#[test]
#[ignore = "W7-11 U2: S-564"]
fn the_first_division_is_the_same_in_the_interpreter() {
    let (stopped, bad) = run(true);
    assert!(bad.is_empty() && stopped > 0, "{stopped} runs stopped\n{}", bad.join("\n\n"));
}
