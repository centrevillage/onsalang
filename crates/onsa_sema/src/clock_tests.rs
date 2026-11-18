//! The names, the stages and the text of the clocks (`clock.rs`, W7-02 U1).

use onsa_diag::internal::InternalBug;
use onsa_diag::{FileId, Span};

use crate::clock::{Clock, ClockName, ClockStage, Ratio};

#[test]
fn a_name_and_its_clock_go_both_ways() {
    for c in ClockName::ALL {
        assert_eq!(ClockName::of_name(c.name()), Some(c));
    }
    assert_eq!(ClockName::ALL.map(ClockName::name), ["init", "block", "sample"]);
    assert_eq!(ClockName::of_name("event"), None);
    assert_eq!(ClockName::of_name("Sig"), None);
    assert_eq!(ClockName::ALL.map(ClockName::clock), [Clock::Init, Clock::Block, Clock::SAMPLE]);
}

#[test]
fn the_stage_of_a_clock() {
    assert_eq!(Clock::SAMPLE, Clock::Tick(Ratio(0)));
    assert_eq!(Clock::Init.stage(), Some(ClockStage::Init));
    assert_eq!(Clock::Block.stage(), Some(ClockStage::Block));
    assert_eq!(Clock::Tick(Ratio(-2)).stage(), Some(ClockStage::Tick(Ratio(-2))));
    for c in [Clock::Const, Clock::Ambient, Clock::Error] {
        assert_eq!(c.stage(), None, "{c:?}");
    }
}

#[test]
fn the_stages_in_their_order() {
    let stages = [ClockStage::Init, ClockStage::Block, ClockStage::Tick(Ratio(-1)), ClockStage::Tick(Ratio(0))];
    assert!(stages.windows(2).all(|w| w[0] < w[1]));
}

#[test]
fn the_text_of_a_clock() {
    let at = Span::new(FileId(0), 0, 1);
    let shown = [Clock::Const, Clock::Init, Clock::Block, Clock::SAMPLE, Clock::Tick(Ratio(-2)), Clock::Tick(Ratio(1))]
        .map(|c| c.shown(at));
    assert_eq!(shown, ["constant", "init", "block", "sample", "sample / 4", "sample * 2"]);
}

#[test]
fn a_clock_with_no_text_is_an_internal_error_at_its_place() {
    let at = Span::new(FileId(0), 3, 7);
    for c in [Clock::Error, Clock::Ambient, Clock::Tick(Ratio(i32::MAX))] {
        let payload = std::panic::catch_unwind(|| c.shown(at)).expect_err("no text");
        let bug = payload.downcast_ref::<InternalBug>().expect("an internal error");
        assert_eq!(bug.span, Some(at), "{c:?}");
    }
}
