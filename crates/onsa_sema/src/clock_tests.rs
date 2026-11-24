//! The names, the stages and the text of the clocks (`clock.rs`, W7-02 U1)
//! and their comparisons (W7-02 U2a).

use onsa_diag::internal::InternalBug;
use onsa_diag::{FileId, Span};

use crate::clock::{
    Clash, Clock, ClockFrame, ClockName, ClockStage, EventSrc, Ratio, delay_out, emit_clock, join, keeps_delay_state,
    loop_clock, promote, readable_at, rebase,
};

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
    assert_eq!(event(0).shown(at), "event");
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

// The comparisons (W7-02 U2a). The expectations follow the table of the
// design (§11.3, §11.4, §11.9, S-567 P3 and K6); the rows of an event
// clock are after them.

const S: Clock = Clock::SAMPLE;

fn tick(k: i32) -> Clock {
    Clock::Tick(Ratio(k))
}

fn joined(ops: &[Clock]) -> Result<Option<Clock>, Clash> {
    join(&ops.iter().copied().map(Some).collect::<Vec<_>>())
}

fn clash_of(i: usize, a: Clock, j: usize, b: Clock) -> Clash {
    Clash { first: (i, a), second: (j, b) }
}

fn is_internal_error<T>(f: impl FnOnce() -> T + std::panic::UnwindSafe) -> bool {
    std::panic::catch_unwind(f).err().is_some_and(|p| p.downcast_ref::<InternalBug>().is_some())
}

#[test]
fn a_join_of_parameter_kinds_is_the_largest() {
    assert_eq!(joined(&[Clock::Const]), Ok(Some(Clock::Const)));
    assert_eq!(joined(&[Clock::Const, Clock::Init]), Ok(Some(Clock::Init)));
    assert_eq!(joined(&[Clock::Block, Clock::Const, Clock::Init]), Ok(Some(Clock::Block)));
    assert_eq!(joined(&[Clock::Init, Clock::Init]), Ok(Some(Clock::Init)));
}

#[test]
fn a_join_of_ticks_needs_one_ratio() {
    assert_eq!(joined(&[S, Clock::Init, S]), Ok(Some(S)));
    assert_eq!(joined(&[tick(-2), Clock::Block]), Ok(Some(tick(-2))));
    assert_eq!(joined(&[Clock::Const, tick(-1), tick(-1)]), Ok(Some(tick(-1))));
    assert_eq!(joined(&[S, tick(-1)]), Err(clash_of(0, S, 1, tick(-1))));
    assert_eq!(joined(&[Clock::Init, tick(-1), Clock::Const, S]), Err(clash_of(1, tick(-1), 3, S)));
}

#[test]
fn bottom_is_the_unit_of_a_join() {
    assert_eq!(join(&[]), Ok(None));
    assert_eq!(join(&[None, None]), Ok(None));
    assert_eq!(join(&[None, Some(Clock::Init)]), Ok(Some(Clock::Init)));
    assert_eq!(join(&[Some(tick(1)), None]), Ok(Some(tick(1))));
    // The indices are of the operands given, ⊥ counted.
    assert_eq!(join(&[Some(S), None, Some(tick(-1))]), Err(clash_of(0, S, 2, tick(-1))));
}

#[test]
fn a_clock_in_error_passes_a_join_with_no_clash() {
    assert_eq!(joined(&[Clock::Init, Clock::Error]), Ok(Some(Clock::Error)));
    assert_eq!(joined(&[Clock::Error, tick(-1), S]), Ok(Some(Clock::Error)));
    assert_eq!(joined(&[tick(1), Clock::Const, Clock::Error]), Ok(Some(Clock::Error)));
    assert_eq!(join(&[None, Some(Clock::Error)]), Ok(Some(Clock::Error)));
}

#[test]
fn sample_tick_follows_a_tick_in_a_join() {
    assert_eq!(joined(&[Clock::Ambient]), Ok(Some(Clock::Ambient)));
    assert_eq!(joined(&[Clock::Ambient, Clock::Init]), Ok(Some(Clock::Ambient)));
    assert_eq!(joined(&[Clock::Block, Clock::Ambient, Clock::Const]), Ok(Some(Clock::Ambient)));
    assert_eq!(joined(&[Clock::Ambient, Clock::Ambient]), Ok(Some(Clock::Ambient)));
    assert_eq!(joined(&[Clock::Ambient, S]), Ok(Some(S)));
    assert_eq!(joined(&[Clock::Init, Clock::Ambient, tick(-1)]), Ok(Some(tick(-1))));
}

#[test]
fn sample_times_n_with_another_operand_clashes() {
    assert_eq!(joined(&[tick(1)]), Ok(Some(tick(1))));
    assert_eq!(joined(&[tick(1), Clock::Const]), Err(clash_of(0, tick(1), 1, Clock::Const)));
    assert_eq!(joined(&[Clock::Init, tick(2)]), Err(clash_of(0, Clock::Init, 1, tick(2))));
    assert_eq!(joined(&[tick(1), tick(1)]), Err(clash_of(0, tick(1), 1, tick(1))));
    assert_eq!(joined(&[S, tick(1)]), Err(clash_of(0, S, 1, tick(1))));
}

#[test]
fn a_parameter_kind_is_read_at_its_kind_or_larger_and_at_a_tick() {
    for (v, p) in [(Clock::Const, Clock::Const), (Clock::Const, Clock::Init), (Clock::Init, Clock::Init)] {
        assert_eq!(readable_at(v, p), Ok(()), "{v:?} at {p:?}");
    }
    for v in [Clock::Const, Clock::Init, Clock::Block] {
        assert_eq!(readable_at(v, S), Ok(()), "{v:?}");
        assert_eq!(readable_at(v, tick(-3)), Ok(()), "{v:?}");
    }
    assert_eq!(readable_at(Clock::Block, Clock::Init), Err(clash_of(0, Clock::Block, 1, Clock::Init)));
    assert_eq!(readable_at(Clock::Init, Clock::Const), Err(clash_of(0, Clock::Init, 1, Clock::Const)));
}

#[test]
fn a_tick_is_read_at_the_same_tick_only() {
    assert_eq!(readable_at(S, S), Ok(()));
    assert_eq!(readable_at(tick(1), tick(1)), Ok(()));
    assert_eq!(readable_at(tick(-1), S), Err(clash_of(0, tick(-1), 1, S)));
    assert_eq!(readable_at(S, tick(-1)), Err(clash_of(0, S, 1, tick(-1))));
    assert_eq!(readable_at(S, Clock::Block), Err(clash_of(0, S, 1, Clock::Block)));
}

#[test]
fn sample_tick_and_a_clock_in_error_where_they_are_read() {
    assert_eq!(readable_at(Clock::Ambient, S), Ok(()));
    assert_eq!(readable_at(Clock::Ambient, tick(-2)), Ok(()));
    assert_eq!(readable_at(Clock::Ambient, Clock::Block), Err(clash_of(0, Clock::Ambient, 1, Clock::Block)));
    assert_eq!(readable_at(Clock::Ambient, Clock::Init), Err(clash_of(0, Clock::Ambient, 1, Clock::Init)));
    assert_eq!(readable_at(Clock::Error, Clock::Init), Ok(()));
    assert_eq!(readable_at(S, Clock::Error), Ok(()));
    assert!(is_internal_error(|| readable_at(Clock::Init, Clock::Ambient)));
}

#[test]
fn at_goes_from_slow_to_fast_up_to_the_sample_of_the_body() {
    for (v, to) in [
        (Clock::Const, Clock::Init),
        (Clock::Init, Clock::Init),
        (Clock::Init, Clock::Block),
        (Clock::Block, S),
        (Clock::Const, tick(-1)),
        (tick(-2), S),
        (tick(-2), tick(-1)),
        (S, S),
    ] {
        assert_eq!(promote(v, to), Ok(to), "{v:?} at {to:?}");
    }
    for (v, to) in [(Clock::Block, Clock::Init), (S, tick(-1)), (S, Clock::Block), (Clock::Init, tick(1)), (tick(1), S)]
    {
        assert_eq!(promote(v, to), Err(clash_of(0, v, 1, to)), "{v:?} at {to:?}");
    }
}

#[test]
fn sample_tick_goes_to_a_tick_and_at_passes_a_clock_in_error() {
    assert_eq!(promote(Clock::Ambient, S), Ok(S));
    assert_eq!(promote(Clock::Ambient, tick(-3)), Ok(tick(-3)));
    assert_eq!(promote(Clock::Ambient, Clock::Block), Err(clash_of(0, Clock::Ambient, 1, Clock::Block)));
    assert_eq!(promote(Clock::Ambient, tick(1)), Err(clash_of(0, Clock::Ambient, 1, tick(1))));
    assert_eq!(promote(Clock::Error, Clock::Block), Ok(Clock::Error));
    assert_eq!(promote(S, Clock::Error), Ok(Clock::Error));
    assert_eq!(promote(Clock::Block, Clock::Error), Ok(Clock::Error));
    assert!(is_internal_error(|| promote(Clock::Init, Clock::Const)));
}

#[test]
fn a_delay_holds_its_state_at_a_tick_of_the_body() {
    for c in [S, tick(-4), Clock::Ambient, Clock::Error] {
        assert!(keeps_delay_state(c), "{c:?}");
    }
    for c in [Clock::Const, Clock::Init, Clock::Block, tick(1)] {
        assert!(!keeps_delay_state(c), "{c:?}");
    }
}

#[test]
fn the_clock_of_a_delay_by_its_first_argument() {
    for looped in [false, true] {
        // A tick and a clock in error are themselves.
        assert_eq!(delay_out(Some(tick(-1)), looped), Some(tick(-1)));
        assert_eq!(delay_out(Some(S), looped), Some(S));
        assert_eq!(delay_out(Some(Clock::Error), looped), Some(Clock::Error));
        // ⊥ gives ⊥; `prev~(sample_tick())` is the `sample` of the body.
        assert_eq!(delay_out(None, looped), None);
        assert_eq!(delay_out(Some(Clock::Ambient), looped), Some(S));
    }
    // A parameter kind (E0813 at the check): ⊥ in a loop, else `sample`.
    for c in [Clock::Const, Clock::Init, Clock::Block] {
        assert_eq!(delay_out(Some(c), true), None, "{c:?}");
        assert_eq!(delay_out(Some(c), false), Some(S), "{c:?}");
    }
}

#[test]
fn a_declared_clock_in_the_frame_of_its_call() {
    let body = ClockFrame { ratio: Ratio(0) };
    let slow = ClockFrame { ratio: Ratio(-2) };
    for c in [Clock::Init, Clock::Block, Clock::Error] {
        assert_eq!(rebase(c, slow), c);
    }
    assert_eq!(rebase(tick(-1), body), tick(-1));
    assert_eq!(rebase(S, slow), tick(-2));
    assert_eq!(rebase(tick(1), slow), tick(-1));
    assert!(is_internal_error(|| rebase(tick(i32::MAX), ClockFrame { ratio: Ratio(1) })));
    assert!(is_internal_error(|| rebase(Clock::Ambient, body)));
}

#[test]
fn the_clock_of_a_loop() {
    for t in [None, Some(Clock::Const), Some(Clock::Init), Some(Clock::Block), Some(Clock::Ambient)] {
        assert_eq!(loop_clock(t), S, "{t:?}");
    }
    assert_eq!(loop_clock(Some(tick(-2))), tick(-2));
    assert_eq!(loop_clock(Some(S)), S);
    assert_eq!(loop_clock(Some(Clock::Error)), Clock::Error);
}

/// The clocks of the grid (no event, S-1095): the parameter kinds,
/// `sample_tick()`, a clock in error and the ticks of the ratios −3 to 3.
fn grid() -> Vec<Clock> {
    let mut v = vec![Clock::Const, Clock::Init, Clock::Block, Clock::Ambient, Clock::Error];
    v.extend((-3..=3).map(tick));
    v
}

/// Two results of a join that agree: the same clock, or both a clash.
fn agree(a: Result<Option<Clock>, Clash>, b: Result<Option<Clock>, Clash>) -> bool {
    match (a, b) {
        (Err(_), Err(_)) => true,
        (a, b) => a == b,
    }
}

#[test]
fn a_join_over_the_grid_is_symmetric_and_has_bottom_as_its_unit() {
    let cs: Vec<Option<Clock>> = std::iter::once(None).chain(grid().into_iter().map(Some)).collect();
    assert_eq!(join(&[]), Ok(None));
    for &a in &cs {
        assert_eq!(join(&[a]), Ok(a), "{a:?}");
        for &b in &cs {
            assert!(agree(join(&[a, b]), join(&[b, a])), "{a:?} {b:?}");
            for &c in &cs {
                let flat = join(&[a, b, c]);
                for p in [[a, c, b], [b, a, c], [b, c, a], [c, a, b], [c, b, a]] {
                    assert!(agree(flat, join(&p)), "{p:?}");
                }
                // A clock in error hides the clash of the others (the table):
                // past it, the join of two and then the third is the same.
                if [a, b, c].contains(&Some(Clock::Error)) {
                    continue;
                }
                let nested = join(&[a, b]).and_then(|ab| join(&[ab, c]));
                assert!(agree(flat, nested), "{a:?} {b:?} {c:?}");
            }
        }
    }
}

/// The comparisons over the grid give a value or an internal error, and no
/// other panic.
#[test]
fn out_of_the_table_is_an_internal_error_and_nothing_else() {
    fn no_other_panic<T>(f: impl FnOnce() -> T + std::panic::UnwindSafe) {
        if let Err(p) = std::panic::catch_unwind(f) {
            assert!(p.downcast_ref::<InternalBug>().is_some(), "a panic that is no internal error");
        }
    }
    for a in grid() {
        for b in grid() {
            no_other_panic(|| readable_at(a, b));
            no_other_panic(|| promote(a, b));
        }
        for k in [0, 1, -2] {
            no_other_panic(|| rebase(a, ClockFrame { ratio: Ratio(k) }));
        }
    }
    assert!(is_internal_error(|| readable_at(Clock::Init, Clock::Ambient)));
    assert!(is_internal_error(|| promote(Clock::Init, Clock::Const)));
}

// The rows of an event clock (§11.11, §11.3), by hand from the letter: the
// order `constant < init < block < event < sample / N < sample < sample * N`,
// and two events of two sources have none.

/// The event clock of the input `i`.
fn event(i: usize) -> Clock {
    Clock::Event(EventSrc::input(i))
}

/// The sources of a body of two inputs: its inputs, then its calls; that of
/// an output of a heading is none of them.
#[test]
fn the_source_of_an_event_is_an_input_or_a_call() {
    assert_eq!(EventSrc::input(0).place(2), Err(0));
    assert_eq!(EventSrc::input(1).place(2), Err(1));
    assert_eq!(EventSrc::call(2, 0).place(2), Ok(0));
    assert_eq!(EventSrc::call(2, 3).place(2), Ok(3));
    assert_ne!(EventSrc::call(2, 0), EventSrc::input(1));
    assert!(EventSrc::OUTPUT.place(2).is_ok_and(|i| i > 1 << 24));
}

/// "イベントのクロックは全ての周期の刻みのクロックの下で、パラメータの種類の上にある";
/// a value of it read faster is stored, whichever the tick.
#[test]
fn the_stage_of_an_event_is_between_block_and_every_tick() {
    let of = |c: Clock| c.stage().expect("a stage");
    assert_eq!(event(1).stage(), Some(ClockStage::Event(EventSrc::input(1))));
    assert!(of(Clock::Block) < of(event(0)) && of(event(7)) < of(tick(-31)));
    for k in [-31, -2, 0, 1] {
        assert!(of(event(0)).stored_slower_than(of(tick(k))), "{k}");
        assert!(!of(tick(k)).stored_slower_than(of(event(0))), "{k}");
    }
    assert!(!of(event(0)).stored_slower_than(of(event(0))));
    assert!(!of(event(0)).stored_slower_than(of(event(1))) && !of(event(1)).stored_slower_than(of(event(0))));
    assert!(!of(Clock::Block).stored_slower_than(of(event(0))));
    assert!(of(tick(-2)).stored_slower_than(of(Clock::SAMPLE)));
    assert!(of(tick(-1)).slow_tick());
    assert!(![of(event(0)), of(Clock::SAMPLE), of(tick(1)), of(Clock::Block)].into_iter().any(ClockStage::slow_tick));
}

/// "パラメータの種類とイベントの値は自由に混ざること", "最大が無ければ E0815"; S-1232: `sample_tick()`
/// is of the event beside it.
#[test]
fn a_join_of_an_event_is_the_tick_or_the_event() {
    let (a, b) = (event(0), event(1));
    for slow in [Clock::Const, Clock::Init, Clock::Block, Clock::Ambient] {
        assert_eq!(joined(&[a, slow]), Ok(Some(a)), "{slow:?}");
        assert_eq!(joined(&[slow, a]), Ok(Some(a)), "{slow:?}");
    }
    for k in [0, -2] {
        assert_eq!(joined(&[a, tick(k)]), Ok(Some(tick(k))), "{k}");
        // Two events and a tick in one expression: the tick is the largest.
        for ops in [[a, b, tick(k)], [a, tick(k), b], [tick(k), a, b]] {
            assert_eq!(joined(&ops), Ok(Some(tick(k))), "{ops:?}");
        }
    }
    assert_eq!(joined(&[a, a]), Ok(Some(a)));
    assert_eq!(join(&[Some(a), None]), Ok(Some(a)));
    assert_eq!(joined(&[a, b, Clock::Error]), Ok(Some(Clock::Error)));
}

/// S-1095: two events with no tick in the expression do not meet, whatever
/// is slower beside them; nor do ticks of two ratios beside them.
#[test]
fn a_join_of_two_events_with_no_tick_clashes() {
    let (a, b) = (event(0), event(1));
    assert_eq!(joined(&[a, b]), Err(clash_of(0, a, 1, b)));
    assert_eq!(joined(&[b, a]), Err(clash_of(0, b, 1, a)));
    assert_eq!(joined(&[Clock::Block, a, Clock::Ambient, b]), Err(clash_of(1, a, 3, b)));
    assert_eq!(joined(&[a, b, event(2)]), Err(clash_of(0, a, 1, b)));
    assert!(joined(&[a, b, tick(0), tick(-2)]).is_err());
    assert!(joined(&[a, tick(1)]).is_err());
}

/// A join with events is the same in every order of its operands.
#[test]
fn a_join_with_events_does_not_depend_on_the_order() {
    let mut cs = grid();
    cs.extend([event(0), event(1)]);
    for &a in &cs {
        for &b in &cs {
            assert!(agree(joined(&[a, b]), joined(&[b, a])), "{a:?} {b:?}");
            for &c in &cs {
                for d in [event(0), event(2)] {
                    let flat = joined(&[a, b, c, d]);
                    for p in [[d, a, b, c], [a, d, c, b], [c, b, a, d], [b, d, a, c], [c, d, b, a]] {
                        assert!(agree(flat, joined(&p)), "{p:?}");
                    }
                }
            }
        }
    }
}

/// The join of up to 4 operands with events against a model by hand from the
/// letter (§11.3, §11.11, S-1095, S-567 K6): an operand in error gives
/// error; `sample * N` meets no other operand, ticks of two ratios clash; with
/// a tick, the tick; two events with no tick clash; else the event, else
/// `sample_tick()`, else the largest parameter kind.
#[test]
fn a_join_with_events_is_the_one_of_the_letter_over_every_operands() {
    fn model(ops: &[Option<Clock>]) -> Result<Option<Clock>, ()> {
        let given: Vec<Clock> = ops.iter().flatten().copied().collect();
        if given.contains(&Clock::Error) {
            return Ok(Some(Clock::Error));
        }
        if given.len() > 1 && given.contains(&tick(1)) {
            return Err(());
        }
        let mut of = given.iter().filter(|c| matches!(c, Clock::Tick(_)));
        if let Some(t) = of.next() {
            return if of.all(|x| x == t) { Ok(Some(*t)) } else { Err(()) };
        }
        let mut of = given.iter().filter(|c| matches!(c, Clock::Event(_)));
        if let Some(e) = of.next() {
            return if of.all(|x| x == e) { Ok(Some(*e)) } else { Err(()) };
        }
        let largest = [Clock::Ambient, Clock::Block, Clock::Init, Clock::Const];
        Ok(largest.into_iter().find(|c| given.contains(c)))
    }
    let mut cs: Vec<Option<Clock>> = vec![None, Some(Clock::Const), Some(Clock::Init), Some(Clock::Block)];
    cs.extend([Clock::Ambient, Clock::Error, tick(-2), tick(0), tick(1), event(0), event(1), event(2)].map(Some));
    let mut lists: Vec<Vec<Option<Clock>>> = vec![Vec::new()];
    for n in 1..=4 {
        let longer = |l: &Vec<Option<Clock>>| cs.iter().map(|&c| [&l[..], &[c]].concat()).collect::<Vec<_>>();
        lists = lists.iter().flat_map(longer).collect();
        assert_eq!(lists.len(), cs.len().pow(n));
        for ops in &lists {
            assert_eq!(join(ops).map_err(|_| ()), model(ops), "{ops:?}");
        }
    }
}

/// "イベントの値は `block` と同じく暗黙に読め、使う所の周期の刻みのクロックの刻みで"; to an input at `init`,
/// `block`, `sample * N` E0815; "イベントの段の式では、周期の刻みのクロックの値は読めず"; "別の入力のイベントの
/// クロックどうしは比べられない".
#[test]
fn an_event_is_read_at_itself_and_at_the_ticks_of_the_body() {
    let a = event(0);
    for (place, ok) in [
        (Clock::Init, false),
        (Clock::Block, false),
        (a, true),
        (event(1), false),
        (tick(-2), true),
        (tick(0), true),
        (tick(1), false),
        (Clock::Error, true),
    ] {
        assert_eq!(readable_at(a, place).is_ok(), ok, "{place:?}");
    }
    for (value, ok) in [
        (Clock::Const, true),
        (Clock::Init, true),
        (Clock::Block, true),
        (Clock::Ambient, true),
        (tick(-2), false),
        (tick(0), false),
        (tick(1), false),
        (Clock::Error, true),
    ] {
        assert_eq!(readable_at(value, a).is_ok(), ok, "{value:?}");
    }
}

/// "`v at sample`・`v at (sample / N)` と書いても同じ意味"; `block` and `init` are slower.
#[test]
fn at_takes_an_event_to_a_tick_of_the_body_only() {
    let a = event(0);
    assert_eq!(promote(a, tick(0)), Ok(tick(0)));
    assert_eq!(promote(a, tick(-2)), Ok(tick(-2)));
    for to in [Clock::Init, Clock::Block, tick(1)] {
        assert!(promote(a, to).is_err(), "{to:?}");
    }
    assert_eq!(promote(a, Clock::Error), Ok(Clock::Error));
    assert!(is_internal_error(move || promote(Clock::Block, a)));
}

/// §11.4: a delay counts the ticks of an event, and is of its clock; the
/// clock of a loop is the event that enters it.
#[test]
fn a_delay_and_a_loop_of_an_event() {
    let a = event(0);
    assert!(keeps_delay_state(a));
    assert_eq!(delay_out(Some(a), false), Some(a));
    assert_eq!(loop_clock(Some(a)), a);
    assert!(is_internal_error(move || rebase(a, ClockFrame::BODY)));
}

/// S-1196: the ticks that give out the events of an output are of the clock
/// of its expression; "パラメータの種類だけなら本体の `sample` の刻みで".
#[test]
fn the_clock_that_gives_out_events() {
    for c in [tick(0), tick(-2), event(3), Clock::Error] {
        assert_eq!(emit_clock(c), c);
    }
    for c in [Clock::Const, Clock::Init, Clock::Block, Clock::Ambient] {
        assert_eq!(emit_clock(c), Clock::SAMPLE, "{c:?}");
    }
    assert_eq!(emit_clock(tick(1)), Clock::SAMPLE);
}

/// S-1077: the N of a derived clock and of `.down~` / `.up~` is a power of
/// 2 that is 2 or more; `/` makes the ratio negative, `*` positive.
#[test]
fn the_ratio_of_an_n_is_its_power_of_two() {
    use onsa_syntax::ast::RatioOp::{Div, Mul};
    assert_eq!(Ratio::of_n(Div, 4), Some(Ratio(-2)));
    assert_eq!(Ratio::of_n(Mul, 2), Some(Ratio(1)));
    assert_eq!(Ratio::of_n(Div, 1 << 31), Some(Ratio(-31)));
    for n in [0, 1, 3, 6, 12, u32::MAX] {
        assert_eq!((Ratio::of_n(Div, n), Ratio::of_n(Mul, n)), (None, None), "{n}");
    }
}

/// The stages are written as their clocks, and a tick of a ratio is not
/// the `sample` of the body.
#[test]
fn a_stage_is_shown_as_its_clock() {
    let at = Span::new(FileId(0), 0, 0);
    let shown =
        [ClockStage::Init, ClockStage::Block, ClockStage::SAMPLE, ClockStage::Tick(Ratio(-2))].map(|s| s.shown(at));
    assert_eq!(shown, ["init", "block", "sample", "sample / 4"]);
    assert!(tick(-2).of_ratio() && tick(1).of_ratio());
    assert!(![S, Clock::Block, Clock::Const, Clock::Error, Clock::Ambient].iter().any(|c| c.of_ratio()));
}
