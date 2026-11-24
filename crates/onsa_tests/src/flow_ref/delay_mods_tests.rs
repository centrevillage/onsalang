//! The tests of `.when~(c)` and `.reset_if~(r)` on a built-in delay on the evaluator (W7-10 U3be; §11.10, §11.4, §11.9, S-1209): the delay ticks at the clock K of its first argument, a `when~` reads its
//! condition there, a stopped delay neither reads nor stores and the caller reads the last output (`T.default()` before the first run, whatever `init` the delay has), the length counts the runs, the
//! arguments are the caller's (evaluated at a stopped tick too), and a `reset_if~` puts the values and the write position back to the `init` before the delay reads. The values are worked out by hand
//! from the spec, in the comment of each test. The inputs are `x` = 1 2 3 ... and the `sample` columns `c` and `r` of 0 and 1.

use super::expr_tests::{def_named, with_checked};
use super::flow::Instance;
use super::sema_view::View;
use super::state_tests::{f32s, same};
use super::value::Value;

const CNT: &str = "flow cnt() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}
";

/// The outputs of the flow `name` of `CNT` and `src` for one call of `process` of `frames` frames, `x` = 1 2 3 ... and the columns `cols` of `Bool`s (as 0 and 1), after a call of 3 frames of other
/// values and `reset` when `again` (§11.6: the generated `reset` puts the instance back to its `init`, so the outputs are the same).
fn outs(src: &str, name: &'static str, frames: usize, cols: &[(&'static str, &[u8])], again: bool) -> Vec<f32> {
    let src = format!("{CNT}{src}");
    let col = |c: &[u8]| c.iter().map(|b| Value::Bool(*b == 1)).collect::<Vec<_>>();
    let cols: Vec<(&'static str, Vec<Value>)> = cols.iter().map(|(n, c)| (*n, col(c))).collect();
    let xs: Vec<Value> = (1..=frames).map(|i| Value::F32(i as f32)).collect();
    with_checked(&src, true, move |a| {
        let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
        let mut ins: Vec<(&str, &[Value])> = vec![("x", &xs[..])];
        ins.extend(cols.iter().map(|(n, c)| (*n, &c[..])));
        if again {
            let junk: Vec<(Vec<Value>, &str)> =
                ins.iter().map(|(n, c)| (c[..3].iter().rev().cloned().collect(), *n)).collect();
            let junk: Vec<(&str, &[Value])> = junk.iter().map(|(c, n)| (*n, &c[..])).collect();
            me.process(&[], &junk, 3, None).expect("process");
            me.reset();
        }
        f32s(&me.process(&[], &ins, frames, None).expect("process"))
    })
}

/// `outs` without the call before, and with it (the same outputs).
fn both(src: &str, name: &'static str, frames: usize, cols: &[(&'static str, &[u8])]) -> Vec<f32> {
    let first = outs(src, name, frames, cols, false);
    same(&outs(src, name, frames, cols, true), &first);
    first
}

#[test]
fn a_when_on_a_delay_runs_it_where_the_condition_holds_and_holds_its_last_output_else() {
    // K = W = `sample`. c = 1 0 1 1 0: frame 0 reads the init 0 and stores 1, frame 1 keeps 0 and stores nothing, frame 2 reads 1 and stores 3, frame 3 reads 3, frame 4 keeps 3.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample { prev~(x).when~(c) }";
    same(&both(src, "f", 5, &[("c", &[1, 0, 1, 1, 0])]), &[0.0, 0.0, 1.0, 3.0, 3.0]);
    // With an init of 5: the frames before the first run give `T.default()`, 0, not 5 (§11.10); the first run (frame 2) reads 5.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample { prev~(x, 5.0).when~(c) }";
    same(&both(src, "f", 5, &[("c", &[0, 0, 1, 1, 0])]), &[0.0, 0.0, 5.0, 3.0, 3.0]);
    // The length counts the runs: delay~(x, 3), c = 1 1 0 1 0 1 1 1 runs the frames 0 1 3 5 6 7 (storing 1 2 4 6 7 8); the run j reads what the run j - 3 stored: 0 0 . 0 . 1 2 4.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample { delay~(x, 3).when~(c) }";
    same(&both(src, "f", 8, &[("c", &[1, 1, 0, 1, 0, 1, 1, 1])]), &[0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 2.0, 4.0]);
}

#[test]
fn a_reset_puts_back_the_ring_and_its_place_to_the_init_before_the_delay_reads() {
    // delay~(x, 2, 7.0), r at the frames 2 and 3: the frames 0 1 read 7 7 (storing 1 2); frame 2 puts the ring back to 7 7, reads 7 and stores 3; frame 3 again, reads 7 and stores 4; frame 4
    // reads 7 (the other place), frame 5 reads 4. A reset to `T.default()` would give 0 at the frames 2 3 4.
    let src = "flow f(x: F32 at sample, r: Bool at sample) -> F32 at sample { delay~(x, 2, 7.0).reset_if~(r) }";
    same(&both(src, "f", 6, &[("r", &[0, 0, 1, 1, 0, 0])]), &[7.0, 7.0, 7.0, 7.0, 7.0, 4.0]);
    // A condition at `sample / 4` outside every `when~` is read at its ticks alone (the frames 0 4 8, k = 1 2 3): it holds at the frame 4, where the delay gives 0; the others give x[n - 1].
    let src = "flow f(x: F32 at sample) -> F32 at sample { prev~(x).reset_if~(cnt~().down~(4) == 2.0) }";
    same(&both(src, "f", 9, &[]), &[0.0, 1.0, 2.0, 3.0, 0.0, 5.0, 6.0, 7.0, 8.0]);
}

#[test]
fn the_order_of_when_and_reset_on_a_delay_says_what_the_reset_reaches() {
    // x = 1 .. 8, c = 1 1 0 1 0 0 1 1, r = 0 0 1 1 0 1 0 0.
    // when then reset: 0 (stores 1), 1 (stores 2); frame 2 is stopped and reset: the stored value and the held output are 0; frame 3 resets and runs: 0 (stores 4); frame 4 keeps 0; frame 5
    // resets the stored 4 and the held 0; frame 6 reads 0 (stores 7); frame 7 reads 7.
    let cols: [(&str, &[u8]); 2] = [("c", &[1, 1, 0, 1, 0, 0, 1, 1]), ("r", &[0, 0, 1, 1, 0, 1, 0, 0])];
    let src = "flow f(x: F32 at sample, c: Bool at sample, r: Bool at sample) -> F32 at sample { prev~(x).when~(c).reset_if~(r) }";
    same(&both(src, "f", 8, &cols), &[0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7.0]);
    // reset then when: only the runs reset: frame 2 keeps 1; frame 3 resets the stored 2 and reads 0 (stores 4); frame 4 keeps 0; frame 5 is stopped (no reset); frame 6 reads 4; frame 7 reads 7.
    let src = "flow f(x: F32 at sample, c: Bool at sample, r: Bool at sample) -> F32 at sample { prev~(x).reset_if~(r).when~(c) }";
    same(&both(src, "f", 8, &cols), &[0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 4.0, 7.0]);
}

#[test]
fn the_arguments_of_a_stopped_delay_are_the_callers_and_go_on() {
    // vdelay~(x, cnt~() * 0.5, 4).when~(c): d = 0.5 1 1.5 2 2.5 3 3.5 4 (cnt~() counts every frame). c = 1 1 0 1 0 1 1 1: the runs j = 0 .. 5 (frames 0 1 3 5 6 7) store e = 1 2 4 6 7 8 and
    // read d = 0.5 (1), 1, 2, 3, 3.5, 4: e[j - k] with the weight 1 - f and e[j - k - 1] with f (0 before e[0]): 0, e0 = 1, e1 - 1 = e0 = 1, e0 = 1, 0.5 e1 + 0.5 e0 = 1.5, e1 = 2.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample { vdelay~(x, cnt~() * 0.5, 4).when~(c) }";
    same(&both(src, "f", 8, &[("c", &[1, 1, 0, 1, 0, 1, 1, 1])]), &[0.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.5, 2.0]);
    // prev~(prev~(x)).when~(c): the inner prev~(x) is the caller's, 0 1 2 3 4 5 at every frame; c = 1 0 1 1 0 1: the outer stores it at the runs 0 2 3 5: 0, 0, 0 (stores 2), 2 (stores 3), 2, 3.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample { prev~(prev~(x)).when~(c) }";
    same(&both(src, "f", 6, &[("c", &[1, 0, 1, 1, 0, 1])]), &[0.0, 0.0, 0.0, 2.0, 2.0, 3.0]);
    // prev~(prev~(x).when~(c)): the inner gives 0 0 1 3 3 4 (its runs 0 2 3 5 store 1 3 4 6) and the plain outer reads it a frame late: 0 0 0 1 3 3.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample { prev~(prev~(x).when~(c)) }";
    same(&both(src, "f", 6, &[("c", &[1, 0, 1, 1, 0, 1])]), &[0.0, 0.0, 0.0, 1.0, 3.0, 3.0]);
}

#[test]
fn each_replica_of_a_par_has_its_delay_and_two_whens_are_both_conditions() {
    // par~: the copy i stores (i + 1) x at the runs of c = 1 1 0 1 0 1 (frames 0 1 3 5): copy 0 gives 0 1 1 2 2 4, copy 1 0 2 2 4 4 8; the output is copy 0 + 10 copy 1.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  let ys = par~ i in 0 ..< 2 { prev~(x * (if i == 0 { 1.0 } else { 2.0 })).when~(c) }
  ys[0] + ys[1] * 10.0
}";
    same(&both(src, "f", 6, &[("c", &[1, 1, 0, 1, 0, 1])]), &[0.0, 21.0, 21.0, 42.0, 42.0, 84.0]);
    // prev~(x).when~(c).when~(r) runs where both hold (§11.10): c = 1 1 0 1 1 1, r = 1 0 1 1 1 0 runs the frames 0 3 4 (storing 1 4 5): 0, 0, 0, 1, 4, 4.
    let src = "flow f(x: F32 at sample, c: Bool at sample, r: Bool at sample) -> F32 at sample { prev~(x).when~(c).when~(r) }";
    same(
        &both(src, "f", 6, &[("c", &[1, 1, 0, 1, 1, 1]), ("r", &[1, 0, 1, 1, 1, 0])]),
        &[0.0, 0.0, 0.0, 1.0, 4.0, 4.0],
    );
}

#[test]
fn a_reset_inside_a_when_on_a_slow_delay_resets_on_the_grid_of_the_runs() {
    // l = cnt~().down~(4) is 1 2 3 ... at the ticks of 4 frames, K = W = `sample / 4`. prev~(l).reset_if~(true at (sample / 8)).when~(l != 3.0) is stopped at the tick 2. The runs j = 0 1 2 3 4 are
    // the ticks 0 1 3 4 5, and the grid of the part counts 4 frames a run, so `sample / 8` is the runs 0 2 4 (the ticks 0 3 5), which read 0 (put back); the others read what the run before stored:
    // tick 0: 0 (stores 1), 1: 1 (stores 2), 2: keeps 1, 3: 0 (stores 4), 4: 4 (stores 5), 5: 0. The grid of the caller would reset at the ticks 0 2 4 (0 1 1 2 0 5). `x * 0.0` adds +0.0.
    let src = "flow f(x: F32 at sample) -> F32 at sample {
  let l = cnt~().down~(4)
  (prev~(l).reset_if~(true at (sample / 8)).when~(l != 3.0) at sample) + x * 0.0
}";
    let want: Vec<f32> = [0.0, 1.0, 1.0, 0.0, 4.0, 0.0].iter().flat_map(|v| [*v; 4]).collect();
    same(&both(src, "f", 24, &[]), &want);
}

#[test]
fn a_feedback_an_array_and_a_condition_by_the_replica_on_a_delay() {
    // §11.2: `^y` in the first argument is the `y` of the frame, which the delay gives: c = 1 1 0 1 gives 0 (stores 1), 1 (stores 2), the stopped frame keeps 1 (stores nothing), 2.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  let y = prev~(^y + 1.0).when~(c)
  y + x * 0.0
}";
    same(&both(src, "f", 4, &[("c", &[1, 1, 0, 1])]), &[0.0, 1.0, 1.0, 2.0]);
    // An array is held whole: c = 0 1 0 1 gives [0, 0] before the first run (`T.default()`), the init [0, 0] at the run of frame 1 (storing [2, 3]), held, then [2, 3]: t0 + 10 t1 = 0 0 0 32.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  let t = prev~([x, x + 1.0]).when~(c)
  t[0] + t[1] * 10.0
}";
    same(&both(src, "f", 4, &[("c", &[0, 1, 0, 1])]), &[0.0, 0.0, 0.0, 32.0]);
    // The copy 0 always runs (5 1 2 3), the copy 1 at c = 0 1 0 1: 0 (never ran), 5 (the init, storing 2), 5, 2. The output is copy 0 + 10 copy 1: 5 51 52 23.
    let src = "flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  let ys = par~ i in 0 ..< 2 { prev~(x, 5.0).when~(c || i == 0) }
  ys[0] + ys[1] * 10.0
}";
    same(&both(src, "f", 4, &[("c", &[0, 1, 0, 1])]), &[5.0, 51.0, 52.0, 23.0]);
}

#[test]
fn a_chain_in_the_object_of_a_match_tilde_whose_binding_a_ring_gathers_ticks_once_a_frame() {
    // The second phase evaluates the object of the `match~` again for the ring (`eval_in_arms`): the chain gives its output of the frame and does not count the frame twice. k = cnt~().down~(4) > 0
    // holds at `sample / 4`, a `reset_if~` inside `when~(true)`: its R is on the grid of the runs, 1 a frame, so it puts the delay back at the frames 0 4 8 12: y = 0 1 2 3 | 0 5 6 7 | 0 9 10 11 | 0 13 14 15.
    // g2~(y).down~(2) reads the ring of the 2 frames before at the frames 0 2 4 ...: [0 0], [0 1], [2 3], [0 5], [6 7], [0 9], [10 11], [0 13]: 0 10 32 50 76 90 120 130, each for 2 frames.
    // A frame counted twice would put back at the frames 0 2 4 ... (30 at the frames 4 and 5).
    let want: Vec<f32> = [0.0, 10.0, 32.0, 50.0, 76.0, 90.0, 120.0, 130.0].iter().flat_map(|v| [*v; 2]).collect();
    for body in [
        "match~ prev~(x).reset_if~(s).when~(true) { v => g2~(v).down~(2) at sample }",
        "let y = prev~(x).reset_if~(s).when~(true)\n  g2~(y).down~(2) at sample",
    ] {
        let src = format!(
            "flow g2(v: F32 at (sample * 2)) -> F32 at sample {{ v[0] + v[1] * 10.0 }}
flow f(x: F32 at sample) -> F32 at sample {{
  let s = cnt~().down~(4) > 0.0
  {body}
}}"
        );
        same(&both(&src, "f", 16, &[]), &want);
    }
}
