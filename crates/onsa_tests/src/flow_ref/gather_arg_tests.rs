//! The argument a chain of `.down~(N)` gathers, written in the call, with a delay in it (W7-16 U6a2/t2, §11.9, §11.3, §11.4): the stage a delay in the argument is of is the stage of its own clock, whatever clock the argument has
//! (`prev~(h) at sample` of `h` at `sample / 2` has the delay of `sample / 2`, so the value the ring gathers is the one the delay read before it saved at the tick, held), the same as when the argument is the name of a `let` that
//! binds it. The values are worked out by hand from the spec, in the comment of each test.
//!
//! `cnt~(p).down~(N)` counts `p` at its ticks (the frames 0, N, 2N, ...: p, 2p, 3p, ... with `p = 3`: 3, 6, 9, 12), `g2` reads the two elements of its input at `sample * 2` as `a[0] * 10 + a[1]` (the older first).

use super::conversion_tests::{p, ramp, rep, run};
use super::state_tests::{f32s, same};
use super::value::Value;

const SRC: &str = "
flow cnt(i0: F32 at block) -> F32 at sample {
  let n = i0 + prev~(^n)
  n
}
flow g2(a: F32 at (sample * 2)) -> F32 at sample { a[0] * 10.0 + a[1] }

// A delay lifted to `sample` by `at` in the call, and the same bound by a `let` (and not, at the stage of the chain, in a `let` at `sample`).
pub flow lifted(p: F32 at block) -> F32 at sample {
  let h = cnt~(p).down~(2)
  g2~(prev~(h) at sample).down~(2) at sample
}
pub flow lifted_let(p: F32 at block) -> F32 at sample {
  let h = cnt~(p).down~(2)
  let a = prev~(h) at sample
  g2~(a).down~(2) at sample
}
pub flow lifted_bound(p: F32 at block) -> F32 at sample {
  let h = cnt~(p).down~(2)
  let r = g2~(prev~(h) at sample).down~(2)
  r at sample
}
pub flow lifted_in_a_let(p: F32 at block) -> F32 at sample {
  let h = cnt~(p).down~(2)
  let r = g2~(prev~(h) at sample).down~(2) at sample
  r + 1.0
}
// A delay of `sample` in the argument, which has the clock of the delay.
pub flow plain(x: F32 at sample) -> F32 at sample { g2~(prev~(x)).down~(2) at sample }

// The argument is at `sample / 2` under a `.down~(4)` (q = 1 - 2 = -1): the delay of `sample / 4` lifted by `at`, the same in a `let`, and a delay of `sample / 2`.
pub flow half(p: F32 at block) -> F32 at sample {
  let h = cnt~(p).down~(4)
  g2~(prev~(h) at (sample / 2)).down~(4) at sample
}
pub flow half_let(p: F32 at block) -> F32 at sample {
  let h = cnt~(p).down~(4)
  let a = prev~(h) at (sample / 2)
  g2~(a).down~(4) at sample
}
pub flow half_plain(p: F32 at block) -> F32 at sample {
  let y = cnt~(p).down~(2)
  g2~(prev~(y)).down~(4) at sample
}

// The chain is in a `par~`: each replica has its own ring and its own delay.
pub flow in_par(p: F32 at block) -> [F32; 2] at sample {
  let h = cnt~(p).down~(2)
  par~ i in 0 ..< 2 { g2~((prev~(h) at sample) + [0.0, 1.0][i]).down~(2) at sample }
}

// The delay is in a branch of an `if~` (a delay is not in an `if`, E0811) that the `block` input decides.
pub flow chosen(p: F32 at block, s: F32 at block) -> F32 at sample {
  let h = cnt~(p).down~(2)
  g2~(if~ s > 0.5 { prev~(h) at sample } else { 7.0 }).down~(2) at sample
}
";

fn one(name: &'static str, frames: usize) -> Vec<f32> {
    f32s(&run(SRC, name, vec![(p(3.0), frames)], &[], &[]))
}

#[test]
fn a_delay_lifted_to_sample_in_the_argument_a_chain_gathers_is_the_delay_of_the_slower_clock() {
    // §11.9, §11.3: `h` is of `sample / 2`, its ticks are the frames 0, 2, 4, 6 and it counts p = 3: 3, 6, 9, 12. `prev~(h)` is the delay of `h`, of its clock: at the ticks it reads the value saved at the tick before (0, 3, 6, 9),
    // and `at sample` holds it, so the argument at `sample` is 0 0 | 3 3 | 6 6 | 9 9 (frame by frame). The tick c of `.down~(2)` gathers the frames c - 2 and c - 1 (§11.9, position 0 has the defaults): tick 0 gets [0, 0], tick 2
    // [arg 0, arg 1] = [0, 0], tick 4 [arg 2, arg 3] = [3, 3], tick 6 [arg 4, arg 5] = [6, 6]. `g2` gives a[0] * 10 + a[1]: 0, 0, 33, 66, held two frames each: 0 0 0 0 33 33 66 66. The `let a = ...` of the same argument, and a call
    // of the same chain in a `let` that is `at sample` (+ 1), give the same. (The value that went wrong was 0 0 3 3 36 36 69 69: the delay saved at each `sample` frame, a delay of `sample`.)
    let want = [0.0, 0.0, 0.0, 0.0, 33.0, 33.0, 66.0, 66.0];
    same(&one("lifted", 8), &want);
    same(&one("lifted_let", 8), &want);
    same(&one("lifted_bound", 8), &want);
    let plus: Vec<f32> = want.iter().map(|x| x + 1.0).collect();
    same(&one("lifted_in_a_let", 8), &plus);
}

#[test]
fn the_same_calls_cut_anywhere_give_the_same_values_as_the_one_call() {
    // §13.4: the calls of `process` cut at any frame give what one call gives, with the delay in the argument too (a tick is on a frame that is a multiple of 2 whatever the cut).
    let want = [0.0, 0.0, 0.0, 0.0, 33.0, 33.0, 66.0, 66.0];
    for sizes in [&[8][..], &[3, 5], &[1; 8], &[2, 0, 6], &[7, 1]] {
        let calls = sizes.iter().map(|n| (p(3.0), *n)).collect();
        same(&f32s(&run(SRC, "lifted", calls, &[], &[])), &want);
    }
}

#[test]
fn a_delay_of_sample_in_the_argument_has_the_clock_of_the_argument() {
    // §11.4: `prev~(x)` of `x` at `sample` (x[c] = c + 1) is the x of the frame before: 0 1 2 3 4 5 6 7. The tick c gathers [prev c - 2, prev c - 1]: tick 2 gets [0, 1] (1), tick 4 [2, 3] (23), tick 6 [4, 5] (45), tick 0 the defaults (0),
    // held two frames each: 0 0 1 1 23 23 45 45.
    let got = f32s(&run(SRC, "plain", vec![(vec![], 8)], &[("x", ramp(8))], &[]));
    same(&got, &[0.0, 0.0, 1.0, 1.0, 23.0, 23.0, 45.0, 45.0]);
}

#[test]
fn a_delay_in_an_argument_slower_than_sample_is_made_at_the_tick_of_the_argument_or_of_its_own_clock() {
    // §11.9 (q = 1 - 2 = -1, the ring takes one element at each tick of `sample / 2`, the frames 0, 2, 4, ...), §11.3. `half`: `h` is of `sample / 4` (the frames 0, 4, 8, 12: 3, 6, 9, 12), `prev~(h)` of its clock: 0, 3, 6, 9 at those frames,
    // `at (sample / 2)` takes it at the frames 0, 2, 4, 6, 8, ...: 0 0 3 3 6 6 9 9. The tick c (a multiple of 4) gathers the elements of the ticks c - 4 and c - 2: tick 0 [0, 0] (0), tick 4 [arg 0, arg 2] = [0, 0] (0), tick 8
    // [arg 4, arg 6] = [3, 3] (33), tick 12 [arg 8, arg 10] = [6, 6] (66), held four frames each: 0 x 8, 33 x 4, 66 x 4. (Saved at each tick of `sample / 2` the delay would give arg 2 = 3: tick 4 gets [0, 3] = 3.)
    // `half_let` binds the argument first and gives the same. `half_plain`: `y` of `sample / 2` counts 3, 6, 9, 12 at the frames 0, 2, 4, 6, `prev~(y)` is its own delay of the clock of the argument: 0, 3, 6, 9 at those frames; tick 4
    // gathers [0, 3] (3), tick 8 [6, 9] (69), tick 0 the defaults (0): 0 x 4, 3 x 4, 69 x 4.
    let want = rep(&[(0.0, 8), (33.0, 4), (66.0, 4)]);
    same(&one("half", 16), &want);
    same(&one("half_let", 16), &want);
    same(&one("half_plain", 12), &rep(&[(0.0, 4), (3.0, 4), (69.0, 4)]));
}

#[test]
fn a_delay_in_a_branch_of_an_if_tilde_in_the_argument_is_the_delay_of_its_clock() {
    // §11.3, §11.5: an `if~` evaluates every branch, so the delay is made at its own stage whichever branch is taken, and the choice is of `block`. s = 1: the branch with the delay, 0 0 0 0 33 33 66 66 as without the `if~`.
    // s = 0: the other one, 7 at each frame, so each tick gathers [7, 7] (position 0 the defaults): tick 0 gives 0, then 77 at the ticks 2, 4, 6: 0 0 77 77 77 77 77 77.
    let at = |s: f32| {
        let params: Vec<(&'static str, Value)> = vec![("p", Value::F32(3.0)), ("s", Value::F32(s))];
        f32s(&run(SRC, "chosen", vec![(params, 8)], &[], &[]))
    };
    same(&at(1.0), &[0.0, 0.0, 0.0, 0.0, 33.0, 33.0, 66.0, 66.0]);
    same(&at(0.0), &[0.0, 0.0, 77.0, 77.0, 77.0, 77.0, 77.0, 77.0]);
}

#[test]
fn each_replica_of_a_par_has_its_own_ring_and_its_own_delay() {
    // §11.5, §11.9: replica i adds `[0.0, 1.0][i]` to the delay lifted by `at` (0 0 | 3 3 | 6 6 | 9 9 as above). Replica 0 gathers what `lifted` does: 0 0 0 0 33 33 66 66. Replica 1: tick 0 has the defaults (0), tick 2 gathers
    // [0 + 1, 0 + 1] (11), tick 4 [3 + 1, 3 + 1] (44), tick 6 [6 + 1, 6 + 1] (77), held two frames each: 0 0 11 11 44 44 77 77.
    let got = run(SRC, "in_par", vec![(p(3.0), 8)], &[], &[]);
    let column = |i: usize| -> Vec<f32> {
        let of = |v: &Value| match v {
            Value::Array(vs) => f32s(&vs[i..=i])[0],
            other => panic!("not an array: {other:?}"),
        };
        got.iter().map(of).collect()
    };
    same(&column(0), &[0.0, 0.0, 0.0, 0.0, 33.0, 33.0, 66.0, 66.0]);
    same(&column(1), &[0.0, 0.0, 11.0, 11.0, 44.0, 44.0, 77.0, 77.0]);
}
