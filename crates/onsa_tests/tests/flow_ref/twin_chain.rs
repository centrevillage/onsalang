//! Chains made at random that have no twin, and the forms that the break side found the evaluator wrong on (W7-10 (P)/t; the
//! `gen.py` of the break side of U3ae, `ST=1`; S-1207, S-1209, S-1226, S-1227). What is held is only that the evaluator and the interpreter
//! give the same outputs (`twin::run` evaluates every test and compares), where the other families hold a twin: so a form that both get wrong
//! in the same way is not found here (the twins of `twin_wrap.rs` are for that), but a form that one of them reads another way is.
//!
//! A seed makes a head (`tk`, `acc`, `slot`), a pattern of blocks (none, `.up~(N).down~(N)`, two of them, a block inside a block, a block and the
//! rate halved and doubled back), 0 to 2 modifiers (`when~`, `reset_if~`) in each place of it, and a condition for each at its clock W: what
//! `twin_when.rs` and `twin_reset.rs` make, and the time alone, `sample_tick() % 3 == 0` (also for a `when~`, where W is `sample` or slower: a
//! block that is stopped from outside reads the time that the grid of `sample / n` of the body that wrote the condition kept at its last tick, the same
//! as the condition with the `at` of W, §11.4, §11.3, §11.10, S-1230 (G); `twin_time.rs` holds the twins of that). The tests are those of `twin_when.rs`, with the
//! chain as `fa` and as `fb` (the same text): `render` on the grid of `ci` and `cb`, and `process` cut at other places with a `reset`.

use std::collections::BTreeSet;

use super::twin::Rng;
use super::twin_reset::{reset_cond, tags};
use super::twin_when::{Cond, HEADER, Head, Mod, Plan, SIGNATURE, cond_at, fits, form_at, program, w_of};

/// The time alone, as a condition of a `when~` or a `reset_if~`: read at W (§11.4, §11.10).
fn time() -> Cond {
    Cond::lit("sample_tick() % 3 == 0", "c_time")
}

/// 0 to 2 modifiers with no condition yet.
fn holes(rng: &mut Rng) -> Vec<Mod> {
    (0..rng.pick(&[0, 0, 1, 1, 2]))
        .map(|_| if rng.chance(50) { Mod::When(Cond::default()) } else { Mod::Reset(Cond::default()) })
        .collect()
}

/// The head and the modifiers of a seed, with the conditions filled in.
fn chain(rng: &mut Rng) -> (Head, Vec<Mod>) {
    loop {
        let head = rng.pick(&[Head::Tk, Head::Acc, Head::Slot, Head::Slot]);
        let n = rng.pick(&[2u32, 4]);
        let rates = match rng.below(7) {
            0 => vec![],
            1..=3 => vec![Mod::Up(n), Mod::Down(n)],
            4 => vec![Mod::Up(2), Mod::Down(2), Mod::Up(n), Mod::Down(n)],
            5 => vec![Mod::Up(2 * n), Mod::Up(2), Mod::Down(2), Mod::Down(2 * n)],
            _ => vec![Mod::Up(n), Mod::Down(n), Mod::Down(2), Mod::Up(2)],
        };
        let mut mods = holes(rng);
        for r in rates {
            mods.push(r);
            mods.extend(holes(rng));
        }
        if !fits(head, &mods) || mods.iter().all(|m| m.cond().is_none()) {
            continue;
        }
        for i in 0..mods.len() {
            let w = w_of(head, &mods, i);
            mods[i] = match &mods[i] {
                Mod::When(_) if w <= 0 && rng.chance(20) => Mod::When(time()),
                Mod::When(_) => Mod::When(cond_at(rng, w)),
                Mod::Reset(_) => Mod::Reset(reset_cond(rng, w)),
                m => m.clone(),
            };
        }
        return (head, mods);
    }
}

/// The program of a seed (the chain is both flows of `twin_when.rs`, and `rot` is not a mutant: there is no twin), and the forms it holds.
pub fn make(seed: u64, _rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let (head, mods) = chain(&mut rng);
    let plan = Plan { kind: "id", head, fa: mods.clone(), fb: mods, at: Vec::new() };
    let mut forms = tags(&plan);
    // The form of the break side's F2: a modifier with the time alone inside a block, and a `when~` outside the block.
    let timed = |i: usize| plan.fa[i].cond().is_some_and(|c| c.tags.contains("c_time"));
    let f2 = (0..plan.fa.len()).any(|i| {
        let after = (i + 1..plan.fa.len())
            .find(|&j| plan.fa[j].is_when() && plan.fa[i + 1..j].iter().any(|m| matches!(m, Mod::Down(_))));
        timed(i) && form_at(head, &plan.fa, i) == Some("in_block") && after.is_some()
    });
    forms.extend(f2.then_some("f2_time_in_block_stopped"));
    (program(&mut rng, &plan), forms)
}

/// A program of one flow `fx` that is `chain`, and the tests of `twin_when.rs` of a render (`render` is the signal) and of chunks
/// (`chunk` is the signal, `states` the spans of each state as `(to, cb, reset before it)`).
fn fixed_program(chain: &str, (render, chunk): (&str, &str), states: &[&[(usize, bool, bool)]]) -> String {
    let lets = if chain.contains("c2") { "let c2 = lb2~(c).down~(2)\n  " } else { "" };
    let mut t = format!("{HEADER}pub flow fx{SIGNATURE} -> F32 at sample {{\n  {lets}{chain}\n}}\n");
    t += &format!("test \"render\" {{\n  let cs: [Bool; 16] = [{render}]\n");
    for (k, (ci, cb)) in [(true, true), (true, false), (false, true)].iter().enumerate() {
        let (cfg, par) = (
            format!("fx.Config {{ ci: {ci}, cti: true, cfi: false }}"),
            format!("fx.Params {{ cb: {cb}, ct: true, cf: false }}"),
        );
        t += &format!("  let o{k} = fx.render({cfg}, {par}, cs, 8.0)\n  assert o{k}.out[0] == o{k}.out[0]\n");
    }
    t += &format!("}}\ntest \"chunks\" {{\n  let cs: [Bool; 16] = [{chunk}]\n");
    for (n, spans) in states.iter().enumerate() {
        t += &format!("  var s{n} = fx.init(fx.Config {{ ci: true, cti: true, cfi: false }}, 8.0)\n");
        let mut from = 0;
        for (m, &(to, cb, reset)) in spans.iter().enumerate() {
            t += &if reset { format!("  fx.reset(inout s{n})\n") } else { String::new() };
            t += &format!("  var o{n}_{m}: [F32; {0}] = [0.0; {0}]\n", to - from);
            let par = format!("fx.Params {{ cb: {cb}, ct: true, cf: false }}");
            t += &format!("  fx.process(inout s{n}, {par}, cs.slice({from}, {to}), inout o{n}_{m})\n");
            t += &if to > from { format!("  assert o{n}_{m}[0] == o{n}_{m}[0]\n") } else { String::new() };
            from = to;
        }
    }
    t + "}\n"
}

const T: &str = "true";
const F: &str = "false";

/// The forms that the break side found the evaluator wrong on or that its mutants of the evaluator needed (U3ae, `b_report.md`): the chain, and the
/// signals and the spans of its tests. A mutant of `cut` that always reads a ring as put back (M10) and one that writes a ring from the raw
/// input and not the input of the moved time (M16) were caught by a seed of the break side's sweeps only; F2 is a `sample_tick()` of a block
/// that a `when~` stops: the ticks of the part are at the frames 0 2 6 13 and the condition reads the time kept at the last tick of the grid of `sample / 2` of the body that
/// wrote it, 0 2 6 12 (S-1230 (G); before it, the time of the frame of the tick, 0 2 6 13). The chain is both flows, so what is held is that the evaluator and the
/// interpreter read it alike, and the values are in `tests/spec/flow_semantics/sample_tick_condition_grid_values.onsa`.
fn fixed_forms() -> [String; 4] {
    let (f2_cs, spans) = (
        [T, T, T, F, T, F, T, F, F, F, F, T, F, T, T, F].join(", "),
        [&[(16, true, false)][..], &[(5, true, false), (11, true, false), (16, true, true)]],
    );
    [
        fixed_program(
            "slot~(1.0).when~((c2 at sample) && c).reset_if~(c).up~(2).reset_if~(cb).down~(2).reset_if~((c2 at sample) && c).when~(cb)",
            (
                &[T, F, F, F, T, T, T, F, F, T, F, T, T, T, T, T].join(", "),
                &[T, T, T, T, F, F, F, F, F, F, T, F, T, T, T, F].join(", "),
            ),
            &[
                &[(6, true, false), (6, false, false), (16, true, false)],
                &[(7, true, false), (10, true, false), (16, true, false)],
            ],
        ),
        fixed_program(
            "slot~(1.0).reset_if~(c && cb).up~(4).down~(4).when~(cb).up~(2).down~(2).reset_if~(!c2)",
            (
                &[T, F, T, T, F, F, T, T, T, F, T, T, T, T, F, F].join(", "),
                &[T, T, T, F, F, F, F, F, F, F, F, F, F, T, T, T].join(", "),
            ),
            &[
                &[(2, false, false), (13, true, false), (16, true, true)],
                &[(7, true, false), (14, true, false), (16, true, true)],
            ],
        ),
        fixed_program("cnt~().up~(2).when~(sample_tick() % 3 == 0).down~(2).when~(c)", (&f2_cs, &f2_cs), &spans),
        fixed_program("cnt~().up~(2).reset_if~(sample_tick() % 3 == 0).down~(2).when~(c)", (&f2_cs, &f2_cs), &spans),
    ]
}

/// The program of the form that a seed picks (no mutant): the seeds 0 and 1 are the forms of the two mutants of the evaluator, 2 and 3 the F2
/// forms (a `when~` and a `reset_if~`).
pub fn make_fixed(seed: u64, _rot: bool) -> (String, BTreeSet<&'static str>) {
    let forms = fixed_forms();
    (forms[seed as usize % forms.len()].clone(), BTreeSet::from(["fixed"]))
}
