//! A `sample_tick()` alone in the condition of a modifier, and its twins (W7-10 S1230/t; S-1230 (G), S-1209, S-1226, S-1227, S-1228). §11.4 and §11.3: a condition that reads
//! no tick value but `sample_tick()` (alone, or mixed with constants, `init` and `block` values) is the same value as the one with the `at` of the clock W that reads it
//! (`W` is `sample / n`: the time that the grid of `sample / n` of the body that wrote the condition kept at its last tick), whichever frame the tick of the part is at, so an
//! outer `when~` that moves the ticks of the part off that grid does not change it; and the same as a port of the clock W of a flow that holds the part (the argument is
//! written in the caller, as a head argument is). A seed makes a head (`tk`, `acc`, `slot`), a block around the modifier (`x.up~(n).when~(K).down~(n)`, with a block
//! before it, a block after it, an `.up~(2)` between it and the `.down~(4)` so that W is faster than the boundary and the condition is gathered, or no `.up~` so that the part
//! is slower than the body) and 0 to 2 modifiers outside it (`when~` and `reset_if~` with the conditions of `twin_when.rs` and `twin_reset.rs`), and in the family `at` one
//! more modifier inside it:
//!
//! - `time_at` (`make_at`): `fa` writes `K` (`sample_tick() % 3 == 0`, or with `sample_rate() > 4.0 &&` or `cb &&` in front) and `fb` writes `(K) at (sample / n)`;
//! - `time_port` (`make_port`): `fa` writes the chain, `fb` calls a flow `gp` that holds the part up to the end of the block, with the condition as its port at `sample / n`
//!   (`gp~(K).when~(c)`); no modifier inside the block but the one of the time (any other would need a port of its own), and no template whose part is slower than the body (the
//!   flow that holds it gives a value of `sample`, and the modifier outside it would read it at another clock).
//!
//! The tests are those of `twin_when.rs` (a `render` on the grid of `ci` and `cb`, and `process` cut at other places, with a `reset`, which a `cb` that changes between the
//! calls goes through), and what the plan gives on the evaluator is compared with the interpreter by `twin::run`.

use std::collections::BTreeSet;

use super::twin::Rng;
use super::twin_reset::reset_cond;
use super::twin_when::{
    Cond, HEADER, Head, Mod, Plan, SIGNATURE, cond_at, fits, flow_body, lets, net, program, tests, w_of,
};

/// The time alone, in the three writings a seed picks from: bare, mixed with an `init` value (`sample_rate()` is 8 in the tests), mixed with a `block` value.
fn time_text(rng: &mut Rng) -> (&'static str, &'static str) {
    match rng.below(10) {
        0..=5 => ("sample_tick() % 3 == 0", "t_plain"),
        6 | 7 => ("sample_rate() > 4.0 && sample_tick() % 3 == 0", "t_init"),
        _ => ("cb && sample_tick() % 3 == 0", "t_block"),
    }
}

/// What a seed makes: the chain of `fa`, the place of the modifier with the time, how many modifiers hold the part (up to the end of its block), the period `n` of its W, the
/// condition (the text and its tag), and the tags of the shape.
pub struct Shape {
    head: Head,
    all: Vec<Mod>,
    ti: usize,
    core: usize,
    n: u32,
    text: &'static str,
    tags: BTreeSet<&'static str>,
}

/// A shape from a seed's generator. With `port` the part holds only the modifier of the time and its net rate is 1.
pub fn shape(rng: &mut Rng, port: bool) -> Shape {
    loop {
        let head = rng.pick(&[Head::Tk, Head::Acc, Head::Slot, Head::Slot]);
        let n = rng.pick(&[2u32, 4]);
        let (text, ttag) = time_text(rng);
        let when = rng.chance(60);
        let hole = |when: bool| if when { Mod::When(Cond::default()) } else { Mod::Reset(Cond::default()) };
        let block = |pre: Vec<Mod>, post: Vec<Mod>| (pre, post, Vec::new());
        let template = rng.below(if port { 4 } else { 5 });
        let (mut pre, mut post, after) = match template {
            0 => block(vec![Mod::Up(n)], vec![Mod::Down(n)]),
            1 => block(vec![Mod::Up(2), Mod::Down(2), Mod::Up(n)], vec![Mod::Down(n)]),
            2 => (vec![Mod::Up(n)], vec![Mod::Down(n)], vec![Mod::Up(2), Mod::Down(2)]),
            3 => block(vec![Mod::Up(2)], vec![Mod::Up(2), Mod::Down(4)]),
            _ => block(Vec::new(), vec![Mod::Down(n)]),
        };
        let extra = !port && rng.chance(40);
        if extra && rng.chance(50) {
            pre.push(hole(rng.chance(50)));
        } else if extra {
            post.insert(0, hole(rng.chance(50)));
        }
        let (ti, core) = (pre.len(), pre.len() + 1 + post.len());
        let time = Mod::When(Cond::lit(text, ttag));
        let time = if when { time } else { Mod::Reset(Cond::lit(text, ttag)) };
        let mut all = [pre, vec![time], post, after].concat();
        all.extend((0..rng.below(3)).map(|_| hole(rng.chance(50))));
        if !fits(head, &all) || (port && net(head, &all[..core]) != 0) {
            continue;
        }
        let w = w_of(head, &all, ti);
        if w >= 0 {
            continue;
        }
        for i in (0..all.len()).filter(|&i| i != ti) {
            let w = w_of(head, &all, i);
            all[i] = match &all[i] {
                Mod::When(c) if c.text.is_empty() => Mod::When(cond_at(rng, w)),
                Mod::Reset(c) if c.text.is_empty() => Mod::Reset(reset_cond(rng, w)),
                m => m.clone(),
            };
        }
        let outside = all[core..].iter().filter(|m| m.cond().is_some());
        let mut tags =
            BTreeSet::from([head.text().1, ttag, ["s_block", "s_before", "s_after", "s_ring", "s_down"][template]]);
        tags.insert(if when { "k_when" } else { "k_reset" });
        tags.insert(if n == 2 { "n_2" } else { "n_4" });
        tags.extend(outside.clone().any(|m| m.is_when()).then_some("out_when"));
        tags.extend(outside.clone().any(|m| !m.is_when()).then_some("out_reset"));
        tags.extend(all[..core].iter().enumerate().any(|(i, m)| i != ti && m.cond().is_some()).then_some("inside"));
        return Shape { head, all, ti, core, n: 1 << -w, text, tags };
    }
}

/// The text of a modifier of a chain.
fn chain_text(mods: &[Mod]) -> String {
    mods.iter().map(Mod::text).collect()
}

/// `(K) at (sample / n)`, with the mutant `% 3 == 1` when `rot`.
fn text_at(s: &Shape, rot: bool) -> String {
    let k = if rot { s.text.replace("% 3 == 0", "% 3 == 1") } else { s.text.to_string() };
    format!("({k}) at (sample / {})", s.n)
}

/// The modifier of the time with another condition.
fn with(m: &Mod, text: &str) -> Mod {
    match m {
        Mod::When(_) => Mod::When(Cond::lit(text, "")),
        _ => Mod::Reset(Cond::lit(text, "")),
    }
}

/// The program of a seed of the family `time_at` (with `rot`, `fb` has the mutant), and the forms it holds.
pub fn make_at(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let s = shape(&mut rng, false);
    let mut fb = s.all.clone();
    fb[s.ti] = with(&s.all[s.ti], &text_at(&s, rot));
    let plan = Plan { kind: "time", head: s.head, fa: s.all.clone(), fb, at: vec![s.ti] };
    (program(&mut rng, &plan), s.tags)
}

/// The program of a seed of the family `time_port`, and the forms it holds.
pub fn make_port(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let s = shape(&mut rng, true);
    let mut core = s.all[..s.core].to_vec();
    core[s.ti] = with(&core[s.ti], "k");
    let head = s.head.text().0;
    let gp =
        format!("pub flow gp(k: Bool at (sample / {})) -> F32 at sample {{\n  {head}{}\n}}\n", s.n, chain_text(&core));
    let fa = format!("pub flow fa{SIGNATURE} -> F32 at sample {{\n  {}\n}}\n", flow_body(s.head, &s.all));
    let arg = if rot { s.text.replace("% 3 == 0", "% 3 == 1") } else { s.text.to_string() };
    let rest = &s.all[s.core..];
    let fb = format!(
        "pub flow fb{SIGNATURE} -> F32 at sample {{\n  {}gp~({arg}){}\n}}\n",
        lets(s.head, rest),
        chain_text(rest)
    );
    (format!("{HEADER}{gp}{fa}{fb}{}", tests(&mut rng)), s.tags)
}
