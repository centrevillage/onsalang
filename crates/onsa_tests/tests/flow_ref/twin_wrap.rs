//! Modifiers inside a block and the same in a named flow (W7-10 U3ae/t; S-1207, S-1209, S-1214, S-1220, S-1226, S-1227). A seed makes
//! one program of two flows `fa` and `fb` that §11.10 and §11.9 say give the same outputs: `fa` writes the block as it is,
//! `head.when~(a).reset_if~(b).up~(N).down~(N)`, and `fb` calls a named flow `w` whose body is the part inside the block, with each
//! condition a parameter of the kind of the value it names: `w~(xv, a, b).up~(N).down~(N)`. A modifier inside a block reads the sum of
//! the ratios outside it (R1), so a block whose ratios cancel (`.up~(N).down~(N)`, the only blocks made) reads at the clock of the
//! flow that holds it, as the body of `w` does; a signal is gathered with the inputs of the head and a value of a `block` kind is the
//! one of the call that runs the part (R6), both as a parameter of `w` is. Both flows are run on the grid and the `process` cut of
//! `twin_when.rs`.
//!
//! The chain is a head (`slot` with a slow stage, `tk`, `acc`, `lp` with an input), 0 to 3 of `when~` and `reset_if~` and the block
//! (`N` of 2 or 4), then one of a block inside it (`X.when~(a).up~(N).down~(N).reset_if~(b).up~(2).down~(2)`: the part `w` is all but
//! the last block) and 0 or 1 of them outside. The condition is a signal, `!c`, a `block` or `init` value, a signal slower than
//! the clock (`c2`, `c4`), or a `block` value `at sample` or `at (sample / 2)` (a value of a parameter kind with an `at` is read
//! when the run is made, and not gathered, §11.3; 1b of U3a). No literal and no condition of the time: a literal is not gathered
//! and a signal is (R2, R3), so the twin of `when~(true)` is not a parameter of `w`.

use std::collections::BTreeSet;

use super::twin::Rng;
use super::twin_when::{Cond, HEADER, Head, Mod, SIGNATURE, lets, tests};

/// The heads a seed picks from: a stage at `sample / 2` that writes a field the stage at `sample` reads (`slot`), the time, a
/// running sum, a head with an input (`lp`).
const HEADS: [Head; 6] = [Head::Slot, Head::Slot, Head::Tk, Head::Acc, Head::Acc, Head::Lp];

/// The condition of a modifier inside the block (a `when~` reads a slower value with no `at`: E0815, §11.10; a `reset_if~` has the
/// clock of the `at`).
fn leaf(rng: &mut Rng, when: bool) -> Cond {
    match rng.below(10) {
        0 | 1 => Cond::signal_n(1),
        2 => Cond::signal_n(1).not(),
        3 | 4 => Cond::lit("cb", "c_block"),
        5 => Cond::lit("ci", "c_init"),
        6 => Cond::signal_n(2 << rng.below(2)),
        7 => Cond::lit("cb at sample", "c_at_sample"),
        8 if !when => Cond::lit("cb at (sample / 2)", "c_at_slow"),
        _ => Cond::lit("cb", "c_block").not(),
    }
}

/// A `when~` or a `reset_if~` with a condition.
fn modifier(rng: &mut Rng) -> Mod {
    let when = rng.chance(50);
    let c = leaf(rng, when);
    if when { Mod::When(c) } else { Mod::Reset(c) }
}

/// What a seed makes: the head, the modifiers before the block, its ratio (0: no block, only with `p`), the modifiers of a block
/// inside it (the block that holds them is `.up~(2).down~(2)`, if there is one), and the modifiers after it.
pub struct Shape {
    pub head: Head,
    pub inside: Vec<Mod>,
    pub n: u32,
    pub nest: Option<Vec<Mod>>,
    pub outside: Vec<Mod>,
}

impl Shape {
    /// The chain of `fa`, and where the body of `w` ends in it (everything before the last block).
    fn chain(&self) -> (Vec<Mod>, usize) {
        let block = |n| [Mod::Up(n), Mod::Down(n)];
        let mut all = [self.inside.clone(), if self.n > 0 { block(self.n).to_vec() } else { Vec::new() }].concat();
        let mut split = self.inside.len();
        if let Some(nest) = &self.nest {
            all.extend(nest.iter().cloned());
            split = all.len();
            all.extend(block(2));
        }
        all.extend(self.outside.iter().cloned());
        (all, split)
    }
}

/// A shape from a seed's generator. With `p` (S-1228: a `reset_if~` goes back before the stages that a `when~` to its left moves to W,
/// so a chain and a named flow that wraps part of it give the same values) the two shapes that the old reading did not give the same
/// values are made: a part with a `when~` and a `reset_if~` outside it that ticks every 2 frames under a block of 4 (the block of `w` is slower than
/// the reset: it is written first and the reset takes it back, as with no `when~`), and no block at all (`w~(cb).reset_if~(r)`).
pub fn shape(rng: &mut Rng, p: bool) -> Shape {
    loop {
        let many = |rng: &mut Rng, n: usize| (0..rng.below(n)).map(|_| modifier(rng)).collect::<Vec<_>>();
        let head = rng.pick(&HEADS);
        let n = if p && rng.chance(25) { 0 } else { rng.pick(&[2, 2, 4]) };
        let inside = many(rng, 4);
        let nest = (n > 0 && rng.chance(25)).then(|| many(rng, 3));
        let mut outside = many(rng, 2);
        // Not the twin (a gap candidate of U3ae/t): a signal slower than the clock in `w` and a modifier outside it. `w~(c4).reset_if~(r)`
        // keeps what the head of the chain holds of its slower input, `x.when~(c4).reset_if~(r)` puts back the held condition.
        let slow = |m: &Mod| m.cond().is_some_and(|c| c.tags.contains("c_sig_slow"));
        if inside.iter().chain(nest.iter().flatten()).any(slow) {
            outside.clear();
        }
        // Not the twin either: a block of 4 in `w`, the outer block of 2 and a `reset_if~` outside it that ticks every 2 frames
        // (the part is put back before its 4 runs are gathered: `fa` never gathers them, `fb` does).
        if !p && nest.is_some() && n == 4 {
            outside
                .retain(|m| !m.cond().is_some_and(|c| c.tags.contains("c_sig_slow") || c.tags.contains("c_at_slow")));
        }
        if inside.len() + nest.as_ref().map_or(0, Vec::len) > 0 {
            return Shape { head, inside, n, nest, outside };
        }
    }
}

/// How a condition goes through a parameter `p` of `w`: the type, the argument (the value as the caller writes it), and the
/// condition that `w` reads (`p` with the `at` of the condition).
fn pass(c: &Cond, p: &str) -> (String, String, String) {
    let (value, at) = match c.text.split_once(" at ") {
        Some((v, a)) => (v, format!(" at {a}")),
        None => (c.text.as_str(), String::new()),
    };
    let clock = match value.trim_start_matches('!') {
        "c" => "sample".to_string(),
        "cb" => "block".to_string(),
        "ci" => "init".to_string(),
        slow => format!("(sample / {})", &slow[1..]),
    };
    (format!("Bool at {clock}"), value.to_string(), format!("{p}{at}"))
}

/// The program of a shape: the flow `w`, `fa` (the block written as it is), `fb` (the call of `w` and the block outside it), and
/// the tests. With `rot` the first condition `fb` passes is the opposite.
pub fn program(rng: &mut Rng, s: &Shape, rot: bool) -> String {
    let (all, split) = s.chain();
    let (mut decls, mut args) = (Vec::new(), Vec::new());
    if s.head == Head::Lp {
        (decls, args) = (vec!["xv: F32 at sample".to_string()], vec!["xv".to_string()]);
    }
    let first = decls.len();
    let body: Vec<Mod> = all[..split]
        .iter()
        .map(|m| {
            let Some(c) = m.cond() else { return m.clone() };
            let p = format!("p{}", decls.len());
            let (ty, arg, read) = pass(c, &p);
            decls.push(format!("{p}: {ty}"));
            args.push(arg);
            if m.is_when() { Mod::When(Cond::lit(&read, "")) } else { Mod::Reset(Cond::lit(&read, "")) }
        })
        .collect();
    if let (true, Some(a)) = (rot, args.get_mut(first)) {
        *a = a.strip_prefix('!').map_or_else(|| format!("!{a}"), str::to_string);
    }
    let text = |mods: &[Mod]| mods.iter().map(Mod::text).collect::<String>();
    let head = s.head.text().0;
    let setup = lets(s.head, &all);
    let flow =
        |name: &str, value: String| format!("pub flow {name}{SIGNATURE} -> F32 at sample {{\n  {setup}{value}\n}}\n");
    let w = format!("pub flow w({}) -> F32 at sample {{\n  {head}{}\n}}\n", decls.join(", "), text(&body));
    let fa = flow("fa", format!("{head}{}", text(&all)));
    let fb = flow("fb", format!("w~({}){}", args.join(", "), text(&all[split..])));
    format!("{HEADER}{w}{fa}{fb}{}", tests(rng))
}

/// The forms of a shape that the seeds of the gate have to hold.
pub fn tags(s: &Shape) -> BTreeSet<&'static str> {
    let mut tags = BTreeSet::from([s.head.text().1, ["n_0", "", "n_2", "", "n_4"][s.n as usize]]);
    let (all, split) = s.chain();
    let (inside, outside) = (&all[..split], &all[split..]);
    tags.insert(
        ["in_0", "in_1", "in_2", "in_3", "in_4", "in_5", "in_6"][inside.iter().filter_map(Mod::cond).count().min(6)],
    );
    tags.extend(s.nest.is_some().then_some("nest"));
    let out = outside.iter().any(|m| m.cond().is_some());
    tags.extend(out.then_some("out_mod"));
    // The head with a block inside a block and with a modifier outside the block.
    let by_head = |slot, tk, acc, lp| match s.head {
        Head::Slot => slot,
        Head::Tk => tk,
        Head::Lp => lp,
        _ => acc,
    };
    tags.extend(s.nest.is_some().then(|| by_head("nest_slot", "nest_tk", "nest_acc", "nest_lp")));
    tags.extend(out.then(|| by_head("out_slot", "out_tk", "out_acc", "out_lp")));
    tags.extend((s.nest.is_some() && out).then_some("nest_out"));
    tags.extend((s.nest.is_some() && s.n == 4).then_some("nest_n4"));
    for m in inside.iter().filter(|m| m.cond().is_some()) {
        tags.insert(if m.is_when() { "in_when" } else { "in_reset" });
        tags.extend(m.cond().iter().flat_map(|c| c.tags.iter().copied()));
    }
    let order = |a: bool, b: bool| {
        inside
            .windows(2)
            .any(|w| w[0].is_when() == a && w[1].is_when() == b && w[0].cond().is_some() && w[1].cond().is_some())
    };
    tags.extend(order(true, false).then_some("when_reset"));
    tags.extend(order(false, true).then_some("reset_when"));
    tags.extend(order(true, true).then_some("when_when"));
    tags.extend(order(false, false).then_some("reset_reset"));
    // The forms of S-1228: a `when~` in `w` and a `reset_if~` outside it (the reset is before the stages that the `when~` moves), and the one that ticks
    // more often than the block of 4 in `w`.
    let reset_out = outside.iter().any(|m| matches!(m, Mod::Reset(_)));
    tags.extend((reset_out && inside.iter().any(Mod::is_when)).then_some("p_reset_over_when"));
    let often = |m: &Mod| matches!(m, Mod::Reset(c) if c.tags.contains("c_sig_slow") || c.tags.contains("c_at_slow"));
    tags.extend((s.nest.is_some() && s.n == 4 && outside.iter().any(often)).then_some("p_n4_reset_often"));
    tags
}

/// The program of a seed (with `rot`, the mutant of the twin), and the forms it holds.
pub fn make(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let s = shape(&mut rng, false);
    (program(&mut rng, &s, rot), tags(&s))
}

/// The program of a seed with the shapes that S-1228 (P) makes twins (`shape` with `p`), and the forms it holds.
pub fn make_p(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let s = shape(&mut rng, true);
    (program(&mut rng, &s, rot), tags(&s))
}
