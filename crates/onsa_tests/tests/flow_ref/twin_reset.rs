//! Chains of `reset_if~` made from a seed, with their twins (W7-10 U2e/t; S-1209, S-1217, S-1218, S-1220, S-1221, S-1225). The
//! program is the one of `twin_when.rs` (`fa` and `fb`, the tests of the grid, the `process` cut at other places, a `reset`), and
//! the chains are a head (one with a slow stage that writes a field a fast stage reads, `slot`; one whose input is slower than
//! the chain, `sl`; one with a `when~` inside whose part has a slow input, `outer2`) and 1 to 5 modifiers of `.down~`, `.up~`, `.when~` and `.reset_if~`. The twins are what §11.10 says is equal:
//!
//! - `rid`: `X.reset_if~(false)` and `X.when~(true)` put in at any place of a chain that has `reset_if~` of its own (`fa` has them
//!   in, `fb` has not; inside or outside a `reset_if~`, a `.up~`, a `.when~`), but a `when~(true)` only where S-1228 keeps it a twin
//!   (`when_twin_ok`: with a `reset_if~` outside it, only for a part that has no stage slower than the reset's tick);
//! - `slowc`: a condition slower than W is held at W, so `.when~(k > 1.5)` (`k` counts the ticks of a slower grid) and
//!   `.when~(sample_tick() >= N)` (true from the tick where `k` is 2) are the same (not inside a block, where a `sample_tick()`
//!   is gathered with the inputs and `k` is read at its own tick);
//! - `atid`: a value of the kind `block` or `init` with the `at` of the clock W (`sample`) put on it, in a `when~` or a
//!   `reset_if~`, is the value (§11.3: the stage of a value of a parameter kind does not change with an `at`), also inside a block;
//! - `rmerge`: `x.reset_if~(a).reset_if~(b)` and `x.reset_if~(a || b)` (the same clock W: the state is given back at the same
//!   ticks, and a state given back is given back once; this one follows from §11.10's composition and is not said in a line).
//!
//! The condition of a `reset_if~` is a value at W, a `block` or `init` value, a signal slower than W, `cb at (sample / N)`, or the
//! time alone (`sample_tick() == K`, `sample_tick() >= K`, read at W).
//! What the plan gives on the evaluator is compared with the interpreter by `twin::run`.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use super::twin::Rng;
use super::twin_when::{Cond, HEADER, Head, Mod, Plan, SIGNATURE, always_true, cond_at, fits, flow_body, in_range};
use super::twin_when::{at_pair, form_at, kinds_apart, program, rate, tags_of, w_of};

/// The heads a seed picks from: a third have a slow stage that writes a field (`slot`), a sixth a slow input (`sl`).
const HEADS: [Head; 15] = [
    Head::Slot,
    Head::Slot,
    Head::Slot,
    Head::Slot,
    Head::Sl,
    Head::Sl,
    Head::SlTk,
    Head::Tk,
    Head::Acc,
    Head::Lp,
    Head::Dws,
    Head::Mk2,
    Head::Mk4,
    Head::Outer,
    Head::Outer,
];

/// Whether `X.when~(true)` put in before `chain[p]` is the twin of the chain without it (§11.10: "その `when~` の外（右）の `reset_if~` は
/// その前に戻し、中の遅い刻みが動く位置では戻した後に書く", S-1228). A `when~` moves the stages of the part to its left that are slower
/// than its W to W's stage (§11.9), and a `reset_if~` outside it goes back before that stage, whereas with no `when~` the stage of
/// the part writes first and the reset takes it back: so the two chains differ where the reset's tick is a tick of such a stage
/// (a slow stage of the head `slot`, a slow input, a copy of a slower condition, a burst dealt, the ring and the array of a block).
/// With a `reset_if~` outside it the `when~(true)` is put in only where the part to its left has none: the head `tk` or `acc` with
/// `.down~` alone to its left. With no `reset_if~` outside it, anywhere.
fn when_twin_ok(head: Head, chain: &[Mod], p: usize) -> bool {
    let reset_outside = chain[p..].iter().any(|m| matches!(m, Mod::Reset(_)));
    let fast = matches!(head, Head::Tk | Head::Acc) && chain[..p].iter().all(|m| matches!(m, Mod::Down(_)));
    !reset_outside || fast
}

/// A condition that never holds, read at W (`w`): a literal, a `block` or `init` input that is false, `c && cf`, or `cf` at a
/// clock that is not faster than W.
fn never(rng: &mut Rng, w: i32) -> Cond {
    match rng.below(if w <= 0 { 6 } else { 5 }) {
        0 => Cond::lit("false", "f_lit"),
        1 => Cond::lit("cf", "f_block"),
        2 => Cond::lit("cfi", "f_init"),
        3 => Cond::lit("cf && cfi", "f_both"),
        4 => at_cond(rng, w, "cf", "f_at"),
        _ => Cond::signal(w).join("&&", &Cond::lit("cf", "f_block")),
    }
}

/// `<name> at (sample / N)` with `sample / N` not faster than W.
fn at_cond(rng: &mut Rng, w: i32, name: &str, tag: &'static str) -> Cond {
    let lo = (-w).max(1) as usize;
    Cond::lit(&format!("{name} at (sample / {})", 1u32 << (lo + rng.below(4 - lo))), tag)
}

/// `sample_tick() == K` or `sample_tick() >= K` alone: a condition of a parameter kind, read at W (§11.4, §11.10). The ticks of W
/// are the multiples of its period; one `K` in four is off them (where `==` never holds).
fn tick_cond(rng: &mut Rng, w: i32) -> Cond {
    let period = 1usize << (-w).max(0);
    let k = period * (1 + rng.below(6)) + usize::from(rng.chance(25));
    let (op, tag) = if rng.chance(50) { ("==", "c_tick_eq") } else { (">=", "c_tick_ge") };
    let clock = if w < 0 { "c_tick_slow" } else { "c_tick_fast" };
    Cond { text: format!("sample_tick() {op} {k}"), tags: BTreeSet::from(["c_tick", tag, clock]), ..Cond::default() }
}

/// The condition of a `reset_if~` read at W: what a `when~` has, a `block` value `at` a slower clock, a signal slower than W,
/// the time alone (`sample_tick()` against a number, where W is `sample` or slower).
pub fn reset_cond(rng: &mut Rng, w: i32) -> Cond {
    let wn = 1u32 << (-w).max(0);
    match rng.below(10) {
        0 | 1 => at_cond(rng, w, "cb", "c_at"),
        4 | 5 if w <= 0 => tick_cond(rng, w),
        2 | 3 if wn < 8 => {
            let slower = Cond::signal_n(wn << (1 + rng.below(3 - wn.trailing_zeros() as usize)));
            Cond { tags: slower.tags.iter().copied().chain(["c_slower"]).collect(), ..slower }
        }
        _ => cond_at(rng, w),
    }
}

/// The modifiers of `mods` with no condition yet get one at their clock W; `slow` is how often (in a hundred) a `when~` gets a
/// condition slower than W (for `slowc`).
fn fill(rng: &mut Rng, head: Head, mods: &mut [Mod], slow: usize) {
    for i in 0..mods.len() {
        let w = w_of(head, mods, i);
        let new = match &mods[i] {
            // Not inside a block: there `sample_tick()` is gathered with the inputs and a slower value is read at its own tick, so
            // the two are not the same (R3 of W7-10 U3).
            Mod::When(c) if c.text.is_empty() && rng.chance(slow) && form_at(head, mods, i) != Some("in_block") => {
                let f = rng.pick(&[2u32, 4, 8]).max(1 << (-w).max(0));
                let text = format!("(k{f} > {})", rng.pick(&["1.5", "2.5"]));
                Mod::When(Cond {
                    text,
                    slow: BTreeSet::from([f]),
                    tags: BTreeSet::from(["c_slowk"]),
                    ..Cond::default()
                })
            }
            Mod::When(c) if c.text.is_empty() => Mod::When(cond_at(rng, w)),
            Mod::Reset(c) if c.text.is_empty() => Mod::Reset(reset_cond(rng, w)),
            m => m.clone(),
        };
        mods[i] = new;
    }
}

/// A head and a chain with a `reset_if~` that U2b passes (no condition yet).
fn base(rng: &mut Rng) -> (Head, Vec<Mod>) {
    loop {
        let mods: Vec<Mod> = (0..1 + rng.below(5))
            .map(|_| match rng.below(10) {
                0 | 1 => Mod::When(Cond::default()),
                2..=4 => Mod::Reset(Cond::default()),
                _ => rate(rng),
            })
            .collect();
        let head = rng.pick(&HEADS);
        if mods.iter().any(|m| matches!(m, Mod::Reset(_))) && fits(head, &mods) {
            return (head, mods);
        }
    }
}

/// `X.reset_if~(false)` and `X.when~(true)` put in at 1 to 3 places of `X` (a chain with a `reset_if~` of its own). With `rot`
/// the one put in changes the chain (a `reset_if~` that holds in every call, a `when~` that never does).
fn plan_rid(rng: &mut Rng, rot: bool) -> Plan {
    let (head, mut base) = base(rng);
    fill(rng, head, &mut base, 0);
    let mut fa = base.clone();
    let mut at: Vec<usize> = Vec::new();
    for _ in 0..1 + rng.below(3) {
        let reset = rng.chance(50);
        let with = |fa: &[Mod], p: usize, m: Mod| [&fa[..p], &[m], &fa[p..]].concat();
        let hole = if reset { Mod::Reset(Cond::default()) } else { Mod::When(Cond::default()) };
        // The places where one more modifier leaves a chain that U2b passes.
        let places: Vec<usize> = (0..=fa.len())
            .filter(|&p| fits(head, &with(&fa, p, hole.clone())) && (reset || when_twin_ok(head, &fa, p)))
            .collect();
        let Some(&p) = places.get(rng.below(places.len().max(1))) else { continue };
        let (w, blk) =
            (w_of(head, &with(&fa, p, hole.clone()), p), form_at(head, &with(&fa, p, hole), p) == Some("in_block"));
        let put = match (reset, rot) {
            (true, false) => Mod::Reset(never(rng, w)),
            (true, true) => Mod::Reset(Cond::lit("ct", "t_mutant")),
            (false, false) => Mod::When(always_true(rng, w, blk)),
            (false, true) => Mod::When(Cond::lit("!ct", "t_mutant")),
        };
        fa.insert(p, put);
        at.iter_mut().filter(|a| **a >= p).for_each(|a| *a += 1);
        at.push(p);
    }
    Plan { kind: "rid", head, fa, fb: base, at }
}

/// `.when~(k > T)` and `.when~(sample_tick() >= N)`: `fa` has `when~` of a condition slower than W (one at least), `fb` the time.
/// With `rot` the time is one tick late.
fn plan_slowc(rng: &mut Rng, rot: bool) -> Plan {
    loop {
        let (head, mut fa) = base(rng);
        fill(rng, head, &mut fa, 60);
        if !fa.iter().any(|m| m.cond().is_some_and(|c| !c.slow.is_empty())) {
            continue;
        }
        let late = u32::from(rot);
        let fb = (fa.iter())
            .map(|m| match m {
                Mod::When(c) if !c.slow.is_empty() => {
                    let f = *c.slow.first().expect("a slow condition names its grid");
                    // `k` is 2 from the tick `F` of the caller, 3 from `2 F`.
                    let n = if c.text.contains("1.5") { f } else { 2 * f };
                    Mod::When(Cond {
                        text: format!("(sample_tick() >= {})", n + late),
                        slow: BTreeSet::new(),
                        ..c.clone()
                    })
                }
                m => m.clone(),
            })
            .collect();
        return Plan { kind: "slowc", head, fa, fb, at: Vec::new() };
    }
}

/// `x.reset_if~(a).reset_if~(b)` and `x.reset_if~(a || b)`, with `a` and `b` at the same clock W, in a chain of 0 to 3
/// modifiers. With `rot` the twin has `&&`.
fn plan_rmerge(rng: &mut Rng, rot: bool) -> Plan {
    let (head, mut fa, at) = loop {
        let mut mods: Vec<Mod> =
            (0..rng.below(4)).map(|_| if rng.chance(25) { Mod::When(Cond::default()) } else { rate(rng) }).collect();
        let at = rng.below(mods.len() + 1);
        mods.splice(at..at, [Mod::Reset(Cond::default()), Mod::Reset(Cond::default())]);
        let head = rng.pick(&HEADS);
        if fits(head, &mods) {
            break (head, mods, at);
        }
    };
    let w = w_of(head, &fa, at);
    let blk = form_at(head, &fa, at) == Some("in_block");
    let (a, b) = loop {
        let (a, b) = (cond_at(rng, w), cond_at(rng, w));
        if !(blk && kinds_apart(&a, &b)) {
            break (a, b);
        }
    };
    fa[at] = Mod::Reset(a.clone());
    fa[at + 1] = Mod::Reset(b.clone());
    fill(rng, head, &mut fa, 0);
    let mut fb = fa.clone();
    fb.splice(at..at + 2, [Mod::Reset(a.join(if rot { "&&" } else { "||" }, &b))]);
    Plan { kind: "rmerge", head, fa, fb, at: vec![at, at + 1] }
}

/// `X.reset_if~(p at sample)` or `X.when~(p at sample)` and the same with `p`, in a chain with a `reset_if~` (`atid`, see `at_pair`).
fn plan_atid(rng: &mut Rng, rot: bool) -> Plan {
    loop {
        let (head, mut base) = base(rng);
        fill(rng, head, &mut base, 0);
        if let Some((fa, fb, at)) = at_pair(rng, head, &base, rot) {
            return Plan { kind: "atid", head, fa, fb, at };
        }
    }
}

/// The forms of a plan that the seeds of the gate have to hold: those of `twin_when.rs`, and what its `reset_if~` are. A modifier
/// to the left of a `reset_if~` is inside what it puts back, one to the right wraps it.
pub fn tags(plan: &Plan) -> BTreeSet<&'static str> {
    let (head, mods) = (plan.head, &plan.fa);
    let mut tags = tags_of(plan);
    let resets: Vec<usize> = (0..mods.len()).filter(|&i| matches!(mods[i], Mod::Reset(_))).collect();
    tags.insert(["r_0", "r_1", "r_2", "r_3", "r_4", "r_5", "r_6"][resets.len().min(6)]);
    let slow_head = matches!(head, Head::Slot | Head::Sl | Head::SlTk | Head::Outer);
    let tick = mods.iter().any(|m| matches!(m, Mod::Reset(c) if c.tags.contains("c_tick")));
    tags.extend((head == Head::Outer && tick).then_some("h_outer_tick"));
    for i in resets {
        let (left, right) = (&mods[..i], &mods[i + 1..]);
        let (up, down) = (|m: &Mod| matches!(m, Mod::Up(_)), |m: &Mod| matches!(m, Mod::Down(_)));
        tags.extend(mods[i].cond().iter().flat_map(|c| c.tags.iter().copied()));
        let found = [
            (left.iter().any(Mod::is_when), "r_has_when"),
            (slow_head && left.iter().any(Mod::is_when), "r_slow_has_when"),
            (left.iter().filter(|m| m.is_when()).count() >= 2, "r_has_two_when"),
            (
                head.out() > 0 && left.iter().any(down) && left.iter().any(Mod::is_when) && right.iter().any(up),
                "r_deal_up",
            ),
            (right.iter().any(Mod::is_when), "r_in_when"),
            (left.iter().any(up), "r_has_up"),
            (right.iter().any(up), "r_in_up"),
            (left.iter().any(down), "r_has_down"),
            (right.iter().any(down), "r_in_down"),
            (form_at(head, mods, i) == Some("in_block"), "r_in_block"),
        ];
        tags.extend(found.iter().filter(|(on, _)| *on).map(|(_, t)| *t));
    }
    tags
}

/// The program of a seed (with `rot`, the mutant of the twin), and the forms it holds.
pub fn make(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let plan = match rng.below(12) {
        0..=5 => plan_rid(&mut rng, rot),
        6 | 7 => plan_slowc(&mut rng, rot),
        8 | 9 => plan_rmerge(&mut rng, rot),
        _ => plan_atid(&mut rng, rot),
    };
    (program(&mut rng, &plan), tags(&plan))
}

/// A case of the matrix of `exotic`: the head, the chain (every condition filled in), the place and the kind (`reset_if~(false)`
/// or `when~(true)`) of the modifier that is put in.
type Case = (Head, Vec<Mod>, usize, bool);

/// The matrix of the twin `rid` that the breaker of U2b went over (`slot~(1.0).when~(b).when~(b).reset_if~(r)` had the state given
/// back before the slow stage wrote, a `when~(true)` after a `.down~` gave a deal array read before it was given back): every
/// chain of up to three of `.up~(2)`, `.down~(2)`, `.down~(4)`, a `when~(cb)` and a `reset_if~(r)` (`r` is the signal at W, `cb`
/// where W is faster) that has a `reset_if~` and that U2b passes, over five heads, with `reset_if~(false)` or `when~(true)` put in
/// at every place that U2b passes.
fn exotic_cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| {
        let letters = [Mod::Up(2), Mod::Down(2), Mod::Down(4), Mod::When(Cond::default()), Mod::Reset(Cond::default())];
        let (mut level, mut chains) = (vec![Vec::new()], Vec::new());
        for _ in 0..3 {
            level = (level.iter())
                .flat_map(|c: &Vec<Mod>| letters.iter().map(move |l| [c.clone(), vec![l.clone()]].concat()))
                .collect();
            chains.extend(level.clone());
        }
        let mut cases = Vec::new();
        for head in [Head::Tk, Head::Slot, Head::Sl, Head::Mk2, Head::Mk4, Head::Outer] {
            for base in chains.iter().filter(|c| c.iter().any(|m| matches!(m, Mod::Reset(_))) && fits(head, c)) {
                let mut base = base.clone();
                for i in 0..base.len() {
                    let w = w_of(head, &base, i);
                    base[i] = match base[i] {
                        Mod::When(_) => Mod::When(Cond::lit("cb", "c_block")),
                        Mod::Reset(_) if w <= 0 => Mod::Reset(Cond::signal(w)),
                        Mod::Reset(_) => Mod::Reset(Cond::lit("cb", "c_block")),
                        ref m => m.clone(),
                    };
                }
                for (p, reset) in (0..=base.len()).flat_map(|p| [(p, true), (p, false)]) {
                    let hole = if reset { Mod::Reset(Cond::default()) } else { Mod::When(Cond::default()) };
                    if fits(head, &[&base[..p], &[hole], &base[p..]].concat())
                        && (reset || when_twin_ok(head, &base, p))
                    {
                        cases.push((head, base.clone(), p, reset));
                    }
                }
            }
        }
        cases
    })
}

/// How many programs `make_exotic` has: the seeds `0 .. exotic_count()` are all of them.
pub fn exotic_count() -> u64 {
    exotic_cases().len() as u64
}

/// The program of the matrix that a seed picks (with `rot` the one put in changes the chain), and the forms it holds.
pub fn make_exotic(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let (head, base, p, reset) = exotic_cases()[seed as usize % exotic_cases().len()].clone();
    let put = match (reset, rot) {
        (true, false) => Mod::Reset(Cond::lit("cf", "f_block")),
        (true, true) => Mod::Reset(Cond::lit("ct", "t_mutant")),
        (false, false) => Mod::When(Cond::lit("ct", "t_block")),
        (false, true) => Mod::When(Cond::lit("!ct", "t_mutant")),
    };
    let mut fa = base.clone();
    fa.insert(p, put);
    let plan = Plan { kind: "rid", head, fa, fb: base, at: vec![p] };
    (program(&mut Rng::new(seed), &plan), tags(&plan))
}

/// Every chain of up to `len` modifiers (`.down~(2)`, `.down~(4)`, `.up~(2)`, `.when~`, `.reset_if~`) with a `reset_if~`, over
/// the heads of the matrix, in range: what it is and its program (the flow `fa` only, every condition the `block` value `cb`).
/// The checker passes every one of them since U3a (the generator makes them all: `fits` is the range).
pub fn chains(len: usize) -> Vec<(String, String)> {
    let words = [Mod::Down(2), Mod::Down(4), Mod::Up(2), Mod::When(Cond::default()), Mod::Reset(Cond::default())];
    let (mut all, mut frontier) = (vec![Vec::new()], vec![Vec::new()]);
    for _ in 0..len {
        frontier = (frontier.iter())
            .flat_map(|c: &Vec<Mod>| words.iter().map(move |w| [c.clone(), vec![w.clone()]].concat()))
            .collect();
        all.extend(frontier.clone());
    }
    let named = |m: &Mod| match m {
        Mod::When(_) => Mod::When(Cond::lit("cb", "")),
        Mod::Reset(_) => Mod::Reset(Cond::lit("cb", "")),
        m => m.clone(),
    };
    let mut out = Vec::new();
    for head in [Head::Slot, Head::Sl, Head::SlTk, Head::Tk, Head::Dws, Head::Mk2, Head::Mk4, Head::Outer] {
        for mods in all.iter().filter(|m| m.iter().any(|m| matches!(m, Mod::Reset(_))) && in_range(head, m)) {
            let filled: Vec<Mod> = mods.iter().map(named).collect();
            let text: String = filled.iter().map(Mod::text).collect();
            let src =
                format!("{HEADER}pub flow fa{SIGNATURE} -> F32 at sample {{\n  {}\n}}\n", flow_body(head, &filled));
            out.push((format!("{}{text}", head.text().0), src));
        }
    }
    out
}
