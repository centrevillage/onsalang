//! A sweep of the clock of the binding of a `match~` arm against a model of the decision (§11.3, §11.4, §11.5, S-1131; W7-20 U4, from the sweep of
//! the break side of W7-06 U3a, `gen1.py`).
//!
//! §11.5: "腕の本体で読む束縛のクロックは、対象のクロックと、最初の腕からその腕までのガードのクロックのうち最も速いものである（ガードの中で読む束縛は
//! 対象のクロック）". A value of that clock is read by an `init` or `block` input of an instance (E0815, §11.9: the clock of an argument is at most the
//! clock of the input), by an `init` argument of a delay (E0815, §11.4), by the arguments of a non-`rt` fn (at most `init`, E0815, §11.3), and by the
//! first argument of a delay, which must be at `sample` or finer (E0813: a `block` or an `init` value there is the error, §11.4). The model is the
//! fastest of the target and the guards up to the arm, and the table of the limits of the six readers; it asks for no other state.
//!
//! The grid is the whole of it: the target at `init`, `block` or `sample`, the guard of the first arm (none, `init`, `block`, `sample`), the same for
//! the second, the arm that reads the binding (the first or the second, if it binds), six readers. The drawn form (`heavy_`) is three to five arms with
//! the guards that read the binding, a guard of a promotion `(gb at sample)` and a constant guard. A flow that has a diagnostic where the model has
//! none, or the other code, or one elsewhere, is a mismatch; the sources are kept in memory (`check_input`, `rules/common.md` 3.7).

use crate::test_support;

use std::collections::HashMap;
use std::sync::OnceLock;

use test_support::sweep::{Rng, Texts, check_input, ended_well, input_of};

/// The clocks of the sweep in the order of §11.3: the slower one is the smaller.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Clock {
    Init,
    Block,
    Sample,
}

const CLOCKS: [Clock; 3] = [Clock::Init, Clock::Block, Clock::Sample];

impl Clock {
    /// The input of the flows below that has this clock (the target `k?`, the guard `g?`).
    fn suffix(self) -> &'static str {
        ["i", "b", "s"][self as usize]
    }
}

/// What the arm that reads the binding does with it.
#[derive(Clone, Copy, Debug)]
enum Cons {
    /// `lp~(x, n)`: a `block` input of an instance.
    Block,
    /// `cfg~(x, n)`: an `init` input of an instance.
    Init,
    /// `prev~(x, n)`: the `init` argument of a delay.
    DelayInit,
    /// `prev~(n)`: the first argument of a delay, which needs `sample`.
    DelayFirst,
    /// `design(n)`: the argument of a non-`rt` fn, at most `init`.
    NonRt,
    /// `acc~(x) + n`: no limit.
    Plain,
}

const CONS: [Cons; 6] = [Cons::Block, Cons::Init, Cons::DelayInit, Cons::DelayFirst, Cons::NonRt, Cons::Plain];

impl Cons {
    fn body(self) -> &'static str {
        match self {
            Cons::Block => "lp~(x, F32.round_from(n))",
            Cons::Init => "cfg~(x, F32.round_from(n))",
            Cons::DelayInit => "prev~(x, F32.round_from(n))",
            Cons::DelayFirst => "prev~(F32.round_from(n))",
            Cons::NonRt => "acc~(x) + design(F32.round_from(n))",
            Cons::Plain => "acc~(x) + F32.round_from(n)",
        }
    }

    /// The code the model gives to a read of a binding of the clock `c`.
    fn expected(self, c: Clock) -> Option<&'static str> {
        match self {
            Cons::Block => (c > Clock::Block).then_some("E0815"),
            Cons::Init | Cons::DelayInit | Cons::NonRt => (c > Clock::Init).then_some("E0815"),
            Cons::DelayFirst => (c < Clock::Sample).then_some("E0813"),
            Cons::Plain => None,
        }
    }
}

/// The guard of an arm: its text, and the clock the model gives it (a constant has none).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Guard {
    No,
    Of(Clock),
    /// `(gb at sample)`: a promotion.
    Promoted,
    /// `true`.
    Const,
    /// `(n > 0)`: reads the binding, which has the clock of the target.
    ReadsN,
    /// `(F32.round_from(n) > 0.5 && gb)`.
    ReadsNAndBlock,
}

impl Guard {
    fn text(self) -> String {
        match self {
            Guard::No => String::new(),
            Guard::Of(c) => format!(" if g{}", c.suffix()),
            Guard::Promoted => " if (gb at sample)".into(),
            Guard::Const => " if true".into(),
            Guard::ReadsN => " if (n > 0)".into(),
            Guard::ReadsNAndBlock => " if (F32.round_from(n) > 0.5 && gb)".into(),
        }
    }

    fn clock(self, scr: Clock) -> Option<Clock> {
        match self {
            Guard::No | Guard::Const => None,
            Guard::Of(c) => Some(c),
            Guard::Promoted => Some(Clock::Sample),
            Guard::ReadsN => Some(scr),
            Guard::ReadsNAndBlock => Some(scr.max(Clock::Block)),
        }
    }
}

struct Arm {
    pat: String,
    guard: Guard,
}

/// One flow: `match~` of a target at `scr`, the arm `ca` reads its binding `n`.
struct Case {
    scr: Clock,
    arms: Vec<Arm>,
    ca: usize,
    cons: Cons,
    catch_all: bool,
}

/// How the model takes the clock of the binding; the later ones are the faults of the model that the sweep must catch.
#[derive(Clone, Copy, Debug)]
enum Rule {
    /// S-1131: the fastest of the target and the guards from the first arm to the arm.
    Decision,
    /// The clock of the target only (what the compiler did before S-1131).
    TargetOnly,
    /// The target and the guard of the arm itself only.
    OwnGuardOnly,
    /// The target and the guards of the arms before the arm (the guard of the arm itself is left out).
    EarlierGuardsOnly,
    /// The slowest, not the fastest.
    Slowest,
}

impl Case {
    fn binding_clock(&self, rule: Rule) -> Clock {
        let guards: Vec<Clock> = self.arms[..=self.ca].iter().filter_map(|a| a.guard.clock(self.scr)).collect();
        let own = self.arms[self.ca].guard.clock(self.scr);
        let fold = |gs: &[Clock]| gs.iter().fold(self.scr, |a, &g| a.max(g));
        match rule {
            Rule::Decision => fold(&guards),
            Rule::TargetOnly => self.scr,
            Rule::OwnGuardOnly => fold(&own.into_iter().collect::<Vec<_>>()),
            Rule::EarlierGuardsOnly => {
                fold(&self.arms[..self.ca].iter().filter_map(|a| a.guard.clock(self.scr)).collect::<Vec<_>>())
            }
            Rule::Slowest => guards.iter().fold(self.scr, |a, &g| a.min(g)),
        }
    }

    fn expected(&self, rule: Rule) -> Option<&'static str> {
        self.cons.expected(self.binding_clock(rule))
    }

    fn text(&self, j: usize) -> String {
        let mut s = format!(
            "pub flow f{j}(x: F32 at sample, ki: U32 at init, kb: U32 at block, ks: U32 at sample, gi: Bool at init, gb: Bool at block, gs: Bool at sample) -> F32 at sample {{\n  match~ k{} {{\n",
            self.scr.suffix()
        );
        for (i, a) in self.arms.iter().enumerate() {
            let body = if i == self.ca { self.cons.body() } else { "x" };
            s.push_str(&format!("    {}{} => {body},\n", a.pat, a.guard.text()));
        }
        if self.catch_all {
            s.push_str("    _ => x,\n");
        }
        s + "  }\n}\n\n"
    }
}

const HEAD: &str = "pub flow lp(x: F32 at sample, g: F32 at block) -> F32 at sample { x * g }\n\n\
pub flow cfg(x: F32 at sample, c: F32 at init) -> F32 at sample { x * c }\n\n\
pub flow acc(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(^y)\n  y\n}\n\n\
pub fn design(v: F32) -> F32 { v * 0.5 }\n\n";

/// The grid of the sweep (the first four lines of the module doc): 936 flows.
fn grid() -> Vec<Case> {
    // The first arm, then the second: a literal or a binding, with a guard or not.
    let opts: Vec<(bool, Guard)> = [false, true]
        .iter()
        .flat_map(|&bind| {
            [Guard::No, Guard::Of(Clock::Init), Guard::Of(Clock::Block), Guard::Of(Clock::Sample)].map(|g| (bind, g))
        })
        .collect();
    let mut cases = Vec::new();
    for scr in CLOCKS {
        for &a0 in &opts {
            for &a1 in &opts {
                // An unguarded binding takes every value: it ends the arms, so it is the last (and the first arm is never one).
                if a0.0 && a0.1 == Guard::No {
                    continue;
                }
                for ca in 0..2 {
                    let spec = [a0, a1];
                    if !spec[ca].0 {
                        continue;
                    }
                    for cons in CONS {
                        let arms = spec
                            .iter()
                            .enumerate()
                            .map(|(i, &(bind, guard))| {
                                let pat = if !bind {
                                    format!("{i}")
                                } else if i == ca {
                                    "n".into()
                                } else {
                                    "_".into()
                                };
                                Arm { pat, guard }
                            })
                            .collect();
                        cases.push(Case { scr, arms, ca, cons, catch_all: !(a1.0 && a1.1 == Guard::No) });
                    }
                }
            }
        }
    }
    cases
}

/// `count` flows of three to five arms drawn from `seed`: the guards read the binding, promote a `block` input, or are constants.
fn drawn(seed: u64, count: usize) -> Vec<Case> {
    let mut rng = Rng::new(seed);
    let kinds = [
        Guard::No,
        Guard::Of(Clock::Init),
        Guard::Of(Clock::Block),
        Guard::Of(Clock::Sample),
        Guard::Promoted,
        Guard::Const,
        Guard::ReadsN,
        Guard::ReadsNAndBlock,
    ];
    (0..count)
        .map(|_| {
            let scr = *rng.pick(&CLOCKS);
            let n = rng.range(3, 5);
            let (ca, cons) = (rng.below(n), *rng.pick(&CONS));
            let mut arms = Vec::new();
            let mut catch_all = true;
            for i in 0..n {
                let own = i == ca;
                let mut guard = loop {
                    let g = *rng.pick(&kinds);
                    if own || !matches!(g, Guard::ReadsN | Guard::ReadsNAndBlock) {
                        break g;
                    }
                };
                // An unguarded binding ends the arms; a `true` guard and the unguarded one are kept for the last place.
                if (guard == Guard::Const || (own && guard == Guard::No)) && i != n - 1 {
                    guard = Guard::Of(Clock::Sample);
                }
                arms.push(Arm { pat: if own { "n".into() } else { i.to_string() }, guard });
                if own && guard == Guard::No {
                    catch_all = false;
                    break;
                }
            }
            Case { scr, arms, ca, cons, catch_all }
        })
        .collect()
}

/// The diagnostics the check gave to each flow (on the line of the arm that reads the binding), and the ones elsewhere.
struct Observed {
    cases: Vec<Case>,
    got: Vec<Vec<String>>,
    stray: Vec<String>,
}

fn observe(cases: Vec<Case>) -> Observed {
    let (mut got, mut stray) = (vec![Vec::new(); cases.len()], Vec::new());
    for (c, chunk) in cases.chunks(50).enumerate() {
        let mut src = HEAD.to_string();
        let mut at = HashMap::new();
        for (k, case) in chunk.iter().enumerate() {
            at.insert(src.lines().count() as u64 + 3 + case.ca as u64, c * 50 + k);
            src.push_str(&case.text(k));
        }
        let mut texts = Texts::new();
        texts.insert("main.onsa".to_string(), src);
        let checked = check_input(&input_of("demo", &texts));
        assert!(ended_well(&checked), "chunk {c}: check did not end as a check does:\n{}", checked.stderr);
        for d in &checked.diags {
            match at.get(&d.line) {
                Some(&i) => got[i].push(d.code.clone()),
                None => stray.push(format!("chunk {c}: {} at {}:{}: {}", d.code, d.line, d.col, d.message)),
            }
        }
    }
    Observed { cases, got, stray }
}

impl Observed {
    /// The flows where the check and the model of `rule` disagree, and the diagnostics that are on no arm that reads the binding.
    fn mismatches(&self, rule: Rule) -> Vec<String> {
        let mut bad = self.stray.clone();
        for (i, (case, got)) in self.cases.iter().zip(&self.got).enumerate() {
            let want: Vec<String> = case.expected(rule).iter().map(|c| c.to_string()).collect();
            if *got != want {
                bad.push(format!("flow {i}: expected {want:?}, got {got:?}\n{}", case.text(i % 50)));
            }
        }
        bad
    }
}

fn the_grid() -> &'static Observed {
    static GRID: OnceLock<Observed> = OnceLock::new();
    GRID.get_or_init(|| observe(grid()))
}

#[test]
fn the_binding_clock_of_a_match_tilde_arm_is_the_fastest_of_the_target_and_the_guards_so_far() {
    let obs = the_grid();
    let bad = obs.mismatches(Rule::Decision);
    assert!(bad.is_empty(), "{} mismatches:\n{}", bad.len(), bad[..bad.len().min(5)].join("\n"));
    // The grid has the size of the sweep and both sides: a read that is an error (both codes) and one that is not.
    let wanted: Vec<_> = obs.cases.iter().map(|c| c.expected(Rule::Decision)).collect();
    let count = |code: Option<&str>| wanted.iter().filter(|w| **w == code).count();
    assert_eq!(obs.cases.len(), 936);
    assert!(count(Some("E0815")) > 200 && count(Some("E0813")) > 20 && count(None) > 300, "{wanted:?}");
}

#[test]
fn a_model_that_takes_the_clock_of_the_binding_another_way_disagrees_with_the_check() {
    let obs = the_grid();
    for rule in [Rule::TargetOnly, Rule::OwnGuardOnly, Rule::EarlierGuardsOnly, Rule::Slowest] {
        let bad = obs.mismatches(rule);
        assert!(bad.len() > 20, "{rule:?} disagrees with the check in {} flows only", bad.len());
    }
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_the_binding_clock_of_drawn_match_tilde_flows_is_the_model_s() {
    let (mut flows, mut errors) = (0, 0);
    for seed in 0..20 {
        let obs = observe(drawn(seed, 50));
        let bad = obs.mismatches(Rule::Decision);
        assert!(bad.is_empty(), "seed {seed}: {} mismatches:\n{}", bad.len(), bad[..bad.len().min(3)].join("\n"));
        flows += obs.cases.len();
        errors += obs.cases.iter().filter(|c| c.expected(Rule::Decision).is_some()).count();
    }
    // The draw has both sides.
    assert!(flows == 1000 && errors > 200 && flows - errors > 200, "{flows} flows, {errors} with a diagnostic");
}
