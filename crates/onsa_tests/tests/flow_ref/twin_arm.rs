//! A chain of `when~` and `reset_if~` on a built-in delay as the object of a `match~` whose binding a slower flow gathers
//! (W7-10 close/t; S-1209, S-1228; §11.5, §11.10). `fa` is `match~ <chain> { v => g2~(v).down~(2) at sample }` and `fb` binds
//! the chain with a `let` before (`let y = <chain>`, then `g2~(y).down~(2) at sample`): §11.5 says a `match~` value is the one of
//! the `let` and an `if~` that write its binding, so the two give the same outputs. The chain is evaluated once in a frame
//! however the ring that gathers the binding reads it, so a `when~` that counts the ticks it ran counts one in a frame (a
//! `reset_if~` of a slower tick inside it, §11.10, shows it). The same form in the copies of a `par~` is the second wrap.
//!
//! The matrix (`arm_cases`) is every chain of one to three modifiers over the letters `when~(c)`, `when~(cb)`, `when~(true)`,
//! `reset_if~(c)`, `reset_if~(cb)`, `reset_if~(c4)` and `reset_if~(c8)` (`c4` and `c8` are signals of `sample / 4` and
//! `sample / 8`), on `prev~`, `delay~` with an `init` and `vdelay~`, in the two wraps: the case of the wrap `w`, the head `h` and
//! the chain `i` is the seed `w * 3 * N + h * N + i` (`N` chains). The mutants of `fb` (`rot`): the first condition negated (an
//! even seed), or the chain not used (an odd seed: `g2~(y - y + xv)`, and in a `par~` `xv + F32.round_from(i) + <chain> * 0.0`:
//! the chain is read, so no binding is unused).

use std::collections::BTreeSet;
use std::sync::OnceLock;

use super::twin::Rng;
use super::twin_when::{Cond, HEADER, Head, Mod, SIGNATURE, lets, tests};

/// The letters of a chain: a `when~` of the signal at `sample`, a `block` value and a literal; a `reset_if~` of the signal at
/// `sample`, a `block` value and the signals of `sample / 4` and `sample / 8` (a tick slower than the grid of the chain).
fn letters() -> [Mod; 7] {
    [
        Mod::When(Cond::signal(0)),
        Mod::When(Cond::lit("cb", "c_block")),
        Mod::When(Cond::lit("true", "c_lit")),
        Mod::Reset(Cond::signal(0)),
        Mod::Reset(Cond::lit("cb", "c_block")),
        Mod::Reset(Cond::signal_n(4)),
        Mod::Reset(Cond::signal_n(8)),
    ]
}

/// The chains of the matrix: every one of one to three letters.
fn chains() -> &'static [Vec<Mod>] {
    static CHAINS: OnceLock<Vec<Vec<Mod>>> = OnceLock::new();
    CHAINS.get_or_init(|| {
        let (mut level, mut all) = (vec![Vec::new()], Vec::new());
        for _ in 0..3 {
            level = (level.iter())
                .flat_map(|c: &Vec<Mod>| letters().into_iter().map(move |l| [c.clone(), vec![l]].concat()))
                .collect();
            all.extend(level.clone());
        }
        all
    })
}

const HEADS: [Head; 3] = [Head::Prev, Head::Delay, Head::Vdelay];

/// How many programs there are: the seeds `0 .. arm_count()` are all of them (a seed above makes the same case with other inputs).
pub fn arm_count() -> u64 {
    (2 * HEADS.len() * chains().len()) as u64
}

/// Whether a `reset_if~` of a signal slower than the grid of the chain is inside a `when~` (to its left): the form where a
/// chain evaluated twice in a frame counts the ticks that the `when~` ran twice.
fn slow_reset_in_when(mods: &[Mod]) -> bool {
    let slow = |m: &Mod| matches!(m, Mod::Reset(c) if c.tags.contains("c_sig_slow"));
    mods.iter().enumerate().any(|(i, m)| slow(m) && mods[i + 1..].iter().any(Mod::is_when))
}

/// The forms of a case that the seeds of the gate hold.
fn tags(head: Head, mods: &[Mod], par: bool) -> BTreeSet<&'static str> {
    let mut tags = BTreeSet::from([head.text().1, if par { "a_par" } else { "a_match" }]);
    tags.insert(["len_0", "len_1", "len_2", "len_3"][mods.len().min(3)]);
    tags.extend(slow_reset_in_when(mods).then_some("slow_in_when"));
    for (i, m) in mods.iter().enumerate() {
        let word = |when: &'static str, reset: &'static str| if m.is_when() { when } else { reset };
        let c = m.cond().expect("a modifier of the chain has a condition");
        tags.extend(c.tags.contains("c_sig").then_some(word("w_sig", "r_sig")));
        tags.extend(c.tags.contains("c_block").then_some(word("w_block", "r_block")));
        tags.extend(c.tags.contains("c_lit").then_some("w_true"));
        tags.extend((c.text == "c4").then_some("r_slow4"));
        tags.extend((c.text == "c8").then_some("r_slow8"));
        tags.extend((i > 0 && m.is_when() && !mods[i - 1].is_when()).then_some("reset_then_when"));
        tags.extend((i > 0 && !m.is_when() && mods[i - 1].is_when()).then_some("when_then_reset"));
    }
    tags
}

/// The program of the matrix that a seed picks (with `rot`, the mutant of `fb`), and the forms it holds.
pub fn make_arm(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let (n, h) = (chains().len(), HEADS.len());
    let i = seed as usize % (2 * h * n);
    let (par, head, mods) = (i >= h * n, HEADS[i / n % h], chains()[i % n].clone());
    let mut fb_mods = mods.clone();
    if rot && seed % 2 == 0 {
        fb_mods[0] = match &mods[0] {
            Mod::When(c) => Mod::When(c.not()),
            Mod::Reset(c) => Mod::Reset(c.not()),
            m => m.clone(),
        };
    }
    let text = |mods: &[Mod]| format!("{}{}", head.text().0, mods.iter().map(Mod::text).collect::<String>());
    let (fa_chain, fb_chain, unused) = (text(&mods), text(&fb_mods), rot && seed % 2 == 1);
    let (fa, fb) = if par {
        let each = |body: String| format!("let ys = par~ i in 0 ..< 2 {{ {body} }}\n  ys[0] + ys[1] * 10.0");
        let value = if unused {
            format!("xv + F32.round_from(i) + {fb_chain} * 0.0")
        } else {
            format!("{fb_chain} + F32.round_from(i)")
        };
        (
            each(format!("match~ {fa_chain} + F32.round_from(i) {{ v => g2~(v).down~(2) at sample }}")),
            each(format!("g2~({value}).down~(2) at sample")),
        )
    } else {
        let y = if unused { "y - y + xv" } else { "y" };
        (
            format!("match~ {fa_chain} {{ v => g2~(v).down~(2) at sample }}"),
            format!("let y = {fb_chain}\n  g2~({y}).down~(2) at sample"),
        )
    };
    let flow = |name: &str, body: &str, mods: &[Mod]| {
        format!("pub flow {name}{SIGNATURE} -> F32 at sample {{\n  {}{body}\n}}\n", lets(head, mods))
    };
    let src = format!("{HEADER}{}{}{}", flow("fa", &fa, &mods), flow("fb", &fb, &fb_mods), tests(&mut Rng::new(seed)));
    (src, tags(head, &mods, par))
}
