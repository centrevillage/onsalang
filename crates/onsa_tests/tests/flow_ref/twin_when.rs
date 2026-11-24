//! Chains of `when~` made from a seed, with their twins (W7-10 U1e/t; S-1209, S-1217, S-1220, S-1222). A seed makes one program
//! of two flows `fa` and `fb` that §11.10 says give the same outputs, and tests that run both on a grid of the `block` and
//! `init` inputs, on a `process` cut at other places, with a `reset` in the grid. The twins are:
//!
//! - `id`: `X.when~(true)` and `X` (a condition that always holds, wherever it is put in the chain: `fa` is the chain with one
//!   or two `when~` of such a condition put in, `fb` the chain);
//! - `commute`: `x.down~(N).when~(c)` and `x.when~(c).down~(N)` (the head has its input and output at `sample`, §11.10 "合成");
//! - `merge`: `x.when~(a).when~(b)` and `x.when~(a && b)` (both read at the clock W; inside a block not for a signal and a `block`
//!   value, which one expression gathers whole, `kinds_apart`);
//! - `atid`: `x.when~(p at sample)` and `x.when~(p)` for a value `p` of a parameter kind, where W is `sample` (§11.3: an `at` does not
//!   change the stage of such a value, so also inside a block it is no signal that is gathered, `at_pair`).
//!
//! A signal inside a block (`x.when~(c).up~(2).down~(2)`) is gathered with the inputs of the head and its phase 0 is `false` (§11.9,
//! §11.10), so the twins that equal a condition to a literal or to a time (`when~(c || ct)` and `when~(true)`) are not made there.
//!
//! The chain is a head and 1 to 5 modifiers (`.down~`, `.up~`, `.when~`). The condition of a `when~` is read at its clock W
//! (the output clock of the part it wraps when that is slower than the place of the modifier, §11.10) or is a `block` or
//! `init` value, a literal: the forms that the check passes (a delay as the head is E0200 until U3b and never made; a modifier
//! inside a block and a `when~` of a burst under an `.up~` are made since U3a). Both writings are made from one plan and printed,
//! and the expectation of the asserts is the spec (a twin); what the plan gives on the evaluator is compared with the interpreter
//! by `twin::run`.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use super::twin::Rng;

/// The flows the chains are made of. `slot` has a stage of `sample / 2` that writes a field and a stage of `sample` that reads it
/// (the head that shows how a `when~` counts the runs, §11.9); `mk2` and `mk4` give a burst (`sample * N`) that a boundary
/// deals out; `dws4` gathers (its output is `sample / 4`); `lb2`, `lb4` and `lb8` make a `Bool` of `sample / N` from the input.
pub const HEADER: &str = "pub flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}
pub flow slot(f: F32 at block) -> F32 at sample {
  let s = acc~(f).down~(2)
  let n = prev~(^n) + 1.0
  (s at sample) * 100.0 + n
}
pub flow tk() -> F32 at sample {
  F32.round_from(sample_tick())
}
pub flow lp(x: F32 at sample) -> F32 at sample {
  x * 0.5 + prev~(x) * 0.5
}
pub flow cnt() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}
pub flow mk2() -> F32 at (sample * 2) {
  let n = cnt~() * 10.0
  [n, n + 1.0]
}
pub flow mk4() -> F32 at (sample * 4) {
  let n = cnt~() * 10.0
  [n, n + 1.0, n + 2.0, n + 3.0]
}
pub flow sum4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] + x[2] + x[3]
}
pub flow dws4(x: F32 at sample) -> F32 at (sample / 4) {
  sum4~(x).down~(4)
}
pub flow g2(x: F32 at (sample * 2)) -> F32 at sample {
  x[0] + x[1] * 10.0
}
pub flow g4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0
}
pub flow sl(p: F32 at (sample / 2)) -> F32 at sample {
  let h = p + 1.0
  h at sample
}
pub flow inner(q: F32 at (sample / 2)) -> F32 at sample {
  let h = q + 1.0
  h at sample
}
pub flow outer2(c: Bool at sample) -> F32 at sample {
  let q = cnt~().down~(2)
  inner~(q).when~(c)
}
pub flow lb2(c: Bool at (sample * 2)) -> Bool at sample {
  c[1]
}
pub flow lb4(c: Bool at (sample * 4)) -> Bool at sample {
  c[3]
}
pub flow lb8(c: Bool at (sample * 8)) -> Bool at sample {
  c[7]
}
";
/// The inputs of `fa` and `fb`: `c` is the one signal (`sample`); `cb` and `ci` change with the call and the grid (a condition
/// reads them); `ct` and `cti` are true in every call (only a condition that always holds reads them), `cf` and `cfi` false
/// in every call (only a condition that never holds reads them).
pub const SIGNATURE: &str = "(c: Bool at sample, cb: Bool at block, ct: Bool at block, cf: Bool at block, ci: Bool at init, \
     cti: Bool at init, cfi: Bool at init)";
/// How many frames a test runs.
pub const FRAMES: usize = 16;

/// The heads, by what they need of the chain. `Slot`, `Tk` and `Acc` have no input; `Lp` and `Dws` take a signal at `sample`
/// of the chain (so the chain rate is `sample`); `Mk2` and `Mk4` give a burst that a `.down~` of the chain deals out.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Head {
    Slot,
    Tk,
    Acc,
    Lp,
    Dws,
    Mk2,
    Mk4,
    /// Heads whose input is slower than the chain (`sample / 2`): a value of the caller's own, or the time (W7-10 U2e/t).
    Sl,
    SlTk,
    /// A head with a `when~` of its own inside, whose part has an input slower than it (`inner~(q).when~(c)`, `q` at `sample / 2`
    /// made in the head): the slow input of a `when~` that a `reset_if~` has to put back (W7-10 U2e/t2).
    Outer,
}

impl Head {
    pub const ALL: [Head; 7] = [Head::Slot, Head::Tk, Head::Acc, Head::Lp, Head::Dws, Head::Mk2, Head::Mk4];
    /// The heads a seed picks from: `Slot` (a stage at `sample / 2` that writes a field the stage at `sample` reads) is the
    /// head of a third of the programs.
    pub const WEIGHTED: [Head; 10] =
        [Head::Slot, Head::Slot, Head::Slot, Head::Tk, Head::Acc, Head::Lp, Head::Dws, Head::Mk2, Head::Mk2, Head::Mk4];

    /// The call, and the tag.
    pub fn text(self) -> (&'static str, &'static str) {
        match self {
            Head::Slot => ("slot~(1.0)", "h_slot"),
            Head::Tk => ("tk~()", "h_tk"),
            Head::Acc => ("acc~(0.5)", "h_acc"),
            Head::Lp => ("lp~(xv)", "h_lp"),
            Head::Dws => ("dws4~(xv)", "h_dws"),
            Head::Mk2 => ("mk2~()", "h_mk2"),
            Head::Mk4 => ("mk4~()", "h_mk4"),
            Head::Sl => ("sl~(q)", "h_sl"),
            Head::SlTk => ("sl~(F32.round_from(sample_tick()))", "h_sltk"),
            Head::Outer => ("outer2~(c)", "h_outer"),
        }
    }

    /// The exponent of the clock of its output, to the chain rate (`sample * 2^e`).
    pub fn out(self) -> i32 {
        match self {
            Head::Dws => -2,
            Head::Mk2 => 1,
            Head::Mk4 => 2,
            _ => 0,
        }
    }

    /// Whether it has an input at the chain rate.
    pub fn input(self) -> bool {
        matches!(self, Head::Lp | Head::Dws | Head::Sl | Head::SlTk | Head::Outer)
    }
}

/// A condition: its text, the `sample / N` signals it names (`c2`, `c4`, `c8`, each bound by a `let` of the flow), its tags.
#[derive(Clone, Debug, Default)]
pub struct Cond {
    pub text: String,
    pub signals: BTreeSet<u32>,
    /// The `k<F>` it names (`let k<F> = acc~(1.0).down~(<F>)`: a value slower than the chain, that a `when~` holds).
    pub slow: BTreeSet<u32>,
    pub tags: BTreeSet<&'static str>,
}

impl Cond {
    pub fn lit(text: &str, tag: &'static str) -> Cond {
        Cond { text: text.to_string(), tags: BTreeSet::from([tag]), ..Cond::default() }
    }

    /// The signal at W (`w` is at most 0): `c` at `sample`, `c<N>` at `sample / N`.
    pub fn signal(w: i32) -> Cond {
        Cond::signal_n(1u32 << (-w))
    }

    /// The signal at `sample / n`.
    pub fn signal_n(n: u32) -> Cond {
        if n == 1 {
            return Cond::lit("c", "c_sig");
        }
        Cond {
            text: format!("c{n}"),
            signals: BTreeSet::from([n]),
            tags: BTreeSet::from(["c_sig", "c_sig_slow"]),
            ..Cond::default()
        }
    }

    pub fn join(&self, op: &str, other: &Cond) -> Cond {
        let tags = self.tags.union(&other.tags).copied().chain([if op == "&&" { "c_and" } else { "c_or" }]).collect();
        let (signals, slow) = (&self.signals | &other.signals, &self.slow | &other.slow);
        Cond { text: format!("{} {op} {}", self.text, other.text), signals, slow, tags }
    }

    pub fn not(&self) -> Cond {
        let tags = self.tags.iter().copied().chain(["c_not"]).collect();
        let text = if self.text.starts_with('!') { format!("!({})", self.text) } else { format!("!{}", self.text) };
        Cond { text, tags, ..self.clone() }
    }

    /// With the parentheses that a `&&` or `||` needs inside another expression.
    pub fn wrapped(&self) -> Cond {
        Cond { text: format!("({})", self.text), ..self.clone() }
    }
}

/// A modifier of the chain.
#[derive(Clone, Debug)]
pub enum Mod {
    Down(u32),
    Up(u32),
    When(Cond),
    /// `.reset_if~` (W7-10 U2e/t): it changes no rate, as `when~`.
    Reset(Cond),
}

impl Mod {
    /// The exponent of the rate it changes (`.down~(4)` is -2).
    pub fn exp(&self) -> i32 {
        match self {
            Mod::Down(n) => -(n.trailing_zeros() as i32),
            Mod::Up(n) => n.trailing_zeros() as i32,
            Mod::When(_) | Mod::Reset(_) => 0,
        }
    }

    pub fn is_when(&self) -> bool {
        matches!(self, Mod::When(_))
    }

    /// The condition of a `when~` or a `reset_if~`.
    pub fn cond(&self) -> Option<&Cond> {
        if let Mod::When(c) | Mod::Reset(c) = self { Some(c) } else { None }
    }

    pub fn text(&self) -> String {
        match self {
            Mod::Down(n) => format!(".down~({n})"),
            Mod::Up(n) => format!(".up~({n})"),
            Mod::When(c) => format!(".when~({})", c.text),
            Mod::Reset(c) => format!(".reset_if~({})", c.text),
        }
    }
}

/// The clock W (as the exponent of `sample`) at which the `when~` at `i` reads its condition (§11.10): the output clock of
/// the part it wraps when that is slower than P, the clock of the place of the modifier, otherwise P.
pub fn w_of(head: Head, mods: &[Mod], i: usize) -> i32 {
    let p: i32 = mods[i + 1..].iter().map(Mod::exp).sum();
    let receiver = head.out() + mods[..i].iter().map(Mod::exp).sum::<i32>();
    if receiver < 0 { p + receiver } else { p }
}

/// The exponent of the clock of the whole chain, at the `sample` of the flow that calls it.
pub fn net(head: Head, mods: &[Mod]) -> i32 {
    head.out() + mods.iter().map(Mod::exp).sum::<i32>()
}

/// The forms that U1 and U2 kept as E0200 and U3a opened (S-1209): a modifier inside a block (an `.up~` outside it and a `.down~`
/// outside that, `x.when~(c).up~(2).down~(2)`), and a `when~` of a burst with an `.up~` outside it (`mk2~().when~(c).up~(2)`).
/// The form of the modifier at `i`; the checker passes both since U3a, so the generator makes them (`fits`).
pub fn form_at(head: Head, mods: &[Mod], i: usize) -> Option<&'static str> {
    let sum = |m: &[Mod]| m.iter().map(Mod::exp).sum::<i32>();
    let is_up = |m: &Mod| matches!(m, Mod::Up(_));
    let is_down = |m: &Mod| matches!(m, Mod::Down(_));
    let (left, right) = (&mods[..i], &mods[i + 1..]);
    let block = right.iter().enumerate().any(|(j, m)| is_up(m) && right[j + 1..].iter().any(is_down));
    let receiver = head.out() + sum(left);
    // A `reset_if~` of a burst with an `.up~` outside it is no form of its own: only the block is.
    match (block, mods[i].is_when() && receiver >= 1 && right.iter().any(is_up)) {
        (true, _) => Some("in_block"),
        (_, true) => Some("burst_under_up"),
        _ => None,
    }
}

/// The first of the forms of the chain, if it has one.
pub fn form(head: Head, mods: &[Mod]) -> Option<&'static str> {
    (0..mods.len()).filter(|&i| mods[i].cond().is_some()).find_map(|i| form_at(head, mods, i))
}

/// Whether the head can have this chain: a head with an input needs the chain rate `sample` (its argument is a signal at
/// `sample`), and no running sum of the rates (from the left or from the right) or the output leaves `-3 ..= 2`.
pub fn in_range(head: Head, mods: &[Mod]) -> bool {
    let all: i32 = mods.iter().map(Mod::exp).sum();
    let sum = |m: &[Mod]| m.iter().map(Mod::exp).sum::<i32>();
    let sums = (0..=mods.len()).flat_map(|i| [sum(&mods[..i]), sum(&mods[i..])]);
    (!head.input() || all == 0) && sums.chain([net(head, mods)]).all(|s| (-3..=2).contains(&s))
}

/// What the generator makes: a chain in range, which the checker passes and lowers (every form of `form` is open since U3a).
pub fn fits(head: Head, mods: &[Mod]) -> bool {
    in_range(head, mods)
}

/// A condition read at W (`w`): a `block` or `init` value or a literal (a `when~` read at `sample * N` has nothing else, U1),
/// and when W is `sample` or slower also the signal at W; negated or joined with another leaf at random.
pub fn cond_at(rng: &mut Rng, w: i32) -> Cond {
    let leaf = |rng: &mut Rng| {
        if w <= 0 && rng.chance(60) {
            return Cond::signal(w);
        }
        rng.pick_in(&[Cond::lit("cb", "c_block"), Cond::lit("ci", "c_init"), Cond::lit("true", "c_lit")]).clone()
    };
    let a = leaf(rng);
    match rng.below(6) {
        0 => a.not(),
        1 => a.join("&&", &leaf(rng)).wrapped(),
        2 => a.join("||", &leaf(rng)).wrapped(),
        _ => a,
    }
}

/// A condition that always holds (every call of the tests gives `ct` and `cti` true; `c || ct` has the signal at W too, but not
/// inside a block (`in_block`): a signal there is gathered with the inputs and phase 0 is `false`, so the first tick does not run
/// the part, and `when~(c || ct)` is not `when~(true)` (§11.9, §11.10: R2 of W7-10 U3)).
pub fn always_true(rng: &mut Rng, w: i32, in_block: bool) -> Cond {
    match rng.below(if w <= 0 && !in_block { 5 } else { 4 }) {
        0 => Cond::lit("true", "t_lit"),
        1 => Cond::lit("ct", "t_block"),
        2 => Cond::lit("cti", "t_init"),
        3 => Cond::lit("ct && cti", "t_both"),
        _ => {
            let s = Cond::signal(w);
            Cond { text: format!("{} || ct", s.text), tags: s.tags.iter().copied().chain(["t_or_sig"]).collect(), ..s }
        }
    }
}

/// The plan of a program: the twin's name, the head, and the modifiers of `fa` and of `fb`.
pub struct Plan {
    pub kind: &'static str,
    pub head: Head,
    pub fa: Vec<Mod>,
    pub fb: Vec<Mod>,
    /// Where the always-true `when~` were put in `fa` (the twin `id`), or the two `when~` that `merge` joins.
    pub at: Vec<usize>,
}

/// The `when~` of `mods` with no condition yet, filled in at their clock W.
pub fn fill(rng: &mut Rng, head: Head, mods: &mut [Mod]) {
    for i in 0..mods.len() {
        if matches!(&mods[i], Mod::When(c) if c.text.is_empty()) {
            mods[i] = Mod::When(cond_at(rng, w_of(head, mods, i)));
        }
    }
}

/// A random rate modifier.
pub fn rate(rng: &mut Rng) -> Mod {
    rng.pick_in(&[Mod::Down(2), Mod::Down(2), Mod::Down(4), Mod::Down(8), Mod::Up(2), Mod::Up(2)]).clone()
}

/// A chain of `len` modifiers, `whens` of them `when~` with no condition yet, and a head of `heads` that fits it.
pub fn chain(rng: &mut Rng, len: usize, whens: usize, heads: &[Head]) -> (Head, Vec<Mod>) {
    loop {
        let mut mods: Vec<Mod> = (0..len).map(|_| rate(rng)).collect();
        for _ in 0..whens {
            let at = rng.below(len);
            mods[at] = Mod::When(Cond::default());
        }
        let fitting: Vec<Head> = heads.iter().copied().filter(|h| fits(*h, &mods)).collect();
        if !fitting.is_empty() {
            return (fitting[rng.below(fitting.len())], mods);
        }
    }
}

/// `X.when~(true)` and `X`: a chain with 0 to 2 `when~` of its own, and one or two that always hold put in at random places.
fn plan_id(rng: &mut Rng, rot: bool) -> Plan {
    loop {
        let len = 1 + rng.below(4);
        let whens = rng.below(3).min(len);
        let (head, mut base) = chain(rng, len, whens, &Head::WEIGHTED);
        fill(rng, head, &mut base);
        let mut fa = base.clone();
        let mut at: Vec<usize> = Vec::new();
        for _ in 0..1 + usize::from(rng.chance(30)) {
            // The places where one more `when~` leaves a chain that U1 runs.
            let places: Vec<usize> = (0..=fa.len())
                .filter(|&p| fits(head, &[&fa[..p], &[Mod::When(Cond::default())], &fa[p..]].concat()))
                .collect();
            let Some(&p) = places.get(rng.below(places.len().max(1))) else { break };
            fa.insert(p, Mod::When(Cond::default()));
            let blk = form_at(head, &fa, p) == Some("in_block");
            let c = if rot { Cond::lit("!ct", "t_mutant") } else { always_true(rng, w_of(head, &fa, p), blk) };
            fa[p] = Mod::When(c);
            at.iter_mut().filter(|a| **a >= p).for_each(|a| *a += 1);
            at.push(p);
        }
        if !at.is_empty() {
            return Plan { kind: "id", head, fa, fb: base, at };
        }
    }
}

/// `x.down~(N).when~(c)` and `x.when~(c).down~(N)`: the head has its input and output at `sample` (no burst, no gather); a
/// `when~` before the pair and one modifier after it are the same in both.
fn plan_commute(rng: &mut Rng, rot: bool) -> Plan {
    loop {
        let head = rng.pick(&[Head::Slot, Head::Tk, Head::Acc, Head::Lp]);
        let mut fa: Vec<Mod> = Vec::new();
        if rng.chance(30) {
            fa.push(Mod::When(Cond::default()));
        }
        let at = fa.len();
        fa.extend([Mod::Down(rng.pick(&[2, 4, 8])), Mod::When(Cond::default())]);
        if rng.chance(40) {
            fa.push(if rng.chance(50) { rate(rng) } else { Mod::When(Cond::default()) });
        }
        if !fits(head, &fa) {
            continue;
        }
        fill(rng, head, &mut fa);
        let mut fb = fa.clone();
        fb.swap(at, at + 1);
        if let (true, Mod::When(c)) = (rot, &fb[at]) {
            fb[at] = Mod::When(c.not());
        }
        if !fits(head, &fb) {
            continue;
        }
        return Plan { kind: "commute", head, fa, fb, at: vec![at, at + 1] };
    }
}

/// Whether two conditions read at the same W inside a block are not the twin of their `&&`: a signal is gathered with the inputs and a
/// value of a `block` kind is read when the run is made, so two modifiers keep them apart, but one expression of both is a signal that
/// is gathered whole, with the `block` value of the call that gathered it (§11.10: the clock of an expression is the fastest of its
/// parts, and a call of `process` that is cut gives the later frames of a tick another value of `cb`).
pub fn kinds_apart(a: &Cond, b: &Cond) -> bool {
    let (sig, blk) = (|c: &Cond| c.tags.contains("c_sig"), |c: &Cond| c.tags.contains("c_block"));
    (sig(a) && !sig(b) && blk(b)) || (sig(b) && !sig(a) && blk(a))
}

/// `x.when~(a).when~(b)` and `x.when~(a && b)`: two `when~` side by side, at the clock W, put in a chain of 0 to 3 modifiers.
fn plan_merge(rng: &mut Rng, rot: bool) -> Plan {
    let len = rng.below(4);
    let whens = rng.below(2).min(len);
    let (head, mut fa, at) = loop {
        let (head, base) =
            if len == 0 { (rng.pick(&Head::ALL), Vec::new()) } else { chain(rng, len, whens, &Head::WEIGHTED) };
        let at = rng.below(base.len() + 1);
        let mut fa = base;
        fa.splice(at..at, [Mod::When(Cond::default()), Mod::When(Cond::default())]);
        if fits(head, &fa) {
            break (head, fa, at);
        }
    };
    let (holes, blk) = (fa.clone(), form_at(head, &fa, at) == Some("in_block"));
    let (a, b) = loop {
        fa = holes.clone();
        fill(rng, head, &mut fa);
        let (Mod::When(a), Mod::When(b)) = (fa[at].clone(), fa[at + 1].clone()) else {
            unreachable!("two when~ were put in")
        };
        if !(blk && kinds_apart(&a, &b)) {
            break (a, b);
        }
    };
    let both = a.join(if rot { "||" } else { "&&" }, &b);
    let mut fb = fa.clone();
    fb.splice(at..at + 2, [Mod::When(both)]);
    Plan { kind: "merge", head, fa, fb, at: vec![at, at + 1] }
}

/// The two chains of the twin `atid` made from a chain with all its conditions filled in: at the modifiers (a `when~` or a `reset_if~`)
/// whose W is `sample` (so that an `at sample` names W, §11.10 and not E0815), a value of the kind `block` or `init` (`cb`, `ci`, now
/// and then negated), with `at sample` in `fa` and without in `fb`. §11.3: the stage of a value that only parameter kinds decide does
/// not change with an `at`, so it is read as it is read without it, also inside a block. With `rot` the one in `fa` is negated.
/// The chains and the places, or `None` if no place has W of `sample` (or none was drawn).
pub fn at_pair(rng: &mut Rng, head: Head, base: &[Mod], rot: bool) -> Option<(Vec<Mod>, Vec<Mod>, Vec<usize>)> {
    let (mut fa, mut fb, mut at) = (base.to_vec(), base.to_vec(), Vec::new());
    for i in (0..base.len()).filter(|&i| base[i].cond().is_some() && w_of(head, base, i) == 0) {
        if !rng.chance(70) {
            continue;
        }
        let (name, kind) = rng.pick(&[("cb", "c_block"), ("ci", "c_init")]);
        let neg = rng.chance(25);
        let plain = Cond::lit(name, kind);
        // A place inside a block is the one where a value that is told from a signal by its stage only is gathered with the inputs.
        let blk = form_at(head, base, i) == Some("in_block");
        let tags = [Some(kind), Some("c_at_sample"), blk.then_some("at_blk")].into_iter().flatten().collect();
        let with = Cond { text: format!("({name} at sample)"), tags, ..Cond::default() };
        let (plain, with) = (if neg { plain.not() } else { plain }, if neg != rot { with.not() } else { with });
        let put = |m: &Mod, c: Cond| if m.is_when() { Mod::When(c) } else { Mod::Reset(c) };
        fa[i] = put(&base[i], with);
        fb[i] = put(&base[i], plain);
        at.push(i);
    }
    (!at.is_empty()).then_some((fa, fb, at))
}

/// `X.when~(p at sample)` and `X.when~(p)` (`p` a `block` or `init` value), in a chain of 1 to 4 modifiers with 1 or 2 `when~`.
fn plan_atid(rng: &mut Rng, rot: bool) -> Plan {
    loop {
        let len = 1 + rng.below(4);
        let whens = 1 + rng.below(2);
        let (head, mut base) = chain(rng, len, whens, &Head::WEIGHTED);
        fill(rng, head, &mut base);
        if let Some((fa, fb, at)) = at_pair(rng, head, &base, rot) {
            return Plan { kind: "atid", head, fa, fb, at };
        }
    }
}

/// The body of a flow for a chain: the `let`s its conditions and its head need, and the chain (wrapped in `g2` or `g4` when
/// it gives a burst, with `at sample` when its output is slower).
pub fn flow_body(head: Head, mods: &[Mod]) -> String {
    let chain = format!("{}{}", head.text().0, mods.iter().map(Mod::text).collect::<String>());
    let conds = || mods.iter().filter_map(Mod::cond);
    let signals: BTreeSet<u32> = conds().flat_map(|c| c.signals.iter().copied()).collect();
    let slow: BTreeSet<u32> = conds().flat_map(|c| c.slow.iter().copied()).collect();
    let mut lets: Vec<String> = signals.iter().map(|n| format!("let c{n} = lb{n}~(c).down~({n})")).collect();
    lets.extend(slow.iter().map(|f| format!("let k{f} = acc~(1.0).down~({f})")));
    match head {
        Head::Lp | Head::Dws => lets.push("let xv = tk~() * 0.25 + (if c { 1.0 } else { -0.5 })".to_string()),
        Head::Sl => lets.push("let q = cnt~().down~(2)".to_string()),
        _ => {}
    }
    let value = match net(head, mods) {
        0 => chain,
        n @ (1 | 2) => format!("g{}~({chain})", 1u32 << n),
        _ => format!("{chain} at sample"),
    };
    lets.into_iter().map(|l| l + "\n  ").collect::<String>() + &value
}

/// The forms a plan holds (the tags that the seeds of the gate have to cover).
pub fn tags_of(plan: &Plan) -> BTreeSet<&'static str> {
    let (head, mods) = (plan.head, &plan.fa);
    let mut tags: BTreeSet<&'static str> = BTreeSet::from([head.text().1]);
    tags.insert(match plan.kind {
        "id" => "k_id",
        "commute" => "k_commute",
        "rid" => "k_rid",
        "atid" => "k_atid",
        "slowc" => "k_slowc",
        "rmerge" => "k_rmerge",
        _ => "k_merge",
    });
    tags.insert(["len_0", "len_1", "len_2", "len_3", "len_4", "len_5", "len_6"][mods.len().min(6)]);
    tags.insert(["when_0", "when_1", "when_2", "when_3", "when_4"][mods.iter().filter(|m| m.is_when()).count().min(4)]);
    tags.insert(match net(head, mods) {
        0 => "o_plain",
        1.. => "o_burst",
        _ => "o_slow",
    });
    let kinds =
        [("m_down2", Mod::Down(2)), ("m_down4", Mod::Down(4)), ("m_down8", Mod::Down(8)), ("m_up2", Mod::Up(2))];
    for (tag, k) in kinds {
        let same = |m: &Mod| matches!((m, &k), (Mod::Down(a), Mod::Down(b)) | (Mod::Up(a), Mod::Up(b)) if a == b);
        if mods.iter().any(same) {
            tags.insert(tag);
        }
    }
    let ups = mods.iter().filter(|m| matches!(m, Mod::Up(_))).count();
    tags.extend((ups >= 2 && mods.iter().any(|m| matches!(m, Mod::Down(_)))).then_some("stacked"));
    for (i, m) in mods.iter().enumerate() {
        let Mod::When(c) = m else { continue };
        tags.extend(c.tags.iter().copied());
        let p: i32 = mods[i + 1..].iter().map(Mod::exp).sum();
        tags.insert(match w_of(head, mods, i) {
            w if w > 0 => "w_pos",
            w if w < p => "w_slow",
            _ => "w_p",
        });
        let up_before = mods[..i].iter().any(|m| matches!(m, Mod::Up(_)));
        tags.extend((up_before && mods[i..].iter().any(|m| matches!(m, Mod::Down(_)))).then_some("in_block"));
        tags.extend((i > 0 && mods[i - 1].is_when()).then_some("double_when"));
        tags.extend(form_at(head, mods, i).map(|f| if f == "in_block" { "blk" } else { "burst_up" }));
        tags.extend((head.out() > 0 && mods[i..].iter().any(|m| matches!(m, Mod::Down(_)))).then_some("deal_when"));
    }
    if matches!(plan.kind, "id" | "rid") {
        let (first, last) = (plan.at.iter().min().copied(), plan.at.iter().max().copied());
        tags.extend((first == Some(0)).then_some("ins_front"));
        tags.extend((last == Some(mods.len() - 1)).then_some("ins_end"));
        tags.extend((first.is_some_and(|f| f > 0) || last.is_some_and(|l| l + 1 < mods.len())).then_some("ins_mid"));
        tags.extend((plan.at.len() == 2).then_some("ins_two"));
    }
    tags
}

/// The values `cb` takes in the parts of a `process`.
pub const BOOLS: &[&str] = &["true", "true", "false"];

/// The tests: `render` of `fa` and `fb` on a grid of `ci` and `cb` (`ct` and `cti` always true), and `process` of both cut at
/// three places with `cb` changing between the parts, a `reset` before the last. Every output of `fa` is asserted equal to the
/// one of `fb`.
pub fn tests(rng: &mut Rng) -> String {
    let signal = |rng: &mut Rng| {
        let mut v = rng.chance(50);
        let bits: Vec<&str> = (0..FRAMES)
            .map(|_| {
                v ^= rng.chance(35);
                if v { "true" } else { "false" }
            })
            .collect();
        bits.join(", ")
    };
    let mut t = format!("test \"render\" {{\n  let cs: [Bool; {FRAMES}] = [{}]\n", signal(rng));
    for (k, (ci, cb)) in [(true, true), (true, false), (false, true)].into_iter().enumerate() {
        for f in ["fa", "fb"] {
            let config = format!("{f}.Config {{ ci: {ci}, cti: true, cfi: false }}");
            let params = format!("{f}.Params {{ cb: {cb}, ct: true, cf: false }}");
            t += &format!("  let {f}{k} = {f}.render({config}, {params}, cs, 8.0)\n");
        }
        (0..FRAMES).for_each(|i| t += &format!("  assert fa{k}.out[{i}] == fb{k}.out[{i}]\n"));
    }
    t += &format!("}}\ntest \"chunks\" {{\n  let cs: [Bool; {FRAMES}] = [{}]\n", signal(rng));
    for n in 0..3 {
        let (a, b) = (rng.below(FRAMES + 1), rng.below(FRAMES + 1));
        let spans = [(0, a.min(b)), (a.min(b), a.max(b)), (a.max(b), FRAMES)];
        let ci = rng.chance(50);
        let cbs: Vec<&str> = spans.iter().map(|_| rng.pick(BOOLS)).collect();
        for f in ["fa", "fb"] {
            t += &format!("  var s{f}{n} = {f}.init({f}.Config {{ ci: {ci}, cti: true, cfi: false }}, 8.0)\n");
            for (m, ((from, to), cb)) in spans.iter().zip(&cbs).enumerate() {
                t += &if m == 2 { format!("  {f}.reset(inout s{f}{n})\n") } else { String::new() };
                t += &format!("  var o{f}{n}_{m}: [F32; {0}] = [0.0; {0}]\n", to - from);
                t += &format!(
                    "  {f}.process(inout s{f}{n}, {f}.Params {{ cb: {cb}, ct: true, cf: false }}, cs.slice({from}, {to}), inout o{f}{n}_{m})\n"
                );
            }
        }
        for (m, (from, to)) in spans.iter().enumerate() {
            (0..to - from).for_each(|i| t += &format!("  assert ofa{n}_{m}[{i}] == ofb{n}_{m}[{i}]\n"));
        }
    }
    t + "}\n"
}

/// The program of a plan: the flows `fa` and `fb` and the tests.
pub fn program(rng: &mut Rng, plan: &Plan) -> String {
    let flow = |name: &str, mods: &[Mod]| {
        format!("pub flow {name}{SIGNATURE} -> F32 at sample {{\n  {}\n}}\n", flow_body(plan.head, mods))
    };
    format!("{HEADER}{}{}{}", flow("fa", &plan.fa), flow("fb", &plan.fb), tests(rng))
}

/// The program of a seed (with `rot`, the mutant of the twin: an inserted condition that never holds, a condition that is
/// negated, `||` for `&&`), and the forms it holds.
pub fn make(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let plan = match rng.below(12) {
        0..=4 => plan_id(&mut rng, rot),
        5..=7 => plan_commute(&mut rng, rot),
        8 | 9 => plan_merge(&mut rng, rot),
        _ => plan_atid(&mut rng, rot),
    };
    (program(&mut rng, &plan), tags_of(&plan))
}

/// A case of the matrix of `exotic_cases`: the head, the chain, the place of the `when~` and its condition.
type Case = (Head, Vec<Mod>, usize, &'static str);

/// The matrix of the twin `id` that the breaker of U1 went over (a burst with blocks inside it gave 0 and an internal error):
/// every chain of `.up~(2)`, `.down~(2)` and `.down~(4)` of one to four, with a `when~` that always holds (`true`, or a `block`
/// value) put in at every place that U1 runs, over the heads `tk` and `slot`.
fn exotic_cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| {
        let letters = [Mod::Up(2), Mod::Down(2), Mod::Down(4)];
        let (mut level, mut chains) = (vec![Vec::new()], Vec::new());
        for _ in 0..4 {
            level = level
                .iter()
                .flat_map(|c: &Vec<Mod>| letters.iter().map(move |l| [c.clone(), vec![l.clone()]].concat()))
                .collect();
            chains.extend(level.clone());
        }
        let with = |base: &[Mod], p: usize| [&base[..p], &[Mod::When(Cond::default())], &base[p..]].concat();
        let mut cases = Vec::new();
        for head in [Head::Tk, Head::Slot] {
            for base in chains.iter().filter(|c| in_range(head, c)) {
                for p in (0..=base.len()).filter(|&p| fits(head, &with(base, p))) {
                    cases.extend(["true", "ct"].map(|c| (head, base.clone(), p, c)));
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

/// The program of the matrix that a seed picks (with `rot`, the condition never holds), and the forms it holds.
pub fn make_exotic(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let cases = exotic_cases();
    let (head, base, p, text) = cases[seed as usize % cases.len()].clone();
    let mut fa = base.clone();
    fa.insert(
        p,
        Mod::When(Cond::lit(if rot { "!ct" } else { text }, if text == "true" { "t_lit" } else { "t_block" })),
    );
    let plan = Plan { kind: "id", head, fa, fb: base, at: vec![p] };
    (program(&mut Rng::new(seed), &plan), tags_of(&plan))
}

/// Every chain of up to `len` modifiers with a `when~` over every head, that is in range: what it is, its program (the flow `fa`
/// only), and which form `form` says it is. The condition of a `when~` is the signal at W when `cond` is `sig` and W is `sample` or
/// slower, otherwise `cond` (an `init` input, `ci`).
pub fn chains(len: usize, cond: &str) -> Vec<(String, String, Option<&'static str>)> {
    let words = [Mod::Down(2), Mod::Down(4), Mod::Up(2), Mod::When(Cond::default())];
    let mut all: Vec<Vec<Mod>> = vec![Vec::new()];
    let mut frontier = all.clone();
    for _ in 0..len {
        frontier =
            frontier.iter().flat_map(|c| words.iter().map(move |w| [c.clone(), vec![w.clone()]].concat())).collect();
        all.extend(frontier.clone());
    }
    let mut out = Vec::new();
    for head in Head::ALL {
        for mods in all.iter().filter(|m| m.iter().any(Mod::is_when) && in_range(head, m)) {
            let mut mods = mods.clone();
            for i in 0..mods.len() {
                if mods[i].is_when() {
                    let w = w_of(head, &mods, i);
                    let sig = cond == "sig" && w <= 0;
                    mods[i] = Mod::When(if sig {
                        Cond::signal(w)
                    } else {
                        Cond::lit(if cond == "sig" { "ci" } else { cond }, "")
                    });
                }
            }
            let text: String = mods.iter().map(Mod::text).collect();
            let src = format!("{HEADER}pub flow fa{SIGNATURE} -> F32 at sample {{\n  {}\n}}\n", flow_body(head, &mods));
            out.push((format!("{}{text}", head.text().0), src, form(head, &mods)));
        }
    }
    out
}
