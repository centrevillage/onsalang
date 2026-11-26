//! Flows made at random with their twins (W7-20 U1): `fa` writes a chain of `if~` as it is, `fb` writes it as the definition
//! of §11.5 says (each branch in a `let` before, then a plain `if` that selects), so that the two give the same outputs
//! (the evaluator asserts it, and the interpreter is compared with what the evaluator gave through `compare_one`). A seed
//! makes one program, from a plan (a tree, not a text) that both writings print; the seeds of the gate are fixed.

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::case::repo_root;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::pending::Pending;

use super::shrink::{LIMITS, MISSING_PANIC, OUT_OF_STAGES, UNEXPECTED_PANIC, class_of, shrink, without_a_line};
use super::twin_match::{self, EXTRA};
use super::{Compared, Tally, compare_one, failures, tally_case};

/// splitmix64, as `sweep.rs` of the CLI tests writes it (a seed means a program).
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x2545_F491_4F6C_DD1D).wrapping_add(0x9E37_79B9_7F4A_7C15))
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    pub fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }

    pub fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        *self.pick_in(xs)
    }

    pub fn pick_in<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

pub const HEADER: &str = "pub flow acc(x: F32 at sample) -> F32 at sample {
  let y = x + prev~(^y)
  y
}
pub flow shift(x: F32 at sample, n: U32 at init) -> F32 at sample { x + F32.round_from(n) }
pub flow scale(x: F32 at sample, k: F32 at block) -> F32 at sample { x * k }
pub flow twice(x: F32 at sample) -> F32 at sample { x * 2.0 }
pub flow ifnest(x: F32 at sample) -> F32 at sample {
  if~ x > 0.25 { acc~(1.0) } else { x }
}
pub rt fn sum2(a: [F32; 2]) -> F32 { a[0] + a[1] }
";
pub const SIGNATURE: &str = "(x: F32 at sample, k: U32 at block, ki: I32 at block, n: U32 at init)";

// The forms of the plan, by their tag (the gate asserts its seeds hold the tags of `COVER`). `{s}` is a stateless expression
// of the sample, `{l}` a literal, `{i}` a small number, `{j}` a small signed one, `{c}` a float to compare with; `IDX` is the
// index of a `par~` (a name in `fa`, its number in each copy of `fb`), and a form that has it is made in a `par~` only.
const SEXPRS: &[&str] = &[
    "x",
    "x * 2.0",
    "x + 1.0",
    "0.5 - x",
    "F32.round_from(k) + x",
    "x * F32.round_from(n)",
    "x + F32.round_from(ki)",
    "x * F32.round_from(IDX)",
    "x + F32.round_from(IDX) * 0.25",
];
#[rustfmt::skip]
const STATEFUL: &[(&str, &str)] = &[
    ("acc", "acc~({s})"), ("prev", "prev~({s})"), ("prev_init", "prev~({s}, {l})"), ("delay", "delay~({s}, 2)"),
    ("delay_init", "delay~({s}, 2, {l})"), ("scale", "scale~({s}, F32.round_from(k) * 0.5)"), ("shift", "shift~({s}, n + {i})"),
    ("twice", "twice~({s})"), ("ifnest", "ifnest~({s})"), ("comb", "(acc~(x) + prev~({s})) * 0.5"), ("inst", "prev~(acc~({s}))"),
    ("par", "sum2(par~ jj in 0 ..< 2 { acc~(x * F32.round_from(jj + 1)) })"),
    ("scale_idx", "scale~(x, F32.round_from(k + IDX))"), ("shift_idx", "shift~(x, n + IDX)"),
    ("acc_idx", "acc~(x * F32.round_from(IDX + 1))"), ("prev_idx", "prev~(x + F32.round_from(IDX))"),
];
#[rustfmt::skip]
const STATELESS: &[(&str, &str)] = &[
    ("lit", "{l}"), ("guarded", "if k != 0 { x / F32.round_from(k) } else { 0.0 }"), ("block_div", "x * F32.round_from(10 / (k + 1))"),
    ("init_in", "x * F32.round_from(n + 1)"), ("expr", "{s}"),
];
#[rustfmt::skip]
const CONDS: &[(&str, &str)] = &[
    ("x_gt", "x > {c}"), ("x_lt", "x < {c}"), ("k_gt", "k > {i}"), ("k_eq", "k == {i}"), ("ki_gt", "ki > {j}"), ("n_gt", "n > {i}"),
    ("and", "x > {c} && k > {i}"), ("or", "x > {c} || k == {i}"), ("and_paren", "(k > {i}) && (x != {c})"),
    ("ki_or_n", "ki < {j} || n == {i}"), ("idx_eq", "IDX == 1"), ("idx_gt", "IDX > 0"), ("idx_div", "10 / (IDX + 1) > 3"),
    ("idx_x", "x > F32.round_from(IDX) * 0.5"), ("idx_k", "k > IDX"),
];
const STATE_CONDS: &[&str] = &["prev~(x) > 0.0", "acc~(x) > 2.0", "prev~(x * 2.0) < 0.5"];
/// How the program is wrapped around the chain (`{}`); the last wraps it in a `par~`.
#[rustfmt::skip]
pub const WRAPS: &[(&str, &str)] = &[
    ("wrap_direct", "{}"), ("wrap_let", "let r = ({})\n  r"), ("wrap_twice", "twice~({})"), ("wrap_half", "0.5 * ({})"),
    ("wrap_prev", "prev~({})"), ("wrap_delay", "delay~({}, 2)"), ("wrap_par", ""),
];
/// The ranges of a `par~`, with the numbers its index takes.
#[rustfmt::skip]
pub const RANGES: &[(&str, &[usize])] = &[("0 ..< 2", &[0, 1]), ("0 ..< 3", &[0, 1, 2]), ("1 ..= 3", &[1, 2, 3]), ("2 ..< 5", &[2, 3, 4])];
const XS: &[&str] = &["-1.0", "-0.5", "0.0", "0.25", "0.5", "1.0", "2.0"];

/// The plan of a branch: an expression of a text, or a chain of `if~` (a condition for each branch but the last).
enum Body {
    Leaf(String),
    If(Vec<String>, Vec<Body>),
    /// A `match~` (as `fa` writes it), the `let`s of its twin and the value they end in.
    Match(String, Vec<String>, String),
}

impl Body {
    /// As `fa` writes it.
    fn fa(&self) -> String {
        match self {
            Body::Leaf(t) | Body::Match(t, ..) => t.clone(),
            Body::If(conds, arms) => {
                let chain: String = (conds.iter().zip(arms).enumerate())
                    .map(|(n, (c, a))| format!("if{} {c} {{ {} }} else ", if n == 0 { "~" } else { "" }, a.fa()))
                    .collect();
                format!("{chain}{{ {} }}", arms[arms.len() - 1].fa())
            }
        }
    }

    /// As `fb` writes it: the `let`s of the branches go to `lets`, the value is the plain `if` that selects. A branch is
    /// bound to `v<n><suffix>`. With `rot` the chain selects the next branch (the mutant that the gate has to catch).
    fn fb(&self, (suffix, n): (&str, &mut usize), lets: &mut Vec<String>, rot: bool) -> String {
        let (conds, arms) = match self {
            Body::If(conds, arms) => (conds, arms),
            Body::Match(_, ls, v) => {
                let (ls, v) = rename(ls, v, suffix);
                lets.extend(ls);
                return v;
            }
            Body::Leaf(t) => return t.clone(),
        };
        let names: Vec<String> = (arms.iter())
            .map(|a| {
                let e = a.fb((suffix, &mut *n), lets, rot);
                *n += 1;
                lets.push(format!("let v{n}{suffix} = {e}"));
                format!("v{n}{suffix}")
            })
            .collect();
        let at = |i: usize| &names[if rot { (i + 1) % names.len() } else { i }];
        let chain: String = conds.iter().enumerate().map(|(i, c)| format!("if {c} {{ {} }} else ", at(i))).collect();
        format!("{chain}{{ {} }}", at(names.len() - 1))
    }
}

struct Gen {
    rng: Rng,
    /// Whether the chain is in a `par~`, and may read its index.
    idx: bool,
    tags: BTreeSet<&'static str>,
    /// What the bindings of the arm of a `match~` around the chain are, as floats (a form may read them).
    env: Vec<String>,
    /// The `match~` that a branch may be (none in an arm of a `match~`, which is as deep as the plan goes).
    m: Option<twin_match::Gen>,
}

impl Gen {
    /// A form of `table` (one with `IDX` only in a `par~`), its `{..}` filled in, with its tag (kept by whoever uses the text:
    /// a tag is of what is in the program).
    fn form(&mut self, table: &[(&'static str, &str)]) -> (&'static str, String) {
        let usable: Vec<_> = table.iter().filter(|(_, t)| self.idx || !t.contains("IDX")).collect();
        let &(tag, t) = self.rng.pick(&usable);
        let bound =
            (!self.env.is_empty() && self.rng.chance(25)).then(|| format!("x + {}", self.rng.pick_in(&self.env)));
        self.tags.extend((bound.is_some() && t.contains("{s}")).then_some("bind_arg"));
        let t = &t.replace("{s}", bound.as_deref().unwrap_or("{s}"));
        let sexprs: Vec<_> = SEXPRS.iter().filter(|t| self.idx || !t.contains("IDX")).copied().collect();
        let sets: [(&str, &[&str]); 5] = [
            ("{s}", &sexprs),
            ("{l}", &["0.0", "1.0", "-1.0", "0.5", "3.0"]),
            ("{i}", &["0", "1", "2"]),
            ("{j}", &["-1", "0", "1"]),
            ("{c}", &["0.0", "0.5", "-0.5", "1.0"]),
        ];
        (tag, sets.iter().fold(t.to_string(), |out, (key, set)| out.replace(key, self.rng.pick(set))))
    }

    fn cond(&mut self, first: bool) -> (&'static str, String) {
        if !self.env.is_empty() && self.rng.chance(30) {
            return ("cond_bind", format!("{} > 0.5", self.rng.pick_in(&self.env)));
        }
        if !(first && self.rng.chance(30)) {
            return self.form(CONDS);
        }
        ("state_cond", self.rng.pick(STATE_CONDS).to_string())
    }

    /// A branch: a chain of its own (the plan is three chains deep at most) or a leaf, with a state when `need`.
    fn body(&mut self, depth: usize, need: bool) -> Body {
        if let Some(m) = self.m.as_mut().filter(|_| self.rng.chance(6)) {
            let (fa, lets, value) = m.nested();
            self.tags.insert("match_in_if");
            return Body::Match(fa, lets, value);
        }
        if depth < 2 && self.rng.chance(25) {
            self.tags.insert("nested");
            return self.chain(depth + 1);
        }
        let stateful = need || self.rng.chance(50);
        let (tag, text) = self.form(if stateful { STATEFUL } else { STATELESS });
        self.tags.insert(tag);
        Body::Leaf(text)
    }

    /// A chain of 2 to 4 branches. A state is in one of the branches (a chain with none is E0812), and a state in a
    /// condition only in the first (E0811). Of three or more, half guard a division by a `block` or `init` input.
    fn chain(&mut self, depth: usize) -> Body {
        let n = self.rng.pick(&[2, 2, 3, 4]);
        self.tags.insert(["chain2", "chain3", "chain4"][n - 2]);
        let mut conds: Vec<_> = (0..n - 1).map(|i| self.cond(i == 0)).collect();
        if n >= 3 && self.rng.chance(50) {
            let v = self.rng.pick(&["k", "n"]);
            let second = ["10 / {} > 2", "(10 / {}) < 3 && x > 0.0", "x > 0.0 || 10 / {} > 4"][self.rng.below(3)];
            conds[..2].clone_from_slice(&[("guard", format!("{v} == 0")), ("guard", second.replace("{}", v))]);
        }
        self.tags.extend(conds.iter().map(|c| c.0));
        let conds = conds.into_iter().map(|c| c.1).collect();
        let with_state = self.rng.below(n);
        Body::If(conds, (0..n).map(|i| self.body(depth, i == with_state)).collect())
    }
}

/// The program of a seed (with `rot`, the mutant of `fb`).
pub fn make(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut g = Gen { rng: Rng::new(seed), idx: false, tags: BTreeSet::new(), env: Vec::new(), m: None };
    let w = g.rng.below(WRAPS.len());
    let par = WRAPS[w].0 == "wrap_par";
    (g.idx, g.m) = (par, Some(twin_match::Gen::new(seed ^ 0x5EED, false, par)));
    let chain = g.chain(0);
    g.tags.insert(WRAPS[w].0);
    let (mut lets, (range, elems)) = (Vec::new(), g.rng.pick(RANGES));
    let (fa, fb, out) = if par {
        let names: Vec<String> = (elems.iter().enumerate())
            .map(|(p, e)| {
                let from = lets.len();
                let b = chain.fb((&format!("_{e}"), &mut 0), &mut lets, rot);
                lets.push(format!("let r{p} = {b}"));
                lets[from..].iter_mut().for_each(|l| *l = l.replace("IDX", &e.to_string()));
                format!("r{p}")
            })
            .collect();
        let (fa, fb, out) =
            (chain.fa().replace("IDX", "i"), format!("[{}]", names.join(", ")), format!("[F32; {}]", elems.len()));
        (format!("par~ i in {range} {{ {fa} }}"), fb, out)
    } else {
        let b = chain.fb(("", &mut 0), &mut lets, rot);
        (WRAPS[w].1.replace("{}", &chain.fa()), WRAPS[w].1.replace("{}", &b), "F32".to_string())
    };
    let fb = format!("{}\n  {fb}", lets.join("\n  "));
    let (helpers, held) = g.m.take().map(twin_match::Gen::done).unwrap_or_default();
    g.tags.extend(held);
    in_par(par, &mut g.tags);
    let head = format!("{HEADER}{EXTRA}{helpers}");
    (program(&mut g.rng, &head, (&fa, &fb, &out), par.then_some(elems.len())), g.tags)
}

/// A chain of `if~` for an arm of a `match~` that reads the floats `env` (what its bindings are): as `fa` writes it, the `let`s
/// of its twin (the names they bind end in `sfx`) and the value they end in, and the forms it holds.
pub fn chain_in(
    seed: u64,
    idx: bool,
    env: Vec<String>,
    sfx: &str,
) -> (String, Vec<String>, String, BTreeSet<&'static str>) {
    let mut g = Gen { rng: Rng::new(seed), idx, tags: BTreeSet::new(), env, m: None };
    let (chain, mut lets) = (g.chain(1), Vec::new());
    let value = chain.fb((sfx, &mut 0), &mut lets, false);
    (chain.fa(), lets, value, g.tags)
}

/// The forms of a program that is a `par~` are in the `par~`: the tags of the forms that matter there are tagged again.
pub fn in_par(par: bool, tags: &mut BTreeSet<&'static str>) {
    const IN: [(&str, &str); 7] = [
        ("nif", "par_nif"),
        ("parm", "par_parm"),
        ("nmatch", "par_nmatch"),
        ("match_in_if", "par_match_in_if"),
        ("prev_b", "par_prev_b"),
        ("delay_b", "par_delay_b"),
        ("struct_bind_state", "par_struct_bind_state"),
    ];
    let held: Vec<_> = IN.iter().filter(|(t, _)| par && tags.contains(t)).map(|(_, p)| *p).collect();
    tags.extend(held);
}

fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// The `lets` and the `value` of a copy (of a `par~`, or of a form that is written more than once): every name that the `lets`
/// bind ends in `sfx`, so that the copies bind a name each.
pub fn rename(lets: &[String], value: &str, sfx: &str) -> (Vec<String>, String) {
    let bound: Vec<&str> =
        (lets.iter()).filter_map(|l| l.strip_prefix("let ")?.split(|c| !is_word(c)).next()).collect();
    let one = |t: &str| -> String {
        t.split_inclusive(|c| !is_word(c))
            .map(|p| {
                let (w, sep) = p.split_at(p.find(|c| !is_word(c)).unwrap_or(p.len()));
                format!("{w}{}{sep}", if bound.contains(&w) { sfx } else { "" })
            })
            .collect()
    };
    (lets.iter().map(|l| one(l)).collect(), one(value))
}

/// The program of the flows `fa` and `fb` (their bodies and their type; with `elems`, the type is the array of the copies of a
/// `par~`, which two flows `ga` and `gb` add up), after `head`, and its tests.
pub fn program(rng: &mut Rng, head: &str, (fa, fb, out): (&str, &str, &str), elems: Option<usize>) -> String {
    let flows = format!(
        "pub flow fa{SIGNATURE} -> {out} at sample {{\n  {fa}\n}}\npub flow fb{SIGNATURE} -> {out} at sample {{\n  {fb}\n}}\n"
    );
    let sum = |f: &str| {
        let terms: Vec<_> = (0..elems.unwrap_or(0)).map(|c| format!("r[{c}] * {}.0", 2 * c + 1)).collect();
        format!(
            "pub flow g{f}{SIGNATURE} -> F32 at sample {{\n  let r = f{f}~(x, k, ki, n)\n  {}\n}}\n",
            terms.join(" + ")
        )
    };
    let adds = if elems.is_some() { sum("a") + &sum("b") } else { String::new() };
    let named = if elems.is_some() { ("ga", "gb") } else { ("fa", "fb") };
    format!("{head}{flows}{adds}{}", tests(rng, elems, named))
}

/// The tests of a program (`channels` is the length of the array of a `par~`): `render` of `fa` and `fb` on a grid of the
/// `block` and `init` inputs; and `process` of `flows` (`fa` and `fb`, or for a `par~` the flows that add up its array, which
/// the evaluator does not take as a planar buffer) over three parts of the input (a part may be empty, each into a buffer of
/// its own) with the inputs changing, and a `reset` before the last.
pub fn tests(rng: &mut Rng, channels: Option<usize>, flows: (&str, &str)) -> String {
    let xs = |rng: &mut Rng| (0..6).map(|_| rng.pick(XS)).collect::<Vec<_>>().join(", ");
    let (chans, at) = (channels.unwrap_or(1), |c: usize| channels.map_or(String::new(), |_| format!("[{c}]")));
    let mut t = format!("test \"render\" {{\n  let xs: [F32; 6] = [{}]\n", xs(rng));
    for (n, k) in [(0, 0), (0, 2), (1, 1), (1, 3), (2, 0), (2, 1)] {
        let ki = rng.below(5) as i32 - 2;
        for f in ["fa", "fb"] {
            let (config, params) = (format!("{f}.Config {{ n: {n} }}"), format!("{f}.Params {{ k: {k}, ki: {ki} }}"));
            t += &format!("  let {f}{n}{k} = {f}.render({config}, {params}, xs, 8.0)\n");
        }
        for (i, c) in (0..6).flat_map(|i| (0..chans).map(move |c| (i, c))) {
            t += &format!("  assert fa{n}{k}.out{0}[{i}] == fb{n}{k}.out{0}[{i}]\n", at(c));
        }
    }
    t += &format!("}}\ntest \"chunks\" {{\n  let xs: [F32; 6] = [{}]\n", xs(rng));
    for n in [0, 1, 2] {
        let (a, b) = (rng.below(7), rng.below(7));
        let spans = [(0, a.min(b)), (a.min(b), a.max(b)), (a.max(b), 6)];
        let params: Vec<String> = (spans.iter())
            .map(|_| format!("k: {}, ki: {}", rng.pick(&[0, 1, 2, 3, 5]), rng.below(6) as i32 - 2))
            .collect();
        for (f, s, o) in [(flows.0, "sa", "oa"), (flows.1, "sb", "ob")] {
            t += &format!("  var {s}{n} = {f}.init({f}.Config {{ n: {n} }}, 8.0)\n");
            for (m, ((from, to), p)) in spans.iter().zip(&params).enumerate() {
                t += &if m == 2 { format!("  {f}.reset(inout {s}{n})\n") } else { String::new() };
                t += &format!("  var {o}{n}_{m}: [F32; {0}] = [0.0; {0}]\n", to - from);
                t += &format!(
                    "  {f}.process(inout {s}{n}, {f}.Params {{ {p} }}, xs.slice({from}, {to}), inout {o}{n}_{m})\n"
                );
            }
        }
        for (m, (from, to)) in spans.iter().enumerate() {
            (0..to - from).for_each(|i| t += &format!("  assert oa{n}_{m}[{i}] == ob{n}_{m}[{i}]\n"));
        }
    }
    t + "}\n"
}

/// How a seed makes a program (with the mutant of `fb` when `rot`), and the forms that the program holds.
pub type Maker = fn(u64, bool) -> (String, BTreeSet<&'static str>);
/// A family of twins: its name (the failure says how to run it again) and how its seeds make programs.
pub type Family = (&'static str, Maker);

/// What a run of seeds came to, summed.
#[derive(Debug, Default)]
pub struct Stats {
    pub programs: usize,
    pub tests: usize,
    pub evaluated: usize,
    pub asserts: usize,
    pub compared: usize,
    pub compared_asserts: usize,
}

/// A program run on the evaluator and, unless `rot`, through the interpreter: what was counted, and what is wrong with it.
fn one(pending: &Pending, wrappers: &Wrappers, path: &str, src: &str, rot: bool) -> (Tally, Compared, Vec<String>) {
    let input = PackageInput::single_file(path, src);
    let (mut t, mut c) = (Tally::default(), Compared::default());
    tally_case(&mut t, pending, wrappers, (path, path), input.clone());
    let mut why = failures(&t);
    let left = t.waiting + t.unavailable.values().sum::<usize>() + t.skipped.values().sum::<usize>();
    why.extend((left > 0).then(|| format!("{left} tests were not evaluated: {:?} {:?}", t.unavailable, t.skipped)));
    if !rot && why.is_empty() {
        compare_one(&mut c, wrappers, path, input);
        why.append(&mut c.failures);
        why.extend(
            (!c.unprintable.is_empty() || c.panicked > 0)
                .then(|| format!("not printed {:?}, panicked {}", c.unprintable, c.panicked)),
        );
    }
    (t, c, why)
}

/// The seeds run on the evaluator and, unless `rot`, through the interpreter: the numbers, and a message (the family, the seed,
/// the forms the program holds, the kind of failure, the program shrunk, how to run it again) for each seed with anything wrong. What
/// the generator makes has to be read, evaluated and printed: a form that the checker, the evaluator or the printer does not
/// take is the generator's failure, never dropped. Only the first three failures of a part are shrunk.
/// The seeds of a `heavy_` run are cut into parts run side by side ([`in_parts`]), joined in the order of the seeds.
pub fn run(seeds: Vec<u64>, family: Family, rot: bool) -> (Stats, Vec<String>) {
    let (mut s, mut bad) = (Stats::default(), Vec::new());
    for (p, b) in in_parts(seeds, |part| run_part(part, family, rot)) {
        (s.programs, s.tests, s.evaluated, s.asserts) =
            (s.programs + p.programs, s.tests + p.tests, s.evaluated + p.evaluated, s.asserts + p.asserts);
        (s.compared, s.compared_asserts) = (s.compared + p.compared, s.compared_asserts + p.compared_asserts);
        bad.extend(b);
    }
    (s, bad)
}

/// `f` on parts of `seeds` in threads side by side, one part for each 25 seeds up to the cores (the seeds of the gate are one
/// part), the results in the order of the seeds: the `heavy_` runs of hundreds of seeds are the longest of the gate item.
pub fn in_parts<T: Send>(seeds: Vec<u64>, f: impl Fn(Vec<u64>) -> T + Sync) -> Vec<T> {
    let cores = std::thread::available_parallelism().map_or(1, usize::from);
    let size = seeds.len().div_ceil((seeds.len() / 25).clamp(1, cores)).max(1);
    let f = &f;
    std::thread::scope(|sc| {
        let parts: Vec<_> = seeds.chunks(size).map(|c| c.to_vec()).map(|c| sc.spawn(move || f(c))).collect();
        parts.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
    })
}

fn run_part(seeds: Vec<u64>, (family, make): Family, rot: bool) -> (Stats, Vec<String>) {
    stack::run(move || {
        let (pending, wrappers) =
            (Pending::load(&repo_root()).expect("the list of things pending"), Wrappers::default());
        let (mut s, mut bad) = (Stats::default(), Vec::new());
        for seed in seeds {
            let (src, tags) = make(seed, rot);
            let path = format!("seed_{seed}.onsa");
            let (t, c, why) = one(&pending, &wrappers, &path, &src, rot);
            (s.programs, s.tests, s.evaluated, s.asserts) =
                (s.programs + 1, s.tests + t.tests, s.evaluated + t.evaluated, s.asserts + t.asserts);
            (s.compared, s.compared_asserts) = (s.compared + c.ran, s.compared_asserts + c.asserts);
            if !why.is_empty() {
                let class = class_of(&why[0]);
                let kind = |m: &String| one(&pending, &wrappers, &path, m, rot).2.first().map(|w| class_of(w));
                let small =
                    (!rot && bad.len() < 3).then(|| shrink(src, class, LIMITS, |s: &String| without_a_line(s), kind));
                bad.push(report(family, Some(seed), &tags, class, &why, small.as_ref().map(|(s, n)| (s.as_str(), *n))));
            }
        }
        (s, bad)
    })
}

/// The message of a failing seed (`None` is a form written by hand): its family and forms, the kind of failure and its text,
/// the program (shrunk, after `tries` candidates), and the command that runs the seed again.
pub fn report(
    family: &str,
    seed: Option<u64>,
    tags: &BTreeSet<&str>,
    class: &str,
    why: &[String],
    shown: Option<(&str, usize)>,
) -> String {
    let (head, again) = match seed {
        Some(s) => (
            format!("seed {s}"),
            format!(
                "ONSA_FLOW_GEN={s}..{} cargo test -p onsa_tests --test flow_ref -- --ignored heavy_{family} --nocapture",
                s + 1
            ),
        ),
        None => ("a form written by hand".to_string(), "cargo test -p onsa_tests --test flow_ref".to_string()),
    };
    // What the plan finds wrong (`twin_pan.rs`) is not what `onsa test` shows of the program: a scene that panics is a test that failed.
    let plan = [UNEXPECTED_PANIC, MISSING_PANIC, OUT_OF_STAGES].contains(&class).then_some(
        "(a failure by the plan does not come again in `onsa test`: it shows a test that panicked as failed, not what the plan says of it)\n",
    );
    let program = shown.map_or("(shown for the first three failures only)".to_string(), |(src, tries)| {
        format!("{}the program, shrunk in {tries} tries:\n{src}", plan.unwrap_or_default())
    });
    format!(
        "{head} ({family}), forms {tags:?}, failure `{class}`: {}\n{program}\nrun it again: {again}",
        why.join("\n")
    )
}
