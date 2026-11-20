//! A drawn sweep of the unused bindings of a flow body against a model of the reach of the spec (§5.1, §18.1, S-129, S-716, S-726, S-727,
//! S-1146; W7-14 U5, from the sweep of the break side of U5, `gen.py`).
//!
//! §5.1: "flow の本体でも同じに数え、さらに、参照されていても出力と `let _` から辿れない `let` が使われない束縛である（`^` の帰還だけで互いを
//! 参照する組も含む）. E0309 の位置は使われない束縛の名前である。E0309 は §18.1 の最後の段で、同じ単位に他の誤りがあれば報告しない". The model:
//! the consumers are the output and the `let`s that bind no name (`let _`, `let (_, _)`, `let Pair { l: _, r: _ }`); a `let` is reached when it is a
//! consumer or one of its names is read by the output or by a reached `let`, a read being a name in the text (`n`, `n[1]`, and `^n` of a `prev~` or a
//! `delay~`, which reads the name of a `let` that is the same or below it); a name that is read by nothing reached is unused, and the unit reports
//! the first of them in the order of the source, once. The model is a fixed point over the whole table of the reads (a pass over every `let` until
//! none is added), where the work list of the `reached` of the implementation is not.
//!
//! The flows are drawn with a fixed seed: lets of one name, of a tuple (all of its names, the first, the second, or none), of a `Pair` pattern, of a
//! `par~` (an array), of a constant, and `let _`; expressions of the inputs and of the names above, sums, `at`, `prev~`, `delay~`, `vdelay~` (with a
//! `^` of the same or a later name), `tap~` (an instance), `if`, `match` (an arm that binds a name and is read), `clip` and `pr`; half of the flows
//! are dense (the lets read the names just above). A flow that is no E0309 and gets another diagnostic is a fault of the generator. The bodies are
//! kept in memory (`check_input`, no file written: `rules/common.md` 3.7).

use crate::test_support;

use std::collections::BTreeSet;

use test_support::sweep::{Rng, Texts, check_input, ended_well, input_of};

const PRELUDE: &str = "pub struct Pair { l: F32, r: F32 }\n\
pub flow split(x: F32 at sample) -> Pair at sample { Pair { l: x, r: x * 0.5 } }\n\
pub flow tap(x: F32 at sample) -> F32 at sample { prev~(x) }\n\
pub rt fn clip(v: F32, hi: F32) -> F32 { if v > hi { hi } else { v } }\n\
pub rt fn pr(a: F32, b: F32) -> (F32, F32) { (a, b) }\n";

const INPUTS: [&str; 4] = ["x", "y", "p", "q"];

/// An expression: its text and the names it reads.
type Expr = (String, BTreeSet<String>);

struct Gen<'a> {
    rng: &'a mut Rng,
    /// The names of the `let`s written so far, and whether the name is an array.
    avail: Vec<(String, bool)>,
    arms: usize,
}

/// One `let`: its line, the names it binds and the names it reads.
struct Let {
    line: String,
    names: Vec<String>,
    reads: BTreeSet<String>,
}

impl Gen<'_> {
    fn atom(&mut self) -> Expr {
        let n = self.avail.len() + INPUTS.len();
        let i = self.rng.below(n);
        if i < self.avail.len() {
            let (name, arr) = self.avail[i].clone();
            let text = if arr { format!("{name}[1]") } else { name.clone() };
            (text, BTreeSet::from([name]))
        } else {
            (INPUTS[i - self.avail.len()].to_string(), BTreeSet::new())
        }
    }

    fn expr(&mut self, depth: usize, state_ok: bool, fb: &[String]) -> Expr {
        if depth == 0 || self.rng.chance(25) {
            return self.atom();
        }
        let k = self.rng.below(100);
        let join = |a: &BTreeSet<String>, b: &BTreeSet<String>| a.union(b).cloned().collect::<BTreeSet<_>>();
        if k < 35 {
            let (a, ra) = self.expr(depth - 1, state_ok, fb);
            let (b, rb) = self.expr(depth - 1, state_ok, fb);
            let op = *self.rng.pick(&["+", "*", "-"]);
            (format!("({a} {op} {b})"), join(&ra, &rb))
        } else if k < 45 {
            let (a, ra) = self.expr(depth - 1, state_ok, fb);
            (format!("(({a} + x) at sample)"), ra)
        } else if k < 60 && state_ok {
            self.delay(depth, fb)
        } else if k < 70 && state_ok {
            let (a, ra) = self.expr(depth - 1, state_ok, fb);
            (format!("tap~({a})"), ra)
        } else if k < 80 {
            let (c, rc) = self.expr(depth - 1, state_ok, fb);
            let (a, ra) = self.expr(depth - 1, false, &[]);
            let (b, rb) = self.expr(depth - 1, false, &[]);
            (format!("(if {c} > 0.5 {{ {a} }} else {{ {b} }})"), join(&join(&rc, &ra), &rb))
        } else if k < 88 {
            let (s, rs) = self.expr(depth - 1, state_ok, fb);
            let (a, ra) = self.expr(depth - 1, false, &[]);
            let (g, rg) = self.expr(depth - 1, false, &[]);
            let (b, rb) = self.expr(depth - 1, false, &[]);
            self.arms += 1;
            let v = format!("m{}", self.arms);
            (
                format!("(match {s} {{ {v} if {g} > 0.5 => {v} + {a}, _ => {b} }})"),
                join(&join(&rs, &ra), &join(&rg, &rb)),
            )
        } else if k < 95 {
            let (a, ra) = self.expr(depth - 1, false, &[]);
            let (b, rb) = self.expr(depth - 1, false, &[]);
            (format!("clip({a}, {b})"), join(&ra, &rb))
        } else {
            let (a, ra) = self.expr(depth - 1, state_ok, fb);
            let (b, rb) = self.expr(depth - 1, state_ok, fb);
            (format!("(pr({a}, {b}).0)"), join(&ra, &rb))
        }
    }

    /// A delay: a `prev~`, `delay~` or `vdelay~` of an expression promoted to `sample`, or of a `^` of a name of the same or a later `let`.
    fn delay(&mut self, depth: usize, fb: &[String]) -> Expr {
        let mut form = self.rng.below(7);
        if form >= 4 && fb.is_empty() {
            form = 0;
        }
        if form >= 4 {
            let n = self.rng.pick(fb).clone();
            let (a, ra) = self.expr(depth - 1, false, &[]);
            let (inner, mut reads) = if self.rng.chance(50) {
                (format!("(^{n} * 0.5 + {a})"), ra)
            } else {
                (format!("^{n}"), BTreeSet::new())
            };
            reads.insert(n);
            let text = if form == 6 { format!("delay~({inner}, 4)") } else { format!("prev~({inner})") };
            return (text, reads);
        }
        let (a, ra) = self.expr(depth - 1, false, &[]);
        match form {
            0 => (format!("prev~((({a} + x) at sample))"), ra),
            1 => (format!("delay~((({a} + x) at sample), 4)"), ra),
            2 => (format!("prev~((({a} + x) at sample), 0.5)"), ra),
            _ => {
                let (d, rd) = self.expr(1, false, &[]);
                (format!("vdelay~((({a} + x) at sample), (({d} + x) at sample), 16)"), ra.union(&rd).cloned().collect())
            }
        }
    }

    /// A `let` of the kind `k`; its names are `v{i}` and the like. A value that a `^` may read is made at `sample` (`+ x`), as a delay needs.
    fn make_let(&mut self, i: usize, k: usize, shape: usize, fb: &[String], dense: bool) -> Let {
        let nm = format!("v{i}");
        let recent: Vec<String> =
            self.avail.iter().filter(|(_, arr)| !arr).map(|(n, _)| n.clone()).rev().take(2).collect();
        let chain = |g: &mut Gen, e: Expr| -> Expr {
            if dense && !recent.is_empty() && g.rng.chance(70) {
                let n = g.rng.pick(&recent).clone();
                let mut r = e.1;
                r.insert(n.clone());
                return (format!("({} + {n})", e.0), r);
            }
            e
        };
        let sampled = |e: Expr| -> Expr { (format!("({} + x)", e.0), e.1) };
        match k {
            // a scalar
            0..=4 => {
                let d = *self.rng.pick(&[0, 1, 2, 2]);
                let e = self.expr(d, true, fb);
                let e = sampled(chain(self, e));
                Let { line: format!("  let {nm}: F32 = {}", e.0), names: vec![nm], reads: e.1 }
            }
            // `let _`
            5 => {
                let d = *self.rng.pick(&[1, 2]);
                let e = self.expr(d, true, fb);
                let e = chain(self, e);
                Let { line: format!("  let _: F32 = {}", e.0), names: vec![], reads: e.1 }
            }
            // a tuple: both names, the first, the second
            6 | 7 => {
                let e1 = self.expr(1, true, fb);
                let e2 = self.expr(1, true, fb);
                let (e1, e2) = (sampled(e1), sampled(e2));
                let (a, b) = (format!("{nm}a"), format!("{nm}b"));
                let reads: BTreeSet<String> = e1.1.union(&e2.1).cloned().collect();
                let t = shape;
                let (pat, names) = if t < 70 {
                    (format!("({a}, {b})"), vec![a, b])
                } else if t < 85 {
                    (format!("({a}, _)"), vec![a])
                } else {
                    (format!("(_, {b})"), vec![b])
                };
                Let { line: format!("  let {pat}: (F32, F32) = ({}, {})", e1.0, e2.0), names, reads }
            }
            // a pattern of a struct, from an instance
            8 | 9 => {
                let e = self.expr(1, true, fb);
                let e = sampled(chain(self, e));
                if shape < 15 {
                    Let { line: format!("  let Pair {{ l: _, r: _ }} = split~({})", e.0), names: vec![], reads: e.1 }
                } else {
                    let l = format!("{nm}l");
                    Let { line: format!("  let Pair {{ l: {l}, r: _ }} = split~({})", e.0), names: vec![l], reads: e.1 }
                }
            }
            // `let (_, _)`: it binds no name
            10 => {
                let e1 = self.expr(1, true, fb);
                let e2 = self.expr(1, true, fb);
                let reads = e1.1.union(&e2.1).cloned().collect();
                Let { line: format!("  let (_, _): (F32, F32) = ({}, {})", e1.0, e2.0), names: vec![], reads }
            }
            // a `par~` (an array of three), written `par` when the body holds nothing with state (§11.5, S-1177)
            11 | 12 => {
                let e = self.expr(1, true, &[]);
                let text = if self.rng.chance(50) { format!("({} + F32.round_from(i))", e.0) } else { e.0 };
                let tilde = if text.contains("~(") { "~" } else { "" };
                Let {
                    line: format!("  let {nm}: [F32; 3] = par{tilde} i in 0 ..< 3 {{ {text} }}"),
                    names: vec![nm],
                    reads: e.1,
                }
            }
            // a constant, of a constant name above sometimes
            _ => {
                let consts: Vec<String> =
                    self.avail.iter().filter(|(n, _)| n.starts_with("k")).map(|(n, _)| n.clone()).collect();
                let name = format!("k{i}");
                if !consts.is_empty() && self.rng.chance(50) {
                    let n = self.rng.pick(&consts).clone();
                    Let {
                        line: format!("  let {name}: F32 = {n} * 2.0"),
                        names: vec![name],
                        reads: BTreeSet::from([n]),
                    }
                } else {
                    Let { line: format!("  let {name}: F32 = 1.0 + 2.0"), names: vec![name], reads: BTreeSet::new() }
                }
            }
        }
    }
}

/// One flow: its source (the head, the lets, the output, the closing brace), the lets, and the names that the output reads.
struct Flow {
    lets: Vec<Let>,
    out: Expr,
    index: usize,
}

fn flow(rng: &mut Rng, index: usize) -> Flow {
    let n = rng.range(2, 9);
    let dense = rng.chance(50);
    let kinds: Vec<usize> = (0..n).map(|_| rng.below(14)).collect();
    // The shape of a tuple (the names it binds) and of a `Pair` pattern, decided before the names are planned.
    let shapes: Vec<usize> = (0..n).map(|_| rng.below(100)).collect();
    // The names each let will bind that a `^` may read (a scalar's, a tuple's, a pair's): the same let's and the later ones.
    let plan: Vec<Vec<String>> = kinds
        .iter()
        .enumerate()
        .map(|(i, &k)| match k {
            0..=4 => vec![format!("v{i}")],
            6 | 7 if shapes[i] < 70 => vec![format!("v{i}a"), format!("v{i}b")],
            6 | 7 if shapes[i] < 85 => vec![format!("v{i}a")],
            6 | 7 => vec![format!("v{i}b")],
            8 | 9 if shapes[i] >= 15 => vec![format!("v{i}l")],
            _ => vec![],
        })
        .collect();
    let mut g = Gen { rng, avail: Vec::new(), arms: 0 };
    let mut lets = Vec::new();
    for (i, &k) in kinds.iter().enumerate() {
        let fb: Vec<String> = if g.rng.chance(60) { vec![] } else { plan[i..].iter().flatten().cloned().collect() };
        let l = g.make_let(i, k, shapes[i], &fb, dense);
        for name in &l.names {
            g.avail.push((name.clone(), k == 11 || k == 12));
        }
        lets.push(l);
    }
    let count = if dense { *g.rng.pick(&[1, 2]) } else { *g.rng.pick(&[1, 1, 2, 3]) };
    let (mut texts, mut reads) = (Vec::new(), BTreeSet::new());
    for _ in 0..count {
        let d = *g.rng.pick(&[0, 1, 1, 2]);
        let e = g.expr(d, false, &[]);
        texts.push(e.0);
        reads.extend(e.1);
    }
    // A third of the flows read every name in the output: the flows with no name unused.
    if g.rng.chance(35) {
        for (name, arr) in g.avail.clone() {
            texts.push(if arr { format!("{name}[0]") } else { name.clone() });
            reads.insert(name);
        }
    }
    Flow { lets, out: (texts.join(" + "), reads), index }
}

impl Flow {
    fn source(&self) -> String {
        let mut s = format!(
            "pub flow f{}(x: F32 at sample, y: F32 at sample, p: F32 at block, q: F32 at init) -> F32 at sample {{\n",
            self.index
        );
        for l in &self.lets {
            s.push_str(&l.line);
            s.push('\n');
        }
        s.push_str(&format!("  {}\n}}\n", self.out.0));
        s
    }

    /// The names the model calls unused, in the order of the source: the fixed point of the reached lets.
    fn unused(&self) -> Vec<(usize, String)> {
        // A let is reached when it binds no name, or when one of its names is read by the output or by a reached let.
        let mut reached: Vec<bool> = self.lets.iter().map(|l| l.names.is_empty()).collect();
        loop {
            let mut read: BTreeSet<&String> = self.out.1.iter().collect();
            for (l, r) in self.lets.iter().zip(&reached) {
                if *r {
                    read.extend(l.reads.iter());
                }
            }
            let mut grown = false;
            for (l, r) in self.lets.iter().zip(reached.iter_mut()) {
                if !*r && l.names.iter().any(|n| read.contains(n)) {
                    *r = true;
                    grown = true;
                }
            }
            if !grown {
                let mut out = Vec::new();
                for (k, l) in self.lets.iter().enumerate() {
                    for n in &l.names {
                        if !read.contains(n) {
                            out.push((k, n.clone()));
                        }
                    }
                }
                return out;
            }
        }
    }
}

/// A package of `per` flows drawn from `seed`: what the check says of each against the model. Returns the flows, those with an unused name and the faults.
fn run(seed: u64, per: usize) -> (usize, usize, usize, Vec<String>) {
    let mut rng = Rng::new(seed);
    let flows: Vec<Flow> = (0..per).map(|i| flow(&mut rng, i)).collect();
    let mut src = PRELUDE.to_string();
    let mut start = Vec::new();
    for f in &flows {
        src.push('\n');
        start.push(src.lines().count() as u64 + 1);
        src.push_str(&f.source());
    }
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), src.clone());
    let checked = check_input(&input_of("demo", &texts));
    assert!(ended_well(&checked), "seed {seed}: check did not end as a check does:\n{}", checked.stderr);
    let mut faults = Vec::new();
    for x in checked.diags.iter().filter(|x| x.code != "E0309") {
        faults.push(format!("seed {seed}: {} at {}:{}: {}", x.code, x.line, x.col, x.message));
    }
    if !faults.is_empty() {
        return (per, 0, 0, faults);
    }
    let (mut flagged, mut cut, mut bad) = (0, 0, Vec::new());
    for (f, &s) in flows.iter().zip(&start) {
        let end = s + f.lets.len() as u64 + 2;
        let mine: Vec<_> = checked.diags.iter().filter(|x| s <= x.line && x.line <= end).collect();
        let unused = f.unused();
        match unused.first() {
            None => {
                if !mine.is_empty() {
                    bad.push(format!("seed {seed} f{}: no name is unused, got {:?}\n{}", f.index, mine, f.source()));
                }
            }
            Some((k, name)) => {
                flagged += 1;
                // The name is read, by a `let` that no consumer reaches (a chain of them, or a `^` pair that only reads each other).
                cut += f.lets.iter().any(|l| l.reads.contains(name)) as usize;
                let line = s + 1 + *k as u64;
                let col = f.lets[*k].line.find(name.as_str()).unwrap() as u64 + 1;
                if mine.len() != 1 || (mine[0].line, mine[0].col) != (line, col) {
                    let got: Vec<_> = mine.iter().map(|x| (x.line, x.col)).collect();
                    bad.push(format!(
                        "seed {seed} f{}: expected `{name}` at {line}:{col}, got {got:?}\n{}",
                        f.index,
                        f.source()
                    ));
                }
            }
        }
    }
    (per, flagged, cut, bad)
}

#[test]
fn the_first_unused_name_of_a_flow_is_the_first_unreached_one() {
    let (mut flows, mut flagged, mut cut, mut bad) = (0, 0, 0, Vec::new());
    for seed in 0..20 {
        let (n, f, c, b) = run(seed, 10);
        flows += n;
        flagged += f;
        cut += c;
        bad.extend(b);
    }
    assert!(bad.is_empty(), "{} mismatches:\n{}", bad.len(), bad.join("\n"));
    // The draw has both sides: flows with a name that is unused and flows with none.
    assert!(flows == 200 && flagged > 40 && flows - flagged > 40, "{flows} flows, {flagged} with an unused name");
    assert!(cut > 20, "{cut} flows with a name that is read only by a `let` that is not reached");
}
