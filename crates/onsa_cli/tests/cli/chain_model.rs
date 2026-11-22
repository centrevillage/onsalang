//! The values of a chain of `.down~` and `.up~` over a head with a gathered port, a dealt output, a slow stage, a counter, the time and the rate are those of a model written from the spec (W7-16 U7c/t; spec §11.9,
//! §11.10 "a modifier wraps the whole of its left", §11.4 `sample_tick()` and `sample_rate()` of a part, §11.3 hold; S-1207, S-1214, S-1217; `rules/leader.md` 4.9: the model of the review of U6b, put in as a
//! small set from a fixed seed).
//!
//! The model (`Part`) reads the chain from the inside, as the spec's rule says and not as a table of the compiler: a head runs its stages from the slowest; a `.down~(N)` runs its left every N-th frame with the time
//! divided by N, gathers the port of the left into a ring (the window of the frames before, as it was before this frame) and deals the output of the left over the next N frames; a `.up~(N)` runs its left N times
//! with the time `N t + j`, a window of the port to each run, and puts the outputs together. A value is the list of its elements (a scalar has one).
//!
//! A form: a head `h` (the port `k` and the output `m` as the exponent of `sample * 2^k`, a counter of a slower clock, the time and the rate read at the output stage), a chain of 1 to 4 boundaries (`ratios`: below 0 a
//! `.down~(2^-r)`, above 0 an `.up~(2^r)`), a caller `top` that passes `b<q>~(x)` (a burst), `x` or a slow counter, the argument written in the call (`acc~(x)`, `(x +% prev~(x))`, a slow flow `ctr3~()`) or as a name,
//! and `process` in 1 to 4 pieces with a `reset` between some. The expected output of its `test` is the model's for each piece from a reset. The sample rate is 2^20, so the rate of the head is exact. The gate runs 40
//! forms of a fixed seed in one file (the `test` of the interpreter, in this process, no file written, `rules/common.md` 3.7); `heavy_` runs 1000. The harness is checked by the model with one order broken (a window
//! written to the ring before the left reads it): the forms it changes then fail.

use std::fmt::Write as _;
use std::num::Wrapping as W;

use crate::slow_written_forms::run_texts;
use crate::test_support::sweep::Rng;
use crate::test_support::{diagnostics, doc_of, record, str_of, tests_of};

const RATE: u32 = 1 << 20;
type V = Vec<u32>;

fn no_port() -> V {
    panic!("a part without a port read one")
}

/// The place and the length in an array of the window at the phase `ph`, where the array has `2^e` elements per frame (`e` below 0: one element for `2^-e` frames).
fn slot(ph: usize, e: i32) -> (usize, usize) {
    if e > 0 { (ph << e, 1 << e) } else { (ph >> -e, 1) }
}

/// The sum of the elements, the j-th by j + 1 (what `r<N>` and the head write).
fn weighted(v: &[u32]) -> W<u32> {
    v.iter().enumerate().fold(W(0), |a, (j, &e)| a + W(e) * W(j as u32 + 1))
}

enum Part {
    Head { f: Form, n: u64, last: V, cnt: u32, tau: u32, val: V },
    Down { x: Box<Part>, n: i32, ring: V, deal: V, val: V },
    Up { x: Box<Part>, u: i32 },
}

impl Part {
    fn down(x: Part, n: i32) -> Part {
        let ring = vec![0; x.k().filter(|&k| k > 0).map_or(0, |k| 1 << k)];
        let deal = vec![0; if x.m() > 0 { 1 << x.m() } else { 0 }];
        Part::Down { x: Box::new(x), n, ring, deal, val: V::new() }
    }

    fn k(&self) -> Option<i32> {
        match self {
            Part::Head { f, .. } => f.k,
            Part::Down { x, n, .. } => x.k().map(|k| k - n),
            Part::Up { x, u } => x.k().map(|k| k + u),
        }
    }

    fn m(&self) -> i32 {
        match self {
            Part::Head { f, .. } => f.m,
            Part::Down { x, n, .. } => x.m() - n,
            Part::Up { x, u } => x.m() + u,
        }
    }

    /// The value of the part at its time `c`, with `port` the value of its port. `ring_first` breaks one order (a control): the ring is written before the left reads it.
    fn tick(&mut self, c: u64, port: &dyn Fn() -> V, ring_first: bool) -> V {
        match self {
            Part::Head { f, n, last, cnt, tau, val } => {
                assert_eq!(c, *n, "the head runs at its own count");
                for x in f.stages().into_iter().filter(|&x| c % (1u64 << -x) == 0) {
                    *cnt += u32::from(Some(x) == f.extra);
                    if Some(x) == f.in_stage() {
                        *last = port();
                    }
                    if x == f.out_stage() {
                        *tau += 1;
                        let mut b = W(*tau) * W(1000003);
                        b += if f.obs_cnt() { W(*cnt) * W(977) } else { W(0) };
                        b += if f.obs_in() { weighted(last) * W(31) } else { W(0) };
                        b += if f.time { W(c as u32) * W(13) } else { W(0) };
                        b += if f.rate { W(f.head_rate()) * W(5) } else { W(0) };
                        *val = (0..1u32 << f.m.max(0)).map(|i| (b + W(7919 * i)).0).collect();
                    }
                }
                *n += 1;
                val.clone()
            }
            Part::Down { x, n, ring, deal, val } => {
                let (n, ph, xk, xm) = (*n, (c & ((1u64 << *n) - 1)) as usize, x.k(), x.m());
                let fill = |ring: &mut V| {
                    let Some(e) = xk.filter(|&k| k > 0).map(|k| k - n) else { return };
                    if c % (1u64 << (-e).max(0)) == 0 {
                        let (at, len) = slot(ph, e);
                        ring[at..at + len].copy_from_slice(&port());
                    }
                };
                if ring_first {
                    fill(ring);
                }
                if ph == 0 {
                    let snap = ring.clone();
                    let gathered = || snap.clone();
                    let from: &dyn Fn() -> V = match xk {
                        None => &no_port,
                        Some(k) if k > 0 => &gathered,
                        Some(_) => port,
                    };
                    let out = x.tick(c >> n, from, ring_first);
                    *if xm > 0 { &mut *deal } else { &mut *val } = out;
                }
                if !ring_first {
                    fill(ring);
                }
                let (at, len) = slot(ph, xm - n);
                if xm > 0 { deal[at..at + len].to_vec() } else { val.clone() }
            }
            Part::Up { x, u } => {
                let (u, kx, mx) = (*u, x.k(), x.m());
                let outs: Vec<V> = (0..1usize << u)
                    .map(|j| {
                        let window = || match kx {
                            None => no_port(),
                            Some(k) if k >= 0 => port()[j << k..(j + 1) << k].to_vec(),
                            Some(k) if k + u > 0 => vec![port()[j >> -k]],
                            Some(_) => port(),
                        };
                        x.tick((c << u) | j as u64, &window, ring_first)
                    })
                    .collect();
                if mx >= 0 {
                    outs.concat()
                } else if mx + u > 0 {
                    (0..1usize << (mx + u)).map(|i| outs[i << -mx][0]).collect()
                } else {
                    outs[0].clone()
                }
            }
        }
    }
}

// ---- the forms

/// How `top` writes its argument (when it passes one).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Arg {
    Name,
    Acc,
    PrevSum,
    SlowCall,
}

#[derive(Clone, Debug)]
struct Form {
    k: Option<i32>,
    m: i32,
    extra: Option<i32>,
    ratios: Vec<i32>,
    at_sample: bool,
    time: bool,
    rate: bool,
    arg: Arg,
    /// The calls of `process`: the number of frames of each, and 0 for a `reset`.
    events: Vec<usize>,
}

impl Form {
    fn in_stage(&self) -> Option<i32> {
        self.k.map(|k| k.min(0))
    }
    fn out_stage(&self) -> i32 {
        self.m.min(0)
    }
    /// The slow stages the head runs, slowest first, then `sample`.
    fn stages(&self) -> Vec<i32> {
        let mut s: Vec<i32> =
            [self.in_stage(), Some(self.out_stage()), self.extra].into_iter().flatten().filter(|&x| x < 0).collect();
        s.extend([0]);
        s.sort();
        s.dedup();
        s
    }
    fn obs_in(&self) -> bool {
        self.in_stage().is_some_and(|s| s <= self.out_stage())
    }
    fn obs_cnt(&self) -> bool {
        self.extra.is_some_and(|s| s <= self.out_stage())
    }
    fn sum(&self) -> i32 {
        self.ratios.iter().sum()
    }
    /// The exponents of the port and of the output as the caller sees them.
    fn q(&self) -> Option<i32> {
        self.k.map(|k| k + self.sum())
    }
    fn o(&self) -> i32 {
        self.m + self.sum()
    }
    /// The rate of the head: the rate of `init` times the chain.
    fn head_rate(&self) -> u32 {
        if self.sum() >= 0 { RATE << self.sum() } else { RATE >> -self.sum() }
    }
    fn ok(&self) -> bool {
        self.q().is_none_or(|q| (-5..=4).contains(&q))
            && (-5..=4).contains(&self.o())
            && self.ratios.iter().map(|r| r.abs()).sum::<i32>() <= 5
    }
    fn frames(&self) -> usize {
        self.events.iter().sum()
    }
    /// The input of the frames: the same for the source and the model.
    fn inputs(&self, i: usize) -> V {
        (0..self.frames()).map(|p| ((p * 7 + 3 + i) % 1000) as u32).collect()
    }

    /// The values of the argument `top` writes (`x`, `acc~(x)`, ...) at each frame of a piece whose input is `xs`.
    fn written(&self, xs: &[u32]) -> V {
        match self.arg {
            Arg::Acc => xs
                .iter()
                .scan(W(0), |a, &x| {
                    *a += W(x);
                    Some(a.0)
                })
                .collect(),
            Arg::PrevSum => (0..xs.len()).map(|i| xs[i].wrapping_add(if i > 0 { xs[i - 1] } else { 0 })).collect(),
            Arg::Name | Arg::SlowCall => xs.to_vec(),
        }
    }

    /// What `top` passes to the head at the frame `p`: `b<q>~(w)` gives `4 w + i` for a burst, a slow counter is the number of the slow tick (and is read only at the slow ticks).
    fn caller_arg(&self, written: &[u32], p: usize) -> V {
        let q = self.q().expect("a port");
        assert!(q >= 0 || p % (1 << -q) == 0, "a slow port read at {p}");
        match q {
            0 => vec![written[p]],
            q if q > 0 => (0..1u32 << q).map(|i| written[p].wrapping_mul(4).wrapping_add(i)).collect(),
            q => vec![(p >> -q) as u32 + 1],
        }
    }
}

fn draw(rng: &mut Rng) -> Form {
    loop {
        let len = *rng.pick(&[1usize, 2, 2, 3, 3, 4]);
        let mut ratios: Vec<i32> =
            (0..len).map(|_| if rng.chance(40) { 1 + rng.below(4) as i32 } else { -*rng.pick(&[1, 1, 2]) }).collect();
        if ratios.iter().all(|&r| r < 0) && !rng.chance(15) {
            ratios[rng.below(len)] = 1 + rng.below(4) as i32;
        }
        let mut f = Form {
            k: *rng.pick(&[None, Some(-2), Some(-1), Some(0), Some(1), Some(2), Some(3)]),
            m: *rng.pick(&[-2, -1, 0, 0, 1, 2, 3]),
            extra: *rng.pick(&[None, None, Some(-1), Some(-2)]),
            ratios,
            at_sample: rng.chance(60),
            time: rng.chance(30),
            rate: rng.chance(30),
            arg: Arg::Name,
            events: Vec::new(),
        };
        if !f.ok() {
            continue;
        }
        // A counter that the output stage does not read is an unused `let` (E0309): it is not written.
        f.extra = f.extra.filter(|_| f.obs_cnt());
        f.arg = match f.q() {
            Some(q) if q >= 0 => *rng.pick(&[Arg::Name, Arg::Name, Arg::Acc, Arg::PrevSum]),
            Some(_) => *rng.pick(&[Arg::Name, Arg::SlowCall]),
            None => Arg::Name,
        };
        for _ in 0..rng.range(1, 4) {
            if !f.events.is_empty() && rng.chance(25) {
                f.events.push(0);
            }
            f.events.push(*rng.pick(&[1, 3, 7, 8, 16, 21, 32]));
        }
        return f;
    }
}

/// The output of form `i` for its input: the model's values of `top` for each piece from a reset.
fn expected(f: &Form, i: usize, ring_first: bool) -> V {
    let (xs, mut out, mut at) = (f.inputs(i), V::new(), 0);
    for piece in f.events.split_inclusive(|&e| e == 0) {
        let n: usize = piece.iter().sum();
        let written = f.written(&xs[at..at + n]);
        at += n;
        let mut part = Part::Head { f: f.clone(), n: 0, last: V::new(), cnt: 0, tau: 0, val: V::new() };
        for &r in &f.ratios {
            part = if r < 0 { Part::down(part, -r) } else { Part::Up { x: Box::new(part), u: r } };
        }
        let (o, mut res) = (part.m(), Vec::new());
        for p in 0..n {
            let port = || if f.q().is_some() { f.caller_arg(&written, p) } else { no_port() };
            let v = part.tick(p as u64, &port, ring_first);
            if p % (1usize << -o.min(0)) == 0 {
                assert!(!v.is_empty(), "no value at the frame {p}");
                res.push(v);
            }
        }
        out.extend((0..n).map(|p| weighted(&res[p >> -o.min(0)]).0));
    }
    out
}

// ---- the source

fn clk(x: i32) -> String {
    match x {
        0 => "sample".into(),
        x if x > 0 => format!("(sample * {})", 1 << x),
        x => format!("(sample / {})", 1 << -x),
    }
}

fn prelude() -> String {
    let mut s = String::new();
    for n in 1..=4 {
        let list = |f: &dyn Fn(usize) -> String, sep| (0..1usize << n).map(f).collect::<Vec<_>>().join(sep);
        let _ = writeln!(
            s,
            "flow b{n}(x: U32 at sample) -> U32 at {} {{ [{}] }}",
            clk(n),
            list(&|i| format!("x *% 4 +% {i}"), ", ")
        );
        let _ = writeln!(
            s,
            "flow r{n}(x: U32 at {}) -> U32 at sample {{ {} }}",
            clk(n),
            list(&|j| format!("(x[{j}] *% {})", j + 1), " +% ")
        );
    }
    s += "flow acc(x: U32 at sample) -> U32 at sample {\n  let n = prev~(^n at sample) +% x\n  n\n}\n";
    for j in 1..=5 {
        let _ =
            writeln!(s, "flow ctr{j}() -> U32 at {0} {{\n  let n = prev~(^n at {0}) +% (1 at {0})\n  n\n}}", clk(-j));
    }
    s
}

fn head_src(i: usize, f: &Form) -> String {
    let oc = clk(f.out_stage());
    let mut lets = format!("  let n = prev~(^n at {oc}) +% (1 at {oc})\n");
    if let Some(e) = f.extra {
        let _ = writeln!(lets, "  let cn = prev~(^cn at {0}) +% (1 at {0})", clk(e));
    }
    let mut terms = vec!["(n *% 1000003)".to_string()];
    terms.extend(f.obs_cnt().then(|| format!("((cn at {oc}) *% 977)")));
    if f.obs_in() {
        let k = f.k.expect("a port");
        let bundle: Vec<String> = (0..1 << k.max(0)).map(|j| format!("(x[{j}] *% {})", j + 1)).collect();
        terms.push(if k > 0 { format!("(({}) *% 31)", bundle.join(" +% ")) } else { format!("((x at {oc}) *% 31)") });
    }
    if f.time {
        terms.push(if f.m < 0 { format!("((sample_tick() at {oc}) *% 13)") } else { "(sample_tick() *% 13)".into() });
    }
    terms.extend(f.rate.then(|| "(U32.trunc_sat_from(sample_rate()) *% 5)".to_string()));
    let base = terms.join(" +% ");
    let out = if f.m > 0 {
        format!("[{}]", (0..1u32 << f.m).map(|j| format!("({base}) +% {}", 7919 * j)).collect::<Vec<_>>().join(", "))
    } else {
        format!("({base})")
    };
    let ins = f.k.map_or(String::new(), |k| format!("x: U32 at {}", clk(k)));
    format!("flow h{i}({ins}) -> U32 at {} {{\n{lets}  {out}\n}}\n", clk(f.m))
}

fn top_src(i: usize, f: &Form) -> String {
    let (mut pre, mut args) = (String::new(), String::new());
    if let Some(q) = f.q() {
        let x = match f.arg {
            Arg::Acc => "acc~(x)",
            Arg::PrevSum => "(x +% prev~(x))",
            _ => "x",
        };
        args = match q {
            q if q > 0 => format!("b{q}~({x})"),
            0 => x.to_string(),
            q if f.arg == Arg::SlowCall => format!("ctr{}~()", -q),
            q => {
                pre = format!("  let sc = prev~(^sc at {0}) +% (1 at {0})\n", clk(q));
                "sc".into()
            }
        };
    }
    let chain: String = f
        .ratios
        .iter()
        .map(|&r| if r < 0 { format!(".down~({})", 1 << -r) } else { format!(".up~({})", 1 << r) })
        .collect();
    let call = format!("h{i}~({args}){chain}");
    let call = match f.o() {
        o if o > 0 => format!("r{o}~({call})"),
        o if o < 0 || f.at_sample => format!("{call} at sample"),
        _ => call,
    };
    format!("pub flow top{i}(x: U32 at sample) -> U32 at sample {{\n{pre}  {call}\n}}\n")
}

/// The flows and the test of form `i`, whose expected output is the model's.
fn form_src(i: usize, f: &Form, ring_first: bool) -> String {
    let list = |v: &[u32]| v.iter().map(u32::to_string).collect::<Vec<_>>().join(", ");
    let n = f.frames();
    let mut t = format!(
        "test \"f{i}\" {{\n  let xs: [U32; {n}] = [{}]\n  var out: [U32; {n}] = [9999; {n}]\n",
        list(&f.inputs(i))
    );
    let _ = writeln!(t, "  var st = top{i}.init({RATE}.0)");
    let mut at = 0;
    for &len in &f.events {
        let _ = match len {
            0 => writeln!(t, "  top{i}.reset(inout st)"),
            _ => writeln!(t, "  top{i}.process(inout st, xs.slice({at}, {0}), inout out.slice({at}, {0}))", at + len),
        };
        at += len;
    }
    format!("{}{}{t}  assert out == [{}]\n}}\n", head_src(i, f), top_src(i, f), list(&expected(f, i, ring_first)))
}

/// Run the forms in one file, with the expectations of the model (or of the one with a broken order); the forms that did not pass, with their text.
fn failures(forms: &[(usize, Form)], ring_first: bool) -> Vec<String> {
    let srcs: Vec<String> = forms.iter().map(|(i, f)| form_src(*i, f, ring_first)).collect();
    let text = prelude() + &srcs.concat();
    let out = run_texts(&["test", "--json"], &text);
    assert!(!out.stderr.contains("internal error"), "internal error: {}\n{text}", out.stderr);
    let doc = doc_of(&out);
    assert!(diagnostics(&doc).is_empty(), "diagnostics: {}\n{text}", out.stdout);
    assert_eq!(tests_of(&doc).len(), forms.len(), "every form is run: {}", out.stdout);
    let passed = |i: usize| str_of(record(&doc, "m", &format!("f{i}")), "status") == "ok";
    (0..forms.len())
        .filter(|&j| !passed(forms[j].0))
        .map(|j| format!("form {} {:?}:\n{}", forms[j].0, forms[j].1, srcs[j]))
        .collect()
}

// ---- the sets

/// `count` forms of the seed, numbered from `from`.
fn forms_of(seed: u64, from: usize, count: usize) -> Vec<(usize, Form)> {
    let mut rng = Rng::new(seed);
    (0..from + count).map(|i| (i, draw(&mut rng))).skip(from).collect()
}

/// The shapes of a form, each with whether the form has it.
fn shapes(f: &Form) -> Vec<(&'static str, bool)> {
    let l = f.ratios.len();
    let (mut kb, mut mb, mut gather, mut deal) = (f.k, f.m, false, false);
    for &r in &f.ratios {
        gather |= r < 0 && kb.is_some_and(|k| k > 0);
        deal |= r < 0 && mb > 0;
        (kb, mb) = (kb.map(|k| k + r), mb + r);
    }
    vec![
        ("an up first", f.ratios[0] > 0),
        ("an up in the middle", f.ratios.iter().enumerate().any(|(j, &r)| r > 0 && j > 0 && j + 1 < l)),
        ("an up last", l > 1 && f.ratios[l - 1] > 0),
        ("three boundaries or more", l >= 3),
        ("a gather", gather),
        ("a deal", deal),
        ("a burst argument", f.q().is_some_and(|q| q > 0)),
        ("a burst output", f.o() > 0),
        ("a slow argument", f.q().is_some_and(|q| q < 0)),
        ("a slow output", f.o() < 0),
        ("a head with a slow stage", f.m < 0 || f.k.is_some_and(|k| k < 0)),
        ("a counter of a slow clock", f.extra.is_some()),
        ("the time", f.time),
        ("the rate", f.rate),
        ("an argument written in the call", matches!(f.arg, Arg::Acc | Arg::PrevSum)),
        ("a slow flow written as the argument", f.arg == Arg::SlowCall),
        ("a reset between pieces", f.events.contains(&0)),
    ]
}

/// The seed was chosen from those whose 40 forms have every shape (`the_forms_of_the_gate_have_every_shape`); a change of the draw asks for a new seed.
const SEED: u64 = 0;

fn gate_forms() -> Vec<(usize, Form)> {
    forms_of(SEED, 0, 40)
}

/// The forms of the gate have each shape.
#[test]
fn the_forms_of_the_gate_have_every_shape() {
    let forms = gate_forms();
    for (j, (shape, _)) in shapes(&forms[0].1).iter().enumerate() {
        assert!(
            forms.iter().any(|(_, f)| shapes(f)[j].1),
            "no form of the seed {SEED} has {shape}; the seed must be revised"
        );
    }
}

/// A chain over a head gives the values of the model: 40 forms.
#[test]
fn the_values_of_drawn_chains_are_the_models() {
    let bad = failures(&gate_forms(), false);
    assert!(
        bad.is_empty(),
        "{} forms differ from the model (seed {SEED}):\n{}",
        bad.len(),
        bad[..bad.len().min(2)].join("\n")
    );
}

/// The harness tells: with the expectations of the model that writes the ring before the left reads it, the forms where that changes the values fail.
#[test]
fn a_model_with_one_order_broken_fails_the_forms_it_changes() {
    let changed: Vec<(usize, Form)> =
        gate_forms().into_iter().filter(|(i, f)| expected(f, *i, true) != expected(f, *i, false)).collect();
    assert!(!changed.is_empty(), "no form of the gate has a value that the broken order changes");
    assert_eq!(failures(&changed, true).len(), changed.len(), "a form that the broken model changes passed");
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_the_values_of_many_drawn_chains_are_the_models() {
    for batch in 0..25 {
        let bad = failures(&forms_of(1, 40 * batch, 40), false);
        assert!(
            bad.is_empty(),
            "batch {batch}: {} forms differ from the model:\n{}",
            bad.len(),
            bad[..bad.len().min(2)].join("\n")
        );
    }
}
