//! The table of the chains of boundaries (W7-21 U2, S-1207, S-1214): what a flow with an input at `sample * 2^k` or an output at `sample * 2^m` (k, m = -2 .. 2) gives when it is run by a chain of any
//! length of `.down~(N)` and `.up~(N)` (`ratios`, innermost first, each -2, -1, 1, 2), the table of `port_table_tests.rs` for the chains of two and more (U2c has the ones of one).
//! The expected values are those of a small model written here from §11.9 only, one boundary at a time (the model is not the evaluator and not a copy of its tables): a `.down~(N)` or `.up~(N)` wraps the whole part on its left, so a part is
//! the head, or a part wrapped by one boundary, and a frame of it is run by `step`:
//! - `.down~(N)` (n = log2 N) on a part P: P runs in the frames of the counter `t` that are multiples of N, with the counter `t / N`. An input of P at `sample * 2^k` (k > 0) is gathered: P reads the `2^k` elements of the stream
//!   that came before the position (`T.default()` = 0 at first), and after the run the elements of the frame go into the ring (position c gathers c - N .. c - 1). An output of P at `sample * 2^m` (m > 0) is dealt: the
//!   array of the tick is read by the frames from the tick, in order (`2^(m-n)` of them each frame, or the one that its slower tick has); any other output is the last one P made, held to its next tick. Any other input
//!   is read as it is (the value of the stream at this position).
//! - `.up~(N)` on P: P runs N times in each frame, with the counters `t * N + j`; the run j takes its part of the frame's elements of an input that is a burst (`2^k` elements for k > 0 of P, the element j of `sample`, the element
//!   `j / 2^-k` of `sample / 2^-k`), and the elements of the outputs of the N runs in a row are the burst of the frame when it is at `sample * 2^m'` (m' > 0), else the last output.
//!
//! The head is the body of a row of `port_table_tests` (`ib_k` and `ob_m`), or `ib` with a stage of its own (`sample / 2^s`: a counter of the ticks it has). The streams that are the arguments are those of the table: the
//! element i has the value `i + 1`, or `p` of the frame the element is in; the elements before the first are 0. The model is held to the values worked out by hand in the tests of the representative rows.

use super::port_table_tests::{
    Arg, Calls, Got, Job, RANGE, calls_of, chain, clock, flows, per_frame, read_call, run_jobs, same_values, tag, two,
};

/// What a port gives: the `2^k` elements of a frame (k > 0), or the one value of the stream.
#[derive(Clone, Debug)]
enum Io {
    Burst(Vec<f32>),
    One(f32),
}

impl Io {
    fn elems(&self) -> Vec<f32> {
        match self {
            Io::Burst(v) => v.clone(),
            Io::One(x) => vec![*x],
        }
    }

    fn one(&self) -> f32 {
        match self {
            Io::One(x) => *x,
            Io::Burst(_) => panic!("a burst where one value was meant"),
        }
    }
}

/// What a run of the body gives: the counter, the frame of the caller it is run in, the inputs.
type HeadRun = Box<dyn FnMut(u64, usize, &[Io]) -> Io>;

/// The body of a row: its input ports (the exponent of each), its output (`m`), and what a run of it (the counter, the frame of the caller it is run in, the inputs) gives.
struct Head {
    ks: Vec<i32>,
    m: i32,
    run: HeadRun,
}

enum Part {
    Head(Head),
    Down { p: Box<Part>, n: i32, ring: Vec<Option<Vec<f32>>>, deal: Vec<f32>, last: Io },
    Up { p: Box<Part>, n: i32 },
}

impl Part {
    /// The exponents of the input ports as the caller of this part reads them.
    fn ks(&self) -> Vec<i32> {
        match self {
            Part::Head(h) => h.ks.clone(),
            Part::Down { p, n, .. } => p.ks().iter().map(|k| k - n).collect(),
            Part::Up { p, n } => p.ks().iter().map(|k| k + n).collect(),
        }
    }

    /// The exponent of the output.
    fn m(&self) -> i32 {
        match self {
            Part::Head(h) => h.m,
            Part::Down { p, n, .. } => p.m() - n,
            Part::Up { p, n } => p.m() + n,
        }
    }

    /// The part the chain `ratios` (innermost first) makes of the head.
    fn build(head: Head, ratios: &[i32]) -> Part {
        let mut part = Part::Head(head);
        for r in ratios {
            part = if *r < 0 {
                let ring = part.ks().iter().map(|k| (*k > 0).then(|| vec![0.0; 1 << k])).collect();
                Part::Down { p: Box::new(part), n: -r, ring, deal: Vec::new(), last: Io::One(0.0) }
            } else {
                Part::Up { p: Box::new(part), n: *r }
            };
        }
        part
    }

    /// One frame of the part at its counter `t`, in the frame `frame` of the caller.
    fn step(&mut self, t: u64, frame: usize, ins: &[Io]) -> Io {
        match self {
            Part::Head(h) => (h.run)(t, frame, ins),
            Part::Down { p, n, ring, deal, last } => {
                let (kp, pm, n) = (p.ks(), p.m(), *n);
                if t % (1 << n) == 0 {
                    let pins: Vec<Io> = ins
                        .iter()
                        .zip(ring.iter())
                        .map(|(v, r)| r.clone().map_or_else(|| v.clone(), Io::Burst))
                        .collect();
                    let out = p.step(t >> n, frame, &pins);
                    match pm > 0 {
                        true => *deal = out.elems(),
                        false => *last = out,
                    }
                }
                for (i, r) in ring.iter_mut().enumerate() {
                    let Some(buf) = r else { continue };
                    let q = kp[i] - n;
                    let new = if q >= 0 || t % (1 << -q) == 0 { ins[i].elems() } else { Vec::new() };
                    buf.extend(&new);
                    buf.drain(..new.len());
                }
                match (pm > 0, pm - n > 0) {
                    (false, _) => last.clone(),
                    (true, true) => {
                        let (w, ph) = (1usize << (pm - n), (t % (1 << n)) as usize);
                        Io::Burst(deal[ph * w..(ph + 1) * w].to_vec())
                    }
                    (true, false) => Io::One(deal[(((t % (1 << n)) << pm) >> n) as usize]),
                }
            }
            Part::Up { p, n } => {
                let (kp, pm, n) = (p.ks(), p.m(), *n);
                let (mut outs, mut last) = (Vec::new(), Io::One(0.0));
                for j in 0..1u64 << n {
                    let pins: Vec<Io> = ins
                        .iter()
                        .zip(&kp)
                        .map(|(v, k)| match k + n > 0 {
                            false => v.clone(),
                            true => {
                                let es = v.elems();
                                let j = j as usize;
                                match *k {
                                    1.. => Io::Burst(es[j << k..(j + 1) << k].to_vec()),
                                    0 => Io::One(es[j]),
                                    _ => Io::One(es[j >> -k]),
                                }
                            }
                        })
                        .collect();
                    let tp = (t << n) + j;
                    let o = p.step(tp, frame, &pins);
                    if pm >= 0 || tp % (1 << -pm) == 0 {
                        outs.extend(o.elems());
                    }
                    last = o;
                }
                match pm + n > 0 {
                    true => Io::Burst(outs),
                    false => last,
                }
            }
        }
    }
}

/// The head of an input row: `ib_k` (the elements `x[0] + 10 x[1] + ...` of the array of a port at `sample * 2^k`, or the value of the port for k <= 0), and the counter of the ticks of its own stage `sample / 2^-s` times 100000 added
/// when it has a stage (`s < 0`).
fn in_head(k: i32, s: i32) -> Head {
    let run = move |t: u64, _: usize, ins: &[Io]| {
        let x = match k > 0 {
            true => ins[0].elems().iter().enumerate().map(|(u, v)| v * 10f32.powi(u as i32)).sum(),
            false => ins[0].one(),
        };
        Io::One(if s < 0 { x + 100000.0 * ((t >> -s) + 1) as f32 } else { x })
    };
    Head { ks: vec![k], m: 0, run: Box::new(run) }
}

/// The head of an output row `ob_m`: the element e of the run n (or the tick n of `sample / 2^-m`) is `e + 1 + 1000 w` with `w` of the frame of the caller that made it.
fn out_head(m: i32, w: Vec<f32>) -> Head {
    let mut last = 0.0;
    let run = move |t: u64, frame: usize, _: &[Io]| match m {
        1.. => Io::Burst((0..1u64 << m).map(|u| ((t << m) + u + 1) as f32 + 1000.0 * w[frame]).collect()),
        0 => Io::One((t + 1) as f32 + 1000.0 * w[frame]),
        _ => {
            if t % (1 << -m) == 0 {
                last = ((t >> -m) + 1) as f32 + 1000.0 * w[frame];
            }
            Io::One(last)
        }
    };
    Head { ks: vec![], m, run: Box::new(run) }
}

/// What the caller gives the port at the clock `q` in its frame `c`: the elements `i` of its stream (`i + 1`, or `p` of the frame the element is in), the elements before the first being 0.
fn feed(q: i32, arg: Arg, p: &[f32], c: usize) -> Io {
    let at = |i: i64| match (i < 0, arg) {
        (true, _) => 0.0,
        (_, Arg::Stream) => (i + 1) as f32,
        (_, Arg::Param) => p[(if q > 0 { i >> q } else { i << -q }) as usize],
    };
    let c = c as i64;
    match q {
        1.. => Io::Burst((0..1i64 << q).map(|e| at((c << q) + e)).collect()),
        0 => Io::One(at(c)),
        _ => Io::One(at(c >> -q)),
    }
}

/// What the caller reads of the call in each of its frames, the frames in a row: a burst is spread, the others are the one value.
fn model_run(head: Head, ratios: &[i32], arg: Arg, p: &[f32]) -> Vec<f32> {
    let mut part = Part::build(head, ratios);
    let ks = part.ks();
    let mut got = Vec::new();
    for c in 0..p.len() {
        let ins: Vec<Io> = ks.iter().map(|q| feed(*q, arg, p, c)).collect();
        got.extend(part.step(c as u64, c, &ins).elems());
    }
    got
}

// ---------------------------------------------------------------------------------------------------------
// The rows.

/// A row: an input row (the head `ib_k` run by the chain, the argument a stream or `p`, `s` the stage of the head's own, 0 for none) or an output row.
#[derive(Clone, Debug)]
enum Row {
    In { k: i32, ratios: Vec<i32>, arg: Arg, s: i32 },
    Out { m: i32, ratios: Vec<i32> },
}

fn ratios_tag(rs: &[i32]) -> String {
    rs.iter().map(|r| if *r > 0 { format!("u{r}") } else { format!("d{}", -r) }).collect()
}

fn chain_all(rs: &[i32]) -> String {
    rs.iter().map(|r| chain(*r)).collect()
}

impl Row {
    fn name(&self) -> String {
        match self {
            Row::In { k, ratios, arg, s } => {
                format!(
                    "ci_{}{}_{}_{}",
                    tag(*k),
                    if *s < 0 { format!("_s{}", -s) } else { String::new() },
                    ratios_tag(ratios),
                    if *arg == Arg::Stream { "s" } else { "p" }
                )
            }
            Row::Out { m, ratios } => format!("co_{}_{}", tag(*m), ratios_tag(ratios)),
        }
    }

    /// The clock of the call as the caller reads it: the one of the output, its exponent `m + sum`.
    fn out_clock(&self) -> i32 {
        match self {
            Row::In { ratios, .. } => ratios.iter().sum(),
            Row::Out { m, ratios } => m + ratios.iter().sum::<i32>(),
        }
    }

    /// Is the row in what the helper flows have: a stream or a bundle of 4 elements at most.
    fn fits(&self) -> bool {
        match self {
            Row::In { k, ratios, .. } => k + ratios.iter().sum::<i32>() <= 4 && self.out_clock() <= 4,
            Row::Out { .. } => self.out_clock() <= 4,
        }
    }

    fn source(&self) -> String {
        match self {
            Row::In { k, ratios, arg, s } => {
                let q = k + ratios.iter().sum::<i32>();
                let (lets, a) = match (arg, q) {
                    (Arg::Param, _) => (String::new(), "p".to_string()),
                    (_, 1..) => (String::new(), format!("gen_{}~(x)", tag(q))),
                    (_, 0) => (String::new(), "x".to_string()),
                    _ => (
                        format!("  let lf = prev~(one at {}, 1.0)\n  let cnt = prev~(^cnt) + lf\n", clock(q)),
                        "cnt".to_string(),
                    ),
                };
                let head = match s {
                    0 => format!("ib_{}~({a})", tag(*k)),
                    s => format!("ibs_d{}~({a}, one)", -s),
                };
                let (call, ret) = read_call(&format!("{head}{}", chain_all(ratios)), self.out_clock());
                format!(
                    "flow {}(x: F32 at sample, one: F32 at block, p: F32 at block) -> {ret} at sample {{\n{lets}  {call}\n}}\n",
                    self.name()
                )
            }
            Row::Out { m, ratios } => {
                let (call, ret) = read_call(&format!("ob_{}~(one, w){}", tag(*m), chain_all(ratios)), self.out_clock());
                format!("flow {}(one: F32 at block, w: F32 at block) -> {ret} at sample {{ {call} }}\n", self.name())
            }
        }
    }

    fn job(&self, calls: Calls) -> Job {
        match self {
            Row::In { .. } => Job { name: self.name(), calls, vary: "p", with_x: true },
            Row::Out { .. } => Job { name: self.name(), calls, vary: "w", with_x: false },
        }
    }

    /// What the model gives for the row, over the frames of `calls_of(scale)` (`p` or `w` is `scale` times 1, 2, 3, 4 in them).
    fn model(&self, v: &[f32]) -> Vec<f32> {
        match self {
            Row::In { k, ratios, arg, s } => model_run(in_head(*k, *s), ratios, *arg, v),
            Row::Out { m, ratios } => model_run(out_head(*m, v.to_vec()), ratios, Arg::Stream, v),
        }
    }
}

/// The source of the rows: the flows of `port_table_tests`, the heads with a stage of their own, and each row.
fn source(rows: &[Row]) -> String {
    let mut s = flows();
    for d in [1, 2] {
        s += &format!(
            "flow ibs_d{d}(x: F32 at sample, one: F32 at block) -> F32 at sample {{\n  let lf = prev~(one at (sample / {}), 1.0)\n  let cnt = prev~(^cnt) + lf\n  x + (cnt at sample) * 100000.0\n}}\n",
            two(-d)
        );
    }
    rows.iter().for_each(|r| s += &r.source());
    s
}

/// Every row against its model: the evaluator gives the values of the model, and a row that stops fails.
fn hold_rows(rows: Vec<Row>, count: usize) {
    let rows: Vec<Row> = rows.into_iter().filter(Row::fits).collect();
    assert_eq!(rows.len(), count, "the rows of the table that fit the helper flows");
    let (pin, wout) = (per_frame(&calls_of(10.0)), per_frame(&calls_of(1.0)));
    let jobs: Vec<Job> =
        rows.iter().map(|r| r.job(calls_of(if matches!(r, Row::In { .. }) { 10.0 } else { 1.0 }))).collect();
    let got: Vec<Got> = run_jobs(source(&rows), jobs);
    assert_eq!(got.len(), rows.len());
    for (row, got) in rows.iter().zip(&got) {
        let want = row.model(if matches!(row, Row::In { .. }) { &pin } else { &wout });
        match got {
            Got::Values(g) => same_values(&row.name(), g, &want),
            got => panic!("{}: the evaluator gave {got:?}, not the values of the model", row.name()),
        }
    }
}

fn pairs() -> Vec<Vec<i32>> {
    let nz = [-2, -1, 1, 2];
    nz.iter().flat_map(|a| nz.iter().map(move |b| vec![*a, *b])).collect()
}

/// Chains of three and four boundaries: the ones of S-1207 (`.up~(4).down~(2).down~(2)`), the ones that deal one after the other, a part that deals wrapped by an up, and a down after an up that wraps a down.
fn longer() -> Vec<Vec<i32>> {
    vec![
        vec![2, -1, -1],
        vec![-1, -1, -1],
        vec![1, -1, 1],
        vec![-1, 1, -1],
        vec![-1, -1, 1],
        vec![1, 1, -2],
        vec![2, -2, 1],
        vec![-1, 2, -1],
        vec![1, -2, 2],
        vec![-2, 1, 1],
        vec![1, -1, 1, -1],
        vec![2, -1, -1, 1],
        vec![-1, 1, -1, 1],
        vec![1, 1, -1, -1],
    ]
}

fn rows_in_two() -> Vec<Row> {
    // 16 chains (r1, r2) in {-2, -1, 1, 2}^2 and the 5 ports k, each with a stream (element i is `i + 1`) and with `p` of `block` (changing at the cuts of the calls of `process`).
    let mut rows = Vec::new();
    for ratios in pairs() {
        for k in RANGE {
            for arg in [Arg::Stream, Arg::Param] {
                rows.push(Row::In { k, ratios: ratios.clone(), arg, s: 0 });
            }
        }
    }
    rows
}

fn rows_out_two() -> Vec<Row> {
    pairs().into_iter().flat_map(|ratios| RANGE.map(move |m| Row::Out { m, ratios: ratios.clone() })).collect()
}

/// The chains of `longer`, with the ports -1 .. 2 (a stream and `p`) and the outputs -1 .. 2.
fn rows_longer() -> Vec<Row> {
    let mut rows = Vec::new();
    for ratios in longer() {
        for k in -1..=2 {
            for arg in [Arg::Stream, Arg::Param] {
                rows.push(Row::In { k, ratios: ratios.clone(), arg, s: 0 });
            }
        }
        rows.extend((-1..=2).map(|m| Row::Out { m, ratios: ratios.clone() }));
    }
    rows
}

/// The head counts the ticks of `sample / 2` or `sample / 4` of its own (S-578, S-1079: its stage is in the caller's stage the boundaries put it in), so a value of the model has the count of the runs of the head that are on the tick,
/// whatever the boundaries wrap.
fn rows_staged() -> Vec<Row> {
    let mut rows = Vec::new();
    for ratios in [vec![2, -2], vec![1, -1], vec![2, -1, -1], vec![-1, 1], vec![-2, 2], vec![1, 1, -2], vec![-1, -1, 2]]
    {
        for s in [-1, -2] {
            rows.push(Row::In { k: 0, ratios: ratios.clone(), arg: Arg::Stream, s });
        }
    }
    rows
}

#[test]
fn the_input_ports_of_the_chains_of_two_boundaries_read_the_stream_the_way_the_model_does() {
    hold_rows(rows_in_two(), 152);
}

#[test]
fn the_output_ports_of_the_chains_of_two_boundaries_are_read_the_way_the_model_does() {
    hold_rows(rows_out_two(), 76);
}

#[test]
fn the_ports_of_the_chains_of_three_and_four_boundaries_are_read_the_way_the_model_does() {
    hold_rows(rows_longer(), 168);
}

#[test]
fn a_head_with_a_stage_of_its_own_in_a_chain_runs_that_stage_in_the_ticks_of_its_counter() {
    hold_rows(rows_staged(), 14);
}

// ---------------------------------------------------------------------------------------------------------
// The rows worked out by hand: the model gives the numbers of the comment. The caller's stream is x[c] = c + 1 (0 before the first), 24 frames.

fn run_model(head: Head, ratios: &[i32], arg: Arg, frames: usize) -> Vec<f32> {
    model_run(head, ratios, arg, &vec![0.0; frames])
}

fn delay_of(by: usize, frames: usize) -> Vec<f32> {
    (0..frames).map(|c| if c < by { 0.0 } else { (c - by + 1) as f32 }).collect()
}

#[test]
#[rustfmt::skip]
fn the_model_gives_the_numbers_worked_out_by_hand_for_the_representative_chains() {
    // §11.9 and S-566 A10: `x.up~(2).down~(2)` runs the body in a block of 2 (at the even c, the runs c and c + 1 take x[c - 2] and x[c - 1]) and deals the 2 outputs to the frames c and c + 1: 2 samples late,
    // y[c] = x[c - 2] = c - 1 for c >= 2. `x.up~(4).down~(4)` is 4 late. S-1207: `x.up~(4).down~(2).down~(2)` is the 4 of its inner boundary and the 2 of the frames its outer one reads of the
    // array of 4, 6 late, y[c] = x[c - 6]. `x.down~(2).up~(2)` runs the body at the even counters of the block, the run j = 0 of each frame takes x[c] (the port is `sample`, nothing is gathered): y = x.
    let ib = || in_head(0, 0);
    assert_eq!(run_model(ib(), &[1, -1], Arg::Stream, 24), delay_of(2, 24));
    assert_eq!(run_model(ib(), &[2, -2], Arg::Stream, 24), delay_of(4, 24));
    assert_eq!(run_model(ib(), &[2, -1, -1], Arg::Stream, 24), delay_of(6, 24));
    assert_eq!(run_model(ib(), &[-1, 1], Arg::Stream, 24), delay_of(0, 24));
    // S-1214 (1): a body with an input at `sample * 4`, `.down~(2).down~(2)`: the tick c = 0 mod 4 gathers x[c - 6 ..= c - 3] (4 elements: the ring of the outer boundary has x[c - 2], x[c - 1], the one of the
    // inner has the 2 elements of the 2 frames of the outer before) and gives `x[0] + 10 x[1] + 100 x[2] + 1000 x[3]`, held for the 4 frames: 0 (c = 0), 2100 (x[-2..=1] = 0, 0, 1, 2), 6543 (3, 4, 5, 6),
    // 10987 (7, 8, 9, 10), 15431 (11 .. 14), 19875 (15 .. 18).
    let mut want = Vec::new();
    for v in [0.0, 2100.0, 6543.0, 10987.0, 15431.0, 19875.0] {
        want.extend([v; 4]);
    }
    assert_eq!(run_model(in_head(2, 0), &[-1, -1], Arg::Stream, 24), want);
    // `.down~(2).up~(2)` of a body with an input at `sample * 2` (S-1214 (2)): the stream is at `sample * 2` (element i is i + 1, the frame c has 2c + 1 and 2c + 2). The down gathers the 2 elements before its tick
    // (c: 2c - 1, 2c), the body gives `x[0] + 10 x[1]` = 22c - 1 (0 at c = 0), and the up gives it in both its runs: a frame late: 0, 21, 43, 65.
    let want: Vec<f32> = (0..24).map(|c| if c == 0 { 0.0 } else { (22 * c - 1) as f32 }).collect();
    assert_eq!(run_model(in_head(1, 0), &[-1, 1], Arg::Stream, 24), want);
    // The port at `sample / 2` lifted by an up and gathered by a down (S-1207 with the clock of the port at the half): `sl~(c).up~(4).down~(4)` reads the stream at `sample / 2` (element j is j + 1, in the frames 2j and 2j + 1)
    // the same, 4 frames late: 0 0 0 0, then 1 1 2 2, 3 3 4 4, ...
    let want: Vec<f32> = (0..24).map(|c: i32| if c < 4 { 0.0 } else { (((c - 4) >> 1) + 1) as f32 }).collect();
    assert_eq!(run_model(in_head(-1, 0), &[2, -2], Arg::Stream, 24), want);
}

#[test]
fn the_model_gives_the_numbers_worked_out_by_hand_for_the_outputs_that_are_dealt_one_after_the_other() {
    // An output at `sample * 4` dealt by `.down~(2).down~(2)` (S-1214: the boundaries deal in turn, nothing is gathered): the body makes the 4 elements e + 1 + 1000 w of its run n at the caller's frame 4n; the frames 4n ..
    // 4n + 3 read them in order. With w = 1 in the first 5 frames, 2 in the next 7, 3, then 4 (`calls_of(1.0)`): the elements 1 .. 4 of the run 0 are 1001 .. 1004 (w of the frame 0), the run 1 (frame 4, w = 1) gives
    // 1005 .. 1008, the run 2 (frame 8, w = 2) 2009 .. 2012.
    let w = per_frame(&calls_of(1.0));
    let got = model_run(out_head(2, w), &[-1, -1], Arg::Stream, &per_frame(&calls_of(1.0)));
    assert_eq!(
        &got[..12],
        &[1001.0, 1002.0, 1003.0, 1004.0, 1005.0, 1006.0, 1007.0, 1008.0, 2009.0, 2010.0, 2011.0, 2012.0]
    );
}
