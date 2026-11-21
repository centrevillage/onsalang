//! The table of the ports of a conversion flow (W7-09 U2c): what a flow with an input at `sample * 2^k` (k = -2 .. 2, `sample / 4` to `sample * 4`) reads of the argument it is given, and what the
//! caller reads of an output at `sample * 2^m`, when the flow is run by a chain of the ratio `2^r` (r = -2 .. 2: `.down~(4)`, `.down~(2)`, none, `.up~(2)`, `.up~(4)`), for every pair (k, r) and (m, r).
//! The expected values are those of a small model of time written here from §11.3, §11.4, §11.9 and S-566, S-567, S-578, S-1079, S-1088 (the model below, not the evaluator and not a copy of its tables), and the model is held
//! to the values worked out by hand in the comments of the tests of the representative rows. Every row gives its values (W7-09 U2e took the last mark off): a row that stops, with `Unavailable`
//! or an internal error, fails.
//!
//! The rule of the model (the frame of the caller is c, the chain runs the body at the ratio `2^r`: r = 0 at each c, r < 0 at the c that are multiples of `2^-r` (position c, n = c / 2^-r), r > 0 `2^r`
//! times in each c, n = c * 2^r + j; the counter n is the `sample` of the instance, §11.9 "位相のカウンタ"):
//! - A port at the clock `sample * 2^k` of the body is an array of `2^k` elements in each run, one at `sample / 2^-k` a value in each run that is a multiple of `2^-k` (held between: `x at sample`).
//!   The call has the clock q = k + r: a stream that is `2^q` values in each frame of the caller (q > 0) or one in each `2^-q` frames (q <= 0), or a value of `block` that is read where it is used.
//!   Element i of the stream is in the frame `i / 2^q` (q > 0) or `i * 2^-q` (q <= 0).
//! - The body takes its input in time order: the tick t of a port with k > 0 takes the elements `t * 2^k` ..., the tick t of a port with k <= 0 the element t; but a tick that runs slower than the stream (k > 0 with
//!   r < 0) takes the `2^k` elements before its position, `(t - 1) * 2^k` ... (S-578 "c - N 〜 c - 1", S-1079 "入力のクロックの直前の M 刻み", `T.default()` where there is none, §11.9 "位相 0").
//! - The output of the body is elements in time order (a run gives `2^m` of them for m > 0, one for m = 0, and one in each run that is a multiple of `2^-m` for m < 0), element e of the clock `o = m + r` of the caller:
//!   the frame c reads the elements `c * 2^o` ... (o > 0), the element c (o = 0), or the last one made, `c / 2^-o` (o < 0).

use super::expr_tests::{def_named, with_checked};
use super::flow::Instance;
use super::scalar::Fault;
use super::sema_view::View;
use super::value::Value;
use onsa_driver::Analyzed;
use onsa_sema::DefId;

fn two(k: i32) -> usize {
    1 << k.unsigned_abs()
}

fn tag(k: i32) -> String {
    match k {
        0 => "z".into(),
        k if k > 0 => format!("u{k}"),
        k => format!("d{}", -k),
    }
}

/// The clock of a port `2^k` times as fast as `sample`.
fn clock(k: i32) -> String {
    match k {
        0 => "sample".into(),
        k if k > 0 => format!("(sample * {})", two(k)),
        k => format!("(sample / {})", two(k)),
    }
}

fn chain(r: i32) -> String {
    match r {
        0 => String::new(),
        r if r > 0 => format!(".up~({})", two(r)),
        r => format!(".down~({})", two(r)),
    }
}

/// The value of a call of the clock `o` as the one flow of the outer flow gives it: a bundle of `2^o` values is taken by `col_o` (an array of the frame), a slower one is read with `at sample`.
fn read_call(call: &str, o: i32) -> (String, String) {
    match o {
        0 => (call.to_string(), "F32".into()),
        o if o > 0 => (format!("col_{}~({call})", tag(o)), format!("[F32; {}]", two(o))),
        _ => (format!("{call} at sample"), "F32".into()),
    }
}

/// How the argument of an input row is made: a stream that is exactly at the clock q (element i of it is `i + 1`), or the `block` value `p` (which the calls of `process` change).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Arg {
    Stream,
    Param,
}

fn in_name(k: i32, r: i32, arg: Arg) -> String {
    format!("in_{}_{}_{}", tag(k), tag(r), if arg == Arg::Stream { "s" } else { "p" })
}

fn out_name(m: i32, r: i32) -> String {
    format!("out_{}_{}", tag(m), tag(r))
}

const RANGE: std::ops::RangeInclusive<i32> = -2..=2;

/// The source of the table. The flows of a row:
/// - `col_o` takes a bundle `sample * 2^o` into an array of the frame; `gen_q` makes the stream of a frame `c = x`: the `2^q` elements `(c - 1) * 2^q + u + 1` (u = 0 .. `2^q`), that is the element
///   i of the stream has the value `i + 1`; for q < 0 the stream is `cnt`, which counts the ticks of its clock (`lf` is 1 at every tick, `one` is 1.0) and has the value `i + 1` at the tick i.
/// - `ib_k` is the body of an input row: its output is, for k > 0, `x[0] + 10 x[1] + 100 x[2] + ...` of the array of the frame, for k <= 0 the input read at `sample`.
/// - `ob_m` is the body of an output row: the run n (or the tick n of `sample / 2^-m`) has the element e with the value `e + 1 + 1000 w`, `w` of `block` read where the element is made.
fn table_source() -> String {
    let mut s = String::new();
    for o in 1..=4 {
        s += &format!("flow col_{}(x: F32 at {}) -> [F32; {}] at sample {{ x }}\n", tag(o), clock(o), two(o));
    }
    for q in 1..=4 {
        let n = two(q);
        let els: Vec<String> = (0..n)
            .map(|u| if u == n - 1 { format!("c * {n}.0") } else { format!("c * {n}.0 - {}.0", n - 1 - u) })
            .collect();
        s += &format!("flow gen_{}(c: F32 at sample) -> F32 at {} {{ [{}] }}\n", tag(q), clock(q), els.join(", "));
    }
    for k in RANGE {
        s += &match k {
            0 => "flow ib_z(x: F32 at sample) -> F32 at sample { x }\n".to_string(),
            k if k > 0 => {
                let dig: Vec<String> = (0..two(k))
                    .map(|u| if u == 0 { "x[0]".into() } else { format!("x[{u}] * {}.0", 10u32.pow(u as u32)) })
                    .collect();
                format!("flow ib_{}(x: F32 at {}) -> F32 at sample {{ {} }}\n", tag(k), clock(k), dig.join(" + "))
            }
            k => format!("flow ib_{}(x: F32 at {}) -> F32 at sample {{ x at sample }}\n", tag(k), clock(k)),
        };
    }
    for k in RANGE {
        for r in RANGE {
            for arg in [Arg::Stream, Arg::Param] {
                let q = k + r;
                let (lets, a) = match (arg, q) {
                    (Arg::Param, _) => (String::new(), "p".to_string()),
                    (_, 1..) => (String::new(), format!("gen_{}~(x)", tag(q))),
                    (_, 0) => (String::new(), "x".to_string()),
                    _ => (
                        format!("  let lf = prev~(one at {}, 1.0)\n  let cnt = prev~(^cnt) + lf\n", clock(q)),
                        "cnt".to_string(),
                    ),
                };
                let (call, ret) = read_call(&format!("ib_{}~({a}){}", tag(k), chain(r)), r);
                s += &format!(
                    "flow {}(x: F32 at sample, one: F32 at block, p: F32 at block) -> {ret} at sample {{\n{lets}  {call}\n}}\n",
                    in_name(k, r, arg)
                );
            }
        }
    }
    for m in RANGE {
        s += &match m {
            0 => "flow ob_z(one: F32 at block, w: F32 at block) -> F32 at sample {\n  let cnt = prev~(^cnt) + one\n  cnt + w * 1000.0\n}\n".to_string(),
            m if m > 0 => {
                let n = two(m);
                let els: Vec<String> = (0..n).map(|u| if u == 0 { "a".into() } else { format!("a + {u}.0") }).collect();
                format!(
                    "flow ob_{}(one: F32 at block, w: F32 at block) -> F32 at {} {{\n  let cnt = prev~(^cnt) + one\n  let a = cnt * {n}.0 - {}.0 + w * 1000.0\n  [{}]\n}}\n",
                    tag(m),
                    clock(m),
                    n - 1,
                    els.join(", ")
                )
            }
            m => format!(
                "flow ob_{}(one: F32 at block, w: F32 at block) -> F32 at {c} {{\n  let lf = prev~(one at {c}, 1.0)\n  let cnt = prev~(^cnt) + lf\n  cnt + w * 1000.0\n}}\n",
                tag(m),
                c = clock(m)
            ),
        };
    }
    for m in RANGE {
        for r in RANGE {
            let (call, ret) = read_call(&format!("ob_{}~(one, w){}", tag(m), chain(r)), m + r);
            s += &format!(
                "flow {}(one: F32 at block, w: F32 at block) -> {ret} at sample {{ {call} }}\n",
                out_name(m, r)
            );
        }
    }
    s
}

/// The calls of `process`: the frames and the value of the `block` input that changes (`p` of an input row, `w` of an output row) in each. The inputs `one` (1.0) and the column `x` (`c + 1`) are the same in all.
type Calls = Vec<(usize, f32)>;

/// 24 frames in four calls, the parameter changing at the cuts (5, 12, 16): an input row has `p` = 10, 20, 30, 40, an output row `w` = 1, 2, 3, 4.
fn calls_of(scale: f32) -> Calls {
    vec![(5, scale), (7, 2.0 * scale), (4, 3.0 * scale), (8, 4.0 * scale)]
}

fn per_frame(calls: &Calls) -> Vec<f32> {
    calls.iter().flat_map(|(n, v)| vec![*v; *n]).collect()
}

/// What an evaluator gave: the values (an array of a frame is spread out), or the way it stopped.
#[derive(Clone, Debug, PartialEq)]
enum Got {
    Values(Vec<f32>),
    Unavailable,
    Internal,
    Other(String),
}

fn spread(v: &Value, to: &mut Vec<f32>) {
    match v {
        Value::F32(x) => to.push(*x),
        Value::Int(_, n, _) => to.push(*n as f32),
        Value::Array(vs) => vs.iter().for_each(|v| spread(v, to)),
        _ => panic!("not an F32: {v:?}"),
    }
}

fn drive(a: &Analyzed, def: DefId, calls: &Calls, vary: &'static str, with_x: bool) -> Got {
    let stop = |f: Fault| match f {
        Fault::Unavailable(_) => Got::Unavailable,
        Fault::Internal(_) => Got::Internal,
        f => Got::Other(format!("{f:?}")),
    };
    let mut me = match Instance::init(View::new(a), def, 48000.0, &[], None) {
        Ok(me) => me,
        Err(e) => return stop(e.fault),
    };
    let (total, mut at, mut got) = (calls.iter().map(|c| c.0).sum::<usize>(), 0, Vec::new());
    let x: Vec<Value> = (0..total).map(|c| Value::F32(c as f32 + 1.0)).collect();
    for (n, v) in calls {
        let params = [("one", Value::F32(1.0)), (vary, Value::F32(*v))];
        let cols: Vec<(&str, &[Value])> = if with_x { vec![("x", &x[at..at + n])] } else { vec![] };
        match me.process(&params, &cols, *n, None) {
            Ok(outs) => outs.iter().for_each(|o| spread(o, &mut got)),
            Err(e) => return stop(e.fault),
        }
        at += n;
    }
    Got::Values(got)
}

/// The rows to run: the flow, the calls and the `block` input that changes in them.
struct Job {
    name: String,
    calls: Calls,
    vary: &'static str,
    with_x: bool,
}

fn input_job(k: i32, r: i32, arg: Arg, calls: Calls) -> Job {
    Job { name: in_name(k, r, arg), calls, vary: "p", with_x: true }
}

fn output_job(m: i32, r: i32, calls: Calls) -> Job {
    Job { name: out_name(m, r), calls, vary: "w", with_x: false }
}

/// The outcomes of the jobs, all on the one checked source of the table (a flow by name).
fn run_jobs(src: String, jobs: Vec<Job>) -> Vec<Got> {
    with_checked(&src, true, move |a| {
        jobs.iter().map(|j| drive(a, def_named(a, &j.name), &j.calls, j.vary, j.with_x)).collect()
    })
}

// ---------------------------------------------------------------------------------------------------------
// The model.

/// The argument of an input row for the model: element i of its stream (see [`Arg`]), and the frame the element is in.
struct Feed<'a> {
    q: i32,
    arg: Arg,
    p: &'a [f32],
}

impl Feed<'_> {
    fn frame(&self, i: i64) -> usize {
        (if self.q > 0 { i >> self.q } else { i << -self.q }) as usize
    }

    /// The element i; before the first, `T.default()`.
    fn at(&self, i: i64) -> f32 {
        match (i < 0, self.arg) {
            (true, _) => 0.0,
            (_, Arg::Stream) => (i + 1) as f32,
            (_, Arg::Param) => self.p[self.frame(i)],
        }
    }
}

/// What the caller reads of the input row (k, r) in each of its frames, `p` being the value of the parameter in each frame: the values the body gives in the runs, which the caller reads at its clock r.
fn model_in(k: i32, r: i32, arg: Arg, p: &[f32]) -> Vec<f32> {
    let feed = Feed { q: k + r, arg, p };
    let run = |n: i64| -> f32 {
        if k > 0 {
            let width = 1i64 << k;
            // the tick n of a run slower than its stream takes the elements before its position
            let start = if r < 0 { (n - 1) * width } else { n * width };
            (0..width).map(|u| feed.at(start + u) * 10f32.powi(u as i32)).sum()
        } else {
            // the last tick of the port at `sample / 2^-k`, at the run n rounded down to a multiple of `2^-k`
            feed.at(n >> -k)
        }
    };
    (0..p.len() as i64)
        .flat_map(|c| match r {
            0 => vec![run(c)],
            r if r > 0 => (0..1i64 << r).map(|j| run((c << r) + j)).collect(),
            r => vec![run(c >> -r)],
        })
        .collect()
}

/// What the caller reads of the output row (m, r) in each frame: the element e has `e + 1 + 1000 w` where `w` is the one of the frame of the run that made it.
fn model_out(m: i32, r: i32, w: &[f32]) -> Vec<f32> {
    let o = m + r;
    let run_of = |e: i64| if m > 0 { e >> m } else { e << -m };
    let frame_of = |n: i64| (if r < 0 { n << -r } else { n >> r }) as usize;
    let element = |e: i64| (e + 1) as f32 + 1000.0 * w[frame_of(run_of(e))];
    (0..w.len() as i64)
        .flat_map(|c| match o {
            0 => vec![element(c)],
            o if o > 0 => (0..1i64 << o).map(|u| element((c << o) + u)).collect(),
            o => vec![element(c >> -o)],
        })
        .collect()
}

fn same_values(row: &str, got: &[f32], want: &[f32]) {
    let eq = |a: &f32, b: &f32| a.to_bits() == b.to_bits();
    assert!(
        got.len() == want.len() && got.iter().zip(want).all(|(a, b)| eq(a, b)),
        "{row}: got {got:?}, want {want:?}"
    );
}

/// The outcome of the row `row` against its model: the values of the model (a row that stops fails).
fn hold(row: &str, got: &Got, want: &[f32]) {
    match got {
        Got::Values(g) => same_values(row, g, want),
        got => panic!("{row}: the evaluator gave {got:?}, not the values of the model"),
    }
}

#[test]
fn the_input_ports_of_the_table_read_the_stream_the_way_the_model_does() {
    // The 50 rows (k, r) in {-2 .. 2}^2 with a stream that is exactly at the clock q = k + r, and with `p` of `block`, which a call of `process` changes (the cuts at the frames 5, 12 and 16 are inside the windows
    // and the ticks of the rows, and the elements are read in the frame they are in, §11.3 "使う所のクロックで変換なしに読める").
    let mut jobs = Vec::new();
    for k in RANGE {
        for r in RANGE {
            for arg in [Arg::Stream, Arg::Param] {
                jobs.push(input_job(k, r, arg, calls_of(10.0)));
            }
        }
    }
    let p = per_frame(&calls_of(10.0));
    let got = run_jobs(table_source(), jobs);
    let mut rows = got.iter();
    for k in RANGE {
        for r in RANGE {
            for arg in [Arg::Stream, Arg::Param] {
                hold(&in_name(k, r, arg), rows.next().expect("a row"), &model_in(k, r, arg, &p));
            }
        }
    }
}

#[test]
fn the_output_ports_of_the_table_are_read_the_way_the_model_does() {
    // The 25 rows (m, r): the body makes the elements e (`e + 1 + 1000 w`, `w` read where the element is made) and the caller reads them at the clock m + r. `w` is 1, 2, 3, 4 in the calls of 5, 7, 4 and 8 frames.
    let mut jobs = Vec::new();
    for m in RANGE {
        for r in RANGE {
            jobs.push(output_job(m, r, calls_of(1.0)));
        }
    }
    let w = per_frame(&calls_of(1.0));
    let got = run_jobs(table_source(), jobs);
    let mut rows = got.iter();
    for m in RANGE {
        for r in RANGE {
            hold(&out_name(m, r), rows.next().expect("a row"), &model_out(m, r, &w));
        }
    }
}

// ---------------------------------------------------------------------------------------------------------
// The check rules out an argument that is not at the clock of the input (E0815).

/// The table and, for each row (k, r) and each other clock q' (-4 .. 4) than the clock q = k + r of the input, a flow that gives it a stream at the clock q' (`gen_`, `x` or `cnt` as in the table): the source,
/// and the byte range of each of these flows in it.
fn wrong_clock_source() -> (String, Vec<(String, usize, usize)>) {
    let mut s = table_source();
    let mut rows = Vec::new();
    for k in RANGE {
        for r in RANGE {
            for q2 in -4..=4 {
                if q2 == k + r {
                    continue;
                }
                let (lets, a) = match q2 {
                    1.. => (String::new(), format!("gen_{}~(x)", tag(q2))),
                    0 => (String::new(), "x".to_string()),
                    _ => (
                        format!("  let lf = prev~(one at {}, 1.0)\n  let cnt = prev~(^cnt) + lf\n", clock(q2)),
                        "cnt".to_string(),
                    ),
                };
                let (call, ret) = read_call(&format!("ib_{}~({a}){}", tag(k), chain(r)), r);
                let name = format!("bad_{}_{}_q{}", tag(k), tag(r), tag(q2));
                let start = s.len();
                s += &format!(
                    "flow {name}(x: F32 at sample, one: F32 at block) -> {ret} at sample {{\n{lets}  {call}\n}}\n"
                );
                rows.push((name, start, s.len()));
            }
        }
    }
    (s, rows)
}

#[test]
fn an_argument_that_is_not_at_the_clock_of_the_input_is_ruled_out_by_the_check_for_every_row() {
    // §11.3: a value of a stream clock is used at another clock only with `at`, from a slower clock to a faster one (to the `sample` at most), and a value is never made slower; `sample * N` is met in a
    // conversion flow only. The clock of the input of a row is q = k + r, so each of the 25 rows (k, r) with a stream at any other of the 9 clocks `sample * 16` .. `sample / 16` (200 flows) is E0815. (The 50
    // rows of the table above, whose stream is exactly at q or is a `block` value, are not ruled out: the source of the table is clean.)
    let (src, rows) = wrong_clock_source();
    assert_eq!(rows.len(), 200);
    let in_rows = with_checked(&src, false, move |a| {
        rows.iter()
            .map(|(name, start, end)| {
                let hit = a.diagnostics.iter().any(|d| {
                    d.code.as_str() == "E0815" && d.span.start as usize >= *start && d.span.end as usize <= *end
                });
                (name.clone(), hit)
            })
            .collect::<Vec<_>>()
    });
    let missed: Vec<&str> = in_rows.iter().filter(|(_, hit)| !hit).map(|(n, _)| n.as_str()).collect();
    assert!(missed.is_empty(), "no E0815 in: {missed:?}");
}

// ---------------------------------------------------------------------------------------------------------
// The rows that are worked out by hand: at least one of each pair of signs of (k, r) and (m, r), the model held to the numbers of the comment.

/// 8 frames in the calls of 3 and 5 frames: the parameter that changes is `p` (10, 20) of an input row and `w` (1, 2) of an output row.
fn p8() -> Vec<f32> {
    per_frame(&vec![(3, 10.0), (5, 20.0)])
}

fn w8() -> Vec<f32> {
    per_frame(&vec![(3, 1.0), (5, 2.0)])
}

#[test]
#[rustfmt::skip]
fn the_model_of_the_input_ports_gives_the_numbers_worked_out_by_hand() {
    // x = 1, 2, 3, ... (frame c has c + 1), the element i of a stream is i + 1 (the frame c has the elements 2^q c + u, u = 0 .. 2^q for q > 0), and the body of k > 0 gives `x[0] + 10 x[1] + 100 x[2] + ...`.
    // Where the stream is the `block` value p, the calls give p = 10 for the frames 0 .. 2 and 20 for 3 .. 7, and the elements are of the frame they are in (§11.3).
    use Arg::{Param, Stream};
    let rows: Vec<(i32, i32, Arg, Vec<f32>, &str)> = vec![
        // k > 0, r > 0 (q = 2): the run n = 2 c + j takes the elements 2 n and 2 n + 1, the values 2 n + 1 and 2 n + 2, and gives (2 n + 1) + 10 (2 n + 2) = 22 n + 21: the frame c has the two runs n = 2 c, 2 c + 1.
        (1, 1, Stream, vec![21., 43., 65., 87., 109., 131., 153., 175., 197., 219., 241., 263., 285., 307., 329., 351.], "k>0 r>0"),
        // k > 0, r = 0 (q = 1): the frame c has the elements 2 c, 2 c + 1: (2 c + 1) + 10 (2 c + 2) = 22 c + 21.
        (1, 0, Stream, vec![21., 43., 65., 87., 109., 131., 153., 175.], "k>0 r=0"),
        // k > 0, r < 0 (q = 0): the run at c = 2 t takes the 2 values before its position (the frames 2 t - 2 and 2 t - 1: the values 2 t - 1 and 2 t, nothing before the frame 0: 0 0), (2 t - 1) + 10 (2 t) = 22 t - 1 for
        // t = 1, 2, 3: 21, 43, 65, and the first run gives 0; held for the two frames of a run.
        (1, -1, Stream, vec![0., 0., 21., 21., 43., 43., 65., 65.], "k>0 r<0"),
        // k = 0, r > 0 (q = 1): the run j of the frame c takes the element 2 c + j, the value 2 c + j + 1.
        (0, 1, Stream, vec![1., 2., 3., 4., 5., 6., 7., 8., 9., 10., 11., 12., 13., 14., 15., 16.], "k=0 r>0"),
        (0, 0, Stream, vec![1., 2., 3., 4., 5., 6., 7., 8.], "k=0 r=0"),
        // k = 0, r < 0 (q = -1): the run n at c = 2 n takes the element n (the value n + 1) of the stream at `sample / 2`, held for two frames.
        (0, -1, Stream, vec![1., 1., 2., 2., 3., 3., 4., 4.], "k=0 r<0"),
        // k < 0, r > 0 (q = 0): the port at `sample / 2` ticks in the runs n that are even, j = 0 of each frame, and takes the x of that frame; `x at sample` holds it for the second run: c + 1 twice.
        (-1, 1, Stream, vec![1., 1., 2., 2., 3., 3., 4., 4., 5., 5., 6., 6., 7., 7., 8., 8.], "k<0 r>0 q=0"),
        // k < 0, r > 0, q > 0 (k = -1, r = 2, q = 1): the four runs of the frame c are n = 4 c + j, the ticks are j = 0 and 2, which take the elements 2 c and 2 c + 1 (the values 2 c + 1 and 2 c + 2): 2 c + 1 twice and 2 c + 2 twice.
        (
            -1,
            2,
            Stream,
            (0..8)
                .flat_map(|c| [2. * c as f32 + 1., 2. * c as f32 + 1., 2. * c as f32 + 2., 2. * c as f32 + 2.])
                .collect(),
            "k<0 r>0 q>0",
        ),
        // k < 0, r = 0 (q = -1): the tick t of the port at `sample / 2` is at c = 2 t and takes the element t: held, floor(c / 2) + 1.
        (-1, 0, Stream, vec![1., 1., 2., 2., 3., 3., 4., 4.], "k<0 r=0"),
        // k < 0, r < 0 (q = -2): the runs are at c = 0, 2, 4, 6 (n = 0 .. 3), the port ticks at n = 0 and 2, that is c = 0 and 4, and takes the elements 0 and 1: 1 for c < 4 and 2 from 4.
        (-1, -1, Stream, vec![1., 1., 1., 1., 2., 2., 2., 2.], "k<0 r<0"),
        // The same with the `block` value: `fold2~(p)` (k = 1, r = 0, q = 1) has the elements of the frame c both p: p + 10 p = 11 p: 110 for the frames 0 .. 2, 220 for 3 .. 7.
        (1, 0, Param, vec![110., 110., 110., 220., 220., 220., 220., 220.], "p k>0 r=0"),
        // k = 2, r = 0: four elements p: 1111 p.
        (2, 0, Param, vec![11110., 11110., 11110., 22220., 22220., 22220., 22220., 22220.], "p k=2 r=0"),
        // k > 0, r < 0 (k = 1, r = -1, q = 0): the run at c = 2 t takes the p of the frames 2 t - 2 and 2 t - 1, each read in its own frame: t = 1 (c = 2) has the frames 0, 1: 10 + 10 10 = 110; t = 2 (c = 4) the frames 2, 3: the
        // p of the frame 2 is 10 and the one of the frame 3 is 20 (the cut of the calls is inside the window): 10 + 10 20 = 210; t = 3 (c = 6) the frames 4, 5: 20 + 200 = 220; t = 0 has nothing before it: 0.
        (1, -1, Param, vec![0., 0., 110., 110., 210., 210., 220., 220.], "p k>0 r<0"),
        // k = 0, r > 0: the two runs of a frame read the p of the frame.
        (0, 1, Param, vec![10., 10., 10., 10., 10., 10., 20., 20., 20., 20., 20., 20., 20., 20., 20., 20.], "p k=0 r>0"),
        // k < 0, r < 0 (q = -2): the port ticks in the runs of c = 0 and 4, and reads the p of that frame: 10 for the frames 0 .. 3 and 20 for 4 .. 7.
        (-1, -1, Param, vec![10., 10., 10., 10., 20., 20., 20., 20.], "p k<0 r<0"),
    ];
    for (k, r, arg, want, what) in rows {
        let got = model_in(k, r, arg, &p8());
        same_values(&format!("{what} {}", in_name(k, r, arg)), &got, &want);
    }
}

#[test]
#[rustfmt::skip]
fn the_model_of_the_output_ports_gives_the_numbers_worked_out_by_hand() {
    // The body counts its runs (or the ticks of its `sample / 2^-m`) from 1 and the element e has the value `e + 1 + 1000 w`, `w` of `block` read where the element is made. `w` is 1 for the frames 0 .. 2 and 2 for 3 .. 7.
    let rows: Vec<(i32, i32, Vec<f32>, &str)> = vec![
        // m > 0, r > 0 (o = 2): the frame c has the elements 4 c .. 4 c + 3, made by its two runs, all with the w of the frame c.
        (1, 1, vec![
                1001., 1002., 1003., 1004., 1005., 1006., 1007., 1008., 1009., 1010., 1011., 1012., 2013., 2014.,
                2015., 2016., 2017., 2018., 2019., 2020., 2021., 2022., 2023., 2024., 2025., 2026., 2027., 2028.,
                2029., 2030., 2031., 2032.,
            ], "m>0 r>0"),
        // m > 0, r = 0 (o = 1): the frame c has the elements 2 c and 2 c + 1.
        (1, 0, vec![
                1001., 1002., 1003., 1004., 1005., 1006., 2007., 2008., 2009., 2010., 2011., 2012., 2013., 2014.,
                2015., 2016.,
            ], "m>0 r=0"),
        // m > 0, r < 0 (o = 0): the run of c = 2 n makes the elements 2 n and 2 n + 1 (the values 2 n + 1 and 2 n + 2 with 1000 w of the frame 2 n) and the frames 2 n and 2 n + 1 read them: the frame 3 reads the element of the run of the
        // frame 2, where w is 1 (not the 2 of the frame 3): 1004 and not 2004; the run of the frame 4 has w = 2.
        (1, -1, vec![1001., 1002., 1003., 1004., 2005., 2006., 2007., 2008.], "m>0 r<0"),
        // m = 0, r > 0 (o = 1): the runs n = 2 c, 2 c + 1 have the elements n: 2 c + 1 and 2 c + 2 with the w of the frame.
        (0, 1, vec![
                1001., 1002., 1003., 1004., 1005., 1006., 2007., 2008., 2009., 2010., 2011., 2012., 2013., 2014.,
                2015., 2016.,
            ], "m=0 r>0"),
        (0, 0, vec![1001., 1002., 1003., 2004., 2005., 2006., 2007., 2008.], "m=0 r=0"),
        // m = 0, r < 0 (o = -1): the run n at c = 2 n gives n + 1 + 1000 w of that frame (w of the frame 2 is 1, of the frame 4 is 2), held for two frames.
        (0, -1, vec![1001., 1001., 1002., 1002., 2003., 2003., 2004., 2004.], "m=0 r<0"),
        // m < 0, r > 0 (o = 0): the output at `sample / 2` ticks in the run j = 0 of each frame, so the element c is made in the frame c.
        (-1, 1, vec![1001., 1002., 1003., 2004., 2005., 2006., 2007., 2008.], "m<0 r>0 o=0"),
        // m < 0, r > 0, o > 0 (m = -1, r = 2): the ticks are the runs j = 0 and 2 of each frame: the elements 2 c and 2 c + 1 with the w of the frame c.
        (-1, 2, vec![
                1001., 1002., 1003., 1004., 1005., 1006., 2007., 2008., 2009., 2010., 2011., 2012., 2013., 2014.,
                2015., 2016.,
            ], "m<0 r>0 o>0"),
        // m < 0, r = 0 (o = -1): the output ticks in the runs c = 0, 2, 4, 6 (n even) and holds: the element e = c / 2 with the w of the frame c.
        (-1, 0, vec![1001., 1001., 1002., 1002., 2003., 2003., 2004., 2004.], "m<0 r=0"),
        // m < 0, r < 0 (o = -2): the runs are at c = 0, 2, 4, 6 (n = 0 .. 3), the output ticks at n = 0 and 2 (c = 0 and 4): the element 0 with w = 1 and the element 1 with w = 2, held for four frames each.
        (-1, -1, vec![1001., 1001., 1001., 1001., 2002., 2002., 2002., 2002.], "m<0 r<0"),
        // m > 0, r < 0, o < 0 (m = 1, r = -2): the runs at c = 0 and 4 make two elements each, the first is read in the frames c, c + 1 and the second in c + 2, c + 3 (the clock `sample / 2`).
        (1, -2, vec![1001., 1001., 1002., 1002., 2003., 2003., 2004., 2004.], "m>0 r<0 o<0"),
        // m = 2, r = -1 (o = 1): the run of the frame 2 n makes the four elements 4 n .. 4 n + 3, the frame 2 n reads the first two and 2 n + 1 the other two; the frame 3 reads 1007 and 1008 (the w of the frame 2).
        (2, -1, vec![
                1001., 1002., 1003., 1004., 1005., 1006., 1007., 1008., 2009., 2010., 2011., 2012., 2013., 2014.,
                2015., 2016.,
            ], "m=2 r=-1"),
    ];
    for (m, r, want, what) in rows {
        let got = model_out(m, r, &w8());
        same_values(&format!("{what} {}", out_name(m, r)), &got, &want);
    }
}

// ---------------------------------------------------------------------------------------------------------
// The forms of W7-09 U2b that are not rows of the table (an array of the parameter kinds for a `.up~` part, a call at `sample * N` in a `let` or in parentheses, an output of `sample_tick()` alone at a tick), and the
// changes the tests of U2b let through.

type Block = Vec<(&'static str, f32)>;

/// A flow of its own source: the outputs (numbers) for the calls `(frames, block inputs)`, the columns of the `sample` inputs (`f32`, the whole length) cut across them.
fn run_src(src: &str, name: &'static str, calls: Vec<(usize, Block)>, cols: &[(&'static str, Vec<f32>)]) -> Got {
    let (calls, cols) = (calls, cols.to_vec());
    with_checked(src, true, move |a| {
        let mut me = match Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None) {
            Ok(me) => me,
            Err(e) => return stopped(e.fault),
        };
        let (mut at, mut got) = (0, Vec::new());
        for (n, params) in calls {
            let params: Vec<(&str, Value)> = params.into_iter().map(|(k, v)| (k, Value::F32(v))).collect();
            let columns: Vec<Vec<Value>> =
                cols.iter().map(|(_, c)| c[at..at + n].iter().map(|v| Value::F32(*v)).collect()).collect();
            let ins: Vec<(&str, &[Value])> = cols.iter().zip(&columns).map(|((k, _), c)| (*k, &c[..])).collect();
            match me.process(&params, &ins, n, None) {
                Ok(outs) => outs.iter().for_each(|o| spread(o, &mut got)),
                Err(e) => return stopped(e.fault),
            }
            at += n;
        }
        Got::Values(got)
    })
}

fn stopped(f: Fault) -> Got {
    match f {
        Fault::Unavailable(_) => Got::Unavailable,
        Fault::Internal(_) => Got::Internal,
        f => Got::Other(format!("{f:?}")),
    }
}

fn rep(parts: &[(f32, usize)]) -> Vec<f32> {
    parts.iter().flat_map(|(v, n)| std::iter::repeat_n(*v, *n)).collect()
}

fn blk(p: f32) -> Block {
    vec![("p", p)]
}

#[test]
fn an_array_that_is_a_block_value_is_read_whole_by_each_run_of_an_up_chain_and_an_array_of_a_stream_is_dealt() {
    // §11.9, §11.3: `st~([p, p + 1.0]).up~(2)` runs `st` (`[F32; 2] at sample`) twice in a frame, and `p` is a value of `block`, read where it is used: both runs read the whole `[p, p + 1.0]`. p = 1: st = 10 p + (p + 1) = 12 in both runs, `fold2` (`x[0] * 100 + x[1]`) = 100 12 + 12 = 1212; p = 2: 23 and 2323.
    // The stream `up2s~(x)` is at `sample * 2` (the type of its element is `[F32; 2]`: the pair): the run j reads the pair j, `[c, c + 1]` and `[c + 2, c + 3]` for x = c: st = 11 c + 1 and 11 c + 23,
    // fold2 = 100 (11 c + 1) + 11 c + 23 = 1111 c + 123: x = 1, 2, 3 give 1234, 2345, 3456.
    let src = "flow st(x: [F32; 2] at sample) -> F32 at sample { x[0] * 10.0 + x[1] }
flow fold2(x: F32 at (sample * 2)) -> F32 at sample { x[0] * 100.0 + x[1] }
flow up2s(c: F32 at sample) -> [F32; 2] at (sample * 2) { [[c, c + 1.0], [c + 2.0, c + 3.0]] }
flow by_param(p: F32 at block) -> F32 at sample { fold2~(st~([p, p + 1.0]).up~(2)) }
flow by_stream(x: F32 at sample) -> F32 at sample { fold2~(st~(up2s~(x)).up~(2)) }";
    let want = rep(&[(1212.0, 3), (2323.0, 3)]);
    hold("repro_up_array_param", &run_src(src, "by_param", vec![(3, blk(1.0)), (3, blk(2.0))], &[]), &want);
    // §13.4: the same for another cut of the calls.
    hold(
        "repro_up_array_param",
        &run_src(src, "by_param", vec![(1, blk(1.0)), (2, blk(1.0)), (3, blk(2.0))], &[]),
        &want,
    );
    let x = vec![1.0, 2.0, 3.0];
    hold(
        "repro_up_array_stream",
        &run_src(src, "by_stream", vec![(3, vec![])], &[("x", x.clone())]),
        &[1234.0, 2345.0, 3456.0],
    );
    hold(
        "repro_up_array_stream",
        &run_src(src, "by_stream", vec![(1, vec![]), (2, vec![])], &[("x", x)]),
        &[1234.0, 2345.0, 3456.0],
    );
}

const TICKS: &str = "flow new4(x: F32 at (sample * 4)) -> F32 at sample { x[3] }
flow sum4(x: F32 at (sample * 4)) -> F32 at sample { x[0] + x[1] + x[2] + x[3] }
flow half(x: F32 at (sample * 2)) -> F32 at sample { x[1] }
flow acc2(v: F32 at sample) -> F32 at (sample / 2) { half~(v).down~(2) }
flow pt(a: F32 at (sample / 2)) -> F32 at (sample / 2) {
  let lf = a
  let q = prev~(^q) + (lf at sample)
  half~(q).down~(2)
}
flow j01(p: F32 at block) -> F32 at sample { pt~(p at (sample / 4)).down~(2) at sample }
flow j02(p: F32 at block) -> F32 at sample { new4~(pt~(p at (sample / 4)).down~(2) at sample).down~(4) at sample }
flow j03(p: F32 at block) -> F32 at sample { sum4~(pt~(p at (sample / 4)).down~(2) at sample).down~(4) at sample }
flow j04(p: F32 at block) -> F32 at sample { new4~(pt~(p at (sample / 2)) at sample).down~(4) at sample }
flow j05(p: F32 at block) -> F32 at sample { pt~(p at (sample / 2)) at sample }
flow k01(p: F32 at block) -> F32 at sample { acc2~((pt~(p at (sample / 4)).down~(2)) at (sample / 2)).down~(2) at sample }
flow acc2_t(p: F32 at block) -> F32 at sample { acc2~(p).down~(2) at sample }
";

#[test]
fn an_argument_that_is_a_call_with_an_output_at_a_tick_is_made_in_the_order_of_time_before_a_chain_gathers_it() {
    // §11.9 (S-578, S-1079, S-1088): `pt` has an input at `sample / 2`, a loop `q = prev~(^q) + (lf at sample)` of its own `sample` (`lf` is the input, held) and an output at `sample / 2` that is the newest of the 2 values
    // of `q` before its tick (`half~(q).down~(2)`: x[1], 0 at the first tick). p is 1, 3, 5, 7 in the four calls of 4 frames. `pt~(p at (sample / 4)).down~(2)` runs at the even c with its `sample` n = c / 2, its input ticks
    // at the even n (c = 0, 4, 8, 12) and reads p there (1, 3, 5, 7): lf is 1, 1 | 3, 3 | 5, 5 | 7, 7 for n = 0 .. 7, q = 1, 2, 5, 8, 13, 18, 25, 32; the output at the ticks n = 0, 2, 4, 6 is 0 and the q before: 0, q1 = 2,
    // q3 = 8, q5 = 18, at c = 0, 4, 8, 12: `j01` (the call alone, read with `at sample`) is 0 x 4, 2 x 4, 8 x 4, 18 x 4.
    // `j02`: the stream that the gather takes is that value at `sample` (0 x 4, 2 x 4, 8 x 4, 18 x 4 as c = 0 .. 15) and `new4~(..).down~(4)` runs at c = 0, 4, 8, 12 and takes x[3] of the 4 frames before it: the
    // frame c - 1: 0 (nothing before), 0, 2, 8: 0 x 8, 2 x 4, 8 x 4. `j03` takes the sum of the 4 frames before: 0, 0, 2 4 = 8, 8 4 = 32: 0 x 8, 8 x 4, 32 x 4.
    // `j04`: `pt` without a chain runs at each c (n = c) and its input ticks at the even n, reading p there: lf = 1 1 1 1 3 3 3 3 5 5 5 5 7 7 7 7, q = 1 2 3 4 7 10 13 16 21 26 31 36 43 50 57 64, the output at the even n is
    // q(n - 1): 0 2 4 10 16 26 36 50, held for two frames each; the gather at c = 4, 8, 12 takes the frame before: 2, 10, 26: 0 x 4, 2 x 4, 10 x 4, 26 x 4.
    // `k01`: `acc2` gathers (`half~(v).down~(2)`, the newest of two) what `pt` gives, read at `sample / 2` (at the even c: 0 0 2 2 8 8 18 18 for c = 0, 2, 4 ...), at its own frames n = c / 2: v(n) is 0 0 2 2 8 8 18 18; its output
    // at its ticks n = 0, 2, 4, 6 is v(n - 1): 0, v1 = 0, v3 = 2, v5 = 8, at c = 0, 4, 8, 12: 0 x 8, 2 x 4, 8 x 4.
    let calls = || (0..4).map(|i| (4, blk(1.0 + 2.0 * i as f32))).collect::<Vec<_>>();
    let cases: [(&str, &str, Vec<f32>); 6] = [
        // the stream `j04` gathers: 0 0 2 2 4 4 10 10 16 16 26 26 36 36 50 50
        ("j05", "repro_j05", vec![0., 0., 2., 2., 4., 4., 10., 10., 16., 16., 26., 26., 36., 36., 50., 50.]),
        ("j01", "repro_j01", rep(&[(0.0, 4), (2.0, 4), (8.0, 4), (18.0, 4)])),
        ("j02", "repro_j02", rep(&[(0.0, 8), (2.0, 4), (8.0, 4)])),
        ("j03", "repro_j03", rep(&[(0.0, 8), (8.0, 4), (32.0, 4)])),
        ("j04", "repro_j04", rep(&[(0.0, 4), (2.0, 4), (10.0, 4), (26.0, 4)])),
        ("k01", "repro_k01", rep(&[(0.0, 8), (2.0, 4), (8.0, 4)])),
    ];
    for (flow, row, want) in cases {
        hold(row, &run_src(TICKS, flow, calls(), &[]), &want);
    }
    // §13.4: not what the calls are cut at. With p = 1 in all calls lf is 1 at every tick and q = 1 2 3 4 5 6 7 8 for n = 0 .. 7, so the output of `pt` at the ticks n = 0, 2, 4, 6 is 0, q1 = 2, q3 = 4, q5 = 6 (at c = 0, 4, 8, 12):
    // `j01` is 0 x 4, 2 x 4, 4 x 4, 6 x 4, and `j02` takes the frame before c = 4, 8, 12 of that: 0, 0, 2, 4 (0 x 8, 2 x 4, 4 x 4).
    for cuts in [&[16][..], &[1; 16], &[5, 0, 7, 4]] {
        let calls = || cuts.iter().map(|n| (*n, blk(1.0))).collect::<Vec<_>>();
        hold("repro_j01", &run_src(TICKS, "j01", calls(), &[]), &rep(&[(0.0, 4), (2.0, 4), (4.0, 4), (6.0, 4)]));
        hold("repro_j02", &run_src(TICKS, "j02", calls(), &[]), &rep(&[(0.0, 8), (2.0, 4), (4.0, 4)]));
    }
}

#[test]
fn a_call_at_sample_times_n_kept_in_a_let_or_in_parentheses_or_given_as_a_block_value_is_read_as_the_value_of_the_call()
{
    // §11.9 ("`sample * N` の値に点ごとの演算をする形は当面は誤り" is for the operators; a name and a parenthesis are not an operation): `let d = ramp4~(p)` and `sum4~(d)` is `sum4~(ramp4~(p))`, `ramp4` giving
    // `[c, c + 1, c + 2, c + 3]` for `c` = p (a `block` value is read where it is used) and `sum4` their sum 4 p + 6: p = 1, 2: 10 x 3, 14 x 3, also with the call in parentheses (`h08`).
    // `ramp4~(p).down~(2)` runs at the even c and its 4 elements are dealt to the two frames in order (`sum2` is x[0] + x[1], `w2` is 10 x[0] + x[1]): the frame 2 n reads [q, q + 1] and 2 n + 1 reads [q + 2, q + 3], q = p of
    // the frame 2 n: p = 1 for the first 4 frames, 2 for the next 4: sum2 is 2 q + 1 and 2 q + 5, 3 7 3 7 5 9 5 9; with `w2` (11 q + 1 and 11 q + 23) added, 13 q + 2 and 13 q + 28: 15 41 15 41 28 54 28 54.
    let src = "flow sum4(x: F32 at (sample * 4)) -> F32 at sample { x[0] + x[1] + x[2] + x[3] }
flow sum2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] }
flow w2(x: F32 at (sample * 2)) -> F32 at sample { x[0] * 10.0 + x[1] }
flow ramp4(c: F32 at sample) -> F32 at (sample * 4) { [c, c + 1.0, c + 2.0, c + 3.0] }
flow h01(p: F32 at block) -> F32 at sample {
  let d = ramp4~(p)
  sum4~(d)
}
flow h08(p: F32 at block) -> F32 at sample { sum4~((ramp4~(p))) }
flow h02(p: F32 at block) -> F32 at sample {
  let d = ramp4~(p).down~(2)
  sum2~(d)
}
flow f09(p: F32 at block) -> F32 at sample {
  let d = ramp4~(p).down~(2)
  sum2~(d) + w2~(d)
}";
    let ten_then_fourteen = rep(&[(10.0, 3), (14.0, 3)]);
    for (flow, row) in [("h01", "repro_h01"), ("h08", "repro_h08")] {
        hold(row, &run_src(src, flow, vec![(3, blk(1.0)), (3, blk(2.0))], &[]), &ten_then_fourteen);
        hold(row, &run_src(src, flow, vec![(1, blk(1.0)), (2, blk(1.0)), (3, blk(2.0))], &[]), &ten_then_fourteen);
    }
    let two_calls = || vec![(4, blk(1.0)), (4, blk(2.0))];
    hold("repro_h02", &run_src(src, "h02", two_calls(), &[]), &[3.0, 7.0, 3.0, 7.0, 5.0, 9.0, 5.0, 9.0]);
    hold("repro_f09", &run_src(src, "f09", two_calls(), &[]), &[15.0, 41.0, 15.0, 41.0, 28.0, 54.0, 28.0, 54.0]);
}

#[test]
fn an_output_that_is_sample_tick_alone_at_a_tick_is_the_counter_of_the_instance_at_the_ticks_it_is_read_at() {
    // §11.4, S-1127 (1): `sample_tick()` is a `U32` of the clock of the place that reads it, the counter of the instance (the time since `init` in the ticks of its `sample`, 0 at the first frame: the existing tests of the
    // tick of a let). `tk` has it for its output at `sample / 2`: it is n = 0, 2, 4 at the ticks n = 0, 2, 4 of the body. `tk~(p at (sample / 4)).down~(2)` runs at the even c with n = c / 2, its output ticks at c = 0, 4, 8, and
    // holds (4 frames of the caller): 0 x 4, 2 x 4, 4 x 4. Without a chain the body is the caller's (n = c, the output ticks at the even c): 0 0 2 2 4 4 6 6 8 8 10 10.
    let src = "flow tk(v: F32 at (sample / 2)) -> U32 at (sample / 2) { sample_tick() }
flow h03(p: F32 at block) -> U32 at sample { tk~(p at (sample / 4)).down~(2) at sample }
flow h04(p: F32 at block) -> U32 at sample { tk~(p at (sample / 2)) at sample }";
    for cuts in [&[12][..], &[5, 7], &[1; 12]] {
        let calls = || cuts.iter().map(|n| (*n, blk(1.0))).collect::<Vec<_>>();
        hold("repro_h03", &run_src(src, "h03", calls(), &[]), &rep(&[(0.0, 4), (2.0, 4), (4.0, 4)]));
        hold(
            "repro_h04",
            &run_src(src, "h04", calls(), &[]),
            &[0.0, 0.0, 2.0, 2.0, 4.0, 4.0, 6.0, 6.0, 8.0, 8.0, 10.0, 10.0],
        );
    }
}

#[test]
fn the_changes_of_u2b_that_the_tests_of_u2b_let_through_are_held() {
    // A loop through three `let`s of a tick that read one another (the passes it takes to settle are not counted in the answer): `lf` is 1 at every tick (p = 1), `s1` is the running sum of `lf`: 1 2 3 at the ticks
    // c = 0, 4, 8, `s2` the running sum of `s1`: 1 3 6, `s3` that of `s2`: 1 4 10: 1 x 4, 4 x 4, 10 x 4.
    let src = "flow ring3(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let s1 = prev~(^s1) + lf
  let s2 = prev~(^s2) + s1
  let s3 = prev~(^s3) + s2
  s3 at sample
}
flow hs(a: F32 at (sample / 2)) -> F32 at sample { a at sample }
flow sum2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] }
flow up_hold(x: F32 at sample) -> F32 at sample { sum2~(hs~(x).up~(2)) }";
    hold("survivor_ring3", &run_src(src, "ring3", vec![(12, blk(1.0))], &[]), &rep(&[(1.0, 4), (4.0, 4), (10.0, 4)]));
    // `hs` takes a stream at `sample` for its input at `sample / 2` (k = -1, r = 1, q = 0), ticks in the first run of each frame, and gives it held to both: x = 1 .. 8: the bundle is [x, x] and `sum2` is 2 x: 2 4 6 .. 16.
    let x: Vec<f32> = (1..=8).map(|c| c as f32).collect();
    let want: Vec<f32> = (1..=8).map(|c| 2.0 * c as f32).collect();
    hold("survivor_up_hold", &run_src(src, "up_hold", vec![(8, vec![])], &[("x", x.clone())]), &want);
    hold("survivor_up_hold", &run_src(src, "up_hold", vec![(3, vec![]), (5, vec![])], &[("x", x)]), &want);
    // §11.9: a part with an output at a tick gives it at its own ticks; a frame that is not one of them does not run its tick. `acc2~(p).down~(2) at sample` (`acc2` makes `half~(v).down~(2)`: the `v` before its tick
    // n = 0, 2, 4, 6 at c = 0, 4, 8, 12) with p = 10 for 3 frames and 20 for 9: v is the p of the frame c = 2 n: 10 (c = 0, 2), 20 (c = 4, 6, ..): the ticks give 0, v(1) = p of c = 2 = 10, v(3) = p of c = 6 = 20: 0 x 4, 10 x 4, 20 x 4.
    // (A frame that reads the p of c = 3, where the call has changed, gives 20 at the tick c = 4.)
    hold(
        "survivor_acc2_cut",
        &run_src(TICKS, "acc2_t", vec![(3, blk(10.0)), (9, blk(20.0))], &[]),
        &rep(&[(0.0, 4), (10.0, 4), (20.0, 4)]),
    );
}

#[test]
fn the_rows_of_the_table_do_not_depend_on_where_the_calls_of_process_are_cut() {
    // §13.4: "呼び出しの切り方によらない". A choice of the rows (every pair of signs of (k, r) and (m, r), with a stream and with a `block` value) is run with the parameter that does not change, cut at the frames of the
    // sizes below (one call, one frame each, a call of 0 frames in it, cuts that fall inside the windows and the ticks: 5, 8, 21, 24 are not multiples of 2 or 4) and each run is held to the model of 24 frames of the one value.
    use Arg::{Param, Stream};
    let inputs = [
        (2, -2, Stream),
        (1, -1, Param),
        (-2, 2, Stream),
        (-1, 1, Stream),
        (2, 2, Param),
        (0, -2, Param),
        (-2, -2, Stream),
        (1, 1, Stream),
        (1, -2, Stream),
        (2, 0, Param),
        (-1, 2, Param),
        (0, 2, Stream),
    ];
    let outputs = [(2, -2), (-2, 2), (1, -1), (-1, -1), (1, 1), (0, 2), (1, -2), (-1, 2), (2, 1), (-2, -1)];
    let cuts: [&[usize]; 5] = [&[24], &[1; 24], &[7, 0, 17], &[5, 3, 13, 3], &[23, 1]];
    let calls = |cut: &[usize], v: f32| cut.iter().map(|n| (*n, v)).collect::<Calls>();
    let mut jobs = Vec::new();
    for cut in cuts {
        jobs.extend(inputs.iter().map(|(k, r, arg)| input_job(*k, *r, *arg, calls(cut, 10.0))));
        jobs.extend(outputs.iter().map(|(m, r)| output_job(*m, *r, calls(cut, 1.0))));
    }
    let got = run_jobs(table_source(), jobs);
    let mut rows = got.iter();
    for _ in cuts {
        for (k, r, arg) in inputs {
            hold(&in_name(k, r, arg), rows.next().expect("a row"), &model_in(k, r, arg, &[10.0; 24]));
        }
        for (m, r) in outputs {
            hold(&out_name(m, r), rows.next().expect("a row"), &model_out(m, r, &[1.0; 24]));
        }
    }
}

#[test]
fn the_ring_a_gather_keeps_is_counted_in_the_places_of_the_tree_for_each_element_of_its_window() {
    // The evaluator holds `Limits::most` (2^20 = 1 048 576) places for the whole tree (its own limit, the spec has none; see the delay lines and the `let`s in `instance_tests`): the ring of a gather has one place for each
    // element of its window. `big~(x).down~(262144)` takes the 2^18 values of the frames before its tick (262 144 places), and `big~(wide~(x)).down~(2)` the same 2^18 values as 2 frames of 2^17 (the stream `wide` is at
    // `sample * 131072`: a ring of 2 frames and 131 072 elements in each). Three of either (786 432 and the 8 places of an instance and one for each step) are made, and the first frame is the default of an input (0);
    // four (1 048 576 and the rest) are over the limit: `Unavailable`. (A ring that counts its frames and not the elements of each is 2 places, and four of them are made.)
    let src = "flow big(x: F32 at (sample * 262144)) -> F32 at sample { x[0] }
flow wide(c: F32 at sample) -> F32 at (sample * 131072) { [c; 131072] }
flow flat3(x: F32 at sample) -> F32 at sample {
  (big~(x).down~(262144) at sample) + (big~(x * 2.0).down~(262144) at sample) + (big~(x * 3.0).down~(262144) at sample)
}
flow flat4(x: F32 at sample) -> F32 at sample {
  (big~(x).down~(262144) at sample) + (big~(x * 2.0).down~(262144) at sample) + (big~(x * 3.0).down~(262144) at sample) + (big~(x * 4.0).down~(262144) at sample)
}
flow wide3(x: F32 at sample) -> F32 at sample {
  (big~(wide~(x)).down~(2) at sample) + (big~(wide~(x * 2.0)).down~(2) at sample) + (big~(wide~(x * 3.0)).down~(2) at sample)
}
flow wide4(x: F32 at sample) -> F32 at sample {
  (big~(wide~(x)).down~(2) at sample) + (big~(wide~(x * 2.0)).down~(2) at sample) + (big~(wide~(x * 3.0)).down~(2) at sample) + (big~(wide~(x * 4.0)).down~(2) at sample)
}";
    for (name, made) in [("flat3", true), ("flat4", false), ("wide3", true), ("wide4", false)] {
        let got = run_src(src, name, vec![(1, vec![])], &[("x", vec![1.0])]);
        match (made, &got) {
            (true, Got::Values(v)) => assert_eq!(v, &[0.0], "{name}"),
            (false, Got::Unavailable) => {}
            _ => panic!("{name}: {got:?}"),
        }
    }
}

#[test]
fn a_row_of_the_table_in_a_par_and_in_a_branch_has_its_own_ring_and_the_branch_not_taken_runs_too() {
    // §11.5, §11.9: `ib_u1~(..).down~(2)` (k = 1, r = -1: the digest `x[0] + 10 x[1]` of the 2 values before the tick, 21, 43, 65 for x = 1, 2, 3 .., 0 at the first) in a `par~` has an instance and a ring for each
    // replica, and in `if~` the branch that is not taken runs as well (§11.5). The replica 1 has 100 more in each value: (2 t - 1 + 100) + 10 (2 t + 100) = 22 t + 1099 for t >= 1 (t = 0 has the defaults, 0). The `if~`
    // has the digest of the replica 0 when `p` is 1 and 0 when it is 0, but the ring has taken the frames of the calls where `p` was 0: t = 0, 1 (c = 0 .. 3) have p = 0 and add 0, t = 2, 3 (c = 4 .. 7) add the digest.
    // The sum is 0 for t = 0, 21 + 1121 = 1142 for t = 1, 43 + 1143 + 43 = 1229 for t = 2 and 65 + 1165 + 65 = 1295 for t = 3, each for two frames.
    let src = format!(
        "{}flow comb(x: F32 at sample, p: F32 at block) -> F32 at sample {{
  let ks = [0.0, 100.0]
  let g = p > 0.5
  let r = par~ i in 0 ..< 2 {{ ib_u1~(x + ks[i]).down~(2) at sample }}
  let s = if~ g {{ ib_u1~(x).down~(2) at sample }} else {{ 0.0 }}
  r[0] + r[1] + s
}}",
        table_source()
    );
    let x: Vec<f32> = (1..=8).map(|c| c as f32).collect();
    let want = [0.0, 0.0, 1142.0, 1142.0, 1229.0, 1229.0, 1295.0, 1295.0];
    // `p` is 0 in the frames 0 .. 3 and 1 in 4 .. 7: no call is across the frame 4. §13.4: the same for the cuts.
    for cuts in [&[4, 4][..], &[2, 2, 2, 2], &[1; 8], &[3, 1, 0, 2, 2]] {
        let mut start = 0;
        let calls = cuts
            .iter()
            .map(|n| {
                start += n;
                (*n, blk(if start > 4 { 1.0 } else { 0.0 }))
            })
            .collect::<Vec<_>>();
        hold("par_branch", &run_src(&src, "comb", calls, &[("x", x.clone())]), &want);
    }
}
