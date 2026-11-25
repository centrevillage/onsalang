//! The twins of the reference to what is below (`^名前`, W7-11 U2b/t2, S-1233, S-1241, S-1244, S-1245): a form `f` and the same flow with the part that reads the `let` below written as a reference `r`, which give the same values
//! (the evaluator holds it, and the interpreter is compared with the evaluator). Three tables: `PAIRS` (12 pairs written by hand, a note of the text each rests on), `HEADS` and `WRAPS` (a seed crosses a head with a wrap), and
//! the pairs whose reads of a `let` are moved where there is a division that panics (`panics`: the stage and the place of the first panic are the same in `f` and in `r`, and the interpreter panics where the evaluator does).
//! The part that reads a name below at a slower stage than the delay it is in (`^名前` in a part that waits for the stage, S-1244 (1)) is `late`: the Core of `d439fac` stops there (R-520), so those twins are ignored until U2b.
//! A form that reads a binding of an arm of a `match~` in the argument of a flow is not a twin (E0801, S-1245 (a), `tests/spec/flow_clock/e0801_match_binding_of_a_caret_*.onsa`).

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Expect, Verdict, run_case_with};

use super::compare::compare_case;
use super::twin::{HEADER, Rng, SIGNATURE, program};
use super::twin_pan::scenes;

/// A flow that has a state of its own to put in the argument of a delay (`HEADER` has the stateless ones, and `acc`).
const HELP: &str = "pub flow gg(x: F32 at sample) -> F32 at sample {\n  x + prev~(x)\n}\n";

/// The lets the pairs read: `block` (`k`), `init` (`n`), the sample, the grid of `sample / 4` (a value of a tick and a value of the block, held), an `Option`, and the condition of the grid.
const KB: &str = "let kb = F32.round_from(k) + 1.0";
const KN: &str = "let kn = F32.round_from(n) + 1.0";
const KD: &str = "let kd = if x > 0.0 { 2.0 } else { 3.5 }";
const D4: &str = "let d4 = prev~(F32.round_from(k) at (sample / 4), 1.0)";
const K4: &str = "let k4 = d4 + 1.0";
const C4: &str = "let c4 = d4 > 1.5";
const W: &str = "let w = x * 0.5";
/// `W` with a division that panics at `block` when `k` is 0 (the same let, the same place in the pair).
const W_DIV: &str = "let w = x * 0.5 + F32.round_from(100 / k)";
const V: &str = "let v: Option[F32] = if x > 0.0 { Some(x) } else { None }";

/// A pair: its tag, whether the part that reads a `let` below waits for the stage (`late`), the lines of the body of `f` and of `r` (the last is the output).
type Pair = (&'static str, bool, &'static [&'static str], &'static [&'static str]);

/// The pairs, by a class of writing. What each rests on: §11.2 "`^名前` is the `let` below at the same frame" and "見えている名前に `^` を付けると…値は同じ" (the value of `^kb` is the value of `kb` where the `let` is above it);
/// §11.3 "値は `let` に分けても分けなくても同じである（`let` は名前を付けるだけ）"; §11.4 "遅延の `e` の中の遅延は、保存の前の出力を読む" (`prev~(inner)` is `let t = inner` and `prev~(t)`); §11.10 for the modifiers.
#[rustfmt::skip]
pub const PAIRS: [Pair; 12] = [
    // The read of a block value in an operand next to a call, as a part of the first argument (S-1244 (1): the part is the value of the stage `block`, put by the end of the stage of the delay).
    ("late_operand", true, &["let y = prev~(gg~(x) * (^kb * 2.0))", KB, "y + x"], &[KB, "let y = prev~(gg~(x) * (kb * 2.0))", "y + x"]),
    // The same, with the delay in the argument of a flow of the user (the call is where it is written, S-1233; §11.2 the `^` is in the first argument of a delay, the delay in the argument is allowed).
    ("late_in_a_flow_argument", true, &["let y = twice~(prev~(x * (^kb * 2.0)))", KB, "y + x"], &[KB, "let y = twice~(prev~(x * (kb * 2.0)))", "y + x"]),
    // A read of a value of the grid of `sample / 4` brought to `sample` by `at` (§11.3: "段が刻みの計算した部分式は…その刻みで評価し"; the value is the tick's).
    ("late_slow", true, &[D4, "let y = prev~((^k4 * 2.0) at sample)", K4, "y + x"], &[D4, K4, "let y = prev~((k4 * 2.0) at sample)", "y + x"]),
    // A `par~` of the argument whose copies read the slow value (§11.5: the copies are of the same stage and each copy has the call of its own).
    ("late_par_slow", true, &[D4, "let y = prev~(par~ i in 0 ..< 2 { gg~(x) + ((^k4 * F32.round_from(i + 1)) at sample) })", K4, "sum2(y) + x"],
        &[D4, K4, "let y = prev~(par~ i in 0 ..< 2 { gg~(x) + ((k4 * F32.round_from(i + 1)) at sample) })", "sum2(y) + x"]),
    // Modifiers on the call in the argument and on the delay itself (§11.10: the conditions are evaluated where they are written; the reset is of the part that is the receiver).
    ("late_modifiers", true, &[D4, "let y = prev~(gg~(x).reset_if~(x < -4.0) + ((^k4 * 2.0) at sample)).reset_if~(x > 6.5)", K4, "y + x"],
        &[D4, K4, "let y = prev~(gg~(x).reset_if~(x < -4.0) + ((k4 * 2.0) at sample)).reset_if~(x > 6.5)", "y + x"]),
    // The read in the `init` of a delay inside a delay (§11.3: the `init` of a delay is evaluated where it is written; the init clock is below the stage of the delay).
    ("init_of_a_nested_delay", false, &["let y = prev~(prev~(x, ^kn))", KN, "y + x"], &[KN, "let y = prev~(prev~(x, kn))", "y + x"]),
    // The read in the `d` of a `vdelay~` with a `reset_if~`, and the inner delay as the `let` that `prev~` reads (§11.4: `prev~(inner)` stores the output of the inner one before its store, which `let t = inner` and `prev~(t)` give).
    ("vdelay_d_with_a_reset", false, &["let c = x < -4.0", "let y = prev~(vdelay~(x, ^kd, 8).reset_if~(c))", KD, "y + x"],
        &["let c = x < -4.0", KD, "let t = vdelay~(x, kd, 8).reset_if~(c)", "let y = prev~(t)", "y + x"]),
    // Calls in the argument of a delay in a `par~` and the read of a `let` of the sample below (the call of each copy is its own; the `let w` is a name, so it stays where it is).
    ("calls_in_a_par", false, &["let ys = par~ i in 0 ..< 2 { prev~(gg~(x * F32.round_from(i + 1)) + ^w) }", W, "sum2(ys) + x"],
        &[W, "let ys = par~ i in 0 ..< 2 { prev~(gg~(x * F32.round_from(i + 1)) + w) }", "sum2(ys) + x"]),
    // A call in the argument of a delay in the argument of a call in a delay; the call that is written inside is moved into a `let` above (§11.3: the same value, and the same place of the work of the call).
    ("nested_calls", false, &["let y = prev~(gg~(prev~(gg~(x) + ^w)) + ^w)", W, "y + x"], &["let a = gg~(x)", W, "let c = gg~(prev~(a + w))", "let y = prev~(c + w)", "y + x"]),
    // A `when~` on the delay over a `par~` of calls; the calls of the copies move into a `let` of the array that `ys` reads by the index (§11.10: the receiver is the delay, its argument is of the caller's stage).
    ("when_over_calls_in_a_par", false, &["let c = x > -4.0", "let ys = par~ i in 0 ..< 2 { prev~(gg~(x * F32.round_from(i + 1)) + ^w).when~(c) }", W, "sum2(ys) + x"],
        &["let c = x > -4.0", W, "let gs = par~ i in 0 ..< 2 { gg~(x * F32.round_from(i + 1)) }", "let ys = par~ i in 0 ..< 2 { prev~(gs[i] + w).when~(c) }", "sum2(ys) + x"]),
    // A delay that has a reset of a condition of `sample / 4` as the first argument of another one, and the reset delay as a `let` (§11.10: "条件の刻みは、条件の式のクロックで決まり"; §11.3: "初期化した後の値").
    ("slow_reset_in_a_delay", false, &[D4, C4, "let y = prev~(prev~(x).reset_if~(c4))", "y + x"], &[D4, C4, "let a = prev~(x).reset_if~(c4)", "let y = prev~(a)", "y + x"]),
    // A binding of an arm of a `match~` whose target reads `^v`, read in the `d` of a delay in the arm (S-1245 (a): the `d` is not the argument of a flow); the `match~` as a `let` below that `prev~` reads.
    ("binding_in_the_d", false, &["let y = prev~(match~ ^v { Some(b) => vdelay~(x, b + 1.0, 8), None => 0.0 })", V, "y + x"],
        &["let y = prev~(^t)", V, "let t = match~ v { Some(b) => vdelay~(x, b + 1.0, 8), None => 0.0 }", "y + x"]),
];

/// The head of a crossed program: its tag, whether it is `late`, the lines above the `let` that is read, the name and the line of that `let`, and the term that reads it (`{R}` is the read: `^name` in `f`, `name` in `r`).
type Head = (&'static str, bool, &'static [&'static str], &'static str, &'static str, &'static str);

/// The heads, by what the read is in: an operand next to a call and a slow value (both wait for the stage), the `init` and the `d` of a delay in the argument, and a `let` of the sample next to a call.
#[rustfmt::skip]
pub const HEADS: [Head; 5] = [
    ("operand", true, &[], "kb", KB, "gg~(x) * ({R} * 2.0)"),
    ("slow", true, &[D4], "k4", K4, "({R} * 2.0) at sample"),
    ("init", false, &[], "kn", KN, "prev~(x, {R}) * 2.0"),
    ("d", false, &[], "kd", KD, "vdelay~(x, {R}, 8)"),
    ("call_sum", false, &[], "w", W, "gg~(x) + {R}"),
];

/// The wraps of the term `{T}` (the first argument of the delay it is in): by themselves, in a delay, in a `par~`, with the modifiers of the delay, and in the argument of a flow.
#[rustfmt::skip]
pub const WRAPS: [(&str, &str); 7] = [
    ("direct", "prev~({T})"), ("in_a_delay", "prev~(prev~({T}))"), ("par", "sum2(par~ j in 0 ..< 2 { prev~({T}) })"),
    ("when", "prev~({T}).when~(x > -4.0)"), ("reset", "prev~({T}).reset_if~(x > 6.5)"), ("flow_arg", "twice~(prev~({T}))"),
    ("when_reset", "prev~({T}).when~(x > -4.0).reset_if~(x > 6.5)"),
];

/// The program of the flows `fa` and `fb` of the lines (`rot`, the mutant: the output of `fb` is one more).
fn make_lines(seed: u64, f: &[&str], r: &[&str], rot: bool) -> String {
    let body = |ls: &[&str], rot: bool| {
        let mut ls: Vec<String> = ls.iter().map(|l| l.to_string()).collect();
        if let (true, Some(last)) = (rot, ls.last_mut()) {
            *last = format!("({last}) + 1.0");
        }
        ls.join("\n  ")
    };
    program(&mut Rng::new(seed), &format!("{HEADER}{HELP}"), (&body(f, false), &body(r, rot), "F32"), None)
}

/// The program of a pair of `PAIRS` (the seed picks it, and makes the inputs): its tags are the tag of the pair, and `late` when it waits for the stage.
pub fn make_pair(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let (tag, late, f, r) = PAIRS[seed as usize % PAIRS.len()];
    (make_lines(seed, f, r, rot), [tag].into_iter().chain(late.then_some("late")).collect())
}

/// The program of a head crossed with a wrap (the seed is `head + 5 * wrap`, and the inputs): `f` reads the `let` below with `^`, `r` has the `let` above and reads its name.
pub fn make_cross(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let (htag, late, above, name, def, term) = HEADS[seed as usize % HEADS.len()];
    let (wtag, wrap) = WRAPS[seed as usize / HEADS.len() % WRAPS.len()];
    let y = |read: &str| format!("let y = {}", wrap.replace("{T}", &term.replace("{R}", read)));
    let [fy, ry] = [y(&format!("^{name}")), y(name)];
    let f = [above, &[fy.as_str(), def, "y + x"][..]].concat();
    let r = [above, &[def, ry.as_str(), "y + x"][..]].concat();
    (make_lines(seed, &f, &r, rot), [htag, wtag].into_iter().chain(late.then_some("late")).collect())
}

/// The seed of a head and a wrap.
pub fn cross_seed(head: usize, wrap: usize) -> u64 {
    (head + HEADS.len() * wrap) as u64
}

/// The pairs that hold a division when `w` is `W_DIV`: the divisor `k` is 0 in some scenes, the `let w` is moved from below to above (and the calls into `let`s) with no change of stage.
pub const DIVIDING: [&str; 3] = ["calls_in_a_par", "nested_calls", "when_over_calls_in_a_par"];

/// The program of the flow `fa` of one side of a dividing pair (`r` when `moved`) with the scenes of `init` and `process` that `twin_order.rs` uses.
fn dividing(tag: &str, moved: bool) -> String {
    let &(_, _, f, r) = PAIRS.iter().find(|p| p.0 == tag).expect("a pair of the table");
    let side = if moved { r } else { f };
    let body = side.iter().map(|l| l.replace(W, W_DIV)).collect::<Vec<_>>().join("\n  ");
    let flow = format!("pub flow fa{SIGNATURE} -> F32 at sample {{\n  {body}\n}}\n");
    let tests: String = scenes(&[0, 2]).iter().map(|s| s.text("[-0.5, -1.0]")).collect();
    format!("{HEADER}{HELP}{flow}{tests}")
}

/// What each test of a program did on the evaluator (the stage it panicked at and the text of the expression it stopped at, none for no panic), and what is wrong in the interpreter.
type Panics = (Vec<Option<(String, String)>>, Vec<String>);

fn panics(src: &str, wrappers: &Wrappers, compared: bool) -> Result<Panics, String> {
    let input = PackageInput::single_file("back.onsa", src);
    let run = run_case_with(input.clone(), wrappers, Expect::Evaluator)?;
    let mut got = Vec::new();
    for t in &run.tests {
        if t.verdict != Verdict::Ok {
            return Err(format!("{}: {:?}", t.name, t.verdict));
        }
        let at = t.panic_span.map(|s| src[s.start as usize..s.end as usize].to_string());
        got.push(t.panic.map(|p| (format!("{p:?}"), at.unwrap_or_default())));
    }
    Ok((got, if compared { compare_case("back.onsa", input, &run).failures } else { Vec::new() }))
}

/// The dividing pairs run: how many scenes panicked, and what is wrong (the interpreter panics at another place; the two sides give another stage or another place of the first panic).
pub fn run_dividing(tags: &[&str]) -> (usize, Vec<String>) {
    let tags: Vec<String> = tags.iter().map(|t| t.to_string()).collect();
    stack::run(move || {
        let (wrappers, mut panicked, mut bad) = (Wrappers::default(), 0, Vec::new());
        for tag in &tags {
            let (f, r) = (dividing(tag, false), dividing(tag, true));
            match (panics(&f, &wrappers, true), panics(&r, &wrappers, false)) {
                (Ok((a, same)), Ok((b, _))) => {
                    panicked += a.iter().flatten().count();
                    bad.extend((!same.is_empty()).then(|| format!("{tag}: the interpreter: {}", same.join("\n"))));
                    bad.extend(
                        (a != b).then(|| format!("{tag}: the first panic of `f` {a:?} is not that of `r` {b:?}")),
                    );
                }
                (a, b) => bad.push(format!("{tag}: not run: {:?} {:?}", a.err(), b.err())),
            }
        }
        (panicked, bad)
    })
}
