//! The order of the work of a stage, by the divisions that panic (W7-11 U2b-e, S-1233): a flow of two to four of the places a division by zero can be in (a `let`, the
//! output, a call that is read and one that is not, calls one in the other, the first argument and the `init` of a delay, a condition of a modifier, a `par~`, an arm of `if~` and
//! `match~`, a child that divides in its `init`, its `block` or a stage of `sample / 4`, and a division of `sample`), each divisor one of the inputs of `init`, `block` and `sample`.
//! Which division is reported first is what the order says (§11.3, §3.5), so two things are held: the evaluator and the interpreter panic at the same stage and place
//! (`compare_case`, the place of the innermost flow), and the program written with each term of its output in a `let` of its own (a move that changes no stage, §11.3: "値は `let` に分けても分けなくても同じ")
//! has the same first division on the evaluator. A seed makes the program; the seeds of the gate are fixed, and a program that no scene panics in is not counted.

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Expect, Verdict, run_case_with};

use super::compare::compare_case;
use super::twin::{HEADER, Rng, SIGNATURE};
use super::twin_pan::scenes;

/// The children that divide: in `block`, in `init`, and in a tick of `sample / 4` (at its first tick the time is 0, so `t4 + b` is `b`).
const KIDS: &str = "pub flow kb(x: F32 at sample, b: U32 at block) -> F32 at sample { x * F32.round_from(100 / b) }
pub flow kn(x: F32 at sample, c: U32 at init) -> F32 at sample { x * F32.round_from(100 / c) }
pub flow ks(x: F32 at sample, b: U32 at block) -> F32 at sample {
  let t4 = sample_tick() at (sample / 4)
  let q = F32.round_from(100 / (t4 + b))
  x + (q at sample) * 0.0
}
";

/// The places, by tag: what is written before the output (`{i}` the number of the place, `{N}` a numerator no other has, `{D}` a divisor of any input, `{U}` and `{V}` one of `init` or `block`) and the term of the output.
#[rustfmt::skip]
pub const PLACES: &[(&str, &str, &str)] = &[
    ("let", "let a{i} = x * F32.round_from({N} / {D})", "a{i}"), ("out", "", "x * F32.round_from({N} / {D})"),
    ("read", "let r{i} = kb~(x, {U})", "r{i}"), ("unread", "let _ = kb~(x, {U})", ""),
    ("nested", "", "kb~(kb~(x, {U}), {V})"), ("delay_arg", "", "prev~(x * F32.round_from({N} / {D}))"),
    ("delay_call", "", "prev~(kb~(x, {U}))"), ("delay_init", "", "prev~(x, F32.round_from({N} / n))"),
    ("cond", "", "kb~(x, {U}).reset_if~({N} / {V} > 3)"), ("par", "", "sum2(par~ j{i} in 0 ..< 2 { kb~(x, {U}) })"),
    ("if", "", "if~ x > 0.0 { kb~(x, {U}) } else { x * F32.round_from({N} / {D}) }"),
    ("match", "", "match~ ku { 0 => kb~(x, {U}), _ => x * F32.round_from({N} / {D}) }"),
    ("child_init", "", "kn~(x, n)"), ("slow", "let s{i} = ks~(x, {U})", "s{i}"), ("sample", "", "x * F32.round_from({N} / ku)"),
    ("delay_if", "", "prev~(if~ x > 0.0 { kb~(x, {U}) } else { x })"), ("delay_match", "", "prev~(match~ ku { 0 => kb~(x, {U}), _ => x })"),
    ("delay_par", "", "sum2(prev~(par~ j{i} in 0 ..< 2 { kb~(x, {U}) }))"),
];

/// A program: the places it holds and its text, with the terms of its output where they are written or each in a `let` (`moved`).
pub fn make(seed: u64, moved: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let (mut lets, mut terms, mut tags) = (Vec::new(), Vec::new(), BTreeSet::new());
    for i in 0..2 + rng.below(3) {
        let (tag, before, term) = *rng.pick_in(PLACES);
        tags.insert(tag);
        let (d, u, v) = (rng.pick(&["k", "n", "ki"]), rng.pick(&["k", "n"]), rng.pick(&["k", "n"]));
        let text = |t: &str| {
            t.replace("{i}", &i.to_string())
                .replace("{N}", &(100 * (i + 1)).to_string())
                .replace("{D}", d)
                .replace("{U}", u)
                .replace("{V}", v)
        };
        lets.extend((!before.is_empty()).then(|| text(before)));
        if !term.is_empty() {
            terms.push(text(term));
        }
    }
    if moved {
        for (i, t) in terms.iter_mut().enumerate() {
            lets.push(format!("let m{i} = {t}"));
            *t = format!("m{i}");
        }
    }
    let body = if terms.is_empty() {
        "x".to_string()
    } else {
        terms.iter().map(|t| format!("({t})")).collect::<Vec<_>>().join(" + ")
    };
    let ku = if (lets.join("") + &body).contains("ku") { "  let ku: U32 = if x > 0.0 { 2 } else { 0 }\n" } else { "" };
    let lets: String = lets.iter().map(|l| format!("  {l}\n")).collect();
    let flow = format!("pub flow fa{SIGNATURE} -> F32 at sample {{\n{ku}{lets}  {body}\n}}\n");
    let tests: String = scenes(&[0, 2]).iter().map(|s| s.text("[-0.5, -1.0]")).collect();
    (HEADER.to_string() + KIDS + &flow + &tests, tags)
}

/// What each test of a program did on the evaluator (the stage it panicked at and the text of the expression it stopped at, none for no panic), and what is wrong in the interpreter.
type Panics = (Vec<Option<(String, String)>>, Vec<String>);

/// The panics of the program `src`.
fn panics(src: &str, wrappers: &Wrappers, compared: bool) -> Result<Panics, String> {
    let input = PackageInput::single_file("order.onsa", src);
    let run = run_case_with(input.clone(), wrappers, Expect::Evaluator)?;
    let mut got = Vec::new();
    for t in &run.tests {
        if t.verdict != Verdict::Ok {
            return Err(format!("{}: {:?}", t.name, t.verdict));
        }
        let at = t.panic_span.map(|s| src[s.start as usize..s.end as usize].to_string());
        got.push(t.panic.map(|p| (format!("{p:?}"), at.unwrap_or_default())));
    }
    Ok((got, if compared { compare_case("order.onsa", input, &run).failures } else { Vec::new() }))
}

/// The seeds run: how many scenes panicked, and what is wrong (the interpreter at another place, the move that gives another first division).
pub fn run(seeds: Vec<u64>, compared: bool) -> (usize, Vec<String>) {
    stack::run(move || {
        let (wrappers, mut panicked, mut bad) = (Wrappers::default(), 0, Vec::new());
        for seed in seeds {
            let (src, tags) = make(seed, false);
            match (panics(&src, &wrappers, compared), panics(&make(seed, true).0, &wrappers, false)) {
                (Ok((a, same)), Ok((b, _))) => {
                    panicked += a.iter().flatten().count();
                    let moved: Vec<_> = a.iter().zip(&b).filter(|(x, y)| x != y).collect();
                    bad.extend((!same.is_empty()).then(|| format!("seed {seed} {tags:?}: {}\n{src}", same.join("\n"))));
                    bad.extend((!moved.is_empty()).then(|| format!("seed {seed} {tags:?}: moved {moved:?}\n{src}")));
                }
                (a, b) => bad.push(format!("seed {seed} {tags:?}: not run: {:?} {:?}\n{src}", a.err(), b.err())),
            }
        }
        (panicked, bad)
    })
}
