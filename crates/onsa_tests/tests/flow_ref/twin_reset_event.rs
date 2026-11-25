//! The twins of a `reset_if~` of an event (W7-11 U2r/e; §11.10, §11.11, §11.3, S-1236, S-1250 (B)). A seed makes one program of two flows `fa` and `fb` of `sample` ports that the text says give the same outputs, and the evaluator
//! asserts it on the grid and the `process` cut of `twin.rs`: `fa` writes a form as it is, `fb` writes it again with the receiver in a flow of its own (the modifier is on its call, §11.10), the condition or the delay in a `let`
//! (§11.3 "値は `let` に分けても分けなくても同じ"; a delay with a modifier is the value where it is written, so the inner one of a nested pair is a `let` as well, S-1250 (B)), or the two `reset_if~`s of one source and one
//! tick folded into one condition with `||` (each condition puts back the whole, and a frame where both hold is one reset, §11.10).

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Expect, Verdict, run_case_with};

use super::compare::compare_case;
use super::twin::{HEADER, Rng, program};

const PARTS: &str = "flow g(x: F32 at sample) -> F32 at event { if x > 0.25 { Some(x) } else { None } }
flow su(e: F32 at event) -> F32 at sample {
  let s = prev~(^s) + e
  s
}
flow wr(e: F32 at event) -> F32 at sample { su~(e) }
flow wh(e: F32 at event) -> F32 at sample { su~(e).reset_if~(e > {T}) }
";

/// A form: `fa` (the `let`s and the output) and `fb`, the other way of writing it. `{T}` and `{U}` are numbers to compare with.
struct Form {
    tag: &'static str,
    fa: (&'static [&'static str], &'static str),
    fb: (&'static [&'static str], &'static str),
}

const PRODUCERS: [&str; 2] = ["let a = g~(x)", "let b = g~(x * 2.0)"];

#[rustfmt::skip]
const FORMS: &[Form] = &[
    Form { tag: "wrap_receiver", fa: (&PRODUCERS, "su~(a).reset_if~(b > {T})"), fb: (&PRODUCERS, "wr~(a).reset_if~(b > {T})") },
    Form { tag: "wrap_with_condition", fa: (&["let a = g~(x)"], "su~(a).reset_if~(a > {T})"), fb: (&["let a = g~(x)"], "wh~(a)") },
    Form { tag: "condition_in_a_let", fa: (&PRODUCERS, "su~(a).reset_if~(b > {T})"),
        fb: (&["let a = g~(x)", "let b = g~(x * 2.0)", "let c = b > {T}"], "su~(a).reset_if~(c)") },
    Form { tag: "folded_with_or", fa: (&PRODUCERS, "su~(a).reset_if~(b > {T}).reset_if~(b > {U})"), fb: (&PRODUCERS, "su~(a).reset_if~((b > {T}) || (b > {U}))") },
    Form { tag: "delay_below", fa: (&["let p = prev~(^d)", "let q = prev~(x, 9.0).reset_if~(p > {T})", "let d = g~(x)"], "q"),
        fb: (&["let p = prev~(^d)", "let c = p > {T}", "let q = prev~(x, 9.0).reset_if~(c)", "let d = g~(x)"], "q") },
    Form { tag: "delay_nested", fa: (&["let p = prev~(^d)", "let q = prev~(prev~(x, 9.0).reset_if~(p > {T}), 7.0)", "let d = g~(x)"], "q"),
        fb: (&["let p = prev~(^d)", "let m = prev~(x, 9.0).reset_if~(p > {T})", "let q = prev~(m, 7.0)", "let d = g~(x)"], "q") },
    Form { tag: "vdelay_below", fa: (&["let p = prev~(^d)", "let q = vdelay~(x, 2.0, 4, 9.0).reset_if~(p > {T})", "let d = g~(x)"], "q"),
        fb: (&["let p = prev~(^d)", "let c = p > {T}", "let q = vdelay~(x, 2.0, 4, 9.0).reset_if~(c)", "let d = g~(x)"], "q") },
    Form { tag: "delay_of_an_event", fa: (&["let a = g~(x)", "let b = g~(x * 2.0)", "let p = prev~(a, 9.0).reset_if~(b > {T})"], "p at sample"),
        fb: (&["let a = g~(x)", "let b = g~(x * 2.0)", "let c = b > {T}", "let p = prev~(a, 9.0).reset_if~(c)"], "p at sample") },
    Form { tag: "loop_through_the_producer", fa: (&["let p = prev~(^d)", "let c: F32 = prev~(^c + 1.0).reset_if~(p > {T})", "let d = g~(c)"], "c"),
        fb: (&["let p = prev~(^d)", "let t = p > {T}", "let c: F32 = prev~(^c + 1.0).reset_if~(t)", "let d = g~(c)"], "c") },
];

/// The tags of the forms.
pub fn cover() -> BTreeSet<&'static str> {
    FORMS.iter().map(|f| f.tag).collect()
}

/// The form a seed makes.
fn form_of(seed: u64) -> &'static Form {
    &FORMS[seed as usize % FORMS.len()]
}

pub fn tag_of(seed: u64) -> &'static str {
    form_of(seed).tag
}

/// A program: `fa` is the form as it is and `fb` the twin (`rot` makes `fb` give one more).
pub fn make(seed: u64, rot: bool) -> String {
    let mut rng = Rng::new(seed);
    let (t, u) = (rng.pick(&["0.5", "1.0", "2.0"]), rng.pick(&["0.25", "1.5"]));
    let text = |(lets, out): (&[&str], &str)| {
        let s = lets.iter().map(|l| format!("{l}\n  ")).collect::<String>() + out;
        s.replace("{T}", t).replace("{U}", u)
    };
    let form = form_of(seed);
    let fb = text(form.fb);
    let fb = if rot { format!("({fb}) + 1.0") } else { fb };
    let defs = PARTS.replace("{T}", t);
    let mut rng = Rng::new(seed ^ 0xE7E7);
    program(&mut rng, &(HEADER.to_string() + &defs), (&text(form.fa), &fb, "F32"), None)
}

/// What the programs came to: how many, their tests, how many were evaluated, those the interpreter ran again, and what is wrong.
#[derive(Debug, Default)]
pub struct Ran {
    pub programs: usize,
    pub tests: usize,
    pub evaluated: usize,
    pub compared: usize,
    pub lowered: usize,
    pub bad: Vec<String>,
}

pub fn run(seeds: Vec<u64>, rot: bool, compare: bool) -> Ran {
    stack::run(move || {
        let (wrappers, mut r) = (Wrappers::default(), Ran::default());
        for seed in seeds {
            let src = make(seed, rot);
            let input = PackageInput::single_file(format!("reset_event_{seed}.onsa"), &src);
            r.programs += 1;
            match run_case_with(input.clone(), &wrappers, Expect::Evaluator) {
                Err(e) => r.bad.push(format!("seed {seed}: not read: {e}\n{src}")),
                Ok(run) => {
                    r.tests += run.tests.len();
                    for t in &run.tests {
                        match &t.verdict {
                            Verdict::Ok if t.panic.is_none() => r.evaluated += 1,
                            v => r.bad.push(format!("seed {seed}: \"{}\": {v:?} {:?}\n{src}", t.name, t.panic)),
                        }
                    }
                    r.lowered += usize::from(run.lowered && !run.e0200);
                    if compare && run.lowered && !run.e0200 {
                        let c = compare_case(&format!("reset_event_{seed}.onsa"), input, &run);
                        r.compared += c.ran;
                        r.bad.extend(c.failures.into_iter().map(|m| format!("seed {seed}: {m}\n{src}")));
                    } else if compare {
                        r.bad.push(format!("seed {seed}: the interpreter does not lower the program\n{src}"));
                    }
                }
            }
        }
        r
    })
}
