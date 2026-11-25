//! The twins of the reads of an event and of a `when~` with an event (W7-11 U3/e; §11.3, §11.10, §11.11, S-563, S-1185, S-1209, S-1210). A seed makes one program of two flows `fa` and `fb` of `sample` ports that the text says give the same
//! outputs, and the evaluator asserts it on the grid and the `process` cut of `twin.rs`. The reads: a read that stays where it is written or is cut to a `let` (`(a at (sample / 4)) at sample` and `let m = a at (sample / 4)`, S-1210), a computed
//! part of an event that is moved to a `let` before (§11.3 "値は `let` に分けても分けなくても同じ"), an event given to a `sample` input. The levels of a `when~` (§11.10): the receiver in a flow of its own (a counter, a delay), the condition in a `let`
//! (the event expression) or with `at sample` (a `(q) at sample` of an event expression is the same value, which `(v at sample) == 0` is not), and two `when~`s folded into one condition with `&&`.

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Expect, Verdict, run_case_with};

use super::compare::compare_case;
use super::twin::{HEADER, Rng, program};

const PARTS: &str = "flow g(x: F32 at sample) -> F32 at event { if x > 0.25 { Some(x) } else { None } }
flow cn() -> F32 at sample {
  let n = prev~(^n) + 1.0
  n
}
flow gt(c: Bool at sample) -> F32 at sample { cn~().when~(c) }
flow dl(x: F32 at sample) -> F32 at sample { prev~(x, 9.0) }
flow idn(v: F32 at sample) -> F32 at sample { v }
";

/// A form: `fa` (the `let`s and the output) and `fb`, the other way of writing it. `{T}` and `{U}` are numbers to compare with; `when` is a form with a `when~` of an event (S-563).
struct Form {
    tag: &'static str,
    when: bool,
    fa: (&'static [&'static str], &'static str),
    fb: (&'static [&'static str], &'static str),
}

const A: &[&str] = &["let a = g~(x)"];

#[rustfmt::skip]
const FORMS: &[Form] = &[
    Form { tag: "slow_read_in_a_let", when: false, fa: (A, "(a at (sample / 4)) at sample"), fb: (&["let a = g~(x)", "let m = a at (sample / 4)"], "m at sample") },
    Form { tag: "computed_in_a_let", when: false, fa: (A, "x + a * 2.0"), fb: (&["let a = g~(x)", "let d = a * 2.0"], "x + d") },
    Form { tag: "computed_under_the_event", when: false, fa: (A, "if a > {T} { a * 2.0 } else { x }"), fb: (&["let a = g~(x)", "let d = a * 2.0"], "if a > {T} { d } else { x }") },
    Form { tag: "given_to_a_flow", when: false, fa: (A, "a at sample"), fb: (A, "idn~(a)") },
    Form { tag: "wrap_the_receiver", when: true, fa: (A, "cn~().when~(a > {T})"), fb: (A, "gt~(a > {T})") },
    Form { tag: "level_in_a_let", when: true, fa: (A, "cn~().when~(a > {T})"), fb: (&["let a = g~(x)", "let on = a > {T}"], "cn~().when~(on)") },
    Form { tag: "level_at_sample", when: true, fa: (A, "cn~().when~(a > {T})"), fb: (A, "cn~().when~((a > {T}) at sample)") },
    Form { tag: "wrap_the_delay", when: true, fa: (A, "prev~(x, 9.0).when~(a > {T})"), fb: (A, "dl~(x).when~(a > {T})") },
    Form { tag: "two_whens", when: true, fa: (A, "cn~().when~(a > {T}).when~(a > {U})"), fb: (A, "cn~().when~((a > {T}) && (a > {U}))") },
    Form { tag: "mixed_with_a_sample", when: true, fa: (A, "cn~().when~((a > {T}) && (x > {U}))"),
        fb: (&["let a = g~(x)", "let on = a > {T}"], "cn~().when~(on && (x > {U}))") },
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

/// Does the program of the seed have a `when~` of an event?
pub fn has_when(seed: u64) -> bool {
    form_of(seed).when
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
    let mut rng = Rng::new(seed ^ 0xE3E3);
    program(&mut rng, &(HEADER.to_string() + PARTS), (&text(form.fa), &fb, "F32"), None)
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
            let input = PackageInput::single_file(format!("when_event_{seed}.onsa"), &src);
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
                        let c = compare_case(&format!("when_event_{seed}.onsa"), input, &run);
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
