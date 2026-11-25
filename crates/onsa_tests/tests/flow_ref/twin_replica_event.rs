//! The twins of the events in a `par~`, a `par` and the arms of an `if~` (W7-17 U6a/e; §11.5, §11.11, §11.3, S-1096, S-1239). A seed makes one program of two flows `fa` and `fb` of `sample` ports that the text says give the same outputs, and the
//! evaluator asserts it on the grid and the `process` cut of `twin.rs`. The forms: the body of a `par~` that makes and receives its events in a flow of its own (`lane~(x, i)` with `i` at `init`), the replicas written out in `let`s, the
//! receiver of an arm in a `let` that a plain `if` chooses from (both arms run, so the twin is the same), the condition of an `if~` in a `let`, the event of a replica read with `at sample`, and the part of an event in a `par` moved to
//! `let`s, and the part of a delayed event that a delay saves where it is written, in a `par` and in a `let`. (A body that reads a `^name` of the flow around it, and one that gives the same source to two inputs, are not twins of a flow of their own, and are not here.)

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Expect, Verdict, run_case_with};

use super::compare::compare_case;
use super::twin::{HEADER, Rng, program};

const PARTS: &str = "flow g(x: F32 at sample) -> F32 at event { if x > 0.25 { Some(x) } else { None } }
flow cn(e: F32 at event) -> F32 at sample {
  let n = prev~(^n) + e
  n
}
flow lane(x: F32 at sample, i: U32 at init) -> F32 at sample { cn~(g~(x * F32.round_from(i + 1))) }
";

/// A form: `fa` (the `let`s and the output) and `fb`, the other way of writing it. `{T}` is a number to compare with.
struct Form {
    tag: &'static str,
    fa: (&'static [&'static str], &'static str),
    fb: (&'static [&'static str], &'static str),
}

const A: &[&str] = &["let a = g~(x)"];

#[rustfmt::skip]
const FORMS: &[Form] = &[
    Form { tag: "wrap_the_body", fa: (&[], "sum2(par~ i in 0 ..< 2 { cn~(g~(x * F32.round_from(i + 1))) })"), fb: (&[], "sum2(par~ i in 0 ..< 2 { lane~(x, i) })") },
    Form { tag: "write_out_the_replicas", fa: (&[], "sum2(par~ i in 0 ..< 2 { cn~(g~(x * F32.round_from(i + 1))) })"),
        fb: (&["let a = cn~(g~(x))", "let b = cn~(g~(x * 2.0))"], "a + b") },
    Form { tag: "the_arm_in_a_let", fa: (&[], "if~ x > {T} { cn~(g~(x)) } else { cn~(g~(x * 2.0)) }"),
        fb: (&["let a = cn~(g~(x))", "let b = cn~(g~(x * 2.0))"], "if x > {T} { a } else { b }") },
    Form { tag: "the_condition_in_a_let", fa: (&[], "if~ x > {T} { cn~(g~(x)) } else { x }"), fb: (&["let c = x > {T}"], "if~ c { cn~(g~(x)) } else { x }") },
    Form { tag: "the_event_of_a_replica_at_sample", fa: (&[], "sum2(par~ i in 0 ..< 2 { g~(x * F32.round_from(i + 1)) at sample })"),
        fb: (&["let a = g~(x) at sample", "let b = g~(x * 2.0) at sample"], "a + b") },
    Form { tag: "the_part_of_a_par_in_lets", fa: (A, "let s = par i in 0 ..< 2 { x + ((a * F32.round_from(i + 1)) at sample) }\n  s[0] + s[1]"),
        fb: (&["let a = g~(x)", "let p = a * 1.0", "let q = a * 2.0"], "(x + (p at sample)) + (x + (q at sample))") },
    Form { tag: "the_part_of_a_delayed_event_saved_where_written", fa: (&["let e = prev~(^d)", "let q = prev~((par i in 0 ..< 2 { x + ((e + F32.round_from(i)) at sample) })[1])", "let d = g~(x)"], "q"),
        fb: (&["let e = prev~(^d)", "let t = par i in 0 ..< 2 { x + ((e + F32.round_from(i)) at sample) }", "let q = prev~(t[1])", "let d = g~(x)"], "q") },
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
    let t = rng.pick(&["0.5", "1.0", "2.0"]);
    let text = |(lets, out): (&[&str], &str)| {
        let s = lets.iter().map(|l| format!("{l}\n  ")).collect::<String>() + out;
        s.replace("{T}", t)
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
            let input = PackageInput::single_file(format!("replica_event_{seed}.onsa"), &src);
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
                        let c = compare_case(&format!("replica_event_{seed}.onsa"), input, &run);
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
