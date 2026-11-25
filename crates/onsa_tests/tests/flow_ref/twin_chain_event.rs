//! The twins of the modifiers on a call with events, the ratios, the blocks and the several events of one stage (W7-17 U4/e1; §11.10, §11.11, §11.9, §11.4, S-562, S-1207, S-1209, S-1229, S-1251). A seed makes one program of two flows `fa` and
//! `fb` of `sample` ports that the text says give the same outputs, and the evaluator asserts it on the grid and the `process` cut of `twin.rs`. The forms: a receiver of events wrapped in a flow with its `when~`, the condition of a `when~`
//! in a `let`, `.when~` inside and outside a `.down~` (the head's input and output at `sample`, §11.10 "同じ意味"), a block `.up~(2).down~(2)` written out and in a flow, and the makers under `.up~(2)` with their receiver wrapped in a flow
//! (S-1251: the receiver is ticked after each run of the maker whether or not a flow is around it). (A form that does not hold by the text is not here: the maker alone wrapped with its reset left outside, a `when~` of an event of the
//! flow's own receiver, a `.reset_if~` inside and outside a boundary, and a `.when~` and a `.reset_if~` of an event in the other order.)

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
flow ord(e: F32 at event) -> F32 at sample {
  let n = prev~(^n) * 3.0 + e
  n
}
flow tkf() -> F32 at event { Some(F32.round_from(sample_tick())) }
flow wk() -> F32 at event { Some(tkf~().up~(2)) }
flow wcn(e: F32 at event, c: Bool at sample) -> F32 at sample { cn~(e).when~(c) }
flow lane() -> F32 at sample { ord~(tkf~().up~(2)) }
flow wbf() -> F32 at event { Some(tkf~().up~(2).down~(2)) }
";

/// A form: `fa` (the `let`s and the output) and `fb`, the other way of writing it. `{T}` is a number to compare with.
struct Form {
    tag: &'static str,
    fa: (&'static [&'static str], &'static str),
    fb: (&'static [&'static str], &'static str),
}

#[rustfmt::skip]
const FORMS: &[Form] = &[
    Form { tag: "the_receiver_with_its_when_in_a_flow", fa: (&[], "cn~(g~(x)).when~(x > {T})"), fb: (&[], "wcn~(g~(x), x > {T})") },
    Form { tag: "the_condition_of_the_when_in_a_let", fa: (&[], "cn~(g~(x)).when~(x > {T})"), fb: (&["let c = x > {T}"], "cn~(g~(x)).when~(c)") },
    Form { tag: "the_when_inside_or_outside_the_down", fa: (&["let w = g~(x)", "let a = cn~(w).down~(2).when~(w > {T})"], "a at sample"),
        fb: (&["let w = g~(x)", "let a = cn~(w).when~(w > {T}).down~(2)"], "a at sample") },
    Form { tag: "the_block_in_a_flow", fa: (&[], "ord~(tkf~().up~(2).down~(2))"), fb: (&[], "ord~(wbf~())") },
    Form { tag: "the_makers_under_up_wrapped_with_their_receiver", fa: (&[], "ord~(tkf~().up~(2))"), fb: (&[], "lane~()") },
    Form { tag: "the_maker_wrapped_under_up_or_alone", fa: (&[], "ord~(tkf~().up~(2))"), fb: (&[], "ord~(wk~())") },
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
    let mut rng = Rng::new(seed ^ 0xC4A1);
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
            let input = PackageInput::single_file(format!("chain_event_{seed}.onsa"), &src);
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
                        let c = compare_case(&format!("chain_event_{seed}.onsa"), input, &run);
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
