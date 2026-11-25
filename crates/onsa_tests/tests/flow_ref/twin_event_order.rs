//! The order of the work of the stages of events, by the divisions that panic (W7-11 U2-e2, S-1233, S-1234, S-1235, S-1236, S-1240): a flow with a division by 0 in each of two to four places that run at one position (the first
//! frame), the evaluator stops at the first one the order says (§11.3, §11.11), and the interpreter stops at the same place (`compare_case`). The places are named by a letter
//! (`@A` is the divisor of a division, `(v - v)` (0) or `(v + 1)`, written on a line with a comment `// A`), and a group is run with its places made safe from the first of its order on, so the line says which came first.
//! The groups are those of `crates/onsa_cli/tests/cli/event_stage_commands.rs` and `event_saved_commands.rs`, which `onsa test` reads (the places are worked out by hand from the text there: the stage of the producer,
//! the receiver that the event ticks right after the producer's work and before the lower expressions of the stage, a receiver above the producer fed through `^`, one event to two inputs in the order of the declaration, the
//! argument of a producer before its work, and what a delay stores, which reads an event where it is written), and two more: the argument of the producer and a division in what an event stage stores.

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Expect, Verdict, run_case_with};

use super::compare::compare_case;

const PRELUDE: &str = "flow gen(v: U32 at sample) -> U32 at event {
  Some(v)
}

flow fwd(v: U32 at event) -> U32 at event {
  Some(v)
}

";
/// The receiver whose division is at the tick of its event input, the producer whose division is in its `sample` stage, and the one ticked by an event.
const RCV: &str = "flow rcv(v: U32 at event) -> U32 at sample {\n  let q = 100 / @C\n  q at sample\n}\n\n";
const MK: &str = "flow mk(v: U32 at sample) -> U32 at event {\n  let z = 100 / @A\n  Some(v + z)\n}\n\n";
const FW: &str = "flow fw(v: U32 at event) -> U32 at event {\n  let z = 100 / @A\n  Some(v + z)\n}\n\n";
/// The producer with two inputs: it gives the event of the first one, and its second input has a division of its own.
const GP: &str = "flow gp(v: U32 at event, u: U32 at event) -> U32 at event {\n  let _ = 100 / @U\n  Some(v)\n}\n\n";
/// A producer that stores a division of its input in an event stage: what a delay saves is evaluated at the end of the stage of the event (`@S`).
const ST: &str = "flow st(v: U32 at event) -> U32 at event {\n  let h = prev~(\n    100 / @S\n  )\n  let z = 100 / @A\n  Some(v + z + h)\n}\n\n";

/// A group: the name, the places in the order they stop the run, the parts and the body of the module.
pub struct Group {
    pub name: &'static str,
    pub order: &'static str,
    pub parts: &'static [&'static str],
    pub body: &'static str,
}

#[rustfmt::skip]
pub const GROUPS: &[Group] = &[
    // The producer is ticked by an event: its work (A), the receiver of what it gives (C), the lower expression of the clock that ticked it (B).
    Group { name: "event_maker", order: "ACB", parts: &[FW, RCV],
        body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  let e = fw~(v)\n  let r = rcv~(e)\n  let w = 100 / @B\n  r + (w at sample)\n}\n" },
    // The producer is a `sample` expression: its work (A), the receiver (C), the lower expression of the event (B), then the rest of the `sample` stage (D).
    Group { name: "sample_maker", order: "ACBD", parts: &[MK, RCV],
        body: "pub flow f() -> U32 at sample {\n  let v = mk~(sample_tick())\n  let r = rcv~(v)\n  let w = 100 / @B\n  let t = 100 / @D\n  r + (w at sample) + t\n}\n" },
    // One event given to two inputs: the first input ticks and the receiver of what it gives (C) comes before the second input (U), though U is written above.
    Group { name: "two_inputs", order: "CU", parts: &[RCV],
        body: "flow both(v: U32 at event, u: U32 at event) -> U32 at sample {\n  let w = 100 / @U\n  let e = fwd~(v)\n  let r = rcv~(e)\n  r + (w at sample)\n}\n\npub flow f() -> U32 at sample {\n  let d = gen~(sample_tick())\n  both~(d, d)\n}\n" },
    // One event given to two inputs of a flow that gives an event: the event of the first input is done (its receiver, C) before the second input ticks (U, written above the output).
    Group { name: "two_inputs_that_give", order: "CU", parts: &[RCV, GP],
        body: "pub flow f() -> U32 at sample {\n  let d = gen~(sample_tick())\n  let e = gp~(d, d)\n  rcv~(e)\n}\n" },
    // A receiver in the argument of the producer, fed by the producer through a delay: the argument is first, then the work of the producer (A), the tick of the receiver (C), the rest of the stage (D).
    Group { name: "receiver_in_argument", order: "ACD", parts: &[MK, RCV],
        body: "pub flow f() -> U32 at sample {\n  let v = mk~(rcv~(prev~(^v)) + sample_tick())\n  let t = 100 / @D\n  (v at sample) + t\n}\n" },
    // A receiver written above the producer and fed through `^`: the producer (A, written below) comes first, then the receiver (C).
    Group { name: "receiver_above", order: "AC", parts: &[MK, RCV],
        body: "pub flow f() -> U32 at sample {\n  let h = rcv~(prev~(^v))\n  let v = mk~(sample_tick())\n  h\n}\n" },
    // A division in the argument of the producer is before the work of the producer (E, A), then the receiver (C) and the rest of the stage (D).
    Group { name: "argument_of_the_producer", order: "EACD", parts: &[MK, RCV],
        body: "pub flow f() -> U32 at sample {\n  let v = mk~(\n    sample_tick() + 100 / @E\n  )\n  let r = rcv~(v)\n  let t = 100 / @D\n  r + t\n}\n" },
    // What an event stage stores: the work of the producer in its stage (A) is before what its delay stores, evaluated at the end of that stage (S), and that is before the receiver (C) of what it gives.
    Group { name: "stored_in_an_event_stage", order: "ASC", parts: &[ST, RCV],
        body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  let e = st~(v)\n  let r = rcv~(e)\n  r\n}\n" },
];

/// The module of a group with the places of `order[..k]` made safe: `@D` and `@E` divide by a value of the time, `@U` by `u`, any other by `v`.
fn fill(text: &str, safe: &str) -> String {
    let (mut out, mut chars) = (String::new(), text.chars().peekable());
    while let Some(c) = chars.next() {
        match chars.peek().copied() {
            Some(l) if c == '@' && l.is_ascii_uppercase() => {
                chars.next();
                let (zero, one) = match l {
                    'D' | 'E' => ("sample_tick() * 0", "sample_tick() + 1"),
                    'U' => ("u - u", "u + 1"),
                    _ => ("v - v", "v + 1"),
                };
                out.push_str(&format!("({}) // {l}", if safe.contains(l) { one } else { zero }));
            }
            _ => out.push(c),
        }
    }
    out
}

/// The module of the group `g` whose first `k` places of its order are safe, and the line of the one that has to stop the run (`order[k]`).
pub fn group_case(g: &Group, k: usize) -> (String, usize) {
    let text = [PRELUDE, &g.parts.concat(), g.body].concat();
    let src = format!(
        "{}\ntest \"stops\" {{\n  let o = f.render(1, 8.0)\n  assert o.out[0] == 0\n}}\n",
        fill(&text, &g.order[..k])
    );
    let mark = format!("// {}", &g.order[k..=k]);
    let line = line_of(&src, &mark);
    (src, line)
}

/// What an event decides, the events a call of a delay reads where it is written (§11.3, S-1240): `p = prev~(^e, 7)` is the event `e` of a call delayed by one event, and `det` gives its input when it is not 0.
const DET: &str = "flow det(x: U32 at sample) -> U32 at event {\n  if x != 0 { Some(x) } else { None }\n}\n\n";

fn saved_module(parts: &[&str], xs: &[u32]) -> String {
    let list: Vec<String> = xs.iter().map(u32::to_string).collect();
    format!(
        "{DET}{}\ntest \"run\" {{\n  let xs: [U32; {}] = [{}]\n  let o = f.render(xs, 8.0)\n  assert o.out[0] == o.out[0]\n}}\n",
        parts.concat(),
        xs.len(),
        list.join(", ")
    )
}

/// The cases of what a delay stores and what a call reads of an event: the module and the mark of the line that stops the run (none for a run that does not stop).
pub fn saved_cases() -> Vec<(&'static str, String, Option<&'static str>)> {
    let kk = |div: &str| {
        format!("flow kk(a: U32 at sample, m: U32 at event) -> U32 at event {{\n  let _ = {div} //K\n  Some(m)\n}}\n\n")
    };
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {\n  let p = prev~(^e, 7)\n  let e = kk~(p at sample, det~(x))\n  e at sample\n}\n";
    let stored = "pub flow f(x: U32 at sample) -> U32 at sample {\n  let p = prev~(^d, 7)\n  let q = prev~(100 / (p at sample)) //S\n  let r = 100 / x //B\n  let d = det~(x)\n  q + r\n}\n";
    // `gk` divides by 0 in its `sample` stage (`//G`) and `hh` adds its two arguments.
    let sib = "flow gk(x: U32 at sample) -> U32 at sample {\n  let _ = 100 / (x - x) //G\n  x\n}\n\nflow hh(a: U32 at sample, b: U32 at sample) -> U32 at sample { a + b }\n\n";
    let sibling = |args: &str| format!("pub flow f(x: U32 at sample) -> U32 at sample {{\n  hh~({args}) //F\n}}\n");
    vec![
        // `p at sample` is read before the producer in the second argument gives the first event (at the sample 0): 0, not the 7 that p has after it.
        ("arg_before_producer", saved_module(&[&kk("100 / a"), f], &[3, 5]), Some("//K")),
        // `p` is 0 before the first event of `e`, 7 (the `init`) after it, then the event before: for `x` = 3 5 9 the events are the `x` and the arguments `p at sample` are 0 7 3 (read before the event of the sample), so
        // `(a + 5) % 10` is 5 2 8 and the run does not stop. A read after the event of the sample (7 3 5) gives 2 8 0 and stops at the sample 2.
        ("later_value_only", saved_module(&[&kk("100 / ((a + 5) % 10)"), f], &[3, 5, 9]), None),
        // The arguments of a call are evaluated in the order written, the work of a call in an argument with them (§11.3): the division written first is first, whatever the call written after it does.
        ("sibling_arguments", saved_module(&[sib, &sibling("100 / (x - x), gk~(x)")], &[3]), Some("//F")),
        (
            "sibling_arguments_the_call_first",
            saved_module(&[sib, &sibling("gk~(x), 100 / (x - x)")], &[3]),
            Some("//G"),
        ),
        // The body is before what the delay stores (the end of the stage): at the sample 0 both divide by 0 and the body stops first.
        ("body_before_stored", saved_module(&[stored], &[0, 1]), Some("//B")),
        // `x = 1`: the body is fine and the stored one divides by p before the event of the sample, 0 (the 7 after it is not the one read).
        ("stored_only", saved_module(&[stored], &[1, 1]), Some("//S")),
    ]
}

fn line_of(src: &str, mark: &str) -> usize {
    1 + src.lines().position(|l| l.contains(mark)).unwrap_or_else(|| panic!("no line with {mark} in {src}"))
}

/// Where the evaluator stopped in `src` (the line), none for a run that did not, and what the interpreter says of the same places (`compared`: only when the program lowers, an error in the list otherwise).
fn stop(src: &str, wrappers: &Wrappers, compared: bool) -> Result<(Option<usize>, Vec<String>), String> {
    let input = PackageInput::single_file("order.onsa", src);
    let run = run_case_with(input.clone(), wrappers, Expect::Evaluator)?;
    let mut lines = Vec::new();
    for t in &run.tests {
        if t.verdict != Verdict::Ok {
            return Err(format!("{}: {:?}", t.name, t.verdict));
        }
        lines.push(t.panic_span.map(|s| 1 + src[..s.start as usize].matches('\n').count()));
    }
    let said = match (compared, run.lowered && !run.e0200) {
        (false, _) => Vec::new(),
        (true, true) => compare_case("order.onsa", input, &run).failures,
        (true, false) => vec!["the interpreter does not lower the program".to_string()],
    };
    Ok((lines.first().copied().flatten(), said))
}

/// The cases run: how many stopped where they had to, and what is wrong (a stop at another line, a run that does not stop, one that does and must not, what the interpreter says).
pub fn run(compared: bool) -> (usize, Vec<String>) {
    stack::run(move || {
        let (wrappers, mut stopped, mut bad) = (Wrappers::default(), 0, Vec::new());
        let mut cases: Vec<(String, String, Option<usize>)> = Vec::new();
        for g in GROUPS {
            for k in 0..g.order.len() {
                let (src, line) = group_case(g, k);
                cases.push((format!("{}_{k}", g.name), src, Some(line)));
            }
        }
        for (name, src, mark) in saved_cases() {
            let line = mark.map(|m| line_of(&src, m));
            cases.push((name.to_string(), src, line));
        }
        for (name, src, want) in cases {
            match stop(&src, &wrappers, compared) {
                Ok((got, said)) => {
                    stopped += usize::from(got.is_some());
                    if got != want {
                        bad.push(format!("{name}: stopped at the line {got:?}, want {want:?}\n{src}"));
                    }
                    bad.extend(said.into_iter().map(|m| format!("{name}: {m}")));
                }
                Err(e) => bad.push(format!("{name}: not run: {e}\n{src}")),
            }
        }
        (stopped, bad)
    })
}
