//! The twins of the events of a flow (W7-11 U2-e2; §11.11, §11.3, §11.5, S-1196, S-1234, S-1236, S-1240, S-1244). A seed makes one program of two flows `fa` and `fb` of `sample` ports only that hold events inside, which
//! the text says give the same outputs, and the evaluator asserts it on the grid and the `process` cut of `twin.rs` (and that a `reset` gives back the first run, `reset_test`): `fa` writes a form as it is, `fb` writes it
//! again with a part of it in a flow of its own, or the whole of it, or a value moved into a `let`:
//!
//! - `wrap`: a part in a named flow (a flow is no more than its body, §11.5, and what it gives is what its body gives, §11.3 "値は `let` に分けても分けなくても同じ"): the producer of an event (the output of such a flow is the
//!   event of the call in it, S-1196: "出力の式のクロックは、呼び出しの出力のイベント"; `-> F32 at event { g~(x) }`), two stages of producers, the receiver of an event (its input is the clock of the event it is given),
//!   the receiver that takes one event to two inputs (S-1236: `wt~(e, e)` has the two inputs of `tw` ticked one after the other as `tw~(e, e)` has them), a producer with no input (`sample / 4`, `sample / 2`, a `block`
//!   value), the call a modifier is on (`ev~(x).reset_if~(c)`: the modifier takes the instance of the flow it is written on, whatever its body is, §11.10);
//! - `split`: an expression that a delay stores, which reads the value of an event where it is written (S-1240) or the end of the stage (`^name`, S-1244), moved into a `let` that is at the same place or (with `^t`) below the
//!   producer: `prev~((p at sample) + 1.0)` and `let t = (p at sample) + 1.0` `let q = prev~(t)` (the nested delay, the part computed at the clock of the event, the target of a `match~`, a branch, a guard, the right side of `&&`, an arm and a part of `sample / 4` that a `^` chooses or holds, S-1249: a read without `^` is the value where it is written whatever the condition or the part reads with `^`);
//! - `whole`: all of the body in a flow that has the ports of `fa` (`block` and `init` carried), `fb` is its call.
//!
//! The forms (the tag of each) are the producer in a `let` or not, a receiver in the argument of a producer, a producer with an input and a state (a delay in the `let` of an event), a hoisted one (an argument of the kind
//! `block`), two sources into one receiver, an event read at `sample / 4`, an event that a delay of the clock of the event holds. The program is checked, evaluated and (waiting for U2, `twin_event_tests.rs`) printed and run again.
//! The interpreter is compared with the evaluator by `compare_case` when the event stage lowers.

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{CaseRun, Expect, Verdict, run_case_with};

use super::compare::compare_case;
use super::twin::{HEADER, Rng, SIGNATURE, program};

/// The flows the forms are made of (all of `F32`): a producer from a `sample` expression, one with a clock of its own, one that is ticked by an event, one with a state, one that filters, the receivers that read an
/// event at `sample` (a sum, the last value, two inputs), and a flow of `sample` ports that holds events inside (`ev`) for a modifier.
const PARTS: &str = "flow g(x: F32 at sample) -> F32 at event { if x > 0.25 { Some(x) } else { None } }
flow q4() -> F32 at event { Some(1.0) at (sample / 4) }
flow q2() -> F32 at event { Some(2.0) at (sample / 2) }
flow gb(p: F32 at block) -> F32 at event { Some(p) }
flow fw(e: F32 at event) -> F32 at event { Some(e * 2.0) }
flow ot(e: F32 at event) -> F32 at event { if e > 1.0 { Some(e) } else { None } }
flow ts(e: F32 at event) -> F32 at event { Some(e + F32.round_from(sample_tick())) }
flow ty(e: F32 at event) -> F32 at event {
  let t = prev~(^t) + e
  Some(t)
}
flow su(e: F32 at event) -> F32 at sample {
  let s = prev~(^s) + e
  s
}
flow ho(e: F32 at event) -> F32 at sample { e }
flow tw(a: F32 at event, b: F32 at event) -> F32 at sample {
  let sa = prev~(^sa) + a
  let sb = prev~(^sb) + b
  (sa at sample) * 100.0 + (sb at sample)
}
flow ev(x: F32 at sample) -> F32 at sample {
  let e = g~(x)
  su~(e)
}
";

/// A part of a form that `fb` writes as a call of a flow of its own: what it is (the tag), the text it replaces (it is in the form once), the flow (its name, its inputs, its output, what it calls, and its body, which
/// is the text when it is empty).
struct Wrap {
    kind: &'static str,
    text: &'static str,
    name: &'static str,
    inputs: &'static str,
    out: &'static str,
    call: &'static str,
    body: &'static str,
}

const fn wrap(
    kind: &'static str,
    text: &'static str,
    (name, inputs, out): (&'static str, &'static str, &'static str),
    call: &'static str,
) -> Wrap {
    Wrap { kind, text, name, inputs, out, call, body: "" }
}

/// A form: the `let`s and the output of `fa`, and (`split`) the `let`s and the output of the twin that moves a value into a `let`.
pub struct Form {
    pub tag: &'static str,
    lets: &'static [&'static str],
    out: &'static str,
    pub split: Option<(&'static [&'static str], &'static str)>,
    wraps: &'static [Wrap],
}

const PRODUCER: &str = "producer";
const PRODUCER2: &str = "producer2";
const RECEIVER: &str = "receiver";
const X: &str = "x: F32 at sample";
const E: &str = "e: F32 at event";
const EV: &str = "F32 at event";
const SA: &str = "F32 at sample";

const WG: Wrap = wrap(PRODUCER, "g~(x)", ("wg", X, EV), "wg~(x)");
const WSU: Wrap = wrap(RECEIVER, "su~(e)", ("wsu", E, SA), "wsu~(e)");
const WHO: Wrap = wrap(RECEIVER, "ho~(e)", ("who", E, SA), "who~(e)");
const WQ4: Wrap = wrap("producer0", "q4~()", ("wq4", "", EV), "wq4~()");
const WEV: Wrap = wrap("call", "ev~(x)", ("wev", X, SA), "wev~(x)");

#[rustfmt::skip]
pub const FORMS: &[Form] = &[
    Form { tag: "named", lets: &["let e = g~(x)"], out: "su~(e)", split: None, wraps: &[WG, WSU] },
    Form { tag: "inline", lets: &[], out: "su~(g~(x))", split: None,
        wraps: &[WG, wrap(RECEIVER, "su~(g~(x))", ("wsg", X, SA), "wsg~(x)")] },
    Form { tag: "two_stage", lets: &["let e = fw~(g~(x))"], out: "ho~(e)", split: None,
        wraps: &[wrap(PRODUCER2, "fw~(g~(x))", ("wfg", X, EV), "wfg~(x)"), WG, WHO] },
    Form { tag: "tally", lets: &["let e = ty~(fw~(g~(x)))"], out: "su~(e)", split: None,
        wraps: &[wrap("producer3", "ty~(fw~(g~(x)))", ("wtfg", X, EV), "wtfg~(x)"), wrap(PRODUCER2, "fw~(g~(x))", ("wfg", X, EV), "wfg~(x)"), WSU] },
    Form { tag: "filter", lets: &["let e = ot~(g~(x))"], out: "su~(e)", split: None,
        wraps: &[wrap(PRODUCER2, "ot~(g~(x))", ("wog", X, EV), "wog~(x)"), WG, WSU] },
    Form { tag: "stamp", lets: &["let e = ts~(g~(x))"], out: "su~(e)", split: None,
        wraps: &[wrap(PRODUCER2, "ts~(g~(x))", ("wtg", X, EV), "wtg~(x)"), WSU] },
    Form { tag: "caret_arg", lets: &["let h = su~(prev~(^d))", "let d = g~(x)"], out: "h + x", split: None, wraps: &[WG] },
    Form { tag: "receiver_in_arg", lets: &["let e = g~(su~(g~(x)))"], out: "ho~(e)", split: None,
        wraps: &[wrap(PRODUCER, "g~(su~(g~(x)))", ("wgsg", X, EV), "wgsg~(x)"), wrap("inner", "su~(g~(x))", ("wsg", X, SA), "wsg~(x)"), WHO] },
    Form { tag: "event_delay", lets: &["let e = g~(x)", "let m = prev~(e, 9.0)"], out: "m + ho~(e)", split: None, wraps: &[WG, WHO] },
    Form { tag: "hoisted", lets: &["let e = gb~(F32.round_from(k))"], out: "su~(e) + x", split: None,
        wraps: &[wrap(PRODUCER, "gb~(F32.round_from(k))", ("wgb", "k: U32 at block", EV), "wgb~(k)"), WSU] },
    Form { tag: "two_inputs", lets: &["let e = g~(x)"], out: "tw~(e, e)", split: None,
        wraps: &[WG, wrap(RECEIVER, "tw~(e, e)", ("wt", E, SA), "wt~(e)"),
            Wrap { kind: "receiver2", text: "tw~(e, e)", name: "wt2", inputs: "a: F32 at event, b: F32 at event", out: SA, call: "wt2~(e, e)", body: "tw~(a, b)" }] },
    Form { tag: "two_sources", lets: &["let a = g~(x)", "let b = q2~()"], out: "tw~(a, b)", split: None,
        wraps: &[WG, wrap("producer0", "q2~()", ("wq2", "", EV), "wq2~()"),
            Wrap { kind: "receiver2", text: "tw~(a, b)", name: "wt3", inputs: "p: F32 at event, q: F32 at event", out: SA, call: "wt3~(a, b)", body: "tw~(p, q)" }] },
    Form { tag: "quarter", lets: &["let e = q4~()"], out: "su~(e) + x", split: None,
        wraps: &[WQ4, WSU] },
    Form { tag: "slow_read", lets: &["let e = g~(x)", "let q = e at (sample / 4)"], out: "(q at sample) + ho~(e)", split: None, wraps: &[WG, WHO] },
    Form { tag: "saved_name", lets: &["let p = prev~(^d)", "let q = prev~((p at sample) + 1.0)", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = (p at sample) + 1.0", "let q = prev~(t)", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_part", lets: &["let p = prev~(^d)", "let q = prev~(((p * 2.0) at sample) + 1.0)", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = ((p * 2.0) at sample) + 1.0", "let q = prev~(t)", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_nested", lets: &["let p = prev~(^d)", "let q = prev~(prev~((p at sample) + 1.0))", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = (p at sample) + 1.0", "let q = prev~(prev~(t))", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_caret", lets: &["let p = prev~(^d)", "let q = prev~(if ^c > 0.0 { p at sample } else { x })", "let c = x - 0.5", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = p at sample", "let q = prev~(if ^c > 0.0 { t } else { x })", "let c = x - 0.5", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_cond_branch", lets: &["let p = prev~(^d)", "let q = prev~(if ^c > (p at sample) { p at sample } else { x })", "let c = x - 0.5", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = p at sample", "let q = prev~(if ^c > t { t } else { x })", "let c = x - 0.5", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_guards", lets: &["let p = prev~(^d)", "let q = prev~(match~ x { v if ^c > 0.0 => v * 2.0 + prev~(x), _ if (p at sample) > 1.0 => p at sample, _ => x })", "let c = x - 0.5", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = p at sample", "let q = prev~(match~ x { v if ^c > 0.0 => v * 2.0 + prev~(x), _ if t > 1.0 => t, _ => x })", "let c = x - 0.5", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_and", lets: &["let p = prev~(^d)", "let q = prev~(if (^c > 0.0) && ((p at sample) > 1.0) { 1.0 } else { x })", "let c = x - 0.5", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = (p at sample) > 1.0", "let q = prev~(if (^c > 0.0) && t { 1.0 } else { x })", "let c = x - 0.5", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_if_tilde", lets: &["let p = prev~(^d)", "let q = prev~(if~ ^c > 0.0 { prev~(x) + (p at sample) } else { x })", "let c = x - 0.5", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = p at sample", "let q = prev~(if~ ^c > 0.0 { prev~(x) + t } else { x })", "let c = x - 0.5", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_init_branch", lets: &["let p = prev~(^d)", "let q = prev~(if ^h { (p * 2.0) at sample } else { x })", "let h = n == 1", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = (p * 2.0) at sample", "let q = prev~(if ^h { t } else { x })", "let h = n == 1", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "saved_slow_part", lets: &["let p = prev~(^d)", "let q = prev~(((((p at (sample / 4)) * 2.0) + ^m)) at sample)", "let m = prev~(^m) + F32.round_from(k at (sample / 4))", "let d = q4~()"], out: "q",
        split: Some((&["let p = prev~(^d)", "let t = p at (sample / 4)", "let q = prev~((((t * 2.0) + ^m)) at sample)", "let m = prev~(^m) + F32.round_from(k at (sample / 4))", "let d = q4~()"], "q")), wraps: &[WQ4] },
    Form { tag: "saved_match", lets: &["let p = prev~(^d)", "let q = prev~(match~ (p at sample) > 1.0 { true => prev~(x), false => x * 2.0 })", "let d = g~(x)"], out: "q",
        split: Some((&["let p = prev~(^d)", "let s = match~ (p at sample) > 1.0 { true => prev~(x), false => x * 2.0 }", "let q = prev~(s)", "let d = g~(x)"], "q")), wraps: &[WG] },
    Form { tag: "mod_reset", lets: &[], out: "ev~(x).reset_if~(x < 0.0)", split: None, wraps: &[WEV] },
    Form { tag: "mod_when", lets: &[], out: "ev~(x).when~(x > 0.0)", split: None, wraps: &[WEV] },
    Form { tag: "mod_block", lets: &[], out: "ev~(x).up~(2).down~(2)", split: None, wraps: &[WEV] },
];

/// The tags of the wraps: the kinds and the flows (the forms have a tag each, and `split` and `whole` are tags of a program).
pub fn kinds() -> BTreeSet<&'static str> {
    FORMS.iter().flat_map(|f| f.wraps.iter().flat_map(|w| [w.kind, w.name])).collect()
}

/// What a program holds: its tags, and `<form>+split` for a form that is written with the move into a `let`.
pub fn covers(seed: u64) -> BTreeSet<String> {
    let tags = make(seed, false).1;
    let moved =
        FORMS.iter().filter(|f| tags.contains(f.tag) && tags.contains("split")).map(|f| format!("{}+split", f.tag));
    tags.iter().map(|t| t.to_string()).chain(moved).collect()
}

/// Everything the seeds of the gate have to hold.
pub fn cover() -> BTreeSet<String> {
    let moved = FORMS.iter().filter(|f| f.split.is_some()).map(|f| format!("{}+split", f.tag));
    FORMS.iter().map(|f| f.tag).chain(kinds()).chain(["split", "whole"]).map(str::to_string).chain(moved).collect()
}

/// The text of a flow (a body of lets and an output).
fn body(lets: &[&str], out: &str) -> String {
    lets.iter().map(|l| format!("{l}\n  ")).collect::<String>() + out
}

/// A program: `fa` is the form as it is, `fb` has what the seed chose of the wraps, the move into a `let` and the whole in a flow (`rot` makes `fb` give one more). The tags are the form, `split`, `whole`, and the kind and the flow of each wrap.
pub fn make(seed: u64, rot: bool) -> (String, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed);
    let form = rng.pick_in(FORMS);
    let mut tags = BTreeSet::from([form.tag]);
    let (mut lets, mut out): (Vec<&str>, &str) = (form.lets.to_vec(), form.out);
    let split = form.split.filter(|_| rng.chance(50));
    if let Some((l, o)) = split {
        (lets, out) = (l.to_vec(), o);
        tags.insert("split");
    }
    let (mut text, mut defs, mut chosen) = (body(&lets, out), String::new(), Vec::<&Wrap>::new());
    for w in form.wraps {
        let apart = chosen.iter().all(|c| !c.text.contains(w.text) && !w.text.contains(c.text));
        if apart && rng.chance(55) {
            chosen.push(w);
        }
    }
    let whole = rng.chance(30);
    if chosen.is_empty() && split.is_none() && !whole {
        chosen.extend(form.wraps.first());
    }
    for w in &chosen {
        assert_eq!(text.matches(w.text).count(), 1, "{}: `{}` is not once in `{text}`", form.tag, w.text);
        text = text.replace(w.text, w.call);
        let inner = if w.body.is_empty() { w.text } else { w.body };
        // The output of a flow of events is an `Option` at the clock of its expression: the events of the call it holds (S-1196).
        let body = if w.out == EV { format!("Some({inner})") } else { inner.to_string() };
        defs += &format!("flow {}({}) -> {} {{ {body} }}\n", w.name, w.inputs, w.out);
        tags.extend([w.kind, w.name]);
    }
    let fa = body(form.lets, form.out);
    if whole {
        defs += &format!("flow wh{SIGNATURE} -> F32 at sample {{\n  {text}\n}}\n");
        (text, _) = ("wh~(x, k, ki, n)".to_string(), tags.insert("whole"));
    }
    let fb = if rot { format!("({text}) + 1.0") } else { text };
    let mut rng = Rng::new(seed ^ 0xE7E7);
    let src = program(&mut rng, &(HEADER.to_string() + PARTS + &defs), (&fa, &fb, "F32"), None);
    (src + &reset_test(&mut rng), tags)
}

/// The test of a `reset`: a run of the six samples, the state given back, and the same run again give the same outputs (the events are given back with the rest, §11.6), for each of `fa` and `fb`.
fn reset_test(rng: &mut Rng) -> String {
    let xs: Vec<&str> = (0..6).map(|_| rng.pick(&["-1.0", "-0.5", "0.0", "0.25", "0.5", "1.0", "2.0"])).collect();
    let mut t = format!("test \"reset\" {{\n  let xs: [F32; 6] = [{}]\n", xs.join(", "));
    for (n, f) in ["fa", "fb"].iter().enumerate() {
        let (cfg, params) = (format!("{f}.Config {{ n: {n} }}"), format!("{f}.Params {{ k: {}, ki: 0 }}", n + 1));
        t += &format!(
            "  var s{n} = {f}.init({cfg}, 8.0)\n  var a{n}: [F32; 6] = [0.0; 6]\n  var b{n}: [F32; 6] = [0.0; 6]\n"
        );
        t += &format!("  {f}.process(inout s{n}, {params}, xs, inout a{n})\n  {f}.reset(inout s{n})\n");
        t += &format!("  {f}.process(inout s{n}, {params}, xs, inout b{n})\n");
        (0..6).for_each(|i| t += &format!("  assert a{n}[{i}] == b{n}[{i}]\n"));
    }
    t + "}\n"
}

/// What the evaluator and the interpreter did with the programs of the seeds: the programs, the tests, the tests the evaluator evaluated (the asserts it held), those the interpreter ran again, and what is wrong.
#[derive(Debug, Default)]
pub struct Ran {
    pub programs: usize,
    pub tests: usize,
    pub evaluated: usize,
    pub asserts: usize,
    pub compared: usize,
    /// The programs whose event stage lowers.
    pub lowered: usize,
    pub bad: Vec<String>,
}

fn evaluated(run: &CaseRun, seed: u64, src: &str, r: &mut Ran) {
    r.tests += run.tests.len();
    for t in &run.tests {
        r.asserts += t.asserts;
        match &t.verdict {
            Verdict::Ok if t.panic.is_none() => r.evaluated += 1,
            v => r.bad.push(format!("seed {seed}: \"{}\": {v:?} {:?}\n{src}", t.name, t.panic)),
        }
    }
}

/// The seeds run on the evaluator (and, with `compare`, through the interpreter, which has to lower the program: while it stops at E0200 that is a failure of the comparison).
pub fn run(seeds: Vec<u64>, rot: bool, compare: bool) -> Ran {
    stack::run(move || {
        let (wrappers, mut r) = (Wrappers::default(), Ran::default());
        for seed in seeds {
            let (src, _) = make(seed, rot);
            let input = PackageInput::single_file(format!("event_{seed}.onsa"), &src);
            r.programs += 1;
            match run_case_with(input.clone(), &wrappers, Expect::Evaluator) {
                Err(e) => r.bad.push(format!("seed {seed}: not read: {e}\n{src}")),
                Ok(run) => {
                    evaluated(&run, seed, &src, &mut r);
                    r.lowered += usize::from(run.lowered && !run.e0200);
                    if compare && run.lowered && !run.e0200 {
                        let c = compare_case(&format!("event_{seed}.onsa"), input, &run);
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
