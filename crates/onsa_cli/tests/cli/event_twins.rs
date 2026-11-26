//! Chains of `reset_if~` with events: the twins of the written forms, and the values of a model of the delays of an event (W7-11 U3/t2; spec §11.10, §11.11, §11.3, §11.4, §11.5; S-1234, S-1236, S-1249, S-1250).
//! A few programs from fixed seeds, each module run in this process (`run_texts`: `onsa test` on a text, no file written, `rules/common.md` 3.7). The sweeps that these are a sample of (thousands of programs) are the business
//! of the break side; what stays here is a small number, so that the gate has the forms and a break of the order of the stage shows.
//!
//! Twins (6 seeds, 5 programs each): a program is two flows, `fa` that writes every receiver straight (`prev~(a, 9).reset_if~(c)`, `delay~(a, 2, 9).reset_if~(c)`, `ac~(a).reset_if~(c)`) and `fb` that writes each
//! delay in a flow of its own (`wp_9~(a).reset_if~(c)`: a flow is its body, §11.5, and a `let` or a call that names a part changes no value, §11.3), the flows that write the same program; a test asserts that their
//! outputs are the same on 14 frames. The producers are four flows of events (`pa`..`pz`, each one gives an event at some frames of `x`, `sample`-clock input); 1 to 3 of them make an event, each is read straight or
//! through `prev~(^d)`; 1 to 3 receivers with 1 to 3 conditions each (an event, or a value of `x`, or a constant), the argument of a receiver is `x`, `x + 1`, an earlier receiver or a receiver of its own (a chain
//! inside a chain); the producer, the reader and the receivers are in any order that reads only what is above (`^` where the name is below). The output is the sum of the receivers, `r0 + r1 * 100 + ..`.
//!
//! Places (W7-17 U4): the same twins, written out, of a delay at the places an event comes late to or a chain of a part (the argument and the conditions of the call that gives the event, an event that event ticks, a delay of an
//! event, two conditions, the ring of a condition a boundary gathers).
//!
//! Models (4 seeds, 5 programs each): a program has 2 to 3 sources of events (the four producers), 0 to 2 readers (`prev~(d)`) and 1 to 3 delays of an event (`prev~(d, init).reset_if~(..)` of a source or a reader, 0
//! to 3 conditions each; an event of a source or a reader above it, or a constant), written in any order that reads only what is above, output `(e0 at sample) + (e1 at sample) * 100 + ..` (the value of an event
//! delay as `sample` is the output of its last tick). The expected values are computed here by a model of the text of the spec, written once for all of them:
//! - a source ticks at the frames where its producer gives `Some(v)`, in the order the producers are written in (§11.11: the tick of an event is right after the work of its producer in the stage of the caller, and the
//!   events of the same frame come in the order the producers come);
//! - a tick of a source goes down the lets from the top: a producer of it takes `v`, a reader of it gives its stored value and stores the value of its argument (the value of the tick, §11.3: what a delay stores is
//!   what is written at its place), and a delay of an event whose condition is of this source (§11.10: "イベントの条件は、外の `when~` が止めている間もその刻みで初期化する") is put back to its init if the condition holds, in the order the
//!   conditions are written, and a delay whose own source this is gives what it holds as its output and stores the value of its argument: the delay that is below the producer of its condition is reset after the
//!   stage of its own, or before it where the condition is of its own source, and a constant is read at the tick of the source of its delay (§11.10: the clock W of an event is the clock of the first argument).
//!
//! The value before the first tick is 0 (§11.11: `T.default()`).

use std::collections::{BTreeMap, BTreeSet};

use crate::slow_written_forms::run_texts;
use crate::test_support::sweep::Rng;
use crate::test_support::{diagnostics, doc_of, str_of, tests_of};

/// How many frames a program runs.
const N: usize = 14;
const TWIN_SEEDS: [u64; 6] = [0x0711_2001, 0x0711_2002, 0x0711_2003, 0x0711_2004, 0x0711_2005, 0x0711_2006];
const MODEL_SEEDS: [u64; 4] = [0x0711_2101, 0x0711_2102, 0x0711_2103, 0x0711_2104];
const PER_SEED: usize = 5;

/// The receiver of the values of a `sample` input that adds them (the receiver that is a flow in both forms of a twin).
const AC: &str = "flow ac(v: U32 at sample) -> U32 at sample {\n  let n = prev~(^n) + v\n  n\n}\n";

/// The producers of the events: what they give at the frame of the value `x`.
const PRODUCERS: [&str; 4] = ["pa", "pb", "pc", "pz"];

fn produced(f: usize, x: u32) -> Option<u32> {
    match f {
        0 => (x % 3 != 0).then_some(x),
        1 => (x % 2 == 0).then_some(x + 1),
        2 => Some(x),
        _ => (x > 4).then_some(x),
    }
}

fn head(xs: &[u32], extra: &str) -> String {
    let list: Vec<String> = xs.iter().map(u32::to_string).collect();
    format!(
        "const XS: [U32; {N}] = [{}]\n\n\
         flow pa(x: U32 at sample) -> U32 at event {{ if x % 3 != 0 {{ Some(x) }} else {{ None }} }}\n\
         flow pb(x: U32 at sample) -> U32 at event {{ if x % 2 == 0 {{ Some(x + 1) }} else {{ None }} }}\n\
         flow pc(x: U32 at sample) -> U32 at event {{ Some(x) }}\n\
         flow pz(x: U32 at sample) -> U32 at event {{ if x > 4 {{ Some(x) }} else {{ None }} }}\n{extra}\n",
        list.join(", ")
    )
}

fn frames_of(rng: &mut Rng) -> Vec<u32> {
    (0..N).map(|_| rng.below(10) as u32).collect()
}

/// The identifiers of a text, each with whether a `^` is just before it.
fn idents(text: &str) -> Vec<(String, bool)> {
    let chars: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i].is_alphabetic() || chars[i] == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            out.push((chars[start..i].iter().collect(), start > 0 && chars[start - 1] == '^'));
        } else {
            i += 1;
        }
    }
    out
}

/// A name of a `let` of a program: a letter `d` `e` `r` `a` and a number.
fn is_name(id: &str, letters: &str) -> bool {
    let mut cs = id.chars();
    cs.next().is_some_and(|c| letters.contains(c)) && id.len() > 1 && cs.all(|c| c.is_ascii_digit())
}

/// `text` with the `^` taken off the names of `above` (what is written above is read straight, not through a `^`).
fn without_carets(text: &str, above: &BTreeSet<String>) -> String {
    let mut out = text.to_string();
    for (id, caret) in idents(text) {
        if caret && above.contains(&id) {
            out = out.replace(&format!("^{id}"), &id);
        }
    }
    out
}

/// The text of the `test`s of a module run in this process: the names of the tests that do not pass (none when the run is as it must be), or the reason the run is not one.
fn failures(text: &str, tests: usize) -> Vec<String> {
    let out = run_texts(&["test", "--json"], text);
    let doc = doc_of(&out);
    let mut wrong = Vec::new();
    if out.code != 0 || !diagnostics(&doc).is_empty() {
        wrong.push(format!("exit {}, diagnostics {:?}, {}", out.code, diagnostics(&doc), out.stderr));
    }
    let records = tests_of(&doc);
    if records.len() != tests {
        wrong.push(format!("{} tests ran of {tests}", records.len()));
    }
    wrong
        .extend(records.iter().filter(|t| str_of(t, "status") != "ok").map(|t| format!("{} fails", str_of(t, "name"))));
    wrong
}

// ---- the twins

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Prev,
    Delay,
    Ac,
}

struct Recv {
    kind: Kind,
    init: usize,
    n: usize,
    arg: Arg,
    conds: Vec<String>,
}

enum Arg {
    Text(String),
    Recv(Box<Recv>),
}

/// A condition: an event (or a delayed one), a value of `x`, or a constant.
fn condition(rng: &mut Rng, events: &[String]) -> String {
    let k = rng.below(100);
    if k < 75 && !events.is_empty() {
        let op = *rng.pick(&[">=", ">", "!=", "<="]);
        format!("{} {op} {}", rng.pick(events), rng.below(8))
    } else if k < 85 {
        format!("x > {}", rng.below(9))
    } else if k < 90 {
        format!("x % 4 == {}", rng.below(4))
    } else {
        (*rng.pick(&["1 > 2", "2 > 1"])).to_string()
    }
}

fn receiver(rng: &mut Rng, depth: usize, earlier: &[String], events: &[String]) -> Recv {
    let mut kind = *rng.pick(&[Kind::Prev, Kind::Prev, Kind::Delay, Kind::Ac]);
    let (init, n) = (rng.below(12), *rng.pick(&[2, 3]));
    let arg = if depth < 2 && rng.chance(30) {
        Arg::Recv(Box::new(receiver(rng, depth + 1, earlier, events)))
    } else {
        let mut options: Vec<String> = ["x", "x", "x", "x + 1"].iter().map(|s| s.to_string()).collect();
        for name in earlier {
            options.extend([name.clone(), name.clone()]);
        }
        Arg::Text(options[rng.below(options.len())].clone())
    };
    let conds = (0..*rng.pick(&[1, 1, 1, 2, 2, 3])).map(|_| condition(rng, events)).collect();
    if kind == Kind::Ac && matches!(arg, Arg::Recv(_)) {
        kind = Kind::Prev;
    }
    Recv { kind, init, n, arg, conds }
}

/// The text of a receiver: straight, or with each delay in a flow of its own (the flows are put in `wrappers`).
fn written(r: &Recv, wrap: bool, wrappers: &mut BTreeMap<String, String>) -> String {
    let arg = match &r.arg {
        Arg::Text(t) => t.clone(),
        Arg::Recv(inner) => written(inner, wrap, wrappers),
    };
    let head = match (r.kind, wrap) {
        (Kind::Ac, _) => format!("ac~({arg})"),
        (Kind::Prev, false) => format!("prev~({arg}, {})", r.init),
        (Kind::Delay, false) => format!("delay~({arg}, {}, {})", r.n, r.init),
        (Kind::Prev, true) => {
            let name = format!("wp_{}", r.init);
            let body = format!("flow {name}(v: U32 at sample) -> U32 at sample {{ prev~(v, {}) }}\n", r.init);
            wrappers.insert(name.clone(), body);
            format!("{name}~({arg})")
        }
        (Kind::Delay, true) => {
            let name = format!("wd_{}_{}", r.n, r.init);
            let body = format!("flow {name}(v: U32 at sample) -> U32 at sample {{ delay~(v, {}, {}) }}\n", r.n, r.init);
            wrappers.insert(name.clone(), body);
            format!("{name}~({arg})")
        }
    };
    head + &r.conds.iter().map(|c| format!(".reset_if~({c})")).collect::<String>()
}

#[derive(Clone, Copy)]
enum Item {
    Producer(usize),
    Event(usize),
    Receiver(usize),
}

impl Item {
    fn name(self) -> String {
        match self {
            Item::Producer(j) => format!("d{j}"),
            Item::Event(j) => format!("e{j}"),
            Item::Receiver(k) => format!("r{k}"),
        }
    }
}

/// A twin program `i`: the text of `fa`, of `fb`, the flows `fb` calls, and the test.
fn twin(rng: &mut Rng, i: usize) -> (String, String, BTreeMap<String, String>, String) {
    loop {
        let producers = rng.pick(&[1, 2, 2, 3]).to_owned();
        let receivers = rng.pick(&[1, 2, 2, 3]).to_owned();
        let kinds: Vec<usize> = (0..producers).map(|_| rng.below(PRODUCERS.len())).collect();
        // The reader of the event: delayed (`prev~(^d)`), or the event itself.
        let reads: Vec<String> =
            (0..producers).map(|j| if rng.chance(60) { format!("prev~(^d{j})") } else { format!("d{j}") }).collect();
        let events: Vec<String> =
            (0..producers).map(|j| format!("e{j}")).chain((0..producers).map(|j| format!("d{j}"))).collect();
        let mut recs: Vec<Recv> = Vec::new();
        let mut names: Vec<String> = Vec::new();
        for k in 0..receivers {
            recs.push(receiver(rng, 0, &names, &events));
            names.push(format!("r{k}"));
        }
        let mut args: Vec<String> = (0..producers)
            .map(|_| if rng.chance(70) { "x".to_string() } else { format!("r{}", rng.below(receivers)) })
            .collect();
        let mut cand: Vec<Item> = (0..producers)
            .map(Item::Producer)
            .chain((0..producers).map(Item::Event))
            .chain((0..receivers).map(Item::Receiver))
            .collect();
        rng.shuffle(&mut cand);
        let text_of = |item: Item, args: &[String], wrap: bool, wrappers: &mut BTreeMap<String, String>| match item {
            Item::Producer(j) => format!("{}~({})", PRODUCERS[kinds[j]], args[j]),
            Item::Event(j) => reads[j].clone(),
            Item::Receiver(k) => written(&recs[k], wrap, wrappers),
        };
        // The order: an item only after the names it reads straight (a `^name` may be below). A cycle through the argument of a producer is given up (the argument is `x`); a cycle of the conditions drops the program.
        let mut placed: Vec<Item> = Vec::new();
        for _ in 0..3 {
            placed.clear();
            let mut rest = cand.clone();
            while !rest.is_empty() {
                let names_above: BTreeSet<String> = placed.iter().map(|p| p.name()).collect();
                let ok = rest.iter().position(|&it| {
                    let text = text_of(it, &args, false, &mut BTreeMap::new());
                    idents(&text).iter().all(|(id, caret)| *caret || !is_name(id, "der") || names_above.contains(id))
                });
                let Some(at) = ok else { break };
                placed.push(rest.remove(at));
            }
            if placed.len() == cand.len() {
                break;
            }
            args = vec!["x".to_string(); producers];
        }
        if placed.len() != cand.len() {
            continue;
        }
        let out: String =
            (0..receivers).map(|k| format!("r{k} * {}", 100usize.pow(k as u32))).collect::<Vec<_>>().join(" + ");
        let mut wrappers = BTreeMap::new();
        let program = |wrap: bool, name: &str, wrappers: &mut BTreeMap<String, String>| {
            let mut above = BTreeSet::new();
            let mut body: Vec<(String, String)> = Vec::new();
            for &it in &placed {
                let text = without_carets(&text_of(it, &args, wrap, wrappers), &above);
                body.push((it.name(), text));
                above.insert(it.name());
            }
            let lets: Vec<String> = body
                .iter()
                .map(|(nm, text)| {
                    let read = |t: &str| idents(t).iter().any(|(id, _)| id == nm);
                    let used = read(&out) || body.iter().any(|(n2, t2)| n2 != nm && read(t2));
                    format!("  let {} = {text}\n", if used { nm.as_str() } else { "_" })
                })
                .collect();
            format!("pub flow {name}(x: U32 at sample) -> U32 at sample {{\n{}  {out}\n}}\n", lets.concat())
        };
        let fa = program(false, &format!("fa{i}"), &mut BTreeMap::new());
        let fb = program(true, &format!("fb{i}"), &mut wrappers);
        let test = format!(
            "test \"case {i}\" {{\n  let a = fa{i}.render(XS, 8.0)\n  let b = fb{i}.render(XS, 8.0)\n  for i in 0 ..< {N} {{\n    assert a.out[i] == b.out[i]\n  }}\n}}\n"
        );
        return (fa, fb, wrappers, test);
    }
}

/// The module of the twins of a seed, and the number of its tests.
fn twin_module(seed: u64) -> (String, usize) {
    let mut rng = Rng::new(seed);
    let xs = frames_of(&mut rng);
    let (mut flows, mut wrappers, mut tests) = (String::new(), BTreeMap::new(), String::new());
    for i in 0..PER_SEED {
        let (fa, fb, w, t) = twin(&mut rng, i);
        flows.push_str(&fa);
        flows.push_str(&fb);
        wrappers.extend(w);
        tests.push_str(&t);
    }
    let wrapper_flows: String = wrappers.values().cloned().collect();
    (format!("{}{flows}{wrapper_flows}{tests}", head(&xs, AC)), PER_SEED)
}

/// §11.3 "値は `let` に分けても分けなくても同じ"、§11.5 (a flow is its body), §11.10 (a chain of `reset_if~`), §11.11: a chain of `reset_if~` with the events of 1 to 3 producers, written straight and with each delay in a
/// flow of its own, gives the same values.
#[test]
fn a_chain_of_resets_with_events_gives_the_same_values_when_its_delays_are_in_flows_of_their_own_u3() {
    let mut wrong = Vec::new();
    for seed in TWIN_SEEDS {
        let (text, tests) = twin_module(seed);
        wrong.extend(failures(&text, tests).into_iter().map(|w| format!("seed {seed:#x}: {w}")));
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The flows of the twins of the places ([`PLACES`]).
const PLACE_FLOWS: &str = "flow kk() -> U32 at event {
  let k = prev~(^k) + 1
  Some(k at sample)
}
flow fwd(m: U32 at event) -> U32 at event { Some(m) }
flow pv(v: U32 at sample) -> U32 at sample { prev~(v, 9) }
flow pve(m: U32 at event) -> U32 at event {
  let p = prev~(m, 9)
  Some(p)
}
flow runs() -> U32 at sample {
  let k = prev~(^k) + 1
  k
}
flow lump(x: U32 at sample) -> U32 at sample { runs~().when~(x > 2).up~(2).down~(2) }
";

/// The twins of the places: a body straight, and with the delay (or the chain) in a flow of its own.
const PLACES: [(&str, &str); 9] = [
    (
        "let e = prev~(^d); let d: U32 = kk~().reset_if~(prev~(x, 9).reset_if~(e >= 3) > 7); d at sample",
        "let e = prev~(^d); let d: U32 = kk~().reset_if~(pv~(x).reset_if~(e >= 3) > 7); d at sample",
    ),
    (
        "let e = prev~(^d); let d: U32 = kk~().when~(prev~(x, 9).reset_if~(e >= 3) > 3); d at sample",
        "let e = prev~(^d); let d: U32 = kk~().when~(pv~(x).reset_if~(e >= 3) > 3); d at sample",
    ),
    (
        "let e = prev~(^d); let d: U32 = pc~(prev~(x, 9).reset_if~(e >= 5)); d at sample",
        "let e = prev~(^d); let d: U32 = pc~(pv~(x).reset_if~(e >= 5)); d at sample",
    ),
    (
        "let e = prev~(^g); let q = prev~(x, 9).reset_if~(e >= 5); let d = pc~(x); let g: U32 = fwd~(d); q",
        "let e = prev~(^g); let q = pv~(x).reset_if~(e >= 5); let d = pc~(x); let g: U32 = fwd~(d); q",
    ),
    (
        "let e = prev~(^g); let d = pc~(x); let q = prev~(d, 9).reset_if~(e >= 5); let g: U32 = fwd~(d); q at sample",
        "let e = prev~(^g); let d = pc~(x); let q = pve~(d).reset_if~(e >= 5); let g: U32 = fwd~(d); q at sample",
    ),
    (
        "let e = prev~(^d); let f = prev~(^g); let q = prev~(x, 9).reset_if~(e >= 9).reset_if~(f >= 5); let d: U32 = pc~(x); let g: U32 = pz~(x); q",
        "let e = prev~(^d); let f = prev~(^g); let q = pv~(x).reset_if~(e >= 9).reset_if~(f >= 5); let d: U32 = pc~(x); let g: U32 = pz~(x); q",
    ),
    (
        "let e = prev~(^d); let q = prev~(x, 9).reset_if~(e >= 2); let d: U32 = kk~().up~(2).reset_if~(q > 5); q",
        "let e = prev~(^d); let q = pv~(x).reset_if~(e >= 2); let d: U32 = kk~().up~(2).reset_if~(q > 5); q",
    ),
    (
        "let d = pz~(x); runs~().when~(x > 2).up~(2).down~(2).reset_if~(d >= 5)",
        "let d = pz~(x); lump~(x).reset_if~(d >= 5)",
    ),
    (
        "let d = pz~(x); runs~().when~(x > 2).up~(2).down~(2).reset_if~(d >= 5).when~(d != 7)",
        "let d = pz~(x); lump~(x).reset_if~(d >= 5).when~(d != 7)",
    ),
];

/// §11.3, §11.5, §11.10, S-1250: a delay (or a chain) an event resets is the same straight and in a flow of its own, where the event comes after the place of the delay and before its store.
#[test]
fn a_delay_at_the_places_a_late_event_resets_gives_the_same_values_in_a_flow_of_its_own_u4() {
    let xs = [1, 6, 2, 7, 3, 4, 1, 1, 5, 2, 8, 1, 3, 2];
    let mut text = head(&xs, PLACE_FLOWS);
    for (i, (a, b)) in PLACES.iter().enumerate() {
        for (name, body) in [("fa", a), ("fb", b)] {
            let body = body.replace("; ", "\n  ");
            text += &format!("pub flow {name}{i}(x: U32 at sample) -> U32 at sample {{\n  {body}\n}}\n");
        }
        text += &format!(
            "test \"place {i}\" {{\n  let a = fa{i}.render(XS, 8.0)\n  let b = fb{i}.render(XS, 8.0)\n  var sum: U32 = 0\n  for i in 0 ..< {N} {{\n    assert a.out[i] == b.out[i]\n    sum = sum + a.out[i]\n  }}\n  assert sum > 0\n}}\n"
        );
    }
    let wrong = failures(&text, PLACES.len());
    assert!(wrong.is_empty(), "{wrong:#?}");
}

// ---- the model of the delays of an event

#[derive(Clone, PartialEq)]
enum MKind {
    Producer,
    Reader,
    Delay,
}

struct Condition {
    /// The name of the event, or none for a constant.
    name: Option<String>,
    src: usize,
    op: &'static str,
    t: u32,
    constant: bool,
}

struct MItem {
    name: String,
    kind: MKind,
    src: usize,
    f: usize,
    arg: String,
    init: u32,
    conds: Vec<Condition>,
}

fn compare(v: u32, op: &str, t: u32) -> bool {
    match op {
        ">=" => v >= t,
        ">" => v > t,
        "<=" => v <= t,
        _ => v != t,
    }
}

/// A program of delays of an event: the text of its flow and the test with the values the model gives.
fn modelled(rng: &mut Rng, xs: &[u32], i: usize) -> (String, String) {
    let sources = *rng.pick(&[2, 2, 3]);
    let mut items: Vec<MItem> = (0..sources)
        .map(|j| MItem {
            name: format!("d{j}"),
            kind: MKind::Producer,
            src: j,
            f: rng.below(PRODUCERS.len()),
            arg: String::new(),
            init: 0,
            conds: vec![],
        })
        .collect();
    for k in 0..*rng.pick(&[0, 1, 2]) {
        let j = rng.below(sources);
        items.push(MItem {
            name: format!("a{k}"),
            kind: MKind::Reader,
            src: j,
            f: 0,
            arg: format!("d{j}"),
            init: 0,
            conds: vec![],
        });
    }
    let cands: Vec<(String, usize)> = items.iter().map(|it| (it.name.clone(), it.src)).collect();
    for k in 0..*rng.pick(&[1, 2, 2, 3]) {
        let (arg, src) = rng.pick(&cands).clone();
        items.push(MItem {
            name: format!("e{k}"),
            kind: MKind::Delay,
            src,
            f: 0,
            arg,
            init: rng.below(12) as u32,
            conds: vec![],
        });
    }
    rng.shuffle(&mut items);
    // An item after what it reads (a reader after its source, a delay after its argument).
    let mut placed: Vec<MItem> = Vec::new();
    while !items.is_empty() {
        let at = items
            .iter()
            .position(|it| it.arg.is_empty() || placed.iter().any(|p| p.name == it.arg))
            .expect("an item whose argument is above");
        placed.push(items.remove(at));
    }
    for idx in 0..placed.len() {
        if placed[idx].kind != MKind::Delay {
            continue;
        }
        let above: Vec<(String, usize)> =
            placed[..idx].iter().filter(|p| p.kind != MKind::Delay).map(|p| (p.name.clone(), p.src)).collect();
        let conds = (0..*rng.pick(&[0, 1, 1, 2, 3]))
            .map(|_| {
                if rng.chance(90) && !above.is_empty() {
                    let (name, src) = rng.pick(&above).clone();
                    Condition {
                        name: Some(name),
                        src,
                        op: rng.pick(&[">=", ">", "<=", "!="]).to_owned(),
                        t: rng.below(8) as u32,
                        constant: false,
                    }
                } else {
                    Condition { name: None, src: 0, op: ">=", t: 0, constant: rng.chance(50) }
                }
            })
            .collect();
        placed[idx].conds = conds;
    }
    let read: BTreeSet<String> = placed
        .iter()
        .flat_map(|p| {
            let mut v = vec![p.arg.clone()];
            v.extend(p.conds.iter().filter_map(|c| c.name.clone()));
            v
        })
        .collect();
    let mut lets = String::new();
    for it in &placed {
        let shown = if read.contains(&it.name) || it.kind == MKind::Delay { it.name.as_str() } else { "_" };
        match it.kind {
            MKind::Producer => lets.push_str(&format!("  let {shown} = {}~(x)\n", PRODUCERS[it.f])),
            MKind::Reader => lets.push_str(&format!("  let {shown} = prev~({})\n", it.arg)),
            MKind::Delay => {
                let chain: String = it
                    .conds
                    .iter()
                    .map(|c| match &c.name {
                        Some(n) => format!(".reset_if~({n} {} {})", c.op, c.t),
                        None => format!(".reset_if~({})", if c.constant { "1 > 0" } else { "1 > 2" }),
                    })
                    .collect();
                lets.push_str(&format!("  let {shown} = prev~({}, {}){chain}\n", it.arg, it.init));
            }
        }
    }
    let delays: Vec<&MItem> = placed.iter().filter(|p| p.kind == MKind::Delay).collect();
    let out: String = delays
        .iter()
        .enumerate()
        .map(|(k, d)| format!("({} at sample) * {}", d.name, 100usize.pow(k as u32)))
        .collect::<Vec<_>>()
        .join(" + ");
    // The model: the state of a delay, what it gave at its last tick, the value of each name at the tick that is going on.
    let mut state: BTreeMap<&str, u32> = BTreeMap::new();
    let (mut gave, mut cur): (BTreeMap<&str, u32>, BTreeMap<&str, u32>) = (BTreeMap::new(), BTreeMap::new());
    for it in &placed {
        match it.kind {
            MKind::Reader => {
                state.insert(&it.name, 0);
            }
            MKind::Delay => {
                state.insert(&it.name, it.init);
                gave.insert(it.name.as_str(), 0u32);
            }
            MKind::Producer => {}
        }
    }
    let mut want = Vec::new();
    for &x in xs {
        for p in placed.iter().filter(|p| p.kind == MKind::Producer) {
            let Some(v) = produced(p.f, x) else { continue };
            for it in &placed {
                match it.kind {
                    MKind::Producer if it.src == p.src => {
                        cur.insert(it.name.as_str(), v);
                    }
                    MKind::Reader if it.src == p.src => {
                        cur.insert(it.name.as_str(), state[it.name.as_str()]);
                        state.insert(&it.name, cur[it.arg.as_str()]);
                    }
                    MKind::Delay => {
                        for c in &it.conds {
                            let hit = if c.name.is_some() { c.src == p.src } else { it.src == p.src };
                            let holds = hit
                                && match &c.name {
                                    Some(n) => compare(cur[n.as_str()], c.op, c.t),
                                    None => c.constant,
                                };
                            if holds {
                                state.insert(&it.name, it.init);
                            }
                        }
                        if it.src == p.src {
                            gave.insert(it.name.as_str(), state[it.name.as_str()]);
                            state.insert(&it.name, cur[it.arg.as_str()]);
                        }
                    }
                    _ => {}
                }
            }
        }
        want.push(delays.iter().enumerate().map(|(k, d)| gave[d.name.as_str()] * 100u32.pow(k as u32)).sum::<u32>());
    }
    let flow = format!("pub flow ea{i}(x: U32 at sample) -> U32 at sample {{\n{lets}  {out}\n}}\n");
    let list: Vec<String> = want.iter().map(u32::to_string).collect();
    let test = format!(
        "test \"e{i}\" {{\n  let a = ea{i}.render(XS, 8.0)\n  let w: [U32; {N}] = [{}]\n  for i in 0 ..< {N} {{\n    assert a.out[i] == w[i]\n  }}\n}}\n",
        list.join(", ")
    );
    (flow, test)
}

fn model_module(seed: u64) -> (String, usize) {
    let mut rng = Rng::new(seed);
    let xs = frames_of(&mut rng);
    let (mut flows, mut tests) = (String::new(), String::new());
    for i in 0..PER_SEED {
        let (f, t) = modelled(&mut rng, &xs, i);
        flows.push_str(&f);
        tests.push_str(&t);
    }
    (format!("{}{flows}{tests}", head(&xs, "")), PER_SEED)
}

/// §11.10 "イベントの条件は、外の `when~` が止めている間もその刻みで初期化する", §11.11 (the order of the ticks), §11.3 (a delay stores what is written at its place), S-1250: the values of the delays of an event that resets are those of the model.
#[test]
fn the_delays_of_an_event_reset_by_events_give_the_values_of_the_model_u3() {
    let mut wrong = Vec::new();
    for seed in MODEL_SEEDS {
        let (text, tests) = model_module(seed);
        wrong.extend(failures(&text, tests).into_iter().map(|w| format!("seed {seed:#x}: {w}")));
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
