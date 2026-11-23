//! Flows that read the time and cross clocks, mutated by the clocks and the numbers of their stages, leave `check` and `dump --core` with an ordinary end (W7-16 U6a4/t; spec §11.3, §11.4, §11.9, §12.4,
//! §18.1, §18.2; S-1217, S-1211, S-1129, S-565; `rules/leader.md` 4.9: a form that the gate did not catch, put in as a small set from a fixed seed).
//!
//! The input: 11 files of `tests/spec/flow_semantics/` and `tests/spec/flow_clock/` that read `sample_tick()` under `.down~`, gather and deal, have flows with a stage of `sample / N` or a slow port, and a flow
//! that takes the time as an argument (`hold4~(sample_tick())`, `pass~(sample_tick()).down~(4)`), with their `test` blocks and comments cut (so that the flows are what is mutated; each flow is checked alone, §18.1, a flow
//! in error does not stop the others). From a fixed seed, 44 mutants (4 of each file, with 1 to 3 changes each; a quarter start by handing the time to a callee and then cut that callee, a quarter cut a callee first,
//! the others are of any kind) of five kinds:
//! - a number: the `N` of a `.down~(N)`, an `.up~(N)`, a `sample / N` and a `sample * N`, put to 0, 1, a number that is not a power of 2, a large one;
//! - an `at <clock>` left out (also of a parameter and of an output, so that `pass~(sample_tick())` meets a port with no clock);
//! - a clock put in place of another (`sample / N`, `sample * 2`, `block`, `sample`);
//! - `sample_tick()` put at another clock (`sample_tick() at (sample / 4)`), delayed, or put at `block`;
//! - the last tokens of the body of one flow left out, so that the flow is in error and its callers are not (a callee that cannot be read, called with the time as an argument).
//!
//! Property: `check` of the file ends with 0 or 1, with no internal error and no signal (the machine has a crash dialog, `rules/common.md` 3.1), and every diagnostic has an error code of the table (`E`
//! and four digits); and when `check` ends with 0, `dump --core` ends with 0 or 1 and no internal error (a form that the check passes and that cannot be lowered is E0200, Q-09, not an internal error). The commands
//! run in this process on the text (`slow_written_forms::run_texts`), with no file written (`rules/common.md` 3.7). A failure names the mutant (its number, the file, the changes) and the seed.
//!
//! Two groups, in two tests, because the second one is a form that a later work gives an ordinary end (a test that would hold the form in the first would hide a regression of the others): the mutants that have a
//! flow that was cut (so that it is in error) and that is called with the time as the head of its argument (`g~(sample_tick() ...)`, `g~((sample_tick() at (sample / 4)))`), and the others.
//!
//! Reach: the mutants contain the forms that were not caught before, each a form the test counts (a form that the file of the mutant did not have as it was, so that the changes made it; the test fails when one is
//! missing, and names the form): a flow that reads `sample_tick()` at a stage `sample / N` with N not a power of 2 (a finding of U6a3), the time as an argument to a flow whose port has no clock, a chain over a
//! flow with a slower output whose head is the time (`pass~(sample_tick()).down~(4)`), and a callee in error (with a slow port, or whose caller passes the time at a slower tick or as the head under a chain) that a caller
//! passes the time to (the findings of the review before U6b). The inputs of those findings are also run as they are (`the_inputs_of_the_findings...`). The seed was chosen from those that reach every form and, in the
//! second group, an input that is an internal error of the table of the time (so the sweep holds the form it was made for); a change of the changes or of the files asks for a new seed.
//!
//! A third group (W7-16 U7c/t; chains and bursts): 40 mutants of 5 files (`bursts_values`, `up_chain_values`, `down_two_boundaries_values`, `down_chain_time_values`, `chain_blocks_ports`), 8 of each, 1 to 3 changes
//! each, of nine kinds: a number (a modifier's N, a clock's N), an `at` left out, a clock put in place of another, a `sample_tick()` put at another clock, an `.up~` for a `.down~`, a modifier added after a call, two
//! modifiers swapped, a bundle element repeated, a line deleted (a third keep their `test` blocks). Where `check` ends clean, `dump --core`, `interface`, `graph` of the first `pub flow` and `test` end with 0 or 1 and no
//! internal error. The reach test counts each kind and the time handed to a flow with a burst port by a change of the chain (S-1218: an E0815 of `check`), the high finding of U6b2.

use std::path::{Path, PathBuf};

use crate::slow_written_forms::run_texts;
use crate::test_support::sweep::Rng;
use crate::test_support::{doc_of, tests_of};

const SEED: u64 = 1338;
/// How many mutants of each file.
const PER_FILE: usize = 4;

const FILES: &[&str] = &[
    "flow_semantics/sample_tick_time_only_values.onsa",
    "flow_semantics/down_chain_time_values.onsa",
    "flow_semantics/down_chain_values.onsa",
    "flow_semantics/down_gather_deal_values.onsa",
    "flow_semantics/down_gather_inline_args.onsa",
    "flow_semantics/sample_tick_child_values.onsa",
    "flow_semantics/sample_tick_at_a_slower_tick_values.onsa",
    "flow_clock/sample_tick_forms.onsa",
    "flow_clock/modifier_down_forms.onsa",
    "flow_clock/sample_tick_in_flows_in_error.onsa",
    "flow_semantics/slow_tick_branches.onsa",
];

fn spec_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec")
}

// ---- reading the text (no syntax tree: a mutant may not parse)

/// The byte offset of the `}` that closes the `{` at `open`, skipping line comments and strings.
fn close_of(text: &str, open: usize) -> Option<usize> {
    let b = text.as_bytes();
    let (mut depth, mut i) = (0usize, open);
    while i < b.len() {
        match b[i] {
            b'/' if b.get(i + 1) == Some(&b'/') => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            b'"' => {
                i += 1;
                while i < b.len() && b[i] != b'"' {
                    i += if b[i] == b'\\' { 2 } else { 1 };
                }
            }
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// A top-level item that starts a line with `start` (`flow `, `pub flow `, `test "`): the offset of its first byte, of its `{` and of its `}`.
fn items(text: &str, starts: &[&str]) -> Vec<(usize, usize, usize)> {
    let mut out = Vec::new();
    let mut at = 0;
    for line in text.split_inclusive('\n') {
        if starts.iter().any(|s| line.starts_with(s)) {
            if let Some(open) = text[at..].find('{').map(|o| o + at) {
                if let Some(close) = close_of(text, open) {
                    out.push((at, open, close));
                }
            }
        }
        at += line.len();
    }
    out
}

fn flows(text: &str) -> Vec<(usize, usize, usize)> {
    items(text, &["flow ", "pub flow "])
}

/// The text without its comments (a change that lands in a comment is no change; the strings of the seeds hold no `//`).
fn strip_comments(text: &str) -> String {
    text.lines().map(|l| l.find("//").map_or(l, |i| l[..i].trim_end())).collect::<Vec<_>>().join("\n") + "\n"
}

/// The text without its `test` blocks and its comments.
fn strip_tests(text: &str) -> String {
    let mut out = text.to_string();
    for (start, _, close) in items(text, &["test \""]).into_iter().rev() {
        out.replace_range(start..=close, "");
    }
    strip_comments(&out)
}

/// The offsets of the numbers that follow each of `prefixes` in the text.
fn numbers_after(text: &str, prefixes: &[&str]) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for p in prefixes {
        for (i, _) in text.match_indices(p) {
            let s = i + p.len();
            let len = text[s..].bytes().take_while(u8::is_ascii_digit).count();
            if len > 0 {
                out.push((s, s + len));
            }
        }
    }
    out
}

/// The clocks written after ` at `: `sample`, `block`, `init`, `(sample / N)` and `(sample * N)` (the offsets of the clock, and of ` at ` before it).
fn at_clocks(text: &str) -> Vec<(usize, usize, usize)> {
    let mut out = Vec::new();
    for (i, _) in text.match_indices(" at ") {
        let s = i + 4;
        let rest = &text[s..];
        let len = if rest.starts_with('(') {
            rest.find(')').map(|c| c + 1)
        } else {
            ["sample", "block", "init"].iter().find(|w| rest.starts_with(**w)).map(|w| w.len())
        };
        if let Some(len) = len {
            out.push((i, s, s + len));
        }
    }
    out
}

// ---- the changes

/// One mutant: the file it comes from (its text as it was), its text now, the changes made (named, for a failure) and the flows that were cut.
struct Mutant {
    file: &'static str,
    seed_text: String,
    text: String,
    changes: Vec<String>,
    cut: Vec<String>,
}

const NUMBERS: &[&str] = &["0", "1", "3", "5", "6", "7", "9", "100", "4096", "16777216", "33554432", "4294967295"];
const CLOCKS: &[&str] =
    &["sample", "block", "(sample / 3)", "(sample * 2)", "(sample / 4)", "(sample * 4)", "(sample / 2)"];
const TICKS: &[&str] = &[
    "(sample_tick() at (sample / 2))",
    "(sample_tick() at (sample / 4))",
    "(sample_tick() at (sample / 3))",
    "(sample_tick() at block)",
    "prev~(sample_tick())",
];

/// The name of a flow from the start of its line up to its `{`.
fn name_of(header: &str) -> String {
    header
        .trim_start_matches("pub ")
        .trim_start_matches("flow ")
        .split(['(', '<'])
        .next()
        .unwrap_or("")
        .trim()
        .to_string()
}

/// The flows that are called with the time as the head of an argument (`name~(sample_tick()`), as (start, `{`, `}`) of their text.
fn time_callees(text: &str) -> Vec<(usize, usize, usize)> {
    let called = |name: &str| {
        text.contains(&format!("{name}~(sample_tick()")) || text.contains(&format!("{name}~((sample_tick() at"))
    };
    flows(text).into_iter().filter(|&(s, o, _)| called(&name_of(&text[s..o]))).collect()
}

/// Of `places` (offsets), the ones inside the header of a flow that is called with the time as an argument when there are some, in half of the choices (so that the other places are reached too).
fn prefer_callee_headers(rng: &mut Rng, text: &str, places: Vec<usize>) -> Vec<usize> {
    let callees = time_callees(text);
    let near: Vec<usize> =
        places.iter().copied().filter(|&p| callees.iter().any(|&(s, o, _)| s <= p && p < o)).collect();
    if !near.is_empty() && rng.chance(50) { near } else { places }
}

const MODIFIERS: &[&str] =
    &[".down~(2)", ".down~(4)", ".up~(2)", ".up~(4)", ".down~(2).up~(2)", ".when~(true)", ".reset_if~(false)"];

/// Apply one change to the mutant, if it has a place for it; false when the text has none.
fn change(rng: &mut Rng, m: &mut Mutant, kind: usize) -> bool {
    let text = &mut m.text;
    match kind {
        0 => {
            let places = numbers_after(text, &[".down~(", ".up~(", "sample / ", "sample * "]);
            if places.is_empty() {
                return false;
            }
            let starts = prefer_callee_headers(rng, text, places.iter().map(|p| p.0).collect());
            let s = *rng.pick(&starts);
            let (s, e) = *places.iter().find(|p| p.0 == s).expect("a place");
            let n = *rng.pick(NUMBERS);
            m.changes.push(format!("number {} -> {n} at byte {s}", &text[s..e]));
            text.replace_range(s..e, n);
        }
        1 | 2 => {
            let places = at_clocks(text);
            if places.is_empty() {
                return false;
            }
            let starts = prefer_callee_headers(rng, text, places.iter().map(|p| p.0).collect());
            let from = *rng.pick(&starts);
            let (from, s, e) = *places.iter().find(|p| p.0 == from).expect("a place");
            if kind == 1 {
                m.changes.push(format!("`{}` left out at byte {from}", &text[from..e]));
                text.replace_range(from..e, "");
            } else {
                let c = *rng.pick(CLOCKS);
                m.changes.push(format!("clock `{}` -> `{c}` at byte {s}", &text[s..e]));
                text.replace_range(s..e, c);
            }
        }
        3 => {
            let places: Vec<usize> = text.match_indices("sample_tick()").map(|(i, _)| i).collect();
            if places.is_empty() {
                return false;
            }
            // The time as the head of an argument (`~(sample_tick()`) is where the callee's port is met.
            let heads: Vec<usize> = places.iter().copied().filter(|&i| text[..i].ends_with("~(")).collect();
            let i = if !heads.is_empty() && rng.chance(60) { *rng.pick(&heads) } else { *rng.pick(&places) };
            let t = *rng.pick(TICKS);
            m.changes.push(format!("`sample_tick()` -> `{t}` at byte {i}"));
            text.replace_range(i..i + "sample_tick()".len(), t);
        }
        5 => {
            let places: Vec<(usize, &str)> =
                [".down~(", ".up~("].iter().flat_map(|p| text.match_indices(p).map(move |(i, _)| (i, *p))).collect();
            if places.is_empty() {
                return false;
            }
            let &(i, p) = rng.pick(&places);
            let (from, to) = if p == ".down~(" { ("down", "up") } else { ("up", "down") };
            m.changes.push(format!("up/down swapped: `{from}~` -> `{to}~` at byte {i}"));
            text.replace_range(i + 1..i + 1 + from.len(), to);
        }
        6 => {
            // After a modifier or an instance that has no argument.
            let mut places: Vec<usize> = numbers_after(text, &[".down~(", ".up~("]).iter().map(|p| p.1 + 1).collect();
            places.extend(text.match_indices("~()").map(|(i, _)| i + 3));
            if places.is_empty() {
                return false;
            }
            let (at, add) = (*rng.pick(&places), *rng.pick(MODIFIERS));
            m.changes.push(format!("modifier added: `{add}` at byte {at}"));
            text.insert_str(at, add);
        }
        7 => {
            let mut mods: Vec<(usize, usize)> = [".down~(", ".up~("]
                .iter()
                .flat_map(|p| text.match_indices(p).map(|(i, _)| (i, i + text[i..].find(')').map_or(0, |c| c + 1))))
                .collect();
            mods.sort();
            let pairs: Vec<&[(usize, usize)]> = mods.windows(2).filter(|w| w[0].1 == w[1].0).collect();
            if pairs.is_empty() {
                return false;
            }
            let w = *rng.pick(&pairs);
            let (a, b) = (text[w[0].0..w[0].1].to_string(), text[w[1].0..w[1].1].to_string());
            m.changes.push(format!("modifiers swapped: `{a}{b}` at byte {}", w[0].0));
            text.replace_range(w[0].0..w[1].1, &(b + &a));
        }
        8 => {
            // A literal of a bundle or an array (not a type `[T; N]`, nor an index).
            let places: Vec<(usize, usize)> = text
                .match_indices('[')
                .filter_map(|(i, _)| text[i..].find(']').map(|c| (i + 1, i + c)))
                .filter(|&(s, e)| text[s..e].contains(',') && !text[s..e].contains(['[', ';', '\n']))
                .collect();
            if places.is_empty() {
                return false;
            }
            let (s, e) = *rng.pick(&places);
            let first = text[s..e].split(',').next().unwrap_or("").trim().to_string();
            m.changes.push(format!("bundle element repeated: `{first}` at byte {s}"));
            text.insert_str(e, &format!(", {first}"));
        }
        9 => {
            let lines: Vec<&str> = text.lines().collect();
            let i = rng.below(lines.len());
            if lines[i].trim().is_empty() {
                return false;
            }
            m.changes.push(format!("line deleted: `{}`", lines[i].trim()));
            *text = lines.iter().enumerate().filter(|&(j, _)| j != i).map(|(_, l)| *l).collect::<Vec<_>>().join("\n")
                + "\n";
        }
        _ => {
            let fs = flows(text);
            if fs.is_empty() {
                return false;
            }
            // A callee of the time is cut more often than the others (its callers stay as they were).
            let callees = time_callees(text);
            let (start, open, close) =
                if !callees.is_empty() && rng.chance(60) { *rng.pick(&callees) } else { *rng.pick(&fs) };
            let name = name_of(&text[start..open]);
            // Leave out the last 1 to 3 tokens of the body (an identifier or number, or one other character), but not the first: the body is cut, not empty.
            let mut end = close;
            for _ in 0..rng.range(1, 3) {
                let body = text[open + 1..end].trim_end();
                let Some(last) = body.chars().next_back() else { break };
                let word = |c: char| c.is_alphanumeric() || c == '_';
                let cut = if word(last) { body.len() - body.trim_end_matches(word).len() } else { last.len_utf8() };
                if body[..body.len() - cut].trim().is_empty() {
                    break;
                }
                end = open + 1 + body.len() - cut;
            }
            if end == close {
                return false;
            }
            m.changes.push(format!("the end of the body of `{name}` cut: `{}`", text[end..close].trim()));
            m.cut.push(name);
            text.replace_range(end..close, " ");
        }
    }
    true
}

/// The seed files, their tests and comments cut, read once.
fn seed_texts() -> &'static [String] {
    static TEXTS: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();
    TEXTS.get_or_init(|| {
        FILES
            .iter()
            .map(|file| {
                strip_tests(
                    &std::fs::read_to_string(spec_dir().join(file)).unwrap_or_else(|e| panic!("read {file}: {e}")),
                )
            })
            .collect()
    })
}

fn mutants() -> Vec<Mutant> {
    mutants_of(SEED)
}

fn mutants_of(seed: u64) -> Vec<Mutant> {
    let mut rng = Rng::new(seed);
    let mut out = Vec::new();
    for (file, seed_text) in FILES.iter().zip(seed_texts()) {
        for _ in 0..PER_FILE {
            let mut m = Mutant {
                file,
                seed_text: seed_text.clone(),
                text: seed_text.clone(),
                changes: Vec::new(),
                cut: Vec::new(),
            };
            let wanted = rng.range(1, 3);
            // A quarter of the mutants hand the time to a callee in another way (kind 3) and then cut that callee (kind 4), a quarter cut a callee first: the caller is not in error, the callee is. The others
            // are changes of any kind.
            let recipe = rng.below(4);
            let mut tries = 0;
            while m.changes.len() < wanted && tries < 20 {
                let kind = match (recipe, m.changes.len()) {
                    (0, 0) => 3,
                    (0, 1) | (1, 0) => 4,
                    _ => rng.below(5),
                };
                change(&mut rng, &mut m, kind);
                tries += 1;
                // A callee of the time that was cut is often the only change: no other error stands before it, and the caller is as it was.
                if cut_callee_of_the_time(&m) && rng.chance(60) {
                    break;
                }
            }
            out.push(m);
        }
    }
    out
}

// ---- the groups and the forms that were not caught

/// Whether the mutant has a flow that was cut and is called with the time as the head of an argument (`g~(sample_tick()`, `g~((sample_tick() at (sample / 4)))`): the callee is in error and the caller is not.
fn cut_callee_of_the_time(m: &Mutant) -> bool {
    m.cut.iter().any(|name| {
        m.text.contains(&format!("{name}~(sample_tick()")) || m.text.contains(&format!("{name}~((sample_tick() at"))
    })
}

/// The name of each flow with its header (up to its `{`) and its body.
fn parts(text: &str) -> Vec<(String, &str, &str)> {
    flows(text)
        .into_iter()
        .map(|(start, open, close)| (name_of(&text[start..open]), &text[start..open], &text[open + 1..close]))
        .collect()
}

/// The forms of the text (the names are in `FORMS`).
fn forms_of(text: &str) -> Vec<&'static str> {
    let fs = parts(text);
    let mut w = Vec::new();
    // A flow that reads `sample_tick()` at a stage `sample / N`, N not a power of 2 (and not 0, 1, 2).
    let stage_ns = |header: &str| -> Vec<u64> {
        header
            .match_indices("sample / ")
            .filter_map(|(i, p)| {
                header[i + p.len()..].chars().take_while(char::is_ascii_digit).collect::<String>().parse().ok()
            })
            .collect()
    };
    if fs
        .iter()
        .any(|(_, h, b)| b.contains("sample_tick()") && stage_ns(h).iter().any(|&n| n >= 3 && !n.is_power_of_two()))
    {
        w.push("tick-at-a-stage-that-is-not-a-power-of-two");
    }
    for (name, header, _) in &fs {
        let params = header.split_once('(').and_then(|(_, r)| r.split_once(") ->")).map_or("", |(p, _)| p);
        // `callee~(sample_tick())` into a port that has no clock.
        if text.contains(&format!("{name}~(sample_tick())"))
            && params.split(',').any(|p| p.contains(':') && !p.contains(" at "))
        {
            w.push("time-as-an-argument-to-a-port-with-no-clock");
        }
        // `callee~(sample_tick()).down~(N)` over a flow whose output is slower than `sample`.
        let slow_output = header.split_once("->").is_some_and(|(_, o)| o.contains("sample /"));
        if text.contains(&format!("{name}~(sample_tick()).down~(")) && slow_output {
            w.push("time-as-the-head-of-a-chain-over-a-slow-output");
        }
    }
    w
}

const FORMS: &[&str] = &[
    "tick-at-a-stage-that-is-not-a-power-of-two",
    "time-as-an-argument-to-a-port-with-no-clock",
    "time-as-the-head-of-a-chain-over-a-slow-output",
    "callee-in-error-with-a-slow-port-called-with-the-time",
    "callee-in-error-with-the-time-at-a-slower-tick",
    "callee-in-error-with-the-time-under-a-chain",
];

/// The forms that the changes made: those of the mutant that its file, as it was, did not have, and the cut callees (in error) that a caller passes the time to.
fn made_forms(m: &Mutant) -> Vec<&'static str> {
    let before = forms_of(&m.seed_text);
    let mut w: Vec<&'static str> = forms_of(&m.text).into_iter().filter(|f| !before.contains(f)).collect();
    let fs = parts(&m.text);
    for name in &m.cut {
        let slow_port =
            fs.iter().any(|(n, h, _)| n == name && h.split_once("->").is_some_and(|(p, _)| p.contains("at (sample /")));
        if slow_port && m.text.contains(&format!("{name}~(sample_tick()")) {
            w.push("callee-in-error-with-a-slow-port-called-with-the-time");
        }
        if m.text.contains(&format!("{name}~((sample_tick() at (sample /")) {
            w.push("callee-in-error-with-the-time-at-a-slower-tick");
        }
        if m.text.contains(&format!("{name}~(sample_tick()).down~(")) {
            w.push("callee-in-error-with-the-time-under-a-chain");
        }
    }
    w
}

fn describe(i: usize, m: &Mutant, seed: u64) -> String {
    format!("mutant {i} of {} (seed {seed:#x}): {}\n{}", m.file, m.changes.join("; "), m.text)
}

/// `check` of the text ends with 0 or 1, no internal error, and the codes of the diagnostics are error codes; where it ends with 0, `dump --core` ends with 0 or 1 and no internal error. `what` names the input in a
/// failure. The result is the exit code of `check`.
fn assert_ends_as_a_check_does(text: &str, what: &str) -> i32 {
    let out = run_texts(&["check", "--json"], text);
    assert!(out.code == 0 || out.code == 1, "check ended with {}: {}\n{what}", out.code, out.stderr);
    assert!(
        !out.stderr.contains("internal error") && !out.stdout.contains("internal error"),
        "internal error in check: {}\n{what}",
        out.stderr
    );
    let doc = doc_of(&out);
    let diags = doc["diagnostics"].as_array().expect("diagnostics");
    assert_eq!(out.code == 0, diags.is_empty(), "the exit code and the diagnostics disagree\n{what}");
    for d in diags {
        let code = d["code"].as_str().expect("a code");
        let is_error_code = code.len() == 5 && code.starts_with('E') && code[1..].bytes().all(|b| b.is_ascii_digit());
        assert!(is_error_code, "the diagnostic {code} is not an error code\n{what}");
    }
    if out.code == 0 {
        let lowered = run_texts(&["dump", "--core"], text);
        let both = format!("{}{}", lowered.stdout, lowered.stderr);
        assert!(
            (lowered.code == 0 || lowered.code == 1) && !both.contains("internal error"),
            "dump --core ended with {}: {both}\n{what}",
            lowered.code
        );
    }
    out.code
}

/// Run each mutant of the group; how many of them pass the check with no diagnostic (they went on to `dump --core`).
fn run_group(group: &[(usize, Mutant)]) -> usize {
    group.iter().filter(|(i, m)| assert_ends_as_a_check_does(&m.text, &describe(*i, m, SEED)) == 0).count()
}

fn grouped(cut_callees: bool) -> Vec<(usize, Mutant)> {
    mutants().into_iter().enumerate().filter(|(_, m)| cut_callee_of_the_time(m) == cut_callees).collect()
}

/// The mutants that have no cut callee of the time end as a check does (`check` with 0 or 1, no internal error, error codes; `dump --core` too where the check is clean).
#[test]
fn clock_and_number_mutants_of_time_flows_end_as_a_check_does() {
    let group = grouped(false);
    let valid = run_group(&group);
    // The changes reach both: some of the programs stay valid (and are lowered), the others are errors.
    assert!(valid > 0 && valid < group.len(), "{valid} of {} mutants pass the check", group.len());
}

/// The mutants that have a flow that was cut and is called with the time as the head of an argument (the callee is in error, the caller is not) end as a check does too. A callee in error whose caller passes the time
/// at a slower tick or under a chain is an internal error of the table of the time (`the time of Tick(Ratio(-4)), a stage of no function`) until W7-16 U6a4.
#[test]
fn mutants_with_a_callee_in_error_that_is_called_with_the_time_end_as_a_check_does() {
    let group = grouped(true);
    assert!(!group.is_empty(), "no mutant has a cut callee that is called with the time");
    run_group(&group);
}

/// The forms that were missed before are among the mutants, each at least once (the changes made them).
#[test]
fn the_mutants_contain_the_forms_that_were_missed() {
    let ms = mutants();
    for f in FORMS {
        let found: Vec<usize> =
            ms.iter().enumerate().filter(|(_, m)| made_forms(m).contains(f)).map(|(i, _)| i).collect();
        assert!(!found.is_empty(), "no mutant has the form `{f}`; the seed {SEED:#x} or the changes must be revised");
    }
}

/// The inputs of the findings of U6a3, as they were found: the time read at `sample / 3`, handed to a port with no clock, handed to a chain whose head has a slower output. Each is an error that `check` reports.
#[test]
fn the_inputs_of_the_findings_of_u6a3_end_as_a_check_does() {
    let inputs = [
        "flow so() -> U32 at (sample / 3) {\n  sample_tick()\n}\n",
        "flow pass(g: U32) -> U32 at sample {\n  g\n}\n\npub flow top() -> U32 at sample {\n  pass~(sample_tick())\n}\n",
        "flow pass(g: U32 at sample) -> U32 at (sample / 2) {\n  g\n}\n\npub flow argument_time() -> U32 at sample {\n  pass~(sample_tick()).down~(4) at sample\n}\n",
    ];
    for text in inputs {
        assert_eq!(assert_ends_as_a_check_does(text, text), 1, "an error: {text}");
    }
}

/// The inputs of the findings of the review before U6b: a callee that cannot be read (its body ends in a `+`), called with the time at a slower tick, and with the time as the head of a chain. The caller is not in
/// error, the callee is: the check reports the error of the callee and ends with 1. An internal error until W7-16 U6a4.
#[test]
fn the_inputs_of_the_findings_of_the_review_with_a_callee_in_error_end_as_a_check_does() {
    let inputs = [
        "flow g(a: U32 at (sample / 4)) -> U32 at sample {\n  a + \n}\n\npub flow f() -> U32 at sample {\n  g~(sample_tick() at (sample / 4))\n}\n",
        "flow g(a: U32 at (sample / 4)) -> U32 at sample {\n  a +\n}\n\npub flow f() -> U32 at sample {\n  g~(sample_tick()).down~(4) at sample\n}\n",
    ];
    for text in inputs {
        assert_eq!(assert_ends_as_a_check_does(text, text), 1, "an error: {text}");
    }
}

// ---- the third group: chains and bursts (W7-16 U7c/t; spec §11.9, §11.10, §18.1, §18.2; S-1207, S-1214, S-1218)

/// The seed files of the third group: chains with an `.up~`, bursts, two boundaries, the time under a chain, a chain of blocks.
const CHAIN_FILES: &[&str] = &[
    "flow_semantics/bursts_values.onsa",
    "flow_semantics/up_chain_values.onsa",
    "flow_semantics/down_two_boundaries_values.onsa",
    "flow_semantics/down_chain_time_values.onsa",
    "flow_semantics/chain_blocks_ports.onsa",
];
const CHAIN_SEED: u64 = 56;
const CHAIN_PER_FILE: usize = 8;
/// The kinds of change of the third group: a number, an `at` left out, a clock, a `sample_tick()`, an `.up~` for a `.down~`, a modifier added, two modifiers swapped, a bundle element repeated, a line deleted.
const CHAIN_KINDS: &[usize] = &[0, 1, 2, 3, 5, 6, 7, 8, 9];
/// How the changes are named, one for each kind.
const CHAIN_NAMES: &[&str] = &[
    "number ",
    " left out at",
    "clock `",
    "`sample_tick()` ->",
    "up/down swapped",
    "modifier added",
    "modifiers swapped",
    "bundle element repeated",
    "line deleted",
];

/// 40 mutants, 8 of each file (a third of them keep their `test` blocks, so that `test` runs something), 1 to 3 changes each.
fn chain_mutants(seed: u64) -> Vec<Mutant> {
    let mut rng = Rng::new(seed);
    let mut out = Vec::new();
    for file in CHAIN_FILES {
        let full = std::fs::read_to_string(spec_dir().join(file)).unwrap_or_else(|e| panic!("read {file}: {e}"));
        for j in 0..CHAIN_PER_FILE {
            let seed_text = if j % 3 == 0 { strip_comments(&full) } else { strip_tests(&full) };
            let mut m =
                Mutant { file, seed_text: seed_text.clone(), text: seed_text, changes: Vec::new(), cut: Vec::new() };
            let wanted = *rng.pick(&[1, 1, 1, 2, 3]);
            for _ in 0..20 {
                if m.changes.len() == wanted {
                    break;
                }
                let kind = *rng.pick(CHAIN_KINDS);
                change(&mut rng, &mut m, kind);
            }
            out.push(m);
        }
    }
    out
}

/// Whether the text hands `sample_tick()` to a flow whose port is `at (sample * N)` and the chain after the call does not take the N back (the caller then meets a burst, S-1218).
fn time_to_a_burst(text: &str) -> bool {
    parts(text).iter().any(|(name, header, _)| {
        let Some(&(s, e)) = numbers_after(header, &["at (sample * "]).first() else { return false };
        let k = header[s..e].parse::<u32>().map_or(0, u32::trailing_zeros) as i32;
        text.match_indices(&format!("{name}~(sample_tick()")).any(|(i, call)| {
            let from = i + call.len();
            let Some(close) = text[from..].find(')').map(|c| from + c + 1) else { return false };
            let (mut net, mut rest) = (0, &text[close..]);
            while let Some((n, tail)) = [(".down~(", -1), (".up~(", 1)].iter().find_map(|&(p, sign)| {
                let tail = rest.strip_prefix(p)?;
                let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
                Some((sign * tail[..digits].parse::<u32>().ok()?.trailing_zeros() as i32, &tail[digits + 1..]))
            }) {
                (net, rest) = (net + n, tail);
            }
            k + net > 0
        })
    })
}

/// The name of the first `pub flow` of the text.
fn first_pub_flow(text: &str) -> Option<String> {
    flows(text).into_iter().find(|&(s, _, _)| text[s..].starts_with("pub ")).map(|(s, o, _)| name_of(&text[s..o]))
}

/// `check` of the mutant ends as a check does (and `dump --core` where it is clean); where it is clean, `interface`, `graph` of its first `pub flow` and `test` end with 0 or 1 and no internal error. The result is
/// the number of tests `test` ran, or none where the check was not clean.
fn assert_chain_commands_end_well(text: &str, what: &str) -> Option<usize> {
    if assert_ends_as_a_check_does(text, what) != 0 {
        return None;
    }
    let mut commands = vec![vec!["interface"], vec!["test", "--json"]];
    let name = first_pub_flow(text);
    commands.extend(name.as_deref().map(|name| vec!["graph", name]));
    let mut ran = 0;
    for words in commands {
        let out = run_texts(&words, text);
        let both = format!("{}{}", out.stdout, out.stderr);
        let well = (out.code == 0 || out.code == 1) && !both.contains("internal error");
        assert!(well, "{words:?} ended with {}: {both}\n{what}", out.code);
        if words[0] == "test" {
            ran = tests_of(&doc_of(&out)).len();
        }
    }
    Some(ran)
}

/// The mutants of the chains and the bursts end well in `check`, `dump --core`, `interface`, `graph` and `test` (no internal error, no exit by a signal; the commands run in this process, no file written), and
/// some of them reach `test` with tests to run.
#[test]
fn mutants_of_chains_and_bursts_end_as_the_commands_do() {
    let ms = chain_mutants(CHAIN_SEED);
    let ran: Vec<usize> = ms
        .iter()
        .enumerate()
        .filter_map(|(i, m)| assert_chain_commands_end_well(&m.text, &describe(i, m, CHAIN_SEED)))
        .collect();
    assert!(!ran.is_empty() && ran.len() < ms.len(), "{} of {} mutants pass the check", ran.len(), ms.len());
    assert!(ran.iter().sum::<usize>() > 0, "no mutant that passes the check has a test to run");
}

/// The mutants have each kind of change, and the form of U6b2's high finding: the time handed to a flow whose port is a burst by a change of the chain (S-1218, an E0815 of `check`).
#[test]
fn the_chain_mutants_have_every_kind_of_change_and_the_time_that_reaches_a_burst() {
    let ms = chain_mutants(CHAIN_SEED);
    for name in CHAIN_NAMES {
        let found = ms.iter().any(|m| m.changes.iter().any(|c| c.contains(name)));
        assert!(found, "no mutant has the change `{name}`; the seed {CHAIN_SEED:#x} must be revised");
    }
    let time = ms.iter().any(|m| time_to_a_burst(&m.text) && !time_to_a_burst(&m.seed_text));
    assert!(time, "no mutant hands the time to a burst; the seed {CHAIN_SEED:#x} must be revised");
}
