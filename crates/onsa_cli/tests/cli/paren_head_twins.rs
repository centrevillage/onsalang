//! A head in parentheses is the instance it holds (W7-17 L4b; spec §11.10, §18.2, `spec/tools.md` §3.3; S-1181): a chain of modifiers whose head, or whose head and first
//! modifiers, are written in parentheses (`(lp~(x)).down~(2)`, `((rs~(ramp~()).when~(c))).reset_if~(r)`) is the same program as the chain written without them.
//!
//! A few pairs from fixed seeds, of the sweep of the break side of L4 (2,000 pairs; `rules/leader.md` 4.9): a head of 8, a chain of 0 to 2 modifiers of 5, a place of 9 in a flow `top`, and how many of the
//! first modifiers the parentheses take with the head (one pair of parentheses or two). The two programs of a pair have the same diagnostics (the code, the message with the names in backticks taken out, the
//! numbers of the candidates and the notes); where there are none, the same Core IR, the same graph of `top` and the same interface. The runs are in this process on texts (`run_texts`), no file written.

use crate::slow_written_forms::run_texts;
use crate::test_support::sweep::Rng;
use crate::test_support::{diagnostics, doc_of, fixes_of, notes_of, str_of};

const SEEDS: [u64; 2] = [1, 2];
const PER_SEED: usize = 30;

const HEAD: &str = "flow ramp() -> F32 at sample {
  let t = prev~(^t) + 1.0
  t
}
flow rs(x: F32 at sample) -> F32 at sample {
  let y = x + prev~(^y)
  y
}
flow lp(x: F32 at sample) -> F32 at sample { prev~(x) }
flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}
";

const HEADS: [&str; 8] =
    ["rs~(ramp~())", "lp~(x)", "prev~(x)", "acc~(f)", "lp~(lp~(x))", "lp~(x + 1.0)", "ramp~()", "lp(x)"];
const MODS: [&str; 5] = [".when~(c)", ".reset_if~(r)", ".down~(2)", ".up~(2)", ".down~(2).down~(2)"];
/// The places of the chain in the body of `top`; `{E}` is the chain.
const PLACES: [&str; 9] = [
    "{E} at sample",
    "let s = {E}\n  s at sample",
    "let s = {E}\n  s",
    "let s = {E}\n  let u = s.when~(c)\n  u at sample",
    "{E} + 1.0",
    "let s = {E} at sample\n  s",
    "let a = {E}\n  let b = {E}\n  (a + b) at sample",
    "{E}.when~(c) at sample",
    "par~ i in 0 ..< 2 { {E} } [0]",
];

fn program(place: &str, chain: &str) -> String {
    let body = place.replace("{E}", chain);
    format!(
        "{HEAD}pub flow top(x: F32 at sample, f: F32 at block, c: Bool at sample, r: Bool at sample) -> F32 at sample {{\n  {body}\n}}\n"
    )
}

/// The diagnostics of `check`, each as its code, its message with what is in backticks taken out, and the numbers of its candidates and notes.
fn shape(text: &str) -> (i32, Vec<(String, String, usize, usize)>) {
    let out = run_texts(&["check", "--json"], text);
    assert!(out.code == 0 || out.code == 1, "check ended with {}: {}\n{text}", out.code, out.stderr);
    let doc = doc_of(&out);
    let shown = |d: &serde_json::Value| {
        let parts: Vec<&str> = str_of(d, "message").split('`').collect();
        parts.iter().step_by(2).copied().collect::<Vec<_>>().join("`_`")
    };
    let ds = diagnostics(&doc).iter();
    (out.code, ds.map(|d| (str_of(d, "code").to_string(), shown(d), fixes_of(d).len(), notes_of(d).len())).collect())
}

#[test]
fn a_head_in_parentheses_is_the_program_of_the_head_without_them() {
    let (mut clean, mut failing) = (0, 0);
    for seed in SEEDS {
        let mut rng = Rng::new(seed);
        for _ in 0..PER_SEED {
            let head = *rng.pick(&HEADS);
            let chain: Vec<&str> = (0..rng.below(3)).map(|_| *rng.pick(&MODS)).collect();
            let place = *rng.pick(&PLACES);
            let taken = rng.below(chain.len() + 1);
            let mut held = format!("({head}{})", chain[..taken].concat());
            if rng.chance(50) {
                held = format!("({held})");
            }
            let plain = program(place, &format!("{head}{}", chain.concat()));
            let paren = program(place, &format!("{held}{}", chain[taken..].concat()));
            let (code, diags) = shape(&plain);
            assert_eq!(
                shape(&paren),
                (code, diags.clone()),
                "seed {seed}: the diagnostics of\n{paren}\nand of\n{plain}"
            );
            if code == 1 {
                failing += 1;
                continue;
            }
            clean += 1;
            for words in [&["dump", "--core"][..], &["graph", "top"], &["interface"]] {
                let (a, b) = (run_texts(words, &plain), run_texts(words, &paren));
                assert_eq!(a.code, 0, "{words:?} of\n{plain}\n{}", a.stderr);
                assert_eq!(
                    (b.code, &b.stdout),
                    (a.code, &a.stdout),
                    "seed {seed}: {words:?} of\n{paren}\nand of\n{plain}"
                );
            }
        }
    }
    // The pairs are of both kinds: programs that pass, and errors (a head that is no instance, a modifier the place does not take).
    assert!(clean >= 10 && failing >= 5, "{clean} pairs with no diagnostic and {failing} with diagnostics");
}
