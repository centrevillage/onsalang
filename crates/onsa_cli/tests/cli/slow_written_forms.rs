//! A slow expression written in the call and the same expression bound to a `let` first give the same values (W7-16 U6a4/t; spec §11.3, §11.9, §11.4, §11.6: "a `let` changes no value"; S-1217, S-1211,
//! S-1161; the sweep of the written forms that the review before U6b asked for).
//!
//! The pairs come from the plan of the review (`diffgen`: contexts the slow expression is written in, times forms of the expression), 23 of them: the expression is written straight in the argument of a
//! chain that gathers (`g2~(X).down~(2) at sample`, `g4~(X).down~(4)`), in a `let` of the chain, in the argument of a chain that is itself in an argument, in two chains of one expression, in a plain
//! call, in a `par~`, and the form is a value of the clock `sample / 2` lifted with `at` (the slow part of U6a2: "an expression lifted with `at` in an argument that is gathered"), a delay of a slow `let`, a value
//! of `block` or `init`, the time at a slower tick (`sample_tick() at (sample / 2)`), the output of another chain lifted with `at` (a deal), a name lifted. Each pair is two flows, `fa` with the expression in place and `fb` with
//! `let a = <expression>` and `a` in its place; a test runs both for two calls of `process` (5 and 11 frames, so that a cut of the frames shows) with the same parameters and asserts the outputs are equal. The
//! values are not written by hand (the form that binds is the reference: §11.3 says a `let` is the value of its expression at its clock); the by-hand values of the same forms are in
//! `tests/spec/flow_semantics/down_gather_inline_args.onsa`, which this sweep does not repeat. A pair that panics, or has a diagnostic, fails here; the harness itself is checked by a control pair that differs.
//!
//! The runs are in this process on texts (`run_texts`: the commands of `onsa` read by `onsa_cli::Cli` and run by `onsa_cli::run_command` on a file in memory), with no file written (`rules/common.md` 3.7).

use std::path::{Path, PathBuf};

use clap::Parser;

use crate::test_support::{Out, diagnostics, doc_of, record, str_of, tests_of};

/// The files of a command that reads one `.onsa` file outside any package (as `onsa check m.onsa` reads it), in memory.
struct One<'a> {
    name: &'a str,
    text: &'a str,
}

impl onsa_cli::Files for One<'_> {
    fn read(&self, path: &Path) -> std::io::Result<String> {
        if path == Path::new(self.name) { Ok(self.text.to_string()) } else { Err(std::io::ErrorKind::NotFound.into()) }
    }

    fn canonical(&self, path: &Path) -> PathBuf {
        path.to_path_buf()
    }

    fn load(&self, path: Option<&Path>) -> Result<onsa_driver::Loaded, String> {
        let path = path.ok_or("the command needs the name of its file")?;
        let text = onsa_cli::Files::read(self, path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        onsa_driver::Loaded::from_input(onsa_driver::PackageInput::single_file(onsa_driver::slash_path(path), text))
    }

    fn replace(&self, _: &Path, _: &str) -> std::io::Result<()> {
        Err(std::io::Error::other("no file is written"))
    }
}

/// `onsa <words> m.onsa` on the file `m.onsa` that holds `text`, run in this process (no file is read or written). `words` is the command and its flags (`["test", "--json"]`).
pub fn run_texts(words: &[&str], text: &str) -> Out {
    let files = One { name: "m.onsa", text };
    let args = std::iter::once("onsa").chain(words.iter().copied()).chain(["m.onsa"]);
    let cli = onsa_cli::Cli::try_parse_from(args).expect("the words are the words of a command");
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let code = onsa_cli::run_command(cli.command, &mut onsa_cli::Io::new(&mut out, &mut err, &files));
    Out {
        code: i32::from(code),
        stdout: String::from_utf8(out).expect("utf-8 standard output"),
        stderr: String::from_utf8_lossy(&err).into_owned(),
    }
}

/// The parts every pair uses: a counter of a block, one that adds the previous value, a delayed one, and the heads that gather 2 and 4 frames.
const HEAD: &str = "\
flow cnt(i0: U32 at block) -> U32 at sample {
  let n = (i0 + prev~(^n)) % 997
  n
}
flow idn(a: U32 at sample) -> U32 at sample { a + prev~(a) }
flow sl(a: U32 at (sample / 2)) -> U32 at sample { (a + prev~(a)) at sample }
flow g2(a: U32 at (sample * 2)) -> U32 at sample { a[0] * 10 + a[1] }
flow g4(a: U32 at (sample * 4)) -> U32 at sample { a[0] * 1000 + a[1] * 100 + a[2] * 10 + a[3] }
flow mk(i0: U32 at block) -> U32 at (sample * 2) { [i0, i0 + 5] }
";

/// The places the expression is written in; `{X}` is the expression.
const CONTEXTS: &[(&str, &str)] = &[
    ("gather", "  g2~({X}).down~(2) at sample\n"),
    ("gather_let", "  let r = g2~({X}).down~(2) at sample\n  r + 1\n"),
    ("gather4", "  g4~({X}).down~(4) at sample\n"),
    ("gather_half", "  g2~({X}).down~(4) at sample\n"),
    ("gather_slowlet", "  let r = g2~({X}).down~(2)\n  (r + 1) at sample\n"),
    ("plain", "  idn~({X})\n"),
    ("par", "  let v = par~ k in 0..<2 {{ (g2~(({X}) + k).down~(2) at sample) }}\n  v[0] + v[1]\n"),
    ("nested", "  g2~(g2~({X}).down~(2) at sample).down~(2) at sample\n"),
    ("nested_inner_let", "  let m = g2~({X}).down~(2)\n  g2~(m at sample).down~(2) at sample\n"),
    ("in_expr", "  1 + (g2~({X}).down~(2) at sample) * 2\n"),
    ("two", "  (g2~({X}).down~(2) at sample) + (g4~({X}).down~(4) at sample)\n"),
];

/// The expression; `h` is `cnt~(p).down~(2)`, `h4` is `cnt~(p).down~(4)`, `xx` is `cnt~(p)` (their `let`s are put in front when the word is used).
const FORMS: &[(&str, &str)] = &[
    ("tick", "(h + 1) at sample"),
    ("tick_block", "(h + p * 2) at sample"),
    ("half", "(h4 + 1) at (sample / 2)"),
    ("name", "h at sample"),
    ("block", "p * 3 + 1"),
    ("init", "c0 * 3 + 1"),
    ("block_init", "p * 3 + c0 * 5"),
    ("prevh", "(prev~(h) + 1) at sample"),
    ("deal", "(mk~(p).down~(4) at sample)"),
    ("time", "(sample_tick() at (sample / 2)) at sample"),
    ("time_expr", "((sample_tick() at (sample / 2)) + h) at sample"),
    ("mixed", "((h + 1) at sample) + xx"),
    ("guard_init", "xx + (if c0 > 2 { p * 7 } else { p * 2 })"),
    ("sr", "U32.trunc_from(sample_rate()) + p"),
    ("nested_at", "((h * 2) at sample) * 3 + p * 2"),
    ("inst", "(sl~(h + 1) + 1)"),
    ("inst_block", "idn~(p * 3 + xx) + p * 5"),
];

/// The pairs, as (context, form): the ones of the review's plan that cover each context and the forms, and the forms of the first high finding of U6a2 (a slow expression lifted with `at` in a gathered argument:
/// `gather` x `tick`, `name`, `prevh`, `deal`, `block`, and `gather_half` x `half`).
const GATHER_PAIRS: &[(&str, &str)] = &[
    ("gather", "tick"),
    ("gather", "name"),
    ("gather", "prevh"),
    ("gather", "deal"),
    ("gather", "block"),
    ("gather", "time"),
    ("gather", "time_expr"),
    ("gather_let", "tick_block"),
    ("gather_let", "block_init"),
    ("gather4", "nested_at"),
    ("gather4", "init"),
    ("gather_half", "half"),
    ("gather_half", "block_init"),
    ("gather_slowlet", "mixed"),
    ("gather_slowlet", "guard_init"),
];
const OTHER_PAIRS: &[(&str, &str)] = &[
    ("plain", "inst_block"),
    ("plain", "sr"),
    ("par", "tick"),
    ("par", "time"),
    ("nested", "time_expr"),
    ("nested_inner_let", "tick"),
    ("in_expr", "prevh"),
    ("two", "time"),
];

fn lookup<'a>(table: &'a [(&str, &str)], name: &str) -> &'a str {
    table.iter().find(|(n, _)| *n == name).unwrap_or_else(|| panic!("no entry `{name}`")).1
}

/// Whether `body` uses the name `word` (as a word, not a part of a longer name).
fn uses(body: &str, word: &str) -> bool {
    let is_word = |c: char| c.is_alphanumeric() || c == '_';
    body.match_indices(word).any(|(i, _)| {
        !body[..i].chars().next_back().is_some_and(is_word)
            && !body[i + word.len()..].chars().next().is_some_and(is_word)
    })
}

/// A flow `name` of the parameters `c0` (at `init`) and `p` (at `block`) whose body is `body` with the `let`s of the names it uses put in front.
fn flow(name: &str, body: &str) -> String {
    let mut lets = String::new();
    for (word, init) in [("h", "cnt~(p).down~(2)"), ("h4", "cnt~(p).down~(4)"), ("xx", "cnt~(p)")] {
        if uses(body, word) {
            lets += &format!("  let {word} = {init}\n");
        }
    }
    format!("pub flow {name}(c0: U32 at init, p: U32 at block) -> U32 at sample {{\n{lets}{body}}}\n")
}

/// The flows of a pair, `fa<k>` (the expression in place) and `fb<k>` (bound to `let a` first), and the test that runs both.
fn pair(k: usize, context: &str, form: &str, differ: bool) -> String {
    let (ctx, expr) = (lookup(CONTEXTS, context), lookup(FORMS, form));
    let a = flow(&format!("fa{k}"), &ctx.replace("{X}", expr));
    let bound = if differ { format!("  let a = ({expr}) + 1\n") } else { format!("  let a = {expr}\n") };
    let b = flow(&format!("fb{k}"), &(bound + &ctx.replace("{X}", "a")));
    let t = format!(
        "test \"{context} x {form}\" {{
  var o1: [U32; 5] = [99; 5]
  var o2: [U32; 5] = [98; 5]
  var o3: [U32; 11] = [99; 11]
  var o4: [U32; 11] = [98; 11]
  var s1 = fa{k}.init(fa{k}.Config {{ c0: 3 }}, 8.0)
  var s2 = fb{k}.init(fb{k}.Config {{ c0: 3 }}, 8.0)
  fa{k}.process(inout s1, fa{k}.Params {{ p: 3 }}, inout o1)
  fb{k}.process(inout s2, fb{k}.Params {{ p: 3 }}, inout o2)
  fa{k}.process(inout s1, fa{k}.Params {{ p: 4 }}, inout o3)
  fb{k}.process(inout s2, fb{k}.Params {{ p: 4 }}, inout o4)
  assert o1 == o2
  assert o3 == o4
}}
"
    );
    format!("{a}{b}{t}")
}

/// Run the pairs in one file and assert each test passes (no diagnostic and no panic): the two writings give the same outputs.
fn assert_pairs_equal(pairs: &[(&str, &str)]) {
    let mut text = HEAD.to_string();
    for (k, (context, form)) in pairs.iter().enumerate() {
        text += &pair(k, context, form, false);
    }
    let out = run_texts(&["test", "--json"], &text);
    assert!(!out.stderr.contains("internal error"), "internal error: {}\n{text}", out.stderr);
    let doc = doc_of(&out);
    assert!(diagnostics(&doc).is_empty(), "diagnostics: {}\n{text}", out.stdout);
    assert_eq!(tests_of(&doc).len(), pairs.len(), "every pair is run: {}", out.stdout);
    for (context, form) in pairs {
        let rec = record(&doc, "m", &format!("{context} x {form}"));
        assert_eq!(str_of(rec, "status"), "ok", "the two writings of {context} x {form} differ: {rec}\n{text}");
    }
    assert_eq!(out.code, 0, "{}", out.stdout);
}

/// An expression written in the argument of a chain that gathers (the slow expression lifted with `at`, a delay of a slow `let`, the output of another chain, a value of `block` and `init`, the time at a slower
/// tick, a clock of `sample / 2` under `.down~(4)`), and the same bound to a `let` first: the same values (§11.3, §11.9; the first high finding of U6a2, hoisting inside a gathered argument).
#[test]
fn an_expression_written_in_a_gathered_argument_gives_the_values_of_its_let() {
    assert_pairs_equal(GATHER_PAIRS);
}

/// The other places an expression is written in: the argument of a plain call, in a `par~`, of a chain that is an argument of a chain, of a chain bound to a `let` and lifted, in a larger expression, and of two chains
/// of one expression, with a delay of a slow `let`, the time at a slower tick, a call of a flow and the rate.
#[test]
fn an_expression_written_in_a_plain_nested_or_par_place_gives_the_values_of_its_let() {
    assert_pairs_equal(OTHER_PAIRS);
}

/// The harness sees a difference: a pair whose second flow adds 1 to the expression is not equal, so the other two tests would fail on a real difference (§11.3's reference is the form that binds).
#[test]
fn the_pair_check_fails_on_a_pair_that_differs() {
    let text = format!("{HEAD}{}", pair(0, "gather", "tick", true));
    let out = run_texts(&["test", "--json"], &text);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = doc_of(&out);
    assert_ne!(str_of(record(&doc, "m", "gather x tick"), "status"), "ok", "{}", out.stdout);
}
