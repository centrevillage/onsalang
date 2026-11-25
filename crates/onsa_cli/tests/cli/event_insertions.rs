//! An event put at the head of the body of a flow leaves a program as it was (W7-11 U3/t2; spec §11.11, §11.3, §11.4, §11.5, §11.6, §19.1 R-519). The flows are the flows of `tests/spec/flow_semantics`, `flow` and
//! `flow_clock` that carry no mark (`//~`, `#~`) and pass `check` with no diagnostic; a seed picks 36 of them and one flow of each, and a statement that makes an event, reads it and gives nothing out is put at the head of the
//! body of that flow, with a part that is written below the statement and a part that is written above it (the event is made in a flow of its own at the end of the file: `zzdet`, which gives `Some(x)` when `x > 0.5`, and `zzacc`,
//! which adds the events).
//!
//! Property 1 (all 36): `check` gives no diagnostic and ends as a check does (no internal error, no abnormal exit). The insertion is a `let` whose name is not read by anything, so a reader that makes a delay of an event
//! its own clock, or a match over an event with guards, or a loop that reads its own name with `^`, has to be taken as it is written (a program the check passed is not made an error by a `let` added above it).
//! Property 2 (10 of them, the files with `mode = "test"` whose flow is called in a `test`): `onsa test` runs the tests of the file as before: each of them passes. The insertion gives no value to any output, so no value of
//! the tests may change; the tests are those of the file, and their values are the file's own (worked out from the spec by the tests that wrote it, not here).
//!
//! The insertions are three: the event given to a part that adds (`let _ = zzacc~(zzdet~(0.0))`), the event as the target of a `match` with guards (two arms with guards, and a read of the result and of the delay of it), and
//! the event added in a loop that reads its own name (`let zzl = prev~(^zzl) + zzdet~(0.0)`). A flow whose output has a clock of a rate (`sample / N`, `sample * N`: the places of the conversion flows) is not taken, as
//! the clock of the head of a flow like that is the business of §11.9. The runs are in this process on texts (`check_file`, `run_texts`), with no file written (`rules/common.md` 3.7); a failure names the file, the flow,
//! the insertion and the seed.

use std::path::{Path, PathBuf};

use crate::slow_written_forms::run_texts;
use crate::test_support::sweep::{Rng, check_file, ended_well};
use crate::test_support::{diagnostics, doc_of, str_of, tests_of};

const SEED: u64 = 0x0711_0002;
/// How many programs property 1 runs on, and how many of them property 2 runs the tests of.
const PROGRAMS: usize = 36;
const WITH_TESTS: usize = 10;

/// The flows of the insertion, at the end of the file.
const MAKERS: &str = "\nflow zzdet(x: F32 at sample) -> F32 at event {\n  if x > 0.5 { Some(x) } else { None }\n}\n\nflow zzacc(e: F32 at event) -> F32 at sample {\n  let n = prev~(^n) + e\n  n\n}\n";

/// (the name of the insertion, its text): each is put at the head of a body.
const INSERTIONS: [(&str, &str); 3] = [
    ("acc", "  let _ = zzacc~(zzdet~(0.0))\n"),
    (
        "match",
        "  let zzr = match zzdet~(0.0) { zzv if zzv > 0.2 && zzv < 0.9 => zzv, zzw if zzw > 0.1 => zzw, _ => 0.0 }\n  let _ = zzr + prev~(zzr)\n",
    ),
    ("loop", "  let zzl = prev~(^zzl) + zzdet~(0.0)\n  let _ = zzl\n"),
];

fn spec_files() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec");
    let mut files = Vec::new();
    for dir in ["flow", "flow_clock", "flow_semantics"] {
        let mut entries: Vec<PathBuf> =
            std::fs::read_dir(root.join(dir)).expect("read a directory").map(|e| e.expect("an entry").path()).collect();
        entries.sort();
        files.extend(entries.into_iter().filter(|p| p.extension().is_some_and(|e| e == "onsa")));
    }
    files
}

/// The heads of the flows of a text written on one line that ends with `{`: the name, the offset just after the line, and whether the flow is called in a `test` of the file. A flow with a clock of a rate in its
/// heading is not one of them.
fn heads_of(text: &str) -> Vec<(String, usize, bool)> {
    let tests_at = text.lines().scan(0, |at, l| {
        let start = *at;
        *at += l.len() + 1;
        Some((start, l))
    });
    let first_test = tests_at.clone().find(|(_, l)| l.starts_with("test \"")).map(|(s, _)| s);
    let mut out = Vec::new();
    for (start, line) in tests_at {
        let rest = line.strip_prefix("pub flow ").or_else(|| line.strip_prefix("flow "));
        let Some(rest) = rest else { continue };
        if !line.ends_with('{') || line.contains("(sample /") || line.contains("(sample *") {
            continue;
        }
        let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        let called = first_test.is_some_and(|t| {
            let tests = &text[t..];
            tests.contains(&format!("{name}.")) || tests.contains(&format!("{name}~"))
        });
        out.push((name, start + line.len() + 1, called));
    }
    out
}

#[test]
fn an_event_put_at_the_head_of_a_flow_leaves_the_diagnostics_and_the_values_as_they_are() {
    let mut files = spec_files();
    let mut rng = Rng::new(SEED);
    rng.shuffle(&mut files);

    let (mut taken, mut with_tests) = (0, 0);
    let mut failed: Vec<String> = Vec::new();
    for path in &files {
        if taken >= PROGRAMS && with_tests >= WITH_TESTS {
            break;
        }
        let Ok(text) = std::fs::read_to_string(path) else { continue };
        if text.contains("//~") || text.contains("#~") || text.contains("zz") {
            continue;
        }
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let heads = heads_of(&text);
        // A file with tests whose flow is called in a test gives the tests their run, while there are fewer than `WITH_TESTS` of those; any other flow is taken while there are fewer than `PROGRAMS`.
        let called: Vec<_> = heads.iter().filter(|h| h.2).collect();
        let run_tests = text.contains("mode = \"test\"") && with_tests < WITH_TESTS && !called.is_empty();
        let from: Vec<_> = if run_tests { called } else { heads.iter().collect() };
        if from.is_empty() || (!run_tests && taken >= PROGRAMS) {
            continue;
        }
        let base = check_file(&name, &text);
        if !ended_well(&base) || !base.diags.is_empty() {
            continue;
        }
        let (flow, at, _) = from[rng.below(from.len())].clone();
        // The tests are run with the insertions that lower: a `match` with guards in the value of a flow is E0200 on the way to a run (W8-06), so its program is checked only.
        let (kind, put) =
            if run_tests { INSERTIONS[[0, 2][with_tests % 2]] } else { INSERTIONS[taken % INSERTIONS.len()] };
        let mut after = text.clone();
        after.insert_str(at, put);
        after.push_str(MAKERS);
        taken += 1;
        with_tests += usize::from(run_tests);
        let c = check_file(&name, &after);
        if !ended_well(&c) || !c.diags.is_empty() {
            let shown: Vec<String> =
                c.diags.iter().map(|d| format!("{} at {}:{}: {}", d.code, d.line, d.col, d.message)).collect();
            failed.push(format!(
                "property 1: {name} flow `{flow}`, insertion `{kind}` (seed {SEED:#x}): exit {} {}{}",
                c.code,
                c.stderr,
                shown.join("; ")
            ));
            continue;
        }
        if run_tests {
            let out = run_texts(&["test", "--json"], &after);
            let doc = doc_of(&out);
            let want = text.lines().filter(|l| l.starts_with("test \"")).count();
            let bad: Vec<String> = tests_of(&doc)
                .iter()
                .filter(|t| str_of(t, "status") != "ok")
                .map(|t| str_of(t, "name").to_string())
                .collect();
            if out.code != 0 || !diagnostics(&doc).is_empty() || !bad.is_empty() || tests_of(&doc).len() != want {
                failed.push(format!(
                    "property 2: {name} flow `{flow}`, insertion `{kind}` (seed {SEED:#x}): exit {}, {} tests of {want}, not ok: {bad:?}, diagnostics {:?}",
                    out.code,
                    tests_of(&doc).len(),
                    diagnostics(&doc).iter().map(|d| str_of(d, "code")).collect::<Vec<_>>()
                ));
            }
        }
    }
    eprintln!(
        "event_insertions: {taken} programs (property 1), {with_tests} of them with their tests run (property 2)"
    );
    assert!(failed.is_empty(), "{} of the insertions changed a program:\n{}", failed.len(), failed.join("\n"));
    assert!(taken >= PROGRAMS && with_tests >= WITH_TESTS, "the programs taken ({taken}, {with_tests} with tests run)");
}
