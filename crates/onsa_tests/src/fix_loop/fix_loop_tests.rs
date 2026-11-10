use std::collections::BTreeMap;
use std::path::Path;
use std::time::{Duration, Instant};

use onsa_diag::{Code, Diagnostic, Edit, FileId, Fix, SourceMap, Span, Stage};

use super::gate::{Inputs, options, verdict};
use super::walk::{Mark, undoes};
use super::*;
use crate::pending::Pending;

/// A made-up language for the walk, one character a token: `a` deletes
/// itself; `n` has no candidate; `p` and `q` turn into each other; `u`
/// turns into `v`, and `v` back into `u` once no `w` is left, which deletes
/// itself; `g` doubles; `c` becomes `x` (nothing) or `n`; `L` becomes `l`
/// (nothing) or `p`; `j` has two candidates that delete it; `i` becomes `!`,
/// which the check fails on; `k` has a candidate in another file. Every
/// other character is fine.
fn made_up(text: &str) -> Result<Checked, String> {
    if text.contains('!') {
        return Err("panicked at made_up".into());
    }
    let mut sources = SourceMap::default();
    let file = sources.add("m.onsa", text);
    let mut diagnostics = Vec::new();
    for (at, c) in text.char_indices() {
        let span = Span::new(file, at as u32, at as u32 + 1);
        let fix = |title: &str, to: &str| Fix::replace(title, span, to);
        let fixes = match c {
            'a' => vec![fix("delete", "")],
            'n' => vec![],
            'p' => vec![fix("to q", "q")],
            'q' => vec![fix("to p", "p")],
            'u' => vec![fix("to v", "v")],
            'v' if !text.contains('w') => vec![fix("to u", "u")],
            'w' => vec![fix("delete", "")],
            'g' => vec![fix("double", "gg")],
            'c' => vec![fix("to x", "x"), fix("to n", "n")],
            'L' => vec![fix("to l", "l"), fix("to p", "p")],
            'j' => vec![fix("delete", ""), fix("delete too", "")],
            'i' => vec![fix("to !", "!")],
            'k' => vec![Fix::new("elsewhere", vec![Edit::replace(Span::new(FileId(7), 0, 1), "")])],
            _ => continue,
        };
        let mut d = Diagnostic::new(Stage::Syntax, Code::E0002, span, format!("`{c}`"));
        d.fixes = fixes;
        diagnostics.push(d);
    }
    Ok(Checked { sources, diagnostics })
}

/// A table of [`by_text`]: a text, and the edits of the candidates of its one diagnostic.
type Table = &'static [(&'static str, &'static [(u32, u32, &'static str)])];

/// A made-up check by whole texts: for a text of `table`, one diagnostic at
/// the start with one candidate per edit `(start, end, replacement)`.
fn by_text(table: Table) -> impl Fn(&str) -> Result<Checked, String> {
    move |text: &str| {
        let mut sources = SourceMap::default();
        let file = sources.add("m.onsa", text);
        let mut diagnostics = Vec::new();
        if let Some((_, edits)) = table.iter().find(|(t, _)| *t == text) {
            let mut d = Diagnostic::new(Stage::Syntax, Code::E0002, Span::new(file, 0, 0), "here");
            d.fixes =
                edits.iter().map(|&(s, e, to)| Fix::replace(format!("to `{to}`"), Span::new(file, s, e), to)).collect();
            diagnostics.push(d);
        }
        Ok(Checked { sources, diagnostics })
    }
}

fn run(text: &str, options: Options) -> Report {
    walk("m.onsa", text, &options, &made_up)
}

fn branches() -> Options {
    Options { branches: true, ..Options::default() }
}

fn one(text: &str) -> Walk {
    let r = run(text, Options::default());
    assert_eq!(r.walks.len(), 1, "{r:?}");
    r.walks[0].clone()
}

fn titles(w: &Walk) -> Vec<(&str, Option<usize>)> {
    w.steps.iter().map(|s| (s.title.as_str(), s.errors)).collect()
}

#[test]
fn the_names_are_those_of_the_json() {
    for s in Stop::ALL {
        assert_eq!(serde_json::to_value(s).unwrap(), serde_json::json!(s.name()));
    }
    for h in How::ALL {
        assert_eq!(serde_json::to_value(h).unwrap(), serde_json::json!(h.name()));
    }
    assert_eq!(Pick::parse("last"), Some(Pick::Last));
    assert_eq!(Pick::parse("middle"), None);
    let r = run("p", Options::default());
    let v = serde_json::to_value(&r).unwrap();
    assert_eq!(
        (&v["pick"], &v["stops"]["cycle"], &v["walks"][0]["how"]),
        (&serde_json::json!("first"), &serde_json::json!(1), &serde_json::json!("state"))
    );
}

#[test]
fn a_walk_stops_clean_or_without_a_candidate() {
    let w = one("xax");
    assert_eq!((w.stop, titles(&w)), (Stop::Clean, vec![("delete", Some(0))]));
    assert_eq!(one("x").stop, Stop::Clean);
    assert!(one("x").steps.is_empty());
    let w = one("ana");
    assert_eq!((w.stop, titles(&w)), (Stop::NoCandidate, vec![("delete", Some(2)), ("delete", Some(1))]));
    // The last diagnostic first: the same stop, the other place first.
    let r = run("ana", Options { pick: Pick::Last, ..Options::default() });
    assert_eq!((r.walks[0].steps[0].col, r.walks[0].stop), (3, Stop::NoCandidate));
    // The order is the printed one, whatever order the check gives.
    let reversed = |t: &str| {
        made_up(t).map(|mut c| {
            c.diagnostics.reverse();
            c
        })
    };
    let r = walk("m.onsa", "ana", &Options::default(), &reversed);
    assert_eq!(r.walks[0].steps[0].col, 1);
}

#[test]
fn a_text_that_comes_back_is_a_cycle_of_state() {
    let w = one("p");
    assert_eq!((w.stop, w.how, w.back_to), (Stop::Cycle, Some(How::State), Some(0)));
    assert_eq!(titles(&w), [("to q", Some(1)), ("to p", Some(1))]);
    // Back to the text after a step, not the input.
    let w = one("ap");
    assert_eq!((w.how, w.back_to, w.steps.len()), (Some(How::State), Some(1), 3));
}

#[test]
fn a_step_that_restores_an_earlier_one_is_a_cycle_of_undo() {
    // `uw`: `u` to `v`, `w` deleted, `v` back to `u`: the text is not the input, but the third
    // step undoes the first (the round trip of S-435).
    let w = one("uw");
    assert_eq!((w.stop, w.how, w.back_to), (Stop::Cycle, Some(How::Undo), Some(1)));
    assert_eq!(titles(&w), [("to v", Some(1)), ("delete", Some(1)), ("to u", Some(1))]);
    let r = run("uw", Options::default());
    assert_eq!((r.count(Stop::Cycle), r.undos), (1, 1));
    // The mark moves with the edits before it.
    let w = one("auw");
    assert_eq!((w.how, w.back_to), (Some(How::Undo), Some(2)));
    // A replacement elsewhere is no undo.
    let fix = made_up("v").unwrap().diagnostics.remove(0).fixes.remove(0);
    let mark = Mark { start: 1, end: 2, old: "u".into(), new: "v".into() };
    assert_eq!(undoes(&[vec![mark.clone()]], "xv", &fix), None);
    assert_eq!(undoes(&[vec![mark]], "v", &fix), None, "the text there is not the mark's");
}

#[test]
fn a_step_that_takes_out_what_a_move_put_undoes_no_step() {
    // `ab@` to `@ab`: the `@` moved to the front, deleted at its place and inserted (two marks).
    let mut sources = SourceMap::default();
    let file = sources.add("m.onsa", "@ab");
    let moved = vec![
        Mark { start: 3, end: 3, old: "@".into(), new: String::new() },
        Mark { start: 0, end: 1, old: String::new(), new: "@".into() },
    ];
    // The `@` at the front taken out: the insertion is restored and the deletion is not (the
    // `@` is not back at its place), so the step is no undo (`pub @fp(strict) fn h`, S-990).
    let out = Fix::replace("take out", Span::new(file, 0, 1), "");
    assert_eq!(undoes(std::slice::from_ref(&moved), "@ab", &out), None);
    // Taken out and written back at its place: both marks restored, an undo.
    let back = Fix::new("back", vec![Edit::delete(Span::new(file, 0, 1)), Edit::insert(file, 3, "@")]);
    assert_eq!(undoes(std::slice::from_ref(&moved), "@ab", &back), Some(0));
    // One mark of a step with one mark restored is an undo, as before.
    let put = vec![Mark { start: 0, end: 1, old: String::new(), new: "@".into() }];
    assert_eq!(undoes(&[put], "@ab", &out), Some(0));
}

#[test]
fn a_deleted_text_written_again_beside_an_insertion_at_its_place_is_an_undo() {
    // `a~b`: `~` deleted; `X` inserted where it was; `~` inserted before the `X` (or after it).
    static BEFORE: Table =
        &[("a~b", &[(1, 2, "")]), ("ab", &[(1, 1, "X")]), ("aXb", &[(1, 1, "~")]), ("a~Xb", &[(1, 2, "")])];
    let r = walk("m.onsa", "a~b", &Options::default(), &by_text(BEFORE));
    assert_eq!((r.walks[0].how, r.walks[0].back_to, r.walks[0].steps.len()), (Some(How::Undo), Some(1), 3), "{r:?}");
    static AFTER: Table =
        &[("a~b", &[(1, 2, "")]), ("ab", &[(1, 1, "X")]), ("aXb", &[(2, 2, "~")]), ("aX~b", &[(2, 3, "")])];
    let r = walk("m.onsa", "a~b", &Options::default(), &by_text(AFTER));
    assert_eq!((r.walks[0].how, r.walks[0].back_to), (Some(How::Undo), Some(1)), "{r:?}");
    // A replacement of the text on both sides of the point ends the mark: `~` inserted in the
    // middle of it is no undo.
    static AROUND: Table = &[("a~b", &[(1, 2, "")]), ("ab", &[(0, 2, "QQQQ")]), ("QQQQ", &[(1, 1, "~")])];
    let r = walk("m.onsa", "a~b", &Options::default(), &by_text(AROUND));
    assert_eq!((r.walks[0].stop, r.walks[0].steps.len()), (Stop::Clean, 3), "{r:?}");
    // One that ends at the point leaves it.
    static BESIDE: Table =
        &[("a~b", &[(1, 2, "")]), ("ab", &[(0, 1, "QQ")]), ("QQb", &[(2, 2, "~")]), ("QQ~b", &[(2, 3, "")])];
    let r = walk("m.onsa", "a~b", &Options::default(), &by_text(BESIDE));
    assert_eq!((r.walks[0].how, r.walks[0].back_to), (Some(How::Undo), Some(1)), "{r:?}");
}

#[test]
fn a_walk_stops_at_the_limit_and_on_a_divergence() {
    let r = run("aaa a", Options { steps: Some(1), ..Options::default() });
    assert_eq!((r.walks[0].stop, r.walks[0].steps.len()), (Stop::Limit, 1));
    // Twice the tokens, comments included but blanks, and 8.
    assert_eq!(step_limit("let a = 1 // one\n"), 18);
    assert_eq!(step_limit("/* one */\n/// two\n"), 12);
    let w = one("g");
    assert_eq!(w.stop, Stop::Diverge);
    assert_eq!(titles(&w).iter().map(|t| t.1).collect::<Vec<_>>(), [Some(2), Some(3), Some(4), Some(5)]);
    let r = run("g", Options { diverge: 1, ..Options::default() });
    assert_eq!(r.walks[0].steps.len(), 1);
}

#[test]
fn a_walk_stops_on_an_internal_error_or_a_candidate_that_does_not_apply() {
    let w = one("i");
    assert_eq!((w.stop, w.message.as_deref()), (Stop::Internal, Some("panicked at made_up")));
    assert_eq!(w.steps[0].errors, None);
    let w = one("k");
    assert_eq!(w.stop, Stop::CannotApply);
    assert!(w.message.unwrap().contains("unknown file"));
    let r = run("!", Options::default());
    assert_eq!((r.internal.as_deref(), r.walks.len()), (Some("panicked at made_up"), 0));
}

#[test]
fn branches_walk_every_candidate_once_per_text() {
    let r = run("c", branches());
    assert_eq!(r.stops, BTreeMap::from([(Stop::Clean, 1), (Stop::NoCandidate, 1)]));
    assert_eq!(
        (r.explored, r.walks.len(), r.discrepancies),
        (3, 1, Some(1)),
        "the first walk, then only the kept ones"
    );
    // Two candidates give the same text: the second joins.
    let r = run("j", branches());
    assert_eq!((r.count(Stop::Clean), r.joined, r.explored), (1, 1, 2));
    // The walks that stop on a cycle are kept.
    let r = run("cp", branches());
    assert_eq!((r.count(Stop::Cycle), r.walks.len()), (2, 2), "{r:?}");
    // Without branches, the first candidate only.
    assert_eq!(run("c", Options::default()).explored, 2);
    // The texts checked are bounded with branches only, after the first round, which ends as a
    // walk without branches does.
    let r = run("cc", Options { states: 1, ..branches() });
    assert!(r.truncated && r.explored == 4 && r.discrepancies == Some(0), "{r:?}");
    assert_eq!((r.walks[0].stop, r.walks[0].steps.len()), (Stop::Clean, 2));
    let r = run("aaaa", Options { states: 1, ..branches() });
    assert!(!r.truncated && r.walks[0].stop == Stop::Clean && r.walks[0].steps.len() == 4, "{r:?}");
    let r = run("aaa", Options { states: 1, ..Options::default() });
    assert!(!r.truncated && r.walks[0].stop == Stop::Clean, "{r:?}");
    let r = run("aaa", Options { deadline: Some(Instant::now()), ..Options::default() });
    assert!(r.timed_out);
}

#[test]
fn branches_take_the_walks_with_fewer_other_candidates_first() {
    // The second candidate of the first diagnostic leads into a cycle; ten diagnostics after it
    // have two candidates each (2^10 texts): the cycle is walked before their combinations.
    let r = run("Lcccccccccc", branches());
    assert_eq!(r.count(Stop::Cycle), 1, "{r:?}");
    assert!(r.truncated && r.discrepancies >= Some(1), "{r:?}");
    let w = r.walks.iter().find(|w| w.stop == Stop::Cycle).unwrap();
    assert_eq!((w.steps[0].candidate, w.how), (2, Some(How::State)));
}

#[test]
fn a_shorter_walk_to_a_text_is_walked_from_again() {
    // `A` to `B1` (then `B2`, `B3`, `X`) or to `X`; `X` and `Y` turn into each other. With a
    // limit of 4 steps, `X` is first reached at the limit; reached in one step, it is walked
    // from again and the cycle is seen.
    static GRAPH: Table = &[
        ("A", &[(0, 1, "B1"), (0, 1, "X")]),
        ("B1", &[(0, 2, "B2")]),
        ("B2", &[(0, 2, "B3")]),
        ("B3", &[(0, 2, "X")]),
        ("X", &[(0, 1, "Y")]),
        ("Y", &[(0, 1, "X")]),
    ];
    let options = Options { steps: Some(4), ..branches() };
    let r = walk("m.onsa", "A", &options, &by_text(GRAPH));
    assert_eq!((r.count(Stop::Limit), r.count(Stop::Cycle)), (1, 1), "{r:?}");
}

#[test]
fn the_heaviest_walks_are_kept() {
    let mut r = Report::new("m.onsa", &Options::default());
    r.leaf(Walk::new(Stop::Clean, Vec::new()));
    for _ in 0..30 {
        r.leaf(Walk::new(Stop::Limit, Vec::new()));
    }
    r.leaf(Walk::cycle(How::State, 0, Vec::new()));
    r.leaf(Walk::new(Stop::Diverge, Vec::new()));
    r.leaf(Walk::new(Stop::Limit, Vec::new()));
    let kept: Vec<Stop> = r.walks.iter().map(|w| w.stop).collect();
    assert_eq!(kept.len(), WALKS);
    assert_eq!(&kept[..3], [Stop::Clean, Stop::Limit, Stop::Limit]);
    assert_eq!(&kept[WALKS - 2..], [Stop::Cycle, Stop::Diverge]);
    assert_eq!((r.count(Stop::Limit), r.count(Stop::Cycle)), (31, 1));
}

#[test]
fn the_text_of_a_walk() {
    let t = text(&[run("uw", Options::default())]);
    assert_eq!(
        t,
        "m.onsa: cycle (undoes step 1) after 3 steps; 2 errors at the start (--pick first)\n  1. E0002 1:1 \
         candidate 1/1 `to v` -> 1 error\n  2. E0002 1:2 candidate 1/1 `delete` -> 1 error\n  3. E0002 1:1 \
         candidate 1/1 `to u` -> 1 error\n"
    );
    let t = text(&[run("c", branches())]);
    assert!(t.starts_with("m.onsa: walks: clean 1, no-candidate 1; 3 texts checked, 0 joined; 1 errors"), "{t}");
    let t = text(&[run("Lcccccccccc", branches())]);
    assert!(t.contains(", truncated (every walk with at most "), "{t}");
}

// ------------------------------------------------------------ the compiler

#[test]
fn the_compiler_is_walked_through_the_check_of_the_contract() {
    // `let mut` (E0020) gives `var`: one step, nothing left.
    let r = walk("m.onsa", "pub fn f() -> I32 {\n  let mut n = 0\n  n\n}\n", &Options::default(), &check);
    assert_eq!((r.errors, r.walks[0].stop), (1, Stop::Clean), "{r:?}");
    assert_eq!(r.walks[0].steps[0].code, "E0020");
    assert_eq!((r.walks[0].steps[0].line, r.walks[0].steps[0].col), (2, 3));
    // No error: no step.
    let r = walk("m.onsa", "pub fn f() -> I32 {\n  1\n}\n", &Options::default(), &check);
    assert_eq!((r.errors, r.walks[0].stop, r.walks[0].steps.len()), (0, Stop::Clean, 0));
    // A flow input without its clock (E0810) has no candidate (§11.3).
    let src = "pub flow f(x: F32) -> F32 at sample {\n  x\n}\n";
    let r = walk("m.onsa", src, &Options::default(), &check);
    assert_eq!((r.errors, r.walks[0].stop), (1, Stop::NoCandidate), "{r:?}");
    // One unit shows its first error only: 20 `let mut` are one error at the start and 20 steps.
    // The result reads them all (an unread binding is an E0309, §5.1).
    let lets: String = (0..20).map(|i| format!("  let mut a{i} = {i}\n")).collect();
    let sum: Vec<String> = (0..20).map(|i| format!("a{i}")).collect();
    let src = format!("pub fn f() -> I32 {{\n{lets}  {}\n}}\n", sum.join(" + "));
    let r = walk("m.onsa", &src, &Options::default(), &check);
    assert_eq!((r.errors, r.walks[0].stop, r.walks[0].steps.len()), (1, Stop::Clean, 20), "{r:?}");
}

/// The manifest of a case's fragment is checked first (§18.1): the walk takes the candidate of its
/// E1104 (the missing `edition`, S-597), then the file's own `let mut`, and stops clean; a fragment
/// the runner cannot read is a file as `onsa check` reads it.
#[test]
fn the_manifest_of_a_fragment_is_walked_first() {
    let text = "// onsa.toml\n// [package]\n// name = \"p\"\n\npub fn f() -> I32 {\n  let mut n = 0\n  n\n}\n";
    let r = walk("m.onsa", text, &Options::default(), &check);
    let codes: Vec<(&str, u32)> = r.walks[0].steps.iter().map(|s| (s.code.as_str(), s.line)).collect();
    assert_eq!((r.errors, r.walks[0].stop, codes), (1, Stop::Clean, vec![("E1104", 2), ("E0020", 7)]), "{r:?}");
    // A fragment that does not read (a `//~` inside it): the file alone, its `let mut`.
    let bad = text.replace("// name = \"p\"", "// name = \"p\" //~ E0001");
    let r = walk("m.onsa", &bad, &Options::default(), &check);
    let codes: Vec<&str> = r.walks[0].steps.iter().map(|s| s.code.as_str()).collect();
    assert_eq!((r.walks[0].stop, codes), (Stop::Clean, vec!["E0020"]), "{r:?}");
}

/// A made-up repository root under the temporary directory.
struct Root(std::path::PathBuf);

impl Root {
    fn new(name: &str, files: &[(&str, &[u8])]) -> Root {
        let root = std::env::temp_dir().join(format!("onsa-fix-loop-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for (rel, data) in files {
            let p = root.join(rel);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, data).unwrap();
        }
        Root(root)
    }

    fn gate(&self, budget: Duration) -> Gate {
        gate(Path::new(&self.0), budget)
    }
}

impl Drop for Root {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const LET_MUT: &[u8] = b"pub fn f() -> I32 {\n  let mut n = 0\n  n\n}\n";
const CLEAN: &[u8] = b"pub fn f() -> I32 {\n  1\n}\n";

#[test]
fn the_gate_walks_the_cases_and_the_saved_inputs() {
    let root = Root::new(
        "good",
        &[
            ("tests/spec/fixes/a.onsa", LET_MUT),
            ("tests/spec/fixes/pkg/onsa.toml", b"[package]\nname = \"pkg\"\nedition = \"2026\"\n"),
            ("tests/fuzz/b.onsa", CLEAN),
            ("tests/pending.toml", b""),
        ],
    );
    let g = root.gate(GATE_BUDGET);
    assert!(!g.failed, "{}", g.text);
    assert_eq!(
        g.text,
        "fix-loop: 2 files (1 packages not walked), walked with --branches in both orders: cycles (state) 0, \
         cycles (undo) 0, limits 0, truncated 0 (walks of a file and an order); breaches (cycles and limits) 0, held \
         by tests/pending.toml 0"
    );
    let g = root.gate(Duration::ZERO);
    assert!(g.failed && g.text.contains("FAIL the time budget (0 s) ran out"), "{}", g.text);
}

#[test]
fn the_gate_fails_when_it_walks_less_than_it_says() {
    let fails = |name: &str, files: &[(&str, &[u8])], why: &str| {
        let g = Root::new(name, files).gate(GATE_BUDGET);
        assert!(g.failed && g.text.contains(why), "{name}: {}", g.text);
    };
    fails("nothing", &[], "FAIL tests/fuzz: cannot read the directory");
    fails("no-fixes", &[("tests/fuzz/a.onsa", LET_MUT)], "FAIL no single-file case under tests/spec/fixes");
    fails("no-fuzz", &[("tests/spec/fixes/a.onsa", LET_MUT)], "FAIL tests/fuzz: cannot read the directory");
    let unreadable: &[(&str, &[u8])] = &[("tests/spec/fixes/a.onsa", LET_MUT), ("tests/fuzz/b.onsa", b"\xff\xfe")];
    fails("unreadable", unreadable, "FAIL tests/fuzz/b.onsa: cannot read it: not UTF-8");
    let clean: &[(&str, &[u8])] = &[("tests/spec/fixes/a.onsa", CLEAN), ("tests/fuzz/b.onsa", CLEAN)];
    fails("clean", clean, "FAIL no walk took a step");
    let no_list: &[(&str, &[u8])] = &[("tests/spec/fixes/a.onsa", LET_MUT), ("tests/fuzz/b.onsa", CLEAN)];
    fails("no-list", no_list, "tests/pending.toml: ");
}

/// The walks of the gate over the made-up language, one per `(name, text)`.
fn gate_walks(inputs: &[(&str, &str)]) -> (Inputs, Vec<Report>) {
    let options = options(Pick::First, Instant::now() + GATE_BUDGET);
    let reports = inputs.iter().map(|(name, text)| walk(name, text, &options, &made_up)).collect();
    let texts = inputs.iter().map(|(n, t)| (n.to_string(), t.to_string())).collect();
    (Inputs { texts, packages: 0, problems: Vec::new() }, reports)
}

/// A list holding the cycles and the limits of `files`.
fn listed(files: &[&str]) -> Pending {
    let entry = |f: &&str| {
        format!(
            "[[pending]]\nkind = \"gate\"\ntarget = \"fix-loop/{f}\"\nreasons = [\"R-1\"]\nuntil = \"W5-24\"\nnote = \"n\"\n"
        )
    };
    Pending::parse(&files.iter().map(entry).collect::<String>()).unwrap()
}

#[test]
fn the_gate_fails_on_a_cycle_and_the_limit_but_not_on_a_divergence() {
    // `p` and `uw` cycle (of state, of undo); `g` grows: its walk in the gate does not stop on
    // the divergence, and stops at the limit, twice its token and 8 (S-475).
    let (inputs, reports) = gate_walks(&[("p.onsa", "p"), ("uw.onsa", "uw"), ("g.onsa", "g"), ("a.onsa", "xax")]);
    assert_eq!((reports[2].walks[0].stop, reports[2].longest, reports[2].count(Stop::Diverge)), (Stop::Limit, 10, 0));
    let g = verdict(inputs, &reports, &Pending::default(), GATE_BUDGET);
    assert!(g.failed, "{}", g.text);
    for f in ["p.onsa", "uw.onsa", "g.onsa"] {
        assert!(g.text.contains(&format!("FAIL {f} (--pick first): a cycle or the limit of the steps")), "{}", g.text);
    }
    assert!(!g.text.contains("FAIL a.onsa") && g.text.contains("cycles (state) 1, cycles (undo) 1, limits 1"));
    assert!(g.text.ends_with("breaches (cycles and limits) 3, held by tests/pending.toml 0"), "{}", g.text);
    // A walk that stops on a divergence (as the CLI's walks do, `--diverge`) fails nothing.
    let diverging = walk("g.onsa", "g", &Options::default(), &made_up);
    assert_eq!(diverging.count(Stop::Diverge), 1);
    let inputs = Inputs { texts: vec![("g.onsa".into(), "g".into())], packages: 0, problems: Vec::new() };
    let g = verdict(inputs, &[diverging], &Pending::default(), GATE_BUDGET);
    assert!(!g.failed, "{}", g.text);
}

#[test]
fn the_list_holds_the_cycles_and_the_limits_of_its_inputs_only() {
    let walks = || gate_walks(&[("p.onsa", "p"), ("g.onsa", "g"), ("a.onsa", "xax"), ("i.onsa", "i")]);
    let (inputs, reports) = walks();
    let g = verdict(inputs, &reports[..3], &listed(&["p.onsa", "g.onsa"]), GATE_BUDGET);
    assert!(!g.failed, "{}", g.text);
    assert!(g.text.ends_with("breaches (cycles and limits) 2, held by tests/pending.toml 2"), "{}", g.text);
    // An entry of an input without a cycle or a limit, or of no input, fails; so does an internal
    // error of a listed input, which the list never holds.
    let (inputs, reports) = walks();
    let g = verdict(inputs, &reports, &listed(&["p.onsa", "g.onsa", "a.onsa", "b.onsa", "i.onsa"]), GATE_BUDGET);
    for why in [
        "FAIL fix-loop/a.onsa: no cycle and no limit, but listed in tests/pending.toml (until W5-24); remove the entry",
        "FAIL tests/pending.toml: `fix-loop/b.onsa` names no input of the item (until W5-24)",
        "FAIL i.onsa (--pick first): an internal error or a candidate that does not apply",
    ] {
        assert!(g.failed && g.text.contains(why), "{why}\n{}", g.text);
    }
}
