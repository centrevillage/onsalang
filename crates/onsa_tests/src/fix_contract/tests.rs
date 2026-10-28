use super::reading::{not_minimal, reading_difference};
use super::same_place::{in_same_place, outer_form};
use super::*;
use crate::fragment::Mode;
use onsa_driver::reduce::Unit;
use std::collections::BTreeSet;

#[test]
fn places_and_leaves() {
    assert_eq!(Place::parse("3:5").unwrap(), Place { file: None, line: 3, col: 5 });
    assert_eq!(Place::parse("src/a.onsa:3:5").unwrap(), Place { file: Some("src/a.onsa".into()), line: 3, col: 5 });
    for bad in ["3", "3:", ":5", "0:1", "1:0", "03:1", "a:b", ":3:5", "x :3:5", "3:5 "] {
        assert!(Place::parse(bad).is_err(), "{bad}");
    }
    assert_eq!(parse_leaf("22:30 E0020").unwrap(), (Place { file: None, line: 22, col: 30 }, Code::E0020));
    assert!(parse_leaf("22:30").is_err());
    assert!(parse_leaf("22:30 E9999").is_err());
}

fn spec(at: &str, leaves: &[&str], clean: bool, same_code: bool) -> FixSpec {
    FixSpec {
        at: at.into(),
        code: "E0020".into(),
        candidate: 1,
        leaves: leaves.iter().map(|s| s.to_string()).collect(),
        clean,
        same_code,
        line: 5,
        at_offset: 0,
    }
}

#[test]
fn entries_that_say_nothing_or_contradict_are_errors() {
    assert!(check_specs(&[spec("3:5", &["3:9 E0020"], false, false)], Mode::Check).is_ok());
    assert!(check_specs(&[spec("3:5", &[], true, false)], Mode::Test).is_ok());
    assert!(check_specs(&[spec("3:5", &[], false, true)], Mode::Check).is_ok());
    let e = |specs: &[FixSpec], mode: Mode| check_specs(specs, mode).unwrap_err();
    assert!(e(&[spec("3:5", &[], false, false)], Mode::Check).contains("only the default"));
    assert!(e(&[spec("3:5", &["3:9 E0020"], true, false)], Mode::Check).contains("cannot have `leaves`"));
    assert!(e(&[spec("3:5", &[], true, false)], Mode::Parse).contains("needs `mode"));
    assert!(e(&[spec("3:5", &["3:9 E0020", "3:9 E0020"], false, false)], Mode::Check).contains("twice"));
    assert!(e(&[spec("x", &[], true, false)], Mode::Check).contains("at:"));
    let mut zero = spec("3:5", &[], true, false);
    zero.candidate = 0;
    assert!(e(&[zero], Mode::Check).contains("from 1"));
    let two = [spec("3:5", &[], true, false), spec("3:5", &[], false, true)];
    assert!(e(&two, Mode::Check).contains("the same candidate"));
}

#[test]
fn same_code_ignores_comments_and_their_lines_but_not_code_or_line_breaks() {
    let before = "let a = 1 /* one */ + 2\n";
    assert_eq!(code_difference(before, "let a = 1 + 2 // one\n"), None, "moved to the end of the line");
    assert_eq!(code_difference(before, "// one\nlet a = 1 + 2\n"), None, "moved above the line");
    assert!(code_difference(before, "let a = 1 // one + 2\n").is_some(), "the code went into the comment");
    assert!(code_difference(before, "let a = 1\n+ 2 // one\n").is_some(), "a line break added");
    assert!(code_difference("a\nb\n", "a b\n").is_some(), "a line break removed");
    assert_eq!(code_difference("a\n\nb\n", "a\nb\n"), None, "one line break or more");
    assert!(code_difference("a\n", "a b\n").unwrap().contains("`b`"));
}

fn units(spans: &[(u32, u32, Option<usize>)]) -> Vec<Unit> {
    spans.iter().map(|&(s, e, p)| Unit { span: Span::new(FileId(0), s, e), parent: p }).collect()
}

/// An edit replacing `s..e` of file 0 with `len` characters.
fn edit(s: u32, e: u32, len: u32) -> Moved {
    Moved { before: Span::new(FileId(0), s, e), after: Span::new(FileId(0), s, s + len) }
}

fn touched(before: &[Unit], after: &[Unit], edits: &[Moved]) -> BTreeSet<usize> {
    correspond(before, after, edits).touched
}

#[test]
fn touched_units_are_all_but_the_untouched_ones() {
    // S-302. 0: an item 0..10; 1: an impl 20..60 with members 2 (25..35) and 3 (40..50).
    let us = units(&[(0, 10, None), (20, 60, None), (25, 35, Some(1)), (40, 50, Some(1))]);
    let t = |after: &[Unit], es: &[Moved]| touched(&us, after, es).into_iter().collect::<Vec<_>>();
    // A replacement of the same length inside the item: the units after are the same.
    assert_eq!(t(&us, &[edit(3, 4, 1)]), [0]);
    // Between the units: nothing touched, the units after it moved.
    let moved = units(&[(0, 10, None), (22, 62, None), (27, 37, Some(1)), (42, 52, Some(1))]);
    assert_eq!(t(&moved, &[edit(12, 12, 2)]), Vec::<usize>::new());
    // An insertion at a border of a unit is not inside it.
    let moved = units(&[(2, 12, None), (22, 62, None), (27, 37, Some(1)), (42, 52, Some(1))]);
    assert_eq!(t(&moved, &[edit(0, 0, 2)]), Vec::<usize>::new());
    // Inside a member: the member, not its impl (moved by the length difference).
    let longer = units(&[(0, 10, None), (20, 61, None), (25, 36, Some(1)), (41, 51, Some(1))]);
    assert_eq!(t(&longer, &[edit(27, 29, 3)]), [2]);
    // The heading of the impl.
    assert_eq!(t(&us, &[edit(21, 22, 1)]), [1]);
    // A border that moved: a unit after it that is no unit before (S-302: a
    // candidate that takes the next item into a comment); the members keep their range.
    let merged = units(&[(0, 60, None), (25, 35, Some(0)), (40, 50, Some(0))]);
    assert_eq!(t(&merged, &[edit(3, 4, 1)]), [0]);
    // Another file is not touched.
    let other = Moved { before: Span::new(FileId(1), 3, 4), after: Span::new(FileId(1), 3, 4) };
    assert_eq!(t(&us, &[other]), Vec::<usize>::new());
}

#[test]
fn the_same_place_is_half_open_and_a_point_for_an_empty_range() {
    let r = |s: u32, e: u32| Span::new(FileId(0), s, e);
    assert!(in_same_place(&[r(3, 6)], r(3, 4)) && in_same_place(&[r(3, 6)], r(5, 9)));
    assert!(!in_same_place(&[r(3, 6)], r(6, 7)), "the end of a range is not in it");
    assert!(!in_same_place(&[r(3, 6)], r(2, 4)));
    assert!(in_same_place(&[r(4, 4)], r(4, 5)) && !in_same_place(&[r(4, 4)], r(5, 5)));
    let other = Span::new(FileId(1), 3, 4);
    assert!(!in_same_place(&[r(3, 6)], other));
    // The forms it caught still are: `;;` fixed by halves, and `---x` (`--`
    // and `-x`) parenthesized by its first operator alone, were violations
    // inside the original range.
    assert!(in_same_place(&[r(10, 12)], r(11, 12)));
}

#[test]
fn the_reading_outside_the_edits_is_compared() {
    let e = |s: u32, e: u32, len: u32| vec![edit(s, e, len)];
    // `let mut` to `var`: the tokens outside are the same, moved.
    let before = "let mut n = 0\n";
    assert_eq!(reading_difference(before, "var n = 0\n", FileId(0), &[edit(0, 3, 3), edit(4, 8, 0)]), None);
    // A block comment written `//` in place takes the code after it (S-302).
    let before = "let a = 1 /* one */ + 2\n";
    let d = reading_difference(before, "let a = 1 // one + 2\n", FileId(0), &e(10, 19, 6)).unwrap();
    assert!(d.contains("token"), "{d}");
    // Blanks are not compared.
    assert_eq!(reading_difference("a  b\n", "a b\n", FileId(0), &e(1, 3, 1)), None);
    // Two tokens that touch after a deletion are read as one.
    assert!(reading_difference("a /*c*/ b\n", "ab\n", FileId(0), &e(1, 8, 0)).is_some());
}

#[test]
fn same_place_finds_a_diagnostic_left_where_the_candidate_was() {
    // `let mut` (E0020) gives `var`: nothing left.
    let ok = same_place("pub fn f() -> I32 {\n  let mut n = 0\n  n\n}\n");
    assert_eq!(ok.candidates, 1, "{ok:?}");
    assert!(ok.violations.is_empty(), "{ok:?}");
    assert!(ok.internal.is_none());
    // No diagnostic: nothing to check.
    assert_eq!(same_place("pub fn f() -> I32 {\n  1\n}\n"), SamePlace::default());
    // The candidate of the E0411 gives `x.narrow_i32()`, an `Option[I32]`: an E0401 of the
    // same stage is left there (until W5-02).
    let left = same_place("pub fn f(x: I64) -> I32 {\n  x as I32\n}\n");
    assert_eq!(left.candidates, 1);
    let v: Vec<(&str, &str, Option<u32>)> =
        left.violations.iter().map(|v| (v.code.as_str(), v.left.as_str(), v.left_line)).collect();
    assert_eq!(v, [("E0411", "E0401", Some(2))], "{left:?}");
    // An E0010 there before the candidate of the E0011 is not left by it, though its message
    // quotes the chain the candidate changed.
    let before = same_place("pub fn f(a: I32, b: I32) -> I32 {\n  a as I32 * 2 % b\n}\n");
    assert!(before.violations.is_empty(), "{before:?}");
    // A stack of prefix operators is one form, fixed whole (S-248, S-297): nothing left.
    let form = same_place("pub fn f(x: I32) -> I32 {\n  - - -x\n}\n");
    assert_eq!(form.candidates, 1, "{form:?}");
    assert!(form.violations.is_empty(), "{form:?}");
    // A stray `1.` holds two errors at one place (E0020 and E0002); the E0002 is
    // reported (S-281), and it has no candidate.
    let stray = same_place("1.\n");
    assert_eq!(stray.candidates, 0, "{stray:?}");
}

/// `before` with the edits `(start, end, replacement)` (in order, apart)
/// applied, and where they went.
fn edited(before: &str, edits: &[(u32, u32, &str)]) -> (String, Vec<Moved>) {
    let (mut after, mut moved, mut delta) = (String::new(), Vec::new(), 0i64);
    let mut at = 0;
    for &(s, e, r) in edits {
        after.push_str(&before[at..s as usize]);
        after.push_str(r);
        let start = (s as i64 + delta) as u32;
        moved.push(Moved {
            before: Span::new(FileId(0), s, e),
            after: Span::new(FileId(0), start, start + r.len() as u32),
        });
        delta += r.len() as i64 - (e - s) as i64;
        at = e as usize;
    }
    after.push_str(&before[at..]);
    (after, moved)
}

fn shapes(before: &str, edits: &[(u32, u32, &str)]) -> (Vec<String>, usize) {
    let (after, moved) = edited(before, edits);
    not_minimal(&Readings::of(FileId(0), before, &after), FileId(0), &moved)
}

/// The check 5 (S-251, X-3): an edit that keeps a token of its range.
#[test]
fn an_edit_that_keeps_a_token_or_a_comment_is_not_minimal() {
    let one = |before: &str, edits: &[(u32, u32, &str)]| {
        let (m, n) = shapes(before, edits);
        assert_eq!(m.len(), 1, "{before:?} {edits:?}: {m:?}");
        (m.into_iter().next().unwrap(), n)
    };
    // `<T>` to `[T]`: one edit keeps `F32` inside it; the two edits are minimal.
    let (m, n) = one("x: Buf<F32>\n", &[(6, 11, "[F32]")]);
    assert!(m.contains("the token `F32` stays inside it (split it"), "{m}");
    assert_eq!(n, 1);
    assert_eq!(shapes("x: Buf<F32>\n", &[(6, 7, "["), (10, 11, "]")]), (vec![], 2));
    // R-237: ` at block` to `) at block` keeps the clock; the `)` alone is minimal.
    let src = "g: fn(F32) -> F32 at block\n";
    let (m, _) = one(src, &[(3, 3, "("), (17, 26, ") at block")]);
    assert!(m.contains("edit 2 is not minimal") && m.contains("last token `block` stays"), "{m}");
    assert_eq!(shapes(src, &[(3, 3, "("), (17, 17, ")")]), (vec![], 0));
    // The first token kept, and an edit that changes nothing.
    assert!(one("a + b\n", &[(0, 3, "a -")]).0.contains("first token `a` stays"));
    assert!(one("a + b\n", &[(0, 1, "a")]).0.contains("first token `a` stays"));
    // A comment of the range written again.
    let (m, _) = one("a /* c */ + b\n", &[(2, 11, "/* c */ -")]);
    assert!(m.contains("the comment `/* c */`"), "{m}");
    // Insertions at the ends of tokens, deletions, blanks: nothing compared.
    assert_eq!(shapes("ab\n", &[(2, 2, "c")]), (vec![], 0));
    assert_eq!(shapes("a b\n", &[(1, 3, "")]), (vec![], 0));
    assert_eq!(shapes("ab\n", &[(1, 1, " ")]), (vec![], 0));
    // A token replaced by others that share none.
    assert_eq!(shapes("i32\n", &[(0, 3, "I32")]), (vec![], 1));
}

/// R-237: the candidate of a clock at the end of a function type inserts
/// `(` and `)` (`tests/spec/fixes/e0020_clock_after_fn_type.onsa`, lines 14
/// and 18), and the check 5 catches the form before the fix.
#[test]
fn the_clock_after_a_function_type_inserts_the_parentheses_only() {
    let path = crate::case::repo_root().join("tests/spec/fixes/e0020_clock_after_fn_type.onsa");
    let text = std::fs::read_to_string(path).unwrap();
    let run = check_text(&text).unwrap();
    let sources = &run.loaded.sources;
    for (line, clock) in [(14, " at block"), (18, " at sample")] {
        let d = run.analyzed.diagnostics.iter().find(|d| sources.file(d.span.file).line_col(d.span.start).line == line);
        let d = d.unwrap_or_else(|| panic!("no diagnostic on line {line}"));
        let fix = &d.fixes[0];
        let edits: Vec<(bool, &str)> = fix.edits().iter().map(|e| (e.span.is_empty(), e.replace.as_str())).collect();
        assert_eq!(edits, [(true, "("), (true, ")")], "line {line}");
        let now = check_candidate(&run, d, fix).unwrap();
        assert!(now.problems.is_empty(), "line {line}: {:?}", now.problems);
        // Before the fix: the clock replaced by `)` and itself.
        let close = fix.edits()[1].span;
        assert!(text[close.start as usize..].starts_with(clock), "line {line}");
        let old = Fix::new(
            fix.title(),
            vec![
                fix.edits()[0].clone(),
                onsa_diag::Edit::replace(
                    Span::new(close.file, close.start, close.start + clock.len() as u32),
                    format!("){clock}"),
                ),
            ],
        );
        let before = check_candidate(&run, d, &old).unwrap();
        assert_eq!(before.text, now.text, "line {line}: the same text after it");
        assert!(
            before.problems.iter().any(|p| p.contains("edit 2 is not minimal") && p.contains("stays (shrink")),
            "line {line}: {:?}",
            before.problems
        );
    }
}

/// The one diagnostic of `src` and its first candidate checked again.
fn first_candidate(src: &str) -> (TextCheck, CandidateCheck) {
    let run = check_text(src).unwrap();
    assert_eq!(run.analyzed.diagnostics.len(), 1, "{src}: {:?}", run.analyzed.diagnostics);
    let d = &run.analyzed.diagnostics[0];
    let now = check_candidate(&run, d, &d.fixes[0]).unwrap();
    (run, now)
}

/// X-3 (α): a candidate that leaves a diagnostic in a unit it does not
/// touch, which held none before it, breaks the contract: here a rename of
/// the declaration alone, made by hand (the candidate of the E0320 renames
/// the use too, S-82).
#[test]
fn a_candidate_that_breaks_a_unit_it_does_not_touch_breaks_the_contract() {
    let src = "pub fn BadFn() -> I32 {\n  1\n}\n\npub fn user() -> I32 {\n  BadFn()\n}\n";
    let run = check_text(src).unwrap();
    let d = &run.analyzed.diagnostics[0];
    let alone = onsa_diag::Fix::replace("rename the declaration alone", d.span, "bad_fn");
    let now = check_candidate(&run, d, &alone).unwrap();
    assert!(
        matches!(&now.problems[..], [p] if p.contains("the units its edits touch hold none")
                && p.contains("the units that held no diagnostic before it hold 6:3 E0302 besides")),
        "{:?}",
        now.problems
    );
    // A later stage too: the E0401 of `Bool` after a candidate of the syntax stage.
    let src = "pub fn f(x: I32) -> I32 {\n  let mut n = x\n  n\n}\n\npub fn g() -> Bool {\n  1\n}\n";
    let run = check_text(src).unwrap();
    assert_eq!(run.analyzed.diagnostics.len(), 2, "{:?}", run.analyzed.diagnostics);
    let (_, now) = first_candidate("pub fn f(x: I32) -> I32 {\n  let mut n = x\n  n\n}\n");
    assert!(now.problems.is_empty(), "{:?}", now.problems);
}

/// X-3 (α): a candidate that shows an error the check held back (it read
/// what the check did not) keeps the contract: the derive list not read
/// (S-460), the fields a syntax error cut (S-260), and a parameter whose
/// type failed to resolve.
#[test]
fn a_candidate_that_shows_an_error_held_back_keeps_the_contract() {
    let forms = [
        (
            "#[derive(PartialEq)]\npub struct Pt {\n  x: I32,\n}\n\nfn ordered(a: Pt, b: Pt) -> Bool {\n  a < b\n}\n",
            Code::E0401,
        ),
        ("pub struct S {\n  x: I32,\n  y: I32;\n}\n\nfn f(s: S) -> I32 {\n  s.z\n}\n", Code::E0413),
        ("fn h(p: i32) -> I32 {\n  1\n}\n\nfn caller() -> I32 {\n  h(true)\n}\n", Code::E0401),
        // The rt recursion through a body the check did not finish (X-3/U1c/b, F1).
        (
            "pub rt fn a(x: I64) -> I64 {\n  b(x)\n}\n\npub rt fn b(x: I64) -> I64 {\n  a(x) + (1 & 1 | 1)\n}\n",
            Code::E0903,
        ),
    ];
    for (src, shown) in forms {
        let (run, now) = first_candidate(src);
        assert!(now.problems.is_empty(), "{src}: {:?}", now.problems);
        assert!(now.diagnostics.iter().any(|d| d.code == shown), "{src}: {:?}", now.diagnostics);
        // The unit of the user is the one the driver gives: the second.
        assert_eq!(run.analyzed.unread_units().into_iter().collect::<Vec<_>>(), [0, 1], "{src}");
    }
}

/// L2: a comment written again with other blanks at its end is the same comment.
#[test]
fn the_blanks_at_the_end_of_a_comment_are_not_compared() {
    let (m, n) = shapes("a // c  \nb\n", &[(0, 8, "z // c")]);
    assert!(matches!(&m[..], [p] if p.contains("the comment `// c`")), "{m:?}");
    assert_eq!(n, 1);
}

#[test]
fn a_candidate_applies_alone_to_the_one_file_or_says_why_not() {
    let mut sources = SourceMap::default();
    let file = sources.add("m.onsa", "let mut n = 0\n");
    let (text, applied) = apply_alone(&sources, &Fix::replace("var", Span::new(file, 0, 7), "var")).unwrap();
    assert_eq!((text.as_str(), applied.ranges[0]), ("var n = 0\n", Span::new(file, 0, 3)));
    let unknown = Fix::new("x", vec![onsa_diag::Edit::delete(Span::new(FileId(3), 0, 1))]);
    let e = apply_alone(&sources, &unknown).unwrap_err();
    assert!(matches!(&e, Unapplied::CannotApply(m) if m.contains("unknown file")), "{e:?}");
    let other = sources.add("n.onsa", "x\n");
    let e = apply_alone(&sources, &Fix::delete("x", Span::new(other, 0, 1))).unwrap_err();
    assert_eq!((e.clone(), e.to_string()), (Unapplied::OtherFile, "it edits a file other than the input".into()));
}

#[test]
fn same_place_does_not_count_the_outer_link_of_a_chain_of_calls() {
    // `g(1)(2)(3)`: the candidate fixes the first link (`g(1).(2)(3)`); the next link, which
    // starts where the first did and ends after it, was not read by the syntax stage before
    // (S-326, S-314): no violation.
    let chain = same_place(
        "pub fn adder(x: I32) -> fn(I32) -> I32 {\n  adder\n}\n\npub fn g(x: I32) -> fn(I32) -> fn(I32) -> I32 {\n  adder\n}\n\npub fn f() -> I32 {\n  g(1)(2)(3)\n}\n",
    );
    assert_eq!(chain.candidates, 1, "{chain:?}");
    assert!(chain.violations.is_empty(), "{chain:?}");
}

#[test]
fn the_outer_form_is_only_one_that_ends_after_the_original() {
    // No input of the compiler has a candidate that leaves its own error on the same range;
    // the test of `outer_form` is on diagnostics made here.
    let d = |start: u32, end: u32, message: &str| {
        Diagnostic::new(onsa_diag::Stage::Syntax, Code::E0020, Span { file: FileId(0), start, end }, message)
    };
    let original = d(10, 15, "m");
    let moved = Span { file: FileId(0), start: 10, end: 16 };
    // The next link of a chain: the same start, a later end.
    assert!(outer_form(&original, &d(10, 20, "m"), moved));
    // A candidate that fixed nothing leaves the same range: a violation.
    assert!(!outer_form(&original, &d(10, 16, "m"), moved));
    // Inside the original (a part of the same form, S-248), another start, another message.
    assert!(!outer_form(&original, &d(10, 12, "m"), moved));
    assert!(!outer_form(&original, &d(11, 20, "m"), moved));
    assert!(!outer_form(&original, &d(10, 20, "other"), moved));
}

/// The diagnostics a failure of the runner names (a `[[test.fix]]` entry
/// that names none, `clean`) are in the printed order
/// (`onsa_diag::printed_order`), not in the order of the stages the check
/// gives them in.
#[test]
fn the_diagnostics_named_are_in_the_printed_order() {
    let mut sources = SourceMap::default();
    let file = sources.add("m.onsa", "fn f() {\n  x\n    y\n}\n");
    let files = Files { list: vec![(file, "m.onsa".into(), "m.onsa".into())], package: false };
    let syntax = Diagnostic::new(onsa_diag::Stage::Syntax, Code::E0020, Span::new(file, 17, 18), "m");
    let types = Diagnostic::new(onsa_diag::Stage::Types, Code::E0401, Span::new(file, 0, 2), "m");
    assert_eq!(describe(&files, &sources, &[syntax, types]), "E0401 at 1:1, E0020 at 3:5");
}
