use super::markers::lacks_found;
use super::*;
use crate::pending::{self, Pending};
use onsa_diag::Diagnostic;
use std::path::PathBuf;

#[test]
fn a_negative_example_needs_found_but_with_an_empty_range() {
    let d = |start: u32, end: u32| {
        Diagnostic::new(
            onsa_diag::Stage::Syntax,
            onsa_diag::Code::E0002,
            onsa_diag::Span::new(onsa_diag::FileId(0), start, end),
            "m",
        )
    };
    assert!(lacks_found(&d(3, 5)), "a range with text and no `found`");
    assert!(!lacks_found(&d(3, 5).with_found("ab")));
    assert!(!lacks_found(&d(4, 4)), "an empty range has no `found` (§18.1)");
}

/// A made-up repository: `files` under its root, `tests/pending.toml` included.
struct Repo(PathBuf);

impl Repo {
    fn new(tag: &str, files: &[(&str, &str)]) -> Repo {
        let root = crate::c::scratch_dir("onsa_test", &format!("run_{tag}"));
        let _ = std::fs::remove_dir_all(&root);
        for (p, text) in files {
            let p = root.join(p);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, text).unwrap();
        }
        if !root.join(pending::PATH).exists() {
            std::fs::write(root.join(pending::PATH), "").unwrap();
        }
        Repo(root)
    }

    fn run(&self) -> Report {
        self.run_with(Update::Off)
    }

    fn run_with(&self, update: Update) -> Report {
        run_all_with(&self.0, update)
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn entry(target: &str) -> String {
    format!(
        "[[pending]]\nkind = \"test-case\"\ntarget = \"{target}\"\nreasons = [\"R-80\"]\nuntil = \"W9-01\"\nnote = \"n\"\n\n"
    )
}

const MANIFEST: &str = "// onsa.toml\n// [package]\n// name = \"m\"\n// edition = \"2026\"\n//\n// [export]\n// prefix = \"onsa_\"\n// flows = [\"m.f\"]\n//\n// [targets.a]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n// panic = \"trap\"\n// provides = []\n//\n// [targets.b]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n// panic = \"poison\"\n// provides = []\n";

fn case<'a>(r: &'a Report, path: &str) -> &'a CaseReport {
    r.cases.iter().find(|c| c.run.path == path).unwrap_or_else(|| panic!("no case {path}"))
}

#[test]
fn build_stage_markers() {
    // E0809 comes from the build of each target (the check is clean).
    let src = format!(
        "{MANIFEST}\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample {{ //~ E0809\n  x * k\n}}\n"
    );
    let targeted = src.replace("//~ E0809", "//~ E0809 [a] //~ E0809 [b]");
    let only_a = src.replace("//~ E0809", "//~ E0809 [a]");
    let repo = Repo::new(
        "build",
        &[("tests/all/m.onsa", &src), ("tests/each/m.onsa", &targeted), ("tests/only_a/m.onsa", &only_a)],
    );
    let r = repo.run();
    // The E0809 of the build has a candidate (add `@param`), which the runner cannot
    // check again (W3-17): it fails on each build, never silenced.
    let unchecked = |f: &String| f.contains("m.onsa:24:30 E0809 fix1: a candidate of the build stage");
    for p in ["tests/all/m.onsa", "tests/each/m.onsa"] {
        let c = case(&r, p);
        assert!(c.failures.len() == 2 && c.failures.iter().all(unchecked), "{p}: {:?}", c.failures);
        let stages: Vec<(Stage, Option<&str>, bool)> =
            c.run.checked.iter().map(|m| (m.stage, m.target.as_deref(), m.matched)).collect();
        assert_eq!(stages, [(Stage::Build, Some("a"), true), (Stage::Build, Some("b"), true)], "{p}");
    }
    // `b` reports E0809 too, but no marker expects it there.
    let c = case(&r, "tests/only_a/m.onsa");
    let differs: Vec<&String> = c.failures.iter().filter(|f| !unchecked(f)).collect();
    assert_eq!(differs.len(), 1, "{:?}", c.failures);
    assert!(differs[0].contains("the build of `b` differs"), "{:?}", c.failures);
}

#[test]
fn errors_of_the_case() {
    let check_error = format!("{MANIFEST}\npub fn g() -> I32 {{ x }} //~ E0302 [a]\n");
    let unknown_target = format!(
        "{MANIFEST}\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample {{ //~ E0809 [z]\n  x * k\n}}\n"
    );
    let golden_and_build = MANIFEST.to_string()
        + "//\n// [test]\n// golden = [\"c\"]\n\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample { //~ E0809\n  x * k\n}\n";
    let old_mode = "//! mode: parse\nfn f() {}\n";
    let repo = Repo::new(
        "errors",
        &[
            ("tests/check_error/m.onsa", &check_error),
            ("tests/unknown_target/m.onsa", &unknown_target),
            ("tests/golden_and_build/m.onsa", &golden_and_build),
            ("tests/old_mode.onsa", old_mode),
            ("tests/golden/c/stale.c", "x"),
            (pending::PATH, &entry("tests/old_mode.onsa")),
        ],
    );
    let r = repo.run();
    let has = |p: &str, needle: &str| {
        let c = case(&r, p);
        assert!(c.failures.iter().any(|f| f.contains(needle)), "{p}: {:?}", c.failures);
    };
    has("tests/check_error/m.onsa", "the build stage does not run");
    has("tests/unknown_target/m.onsa", "not a target of the case");
    has("tests/golden_and_build/m.onsa", "expects build diagnostics, but the case declares its golden C");
    // an error of the case is never pending
    has("tests/old_mode.onsa", "`//! mode:` is gone");
    assert!(r.failures.iter().any(|f| f.contains("tests/golden/c/stale.c: no case declares")), "{:?}", r.failures);
}

#[test]
fn fmt_and_parser_checks() {
    let repo = Repo::new(
        "fmt",
        &[
            ("tests/ugly.onsa", "pub fn f()->I32{1}\n"),
            ("tests/none.onsa", "// onsa.toml\n// [test]\n// mode = \"none\"\n\nif c { a }\n"),
            // `canonical = false`: fmt changes it, and that is all the case says.
            ("tests/ugly_said.onsa", "// onsa.toml\n// [test]\n// canonical = false\n\npub fn f()->I32{1}\n"),
            ("tests/fine_said.onsa", "// onsa.toml\n// [test]\n// canonical = false\n\npub fn f() -> I32 {\n  1\n}\n"),
            (
                "tests/marked_said.onsa",
                "// onsa.toml\n// [test]\n// canonical = false\n\npub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n",
            ),
            (
                "tests/syntax.onsa",
                // E0003 only the syntax stage reports: its marker must come from the parser.
                "// onsa.toml\n// [test]\n// mode = \"parse\"\n\npub fn f() -> I32 { 1 } //~ E0003\n",
            ),
        ],
    );
    let r = repo.run();
    assert!(case(&r, "tests/ugly.onsa").failures.iter().any(|f| f.contains("fmt changes it")));
    assert!(case(&r, "tests/none.onsa").failures.is_empty());
    assert!(case(&r, "tests/ugly_said.onsa").failures.is_empty(), "{:?}", case(&r, "tests/ugly_said.onsa").failures);
    assert!(
        case(&r, "tests/fine_said.onsa").failures.iter().any(|f| f.contains("leaves every file of the case unchanged")),
        "{:?}",
        case(&r, "tests/fine_said.onsa").failures
    );
    assert!(
        case(&r, "tests/marked_said.onsa").failures.iter().any(|f| f.contains("asks nothing")),
        "{:?}",
        case(&r, "tests/marked_said.onsa").failures
    );
    // In a package, one file fmt changes is enough; the others stay in the normal form.
    let toml = "[package]\nname = \"p\"\nedition = \"2026\"\n";
    let pkg = Repo::new(
        "canonical_pkg",
        &[
            ("tests/p/onsa.toml", toml),
            ("tests/p/a.onsa", "// onsa.toml\n// [test]\n// canonical = false\n\npub fn f()->I32{1}\n"),
            ("tests/p/b.onsa", "pub fn g() -> I32 {\n  2\n}\n"),
        ],
    );
    let pr = pkg.run();
    assert!(case(&pr, "tests/p").failures.is_empty(), "{:?}", case(&pr, "tests/p").failures);
    assert!(
        case(&r, "tests/syntax.onsa").failures.iter().any(|f| f.contains("the parser's diagnostics differ")),
        "{:?}",
        case(&r, "tests/syntax.onsa").failures
    );
}

#[test]
fn fix_files() {
    // `fixes = 1`: the candidate of `let mut` gives the `.fix1` file, compared
    // without the whitespace tokens; a wrong one, a missing count and an orphan fail.
    let src = "// onsa.toml\n// [test]\n// fixes = 1\n\npub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n";
    let good = src.replace("let mut n = 0 ", "var  n = 0 ");
    let bad = src.replace("let mut n = 0 ", "var n = 1 ");
    let two = src.replace("fixes = 1", "fixes = 2");
    let repo = Repo::new(
        "fixes",
        &[
            ("tests/good.onsa", src),
            ("tests/good.onsa.fix1", &good),
            ("tests/bad.onsa", src),
            ("tests/bad.onsa.fix1", &bad),
            ("tests/two.onsa", &two),
            ("tests/two.onsa.fix1", &good),
            ("tests/stray.onsa.fix1", "x"),
            ("tests/good.onsa.fix2", "x"),
        ],
    );
    let r = repo.run();
    assert!(case(&r, "tests/good.onsa").failures.is_empty(), "{:?}", case(&r, "tests/good.onsa").failures);
    let bad = &case(&r, "tests/bad.onsa").failures;
    assert!(
        bad.iter().any(|f| f.contains("differs from the copy bad.onsa.fix1: expected `1` (line 6), got `0`")),
        "{bad:?}"
    );
    let two = &case(&r, "tests/two.onsa").failures;
    assert!(two.iter().any(|f| f.contains("no diagnostic has a candidate 2")), "{two:?}");
    assert!(r.failures.iter().any(|f| f.contains("tests/stray.onsa.fix1: no case declares")), "{:?}", r.failures);
    assert!(r.failures.iter().any(|f| f.contains("tests/good.onsa.fix2: its case declares `fixes = 1`")));
    assert_eq!(r.cases.iter().map(|c| c.run.fix_copies).sum::<usize>(), 3, "good, bad and two: the copies read");
    assert!(!r.failures.iter().any(|f| f.contains("no copy")), "{:?}", r.failures);
}

/// A written `fixes = 0` counts the candidates (X-15): a diagnostic with one
/// fails, one without passes. A case that does not write `fixes` does not
/// count them, and `fixes = 1` compares its copy as before.
#[test]
fn written_fixes_zero_checks_that_no_candidate_is_given() {
    let with = "// onsa.toml\n// [test]\n// fixes = 0\n\npub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n";
    let without = "// onsa.toml\n// [test]\n// fixes = 0\n\npub const _1: I32 = 1 //~ E0320\n";
    let unwritten = with.replace("// fixes = 0\n", "// spec = [\"§18.1\"]\n");
    let one = with.replace("fixes = 0", "fixes = 1");
    let one_copy = one.replace("let mut n = 0 ", "var n = 0 ");
    let repo = Repo::new(
        "fixes_zero",
        &[
            ("tests/with.onsa", with),
            ("tests/without.onsa", without),
            ("tests/unwritten.onsa", &unwritten),
            ("tests/one.onsa", &one),
            ("tests/one.onsa.fix1", &one_copy),
        ],
    );
    let r = repo.run();
    let failed = &case(&r, "tests/with.onsa").failures;
    assert!(
        failed
            .iter()
            .any(|f| f.contains("E0020 at tests/with.onsa:6:3 has 1 candidates, more than `fixes = 0` declares")),
        "{failed:?}"
    );
    for passes in ["tests/without.onsa", "tests/unwritten.onsa", "tests/one.onsa"] {
        assert!(case(&r, passes).failures.is_empty(), "{passes}: {:?}", case(&r, passes).failures);
    }
    assert_eq!(case(&r, "tests/one.onsa").run.fix_copies, 1, "the copy of `fixes = 1` is read");
}

/// The copies (Q-04, X-3) are a failure of their own: an entry of kind
/// `fix-contract` does not silence them, and a case listed as a whole does
/// not judge them (it passes when the copy alone differs). With no copy at
/// all, the run fails.
#[test]
fn copies_are_not_silenced_and_do_not_keep_a_case_pending() {
    let src = "// onsa.toml\n// [test]\n// fixes = 1\n\npub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n";
    let bad = src.replace("let mut n = 0 ", "var n = 1 ");
    let files = [
        ("tests/whole.onsa", src),
        ("tests/whole.onsa.fix1", bad.as_str()),
        ("tests/one.onsa", src),
        ("tests/one.onsa.fix1", bad.as_str()),
        ("tests/missing.onsa", src),
    ];
    let target = {
        let r = Repo::new("copies_probe", &files).run();
        case(&r, "tests/one.onsa").run.fix_targets[0].clone()
    };
    let pending = format!("{}{}", entry("tests/whole.onsa"), fix_entry(&target));
    let mut with = files.to_vec();
    with.push((pending::PATH, &pending));
    let r = Repo::new("copies", &with).run();
    let whole = &case(&r, "tests/whole.onsa").failures;
    assert!(whole.len() == 1 && whole[0].contains("passes but is listed"), "{whole:?}");
    let one = &case(&r, "tests/one.onsa").failures;
    assert!(one.iter().any(|f| f.contains("differs from the copy one.onsa.fix1")), "{one:?}");
    assert!(one.iter().any(|f| f.contains("keeps the contract but is listed")), "{one:?}");
    let missing = &case(&r, "tests/missing.onsa").failures;
    assert!(missing.iter().any(|f| f.contains("its copy missing.onsa.fix1 is missing")), "{missing:?}");
    // The copy of the case listed as a whole is counted, not judged (X-3, M2).
    assert_eq!(r.unjudged_copies, 1);
    assert!(r.summary().contains("not judged (cases listed as a whole): 1"), "{}", r.summary());
    // No copy at all: the run fails.
    let r = Repo::new("no_copies", &[("tests/missing.onsa", src)]).run();
    assert!(r.failures.iter().any(|f| f.contains("no copy of the text after the candidates")), "{:?}", r.failures);
}

/// The guard on rewriting the copies (X-3), through the cases: the copies
/// of `tests/spec/fixes/pkg_rename` that held S-82 (every use renamed)
/// are not rewritten by an output that renames the declaration only; with
/// `worse` they are, and the summary lists them.
#[test]
fn the_guard_refuses_a_rewriting_that_loses_a_rule() {
    let main = "// onsa.toml\n// [test]\n// fixes = 1\n\nuse util.{BadName, ok_name}\n\npub fn run() -> I32 {\n  \
                    BadName() + ok_name()\n}\n";
    let util = "pub fn BadName() -> I32 { //~ E0320\n  1\n}\n\npub fn ok_name() -> I32 {\n  2\n}\n";
    let files = [
        ("tests/p/onsa.toml", "[package]\nname = \"rename\"\nedition = \"2026\"\n"),
        ("tests/p/main.onsa", main),
        ("tests/p/util.onsa", util),
        ("tests/p/util.onsa.fix1", &util.replace("BadName", "bad_name")),
        ("tests/p/main.onsa.fix1", &main.replace("BadName", "bad_name")),
    ];
    let repo = Repo::new("guard", &files);
    let copy = repo.0.join("tests/p/main.onsa.fix1");
    let r = repo.run_with(Update::Rewrite);
    let p = case(&r, "tests/p");
    assert_eq!(p.run.copies_guarded, 1);
    assert!(p.run.copies_rewritten.is_empty(), "{:?}", p.run.copies_rewritten);
    let refused = |f: &String| {
        f.contains("UPDATE_GOLDEN=1 does not rewrite the copies of the candidates 1 (main.onsa.fix1)")
            && f.contains("reports E0302 at main.onsa:")
    };
    assert!(p.failures.iter().any(refused), "{:?}", p.failures);
    assert_eq!(std::fs::read_to_string(&copy).unwrap(), main.replace("BadName", "bad_name"));
    let r = repo.run_with(Update::Worse);
    let p = case(&r, "tests/p");
    assert!(!p.failures.iter().any(refused), "{:?}", p.failures);
    assert_eq!(p.run.copies_rewritten, ["tests/p/main.onsa.fix1"]);
    assert!(
        matches!(&p.run.copies_forced[..], [f] if f.starts_with("tests/p/main.onsa.fix1 (E0302 at main.onsa:")),
        "{:?}",
        p.run.copies_forced
    );
    assert!(r.summary().contains("copies rewritten over the guard by UPDATE_GOLDEN=worse (1): tests/p/main.onsa.fix1"));
    assert!(!copy.exists());
}

/// The guard lets through a copy that held an error the output does not,
/// and does not look at a copy created (the output's hidden error aside).
#[test]
fn the_guard_lets_a_better_output_through_and_does_not_guard_a_new_copy() {
    let src = "// onsa.toml\n// [test]\n// fixes = 1\n\npub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n";
    let hidden = src.replace("  n\n}", "  q\n}");
    let repo = Repo::new(
        "guard_better",
        &[
            ("tests/a.onsa", src),
            ("tests/a.onsa.fix1", &src.replace("let mut n = 0 ", "var n = 0 ").replace("  n\n}", "  q\n}")),
            ("tests/b.onsa", &hidden),
        ],
    );
    let r = repo.run_with(Update::Rewrite);
    let (a, b) = (case(&r, "tests/a.onsa"), case(&r, "tests/b.onsa"));
    assert!(a.failures.is_empty() && a.run.copies_guarded == 1, "{:?}", a.failures);
    assert_eq!(a.run.copies_rewritten, ["tests/a.onsa.fix1"]);
    assert_eq!(
        std::fs::read_to_string(repo.0.join("tests/a.onsa.fix1")).unwrap(),
        src.replace("let mut n = 0 ", "var n = 0 ")
    );
    // Created: the check after it reports the E0302 of `q`, which no copy left; no guard.
    assert!(b.failures.is_empty() && b.run.copies_guarded == 0, "{:?}", b.failures);
    assert_eq!(b.run.copies_rewritten, ["tests/b.onsa.fix1"]);
    assert!(r.cases.iter().all(|c| c.run.copies_forced.is_empty()));
}

fn fix_entry(target: &str) -> String {
    format!(
        "[[pending]]\nkind = \"fix-contract\"\ntarget = \"{target}\"\nreasons = [\"S-236\"]\nuntil = \"W9-01\"\nnote = \"n\"\n\n"
    )
}

/// W3-17: every candidate is applied alone and the case checked again
/// (§18.1, S-236); `[[test.fix]]` and the entries of kind `fix-contract`.
#[test]
fn fix_contract_of_the_units_clean_before() {
    // X-3 (α): renaming the declaration alone leaves an E0302 in `user`, which it does not touch
    // and which held no diagnostic before it; `leaves` writes it.
    let rename = |leaves: &str| {
        let entry = if leaves.is_empty() {
            String::new()
        } else {
            format!("// [[test.fix]]\n// at = \"9:8\"\n// code = \"E0320\"\n// candidate = 1\n// leaves = [{leaves}]\n")
        };
        format!(
            "// onsa.toml\n// [test]\n{entry}\npub fn BadFn() -> I32 {{ //~ E0320\n  1\n}}\n\npub fn user() -> I32 {{\n  \
                 BadFn()\n}}\n"
        )
    };
    let repo = Repo::new(
        "fix_contract_clean",
        &[
            ("tests/none.onsa", &rename("")),
            ("tests/right.onsa", &rename("\"14:3 E0302\"")),
            ("tests/wrong.onsa", &rename("\"14:4 E0302\"")),
        ],
    );
    let r = repo.run();
    let none = &case(&r, "tests/none.onsa").failures;
    let message = "the units its edits touch hold none of its stage or an earlier one, and the units that held no \
                       diagnostic before it hold";
    assert!(none.iter().any(|f| f.contains(&format!("{message} 9:3 E0302 besides"))), "{none:?}");
    assert!(case(&r, "tests/right.onsa").failures.is_empty(), "{:?}", case(&r, "tests/right.onsa").failures);
    let wrong = &case(&r, "tests/wrong.onsa").failures;
    assert!(wrong.iter().any(|f| f.contains("14:3 E0302 besides (of any stage); expected 14:4 E0302")), "{wrong:?}");
    let vacuous = "looked at no unit that held no diagnostic before its candidate";
    assert!(case(&r, "tests/right.onsa").run.clean_units > 0);
    assert!(!r.failures.iter().any(|f| f.contains(vacuous)), "{:?}", r.failures);
    // Nothing passes vacuously: a case of one unit has none.
    let one = Repo::new(
        "fix_contract_clean_none",
        &[("tests/one.onsa", "pub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n")],
    );
    let r = one.run();
    assert_eq!(case(&r, "tests/one.onsa").run.clean_units, 0);
    assert!(r.failures.iter().any(|f| f.contains(vacuous)), "{:?}", r.failures);
}

#[test]
fn fix_contract() {
    // The candidate of the E0411 gives `x.narrow_i32()`, an `Option[I32]`: an E0401 is left
    // (until W5-02, a candidate that breaks the contract).
    let breaks = "pub fn f(x: I64) -> I32 {\n  x as I32 //~ E0411\n}\n";
    let keeps = "pub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n";
    // Two errors in one unit: the candidate of `i32` leaves the E0020 of `f32`.
    let two = |leaves: &str| {
        format!(
            "// onsa.toml\n// [[test.fix]]\n// at = \"8:13\"\n// code = \"E0020\"\n// candidate = 1\n// leaves = [{leaves}]\n\n\
                 pub fn g(x: i32) -> f32 {{ //~ E0020\n  1.0\n}}\n"
        )
    };
    let promise = |what: &str, at: &str, body: &str| {
        format!(
            "// onsa.toml\n// [[test.fix]]\n// at = \"{at}\"\n// code = \"E0020\"\n// candidate = 1\n// {what} = true\n\n{body}"
        )
    };
    let two_units = "pub fn f() -> I32 {\n  let mut n = 0 //~ E0020\n  n\n}\n\npub fn g() -> I32 {\n  let mut m = 0 //~ E0020\n  m\n}\n";
    let list = [
        fix_entry("tests/listed.onsa:2:3 E0411 fix1"),
        fix_entry("tests/keeps_listed.onsa:2:3 E0020 fix1"),
        fix_entry("tests/nothing.onsa:2:3 E0411 fix1"),
        fix_entry("tests/breaks.onsa:2:3 E0411 fix2"),
        entry("tests/whole.onsa"),
    ]
    .concat();
    let repo = Repo::new(
        "fix_contract",
        &[
            ("tests/breaks.onsa", breaks),
            ("tests/listed.onsa", breaks),
            ("tests/whole.onsa", &breaks.replace("//~ E0411", "")),
            ("tests/keeps.onsa", keeps),
            ("tests/keeps_listed.onsa", keeps),
            ("tests/leaves_right.onsa", &two("\"8:21 E0020\"")),
            ("tests/leaves_wrong.onsa", &two("\"8:22 E0020\"")),
            // The candidate of `let mut` changes the code: `same_code` does not hold.
            ("tests/same_code.onsa", &promise("same_code", "9:3", keeps)),
            ("tests/clean.onsa", &promise("clean", "9:3", two_units)),
            ("tests/clean_ok.onsa", &promise("clean", "9:3", keeps)),
            ("tests/no_diagnostic.onsa", &promise("clean", "9:3", "pub fn f() -> I32 {\n  1\n}\n")),
            (pending::PATH, &list),
        ],
    );
    let r = repo.run();
    let failures = |p: &str| case(&r, p).failures.clone();
    let has = |p: &str, needle: &str| {
        let f = failures(p);
        assert!(f.iter().any(|x| x.contains(needle)), "{p}: {f:?}");
    };
    has("tests/breaks.onsa", "fix candidate tests/breaks.onsa:2:3 E0411 fix1");
    has("tests/breaks.onsa", "hold 2:3 E0401 of its stage or an earlier one; expected none");
    // An entry silences its candidate only.
    let listed = case(&r, "tests/listed.onsa");
    assert!(listed.failures.is_empty(), "{:?}", listed.failures);
    assert_eq!(listed.pending_fixes, ["tests/listed.onsa:2:3 E0411 fix1"]);
    // A whole-case entry does not silence a candidate.
    has("tests/whole.onsa", "fix candidate tests/whole.onsa:2:3 E0411 fix1");
    assert!(case(&r, "tests/keeps.onsa").failures.is_empty(), "{:?}", failures("tests/keeps.onsa"));
    has("tests/keeps_listed.onsa", "keeps the contract but is listed");
    for t in ["tests/nothing.onsa:2:3 E0411 fix1", "tests/breaks.onsa:2:3 E0411 fix2"] {
        assert!(
            r.failures.iter().any(|f| f.contains(t) && f.contains("names no fix candidate")),
            "{t}: {:?}",
            r.failures
        );
    }
    assert!(failures("tests/leaves_right.onsa").is_empty(), "{:?}", failures("tests/leaves_right.onsa"));
    has("tests/leaves_wrong.onsa", "hold 8:21 E0020 of its stage or an earlier one; expected 8:22 E0020 (`leaves`)");
    has("tests/same_code.onsa", "`same_code`: in tests/same_code.onsa, token 9: `let` before, `var` after");
    has("tests/clean.onsa", "`clean`: the check after it reports E0020 at 14:3");
    assert!(failures("tests/clean_ok.onsa").is_empty(), "{:?}", failures("tests/clean_ok.onsa"));
    has("tests/no_diagnostic.onsa", "error in the case: line 2: [[test.fix]]: no diagnostic E0020 at 9:3");
    let checked: usize = r.cases.iter().map(|c| c.run.fix_targets.len()).sum();
    assert_eq!(checked, 11, "{:?}", r.cases.iter().map(|c| &c.run.fix_targets).collect::<Vec<_>>());
    assert!(!r.failures.iter().any(|f| f.contains("no fix candidate was checked")), "{:?}", r.failures);
    // A package names the file of a place; its candidates are named from the root.
    let toml = "[package]\nname = \"p\"\nedition = \"2026\"\n";
    let in_pkg = |at: &str, leaf: &str| {
        format!(
            "// onsa.toml\n// [[test.fix]]\n// at = \"{at}\"\n// code = \"E0020\"\n// candidate = 1\n// leaves = [\"{leaf}\"]\n\n\
                 pub fn g(x: i32) -> f32 {{ //~ E0020\n  1.0\n}}\n"
        )
    };
    let pkg = Repo::new(
        "fix_contract_pkg",
        &[
            ("tests/right/onsa.toml", toml),
            ("tests/right/a.onsa", &in_pkg("a.onsa:8:13", "a.onsa:8:21 E0020")),
            ("tests/bare/onsa.toml", toml),
            ("tests/bare/a.onsa", &in_pkg("8:13", "8:21 E0020")),
        ],
    );
    let r = pkg.run();
    let right = case(&r, "tests/right");
    assert!(right.failures.is_empty(), "{:?}", right.failures);
    assert_eq!(right.run.fix_targets, ["tests/right/a.onsa:8:13 E0020 fix1"]);
    let bare = &case(&r, "tests/bare").failures;
    assert!(bare.iter().any(|f| f.contains("a package names the file")), "{bare:?}");
    // A candidate in a `mode = "parse"` case cannot be checked: it fails.
    let parse = Repo::new(
        "fix_contract_parse",
        &[(
            "tests/p.onsa",
            "// onsa.toml\n// [test]\n// mode = \"parse\"\n\npub fn g(x: i32) -> I32 { //~ E0020\n  1\n}\n",
        )],
    );
    let r = parse.run();
    let p = &case(&r, "tests/p.onsa").failures;
    assert!(p.iter().any(|f| f.contains("tests/p.onsa:5:13 E0020 fix1") && f.contains("mode = \"parse\"")), "{p:?}");
    // Nothing passes without a candidate checked.
    let none = Repo::new("fix_contract_none", &[("tests/plain.onsa", "pub fn f() -> I32 {\n  1\n}\n")]);
    let r = none.run();
    assert!(r.failures.iter().any(|f| f.contains("no fix candidate was checked")), "{:?}", r.failures);
}

#[test]
fn conformance_scope() {
    let head = |flows: &str| {
        format!(
            "// onsa.toml\n// [package]\n// name = \"m\"\n// edition = \"2026\"\n//\n// [export]\n// prefix = \"onsa_\"\n\
                 // flows = [{flows}]\n//\n// [targets.t]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n\
                 // panic = \"trap\"\n// provides = []\n//\n// [test]\n// conformance = true\n\n"
        )
    };
    let two = "pub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n\npub flow g(x: F32 at sample) -> F32 at sample {\n  x * 2.0\n}\n";
    let init_only = "pub flow f(x: F32 at sample, n: F32 at init) -> F32 at sample {\n  x * n\n}\n";
    let repo = Repo::new(
        "conformance",
        &[
            ("tests/partial/m.onsa", &(head("\"m.f\"") + two)),
            ("tests/empty/m.onsa", &(head("") + two)),
            ("tests/init/m.onsa", &(head("\"m.f\"") + init_only)),
            ("tests/full/m.onsa", &(head("\"m.f\", \"m.g\"") + two)),
        ],
    );
    let r = repo.run();
    let has = |p: &str, needle: &str| {
        let c = case(&r, p);
        assert!(c.failures.iter().any(|f| f.contains(needle)), "{p}: {:?}", c.failures);
    };
    has("tests/partial/m.onsa", "`m.g` is not in `[export] flows`");
    has("tests/empty/m.onsa", "needs `[export] flows`");
    // The C checks run the builds (`crate::ccheck`); the runner keeps them.
    for p in ["tests/init/m.onsa", "tests/full/m.onsa"] {
        let c = case(&r, p);
        assert!(c.failures.is_empty(), "{p}: {:?}", c.failures);
        let builds: Vec<(&str, bool)> = c.run.builds.iter().map(|b| (b.target.as_str(), b.conformance)).collect();
        assert_eq!(builds, [("t", true)], "{p}");
    }
}

#[test]
fn small_holes() {
    let bad_target = MANIFEST.replace("panic = \"poison\"", "panic = \"boom\"") + "\npub fn f() -> I32 {\n  1\n}\n";
    let flow = |name: &str| {
        MANIFEST.replace("name = \"m\"", &format!("name = \"{name}\"")).replace("m.f", &format!("{name}.f"))
            + "\npub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n"
    };
    let repo = Repo::new(
        "holes",
        &[
            ("tests/testfail.onsa", "test \"x\" { //~ TESTFAIL \"x\"\n  assert 1 == 2\n}\n"),
            ("tests/none.onsa", "// onsa.toml\n// [test]\n// mode = \"none\"\n\nx //~ E9999\n"),
            ("tests/no_tests.onsa", "// onsa.toml\n// [test]\n// mode = \"test\"\n\npub fn f() -> I32 {\n  1\n}\n"),
            ("tests/bad_target/m.onsa", &bad_target),
            ("tests/a_b.onsa", &flow("a_b")),
            ("tests/a/b.onsa", &flow("b")),
            ("tests/onsa.toml", "[package]\nname = \"all\"\nedition = \"2026\"\n"),
            ("tests/locked/x.onsa", "pub fn f() -> I32 {\n  1\n}\n"),
            (pending::PATH, &entry("tests/bad_target/m.onsa")),
        ],
    );
    let locked = repo.0.join("tests/locked");
    let mut perm = std::fs::metadata(&locked).unwrap().permissions();
    std::os::unix::fs::PermissionsExt::set_mode(&mut perm, 0o000);
    std::fs::set_permissions(&locked, perm.clone()).unwrap();
    let r = repo.run();
    std::os::unix::fs::PermissionsExt::set_mode(&mut perm, 0o755);
    std::fs::set_permissions(&locked, perm).unwrap();
    let has = |p: &str, needle: &str| {
        let c = case(&r, p);
        assert!(c.failures.iter().any(|f| f.contains(needle)), "{p}: {:?}", c.failures);
    };
    has("tests/testfail.onsa", "`//~ TESTFAIL` needs `mode = \"test\"`");
    has("tests/none.onsa", "unknown code `E9999`");
    has("tests/no_tests.onsa", "has no `test` block");
    // the case's own settings are wrong: never pending
    has("tests/bad_target/m.onsa", "unknown panic setting `boom`");
    assert!(case(&r, "tests/bad_target/m.onsa").pending.is_none());
    // the two flatten to the same name; each has its own scratch directory
    for p in ["tests/a_b.onsa", "tests/a/b.onsa"] {
        assert!(case(&r, p).failures.is_empty(), "{p}: {:?}", case(&r, p).failures);
    }
    assert!(r.failures.iter().any(|f| f.contains("the root of the cases is not a package")), "{:?}", r.failures);
    assert!(r.failures.iter().any(|f| f.contains("tests/locked: cannot read the directory")), "{:?}", r.failures);
}

#[test]
fn pending_list() {
    let failing = "pub fn f() -> I32 { 1 } //~ E0302\n";
    let passing = "pub fn f() -> I32 { 1 }\n";
    let tests = "// onsa.toml\n// [test]\n// mode = \"test\"\n\ntest \"bad\" {\n  assert 1 == 2\n}\n\ntest \"good\" {\n  assert 1 == 1\n}\n";
    let list = [
        entry("tests/failing.onsa"),
        entry("tests/passing.onsa"),
        entry("tests/gone.onsa"),
        entry("tests/tests.onsa::bad"),
        entry("tests/tests.onsa::good"),
        entry("tests/tests.onsa::missing"),
    ]
    .concat();
    let repo = Repo::new(
        "pending",
        &[
            ("tests/failing.onsa", failing),
            ("tests/passing.onsa", passing),
            ("tests/tests.onsa", tests),
            (pending::PATH, &list),
        ],
    );
    let r = repo.run();
    let c = case(&r, "tests/failing.onsa");
    assert!(c.failures.is_empty() && c.pending.is_some(), "{:?}", c.failures);
    let c = case(&r, "tests/passing.onsa");
    assert!(c.failures.iter().any(|f| f.contains("passes but is listed")), "{:?}", c.failures);
    assert!(r.failures.iter().any(|f| f.contains("`tests/gone.onsa` names no case")), "{:?}", r.failures);
    let c = case(&r, "tests/tests.onsa");
    assert_eq!(c.pending_tests, ["bad"]);
    assert_eq!(c.failures.len(), 2, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"good\" passes but is listed"), "{:?}", c.failures);
    assert!(c.failures[1].contains("does not have"), "{:?}", c.failures);
}

/// R-184: a test is identified by its module path and name (§11.8):
/// `TESTFAIL` names the test of the module of its file, an entry names a
/// test by its full name text, and a bare name of tests of several
/// modules names none of them.
#[test]
fn tests_are_identified_by_module_and_name() {
    let manifest = "[package]\nname = \"p\"\nedition = \"2026\"\n";
    let a =
        "// onsa.toml\n// [test]\n// mode = \"test\"\n\ntest \"same\" { //~ TESTFAIL \"same\"\n  assert 1 == 2\n}\n";
    let b = "test \"same\" {\n  assert 1 == 2\n}\n";
    let run = |tag: &str, target: &str| {
        let list = entry(target);
        let files =
            [("tests/p/onsa.toml", manifest), ("tests/p/a.onsa", a), ("tests/p/b.onsa", b), (pending::PATH, &list)];
        Repo::new(tag, &files).run()
    };
    // The entry is TOML: the quotes of the full name text are escaped.
    let r = run("by_module", r#"tests/p::b \"same\""#);
    let c = case(&r, "tests/p");
    assert!(c.failures.is_empty(), "{:?}", c.failures);
    assert_eq!(c.pending_tests, [r#"b "same""#]);

    let r = run("by_module_bare", "tests/p::same");
    let c = case(&r, "tests/p");
    assert!(c.failures.iter().any(|f| f.contains("several modules")), "{:?}", c.failures);
    assert!(c.failures.iter().any(|f| f.contains(r#"test b "same" failed"#)), "{:?}", c.failures);
}

/// X9-36: `//~ PANIC` names the line (and column) where the body of the
/// test sees the panic, and a failed `assert` is not a panic.
#[test]
fn panic_marks() {
    let head = "// onsa.toml\n// [test]\n// mode = \"test\"\n\n";
    let marks = format!(
        r#"{head}use std.dsp.test.{{assert_near}}

fn pick(xs: [I32; 2], i: U32) -> I32 {{
  xs[i]
}}

fn check(x: I32) {{
  assert x == 0
}}

test "near" {{
  assert_near(1.0, 2.0, 0.5) //~ PANIC "near"
}}

test "near tol" {{
  assert_near(1.0, 1.0, -1.0) //~ PANIC "near tol"
}}

test "callee" {{
  check(1) //~ PANIC "callee"
}}

test "callee line" {{
  let x = 1 //~ PANIC "callee line"
  check(x)
}}

test "at" {{
  let xs = [1, 2]
  let i = 2
  let y = xs[0] + xs[i] //~ PANIC "at" @19
  assert y == 0
}}

test "in an assert" {{
  let xs = [1, 2]
  let i = 2
  assert xs[i] == 0 //~ PANIC "in an assert"
}}

test "call" {{
  let xs = [1, 2]
  let y = pick(xs, 5) //~ PANIC "call" @11
  assert y == 0
}}

test "other line" {{
  let xs = [1, 2]
  let i = 4 //~ PANIC "other line"
  assert xs[i] == 0
}}

test "other column" {{
  let xs = [1, 2]
  let i = 2
  let y = xs[0] + xs[i] //~ PANIC "other column" @11
  assert y == 0
}}

test "by assert" {{
  assert 1 == 2 //~ PANIC "by assert"
}}

test "passes" {{ //~ PANIC "passes"
  assert 1 == 1
}}
"#
    );
    let fails = "test \"x\" { //~ TESTFAIL \"x\" //~ PANIC \"x\"\n  assert [1][1] == 0\n}\n";
    let listed = "test \"x\" {\n  assert [1][1] == 0 //~ PANIC \"x\"\n}\n";
    let names = "test \"x\" {\n  assert [1][1] == 0 //~ PANIC \"x\" //~ PANIC \"x\"\n} //~ PANIC \"y\"\n";
    let same = "test \"same\" {\n  assert [1][1] == 0 //~ PANIC \"same\"\n}\n";
    let files = [
        ("tests/marks.onsa", marks.clone()),
        ("tests/both.onsa", format!("{head}{fails}")),
        ("tests/listed.onsa", format!("{head}{listed}")),
        ("tests/names.onsa", format!("{head}{names}")),
        ("tests/check.onsa", listed.to_string()),
        ("tests/p/onsa.toml", "[package]\nname = \"p\"\nedition = \"2026\"\n".into()),
        ("tests/p/a.onsa", format!("{head}{same}")),
        ("tests/p/b.onsa", "test \"same\" {\n  assert [1][2] == 0\n}\n".into()),
        (pending::PATH, entry("tests/listed.onsa::x")),
    ];
    let files: Vec<(&str, &str)> = files.iter().map(|(p, t)| (*p, t.as_str())).collect();
    let r = Repo::new("panic_marks", &files).run();
    let line = |needle: &str| marks.lines().position(|l| l.contains(needle)).unwrap() + 1;
    let expect = [
        format!(
            r#""other line" is marked PANIC at line {}, but it panicked at tests/marks.onsa:{}:10: index 4"#,
            line("PANIC \"other line\""),
            line("PANIC \"other line\"") + 1
        ),
        format!(
            r#""other column" is marked PANIC at line {0} @11, but it panicked at tests/marks.onsa:{0}:19: index 2"#,
            line("PANIC \"other column\"")
        ),
        format!(
            r#""by assert" is marked PANIC at line {}, but it failed by an assert: assert 1 == 2"#,
            line("PANIC \"by assert\"")
        ),
        r#"test marks "passes" passed but is marked PANIC"#.to_string(),
        // A failed assertion of the body is not a panic, `assert_near` too
        // (its message does not begin with `assert `).
        format!(
            r#""near" is marked PANIC at line {}, but it failed by an assert: assert_near failed: 1.0 and 2.0"#,
            line("PANIC \"near\"")
        ),
        format!(
            r#""near tol" is marked PANIC at line {}, but it failed by an assert: assert_near: the tolerance"#,
            line("PANIC \"near tol\"")
        ),
        // One in a called function is the call's: "callee" matches.
        format!(
            r#""callee line" is marked PANIC at line {}, but it panicked at tests/marks.onsa:{}:3: assert x == 0"#,
            line("PANIC \"callee line\""),
            line("PANIC \"callee line\"") + 1
        ),
    ];
    let has = |p: &str, needles: &[&str]| {
        let c = case(&r, p);
        assert_eq!(c.failures.len(), needles.len(), "{p}: {:?}", c.failures);
        for n in needles {
            assert!(c.failures.iter().any(|f| f.contains(n)), "{p}: {n:?} in {:?}", c.failures);
        }
    };
    has("tests/marks.onsa", &expect.iter().map(String::as_str).collect::<Vec<_>>());
    has("tests/both.onsa", &["marked both TESTFAIL and PANIC; keep one"]);
    has("tests/listed.onsa", &["\"x\" is both marked PANIC and listed in tests/pending.toml; keep one"]);
    has(
        "tests/names.onsa",
        &["PANIC names the test \"x\" of module `names` twice", "PANIC names an unknown test \"y\""],
    );
    has("tests/check.onsa", &["`//~ PANIC` needs `mode = \"test\"`"]);
    // The mark names the test of the module of its file (R-184).
    has("tests/p", &[r#"test b "same" failed"#]);
}

/// W1-04: an internal error is not silenced by the list, unless the entry
/// expects it (`expect = "internal"`).
#[test]
fn internal_errors_and_the_list() {
    let run = |path: &str, problems: Vec<Problem>| CaseRun {
        path: path.into(),
        mode: Mode::Check,
        ran: true,
        problems,
        ..Default::default()
    };
    let internal = || Problem::Internal("internal error: boom".into());
    let failed = || Problem::Failed("the check diagnostics differ".into());
    let expect = |e: String| e.replace("note = \"n\"\n", "note = \"n\"\nexpect = \"internal\"\n");
    let list = Pending::parse(
        &[
            entry("tests/plain.onsa"),
            entry("tests/plain_failed.onsa"),
            expect(entry("tests/expected.onsa")),
            expect(entry("tests/expected_other.onsa")),
            expect(entry("tests/expected_passes.onsa")),
        ]
        .concat(),
    )
    .unwrap();
    let runs = vec![
        run("tests/plain.onsa", vec![failed(), internal()]),
        run("tests/plain_failed.onsa", vec![failed()]),
        run("tests/expected.onsa", vec![failed(), internal()]),
        run("tests/expected_other.onsa", vec![failed()]),
        run("tests/expected_passes.onsa", vec![]),
        run("tests/unlisted.onsa", vec![internal()]),
    ];
    let r = reconcile(runs, &list);
    let c = |p: &str| r.cases.iter().find(|c| c.run.path == p).unwrap();
    // without `expect`: the internal error is never pending
    assert_eq!(c("tests/plain.onsa").failures, ["internal error: boom"]);
    assert!(c("tests/plain.onsa").pending.is_none());
    assert!(c("tests/plain_failed.onsa").failures.is_empty() && c("tests/plain_failed.onsa").pending.is_some());
    // with it: pending only while the case ends in an internal error
    assert!(c("tests/expected.onsa").failures.is_empty(), "{:?}", c("tests/expected.onsa").failures);
    assert!(c("tests/expected.onsa").pending.is_some());
    let other = &c("tests/expected_other.onsa").failures;
    assert!(other.len() == 1 && other[0].contains("fails without an internal error"), "{other:?}");
    let passes = &c("tests/expected_passes.onsa").failures;
    assert!(passes.len() == 1 && passes[0].contains("passes but is listed"), "{passes:?}");
    assert_eq!(c("tests/unlisted.onsa").failures, ["internal error: boom"]);
}

#[test]
fn runs_as_json() {
    let src = format!(
        "{MANIFEST}\npub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample {{ //~ E0809\n  x * k\n}}\n"
    );
    let repo = Repo::new(
        "json",
        &[
            ("tests/build/m.onsa", &src),
            ("tests/check.onsa", "pub fn f() -> I32 { y } //~ E0302\n"),
            ("tests/wrong.onsa", "pub fn f() -> I32 { 1 } //~ E0302\n"),
            ("tests/none.onsa", "// onsa.toml\n// [test]\n// mode = \"none\"\n\nx //~ E0302\n"),
        ],
    );
    let (cases, errors) = case::collect(&repo.0);
    let runs = run_each(&repo.0, &cases, |_| Update::Off, HostSteps::Skip);
    let json = runs_json(&runs, &errors);
    let case = |p: &str| json["cases"].as_array().unwrap().iter().find(|c| c["path"] == p).unwrap().clone();
    // a marker without targets is compared once per target
    let b = case("tests/build/m.onsa");
    assert_eq!(b["mode"], "check");
    assert_eq!(b["ran"], true);
    let m = b["markers"].as_array().unwrap();
    assert_eq!(m.len(), 2, "{b}");
    assert_eq!(m[0]["code"], "E0809");
    assert_eq!(m[0]["file"], "m.onsa");
    assert_eq!(m[0]["stage"], "build");
    assert_eq!(m[0]["target"], "a");
    assert_eq!(m[1]["target"], "b");
    assert_eq!(m[0]["matched"], true);
    let c = case("tests/check.onsa");
    assert_eq!(c["markers"][0]["file"], "tests/check.onsa");
    assert_eq!(c["markers"][0]["stage"], "check");
    assert_eq!(c["markers"][0]["target"], serde_json::Value::Null);
    assert_eq!(c["markers"][0]["matched"], true);
    assert_eq!(c["problems"].as_array().unwrap().len(), 0);
    // a marker that no diagnostic matched is listed as not matched, with the problem
    let w = case("tests/wrong.onsa");
    assert_eq!(w["markers"][0]["matched"], false);
    assert_eq!(w["problems"].as_array().unwrap().len(), 1);
    assert_eq!(w["problems"][0]["kind"], "failed");
    assert!(w["problems"][0]["text"].as_str().unwrap().contains("differ from the markers"), "{w}");
    // `mode = "none"` compares nothing
    let n = case("tests/none.onsa");
    assert_eq!(n["mode"], "none");
    assert_eq!(n["ran"], false);
    assert_eq!(n["markers"].as_array().unwrap().len(), 0);
    assert_eq!(json["errors"].as_array().unwrap().len(), 0);
}

#[test]
fn package_fragments() {
    let toml = "[package]\nname = \"p\"\nedition = \"2026\"\n";
    let frag = "// onsa.toml\n// [test]\n// spec = [\"§15.1\"]\n\npub fn f() -> I32 { 1 }\n";
    let repo = Repo::new(
        "packages",
        &[
            ("tests/one/onsa.toml", toml),
            ("tests/one/a.onsa", frag),
            ("tests/one/b.onsa", "pub fn g() -> I32 { 2 }\n"),
            ("tests/two/onsa.toml", toml),
            ("tests/two/a.onsa", frag),
            ("tests/two/b.onsa", frag),
            ("tests/three/onsa.toml", toml),
            ("tests/three/m.onsa", &format!("{MANIFEST}\npub fn f() -> I32 {{ 1 }}\n")),
        ],
    );
    let r = repo.run();
    let c = case(&r, "tests/one");
    assert!(c.failures.is_empty(), "{:?}", c.failures);
    assert!(case(&r, "tests/two").failures.iter().any(|f| f.contains("a second fragment")));
    assert!(case(&r, "tests/three").failures.iter().any(|f| f.contains("holds only `[test]`")));
}
