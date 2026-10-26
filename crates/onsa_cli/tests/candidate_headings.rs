//! A candidate does not make a heading error: apply each candidate of each diagnostic alone, check again, and
//! count the E0303 (spec §15.1, §18.1; S-665, S-698, S-700; W4-03 U4b). The sweep moved here from the script
//! of the break side (`fixnew.py`) that found, after U4b, that the candidate of an E0020 in the body of a
//! function made an E0303 appear in its head (the alias `type Eleven = (I32, ...)` that a `pub fn` names was
//! judged by its own word), which the gate had passed. The loop of `onsa_cases --fix-loop` counts the errors
//! left and not the kinds, so a candidate that takes one error away and brings another does not show there.
//!
//! What the spec fixes, and so what is checked:
//! - §18.1: a candidate applied alone leaves no diagnostic of the same stage or before in what it touches;
//!   a later stage may show one (an error that was hidden by the first, S-698). The E0303 of a head is of
//!   the stage of the types, so after a candidate of a name or syntax error it may appear in the unit that
//!   was edited, and in a unit that named the name that failed. The sweep asks more than that for the files
//!   it is given: that no E0303 is added. It holds for the files below, whose heads are narrow nowhere
//!   (a file where one is hidden is a file of the exact tests at the end);
//! - the files: the single files of `tests/spec` (out of the packages) that have both a `pub` declaration
//!   and a declaration with no word that a head could name (a `type`, `struct`, `enum` or `flow` at the left
//!   edge), as the repository has them. Of the 1022 files, 48, which have 155 candidates. The existing files
//!   change with the work, so the test asks only that the subject is large (below).
//!
//! The exact tests: the two forms where a candidate does bring an E0303, which the spec gives by the order of
//! the stages: the `pub` that is redundant on a member of an `impl` with a narrow name in it (S-698, the
//! candidate shows the E0303 that was behind the E0020), and the alias that failed (the head that names it
//! has no E0303 until the candidate makes it a type, §18.1: a failed name is read as a part that could not be
//! read).

mod test_support;

use std::path::Path;

use test_support::sweep::*;

fn repo_root() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn collect(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir).expect("read a directory").map(|e| e.unwrap().path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            if p.file_name().is_some_and(|n| n == "packages") {
                continue;
            }
            collect(&p, out);
        } else if p.extension().is_some_and(|e| e == "onsa") && !dir.join("onsa.toml").exists() {
            out.push(p);
        }
    }
}

/// A line of the file starts with one of the words (at the left edge, as the files are written).
fn starts_a_line(text: &str, words: &[&str]) -> bool {
    text.lines().any(|l| words.iter().any(|w| l.starts_with(w)))
}

fn heading_count(c: &Checked) -> usize {
    c.of_code("E0303").len()
}

/// §18.1: for the files with a `pub` declaration next to a declaration a head could name, each candidate of
/// each diagnostic, applied alone, ends the command as a check does and adds no E0303.
#[test]
fn a_candidate_applied_alone_adds_no_heading_error_to_the_single_files_of_the_spec() {
    let mut files = Vec::new();
    collect(&repo_root().join("tests/spec"), &mut files);
    let mut problems = Vec::new();
    let (mut used, mut applied) = (0, 0);
    let mut names = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(path).expect("read a case file");
        if !starts_a_line(&text, &["pub fn ", "pub rt fn ", "pub flow ", "pub const ", "pub type ", "pub struct "])
            || !starts_a_line(&text, &["type ", "struct ", "enum ", "flow "])
        {
            continue;
        }
        let file = path.file_name().unwrap().to_string_lossy().into_owned();
        let name = path.strip_prefix(repo_root()).unwrap().to_string_lossy().into_owned();
        let texts = Texts::from([(file, text)]);
        let d = package("candidate_headings", "demo", &texts);
        let base = check_package(d.root());
        if !ended_well(&base) {
            problems.push(format!("{name}: the file ends with code {} {}", base.code, base.stderr));
            continue;
        }
        used += 1;
        let before = heading_count(&base);
        for diag in &base.diags {
            for (k, fix) in diag.fixes.iter().enumerate() {
                let mut t = texts.clone();
                apply_fix_texts(&mut t, fix);
                write_texts(&d, &t);
                let after = check_package(d.root());
                applied += 1;
                if !ended_well(&after) {
                    problems.push(format!(
                        "{name}: {} line {} candidate {k}: ends with code {}",
                        diag.code, diag.line, after.code
                    ));
                } else if heading_count(&after) > before {
                    problems.push(format!(
                        "{name}: {} line {} candidate {k} ({}): E0303 {before} -> {}",
                        diag.code,
                        diag.line,
                        fix["title"],
                        heading_count(&after)
                    ));
                }
            }
        }
        write_texts(&d, &texts);
        names.push(name);
    }
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
    // The sweep must have a subject: many files, many candidates, and the file that the old reading of an
    // alias (by its own word) made a candidate fail on.
    assert!(used >= 30, "only {used} files were used");
    assert!(applied >= 100, "only {applied} candidates were applied");
    assert!(names.iter().any(|n| n.ends_with("fixes/tuple_index_leading_zero.onsa")), "{names:?}");
}

/// The `check` of the one file `m.onsa` with `text`: the codes and lines of the diagnostics, in order.
fn codes_of(c: &Checked) -> Vec<(String, u64)> {
    c.diags.iter().map(|d| (d.code.clone(), d.line)).collect()
}

/// §15.1, §18.1 (S-662, S-698): a member of an `impl` is wider than its type and has a narrow name in its
/// head: the E0020 alone, and its candidate (the `pub` taken off) shows the E0303 on the same line, which has
/// no candidate.
#[test]
fn the_candidate_of_a_wide_member_shows_the_heading_error_that_was_behind_it() {
    let text =
        "struct Pkg { x: I32 }\npriv struct Hid { x: I32 }\nimpl Pkg { pub fn leak() -> Hid { Hid { x: 1 } } }\n";
    let texts = Texts::from([("m.onsa".to_string(), text.to_string())]);
    let d = package("candidate_wide", "demo", &texts);
    let c = check_package(d.root());
    assert_eq!(codes_of(&c), [("E0020".to_string(), 3)], "{:?}", c.diags);
    assert_eq!(c.diags[0].fixes.len(), 1);
    let mut t = texts.clone();
    apply_fix_texts(&mut t, &c.diags[0].fixes[0]);
    write_texts(&d, &t);
    let after = check_package(d.root());
    assert_eq!(codes_of(&after), [("E0303".to_string(), 3)], "{:?}", after.diags);
    assert!(after.diags[0].fixes.is_empty(), "an E0303 of a head has no candidate");
}

/// §15.1, §11.6, §18.1: the alias of a flow name is E0302 with the candidate `voice.State`; the `pub` function
/// whose head names the alias has no diagnostic while the alias has failed, and has the E0303 once it is a type,
/// since the state of a flow with no word reaches the package alone.
#[test]
fn the_candidate_of_a_failed_alias_shows_the_heading_error_of_the_unit_that_names_it() {
    let text = "flow voice(x: F32 at sample) -> F32 at sample { x }\ntype S5 = voice\npub fn f9(a: S5) -> I32 { 0 }\n";
    let texts = Texts::from([("m.onsa".to_string(), text.to_string())]);
    let d = package("candidate_failed_alias", "demo", &texts);
    let c = check_package(d.root());
    assert_eq!(codes_of(&c), [("E0302".to_string(), 2)], "{:?}", c.diags);
    assert!(!c.diags[0].fixes.is_empty(), "a candidate that writes the state type");
    let mut t = texts.clone();
    apply_fix_texts(&mut t, &c.diags[0].fixes[0]);
    assert!(t["m.onsa"].contains("type S5 = voice.State"), "{}", t["m.onsa"]);
    write_texts(&d, &t);
    let after = check_package(d.root());
    assert_eq!(codes_of(&after), [("E0303".to_string(), 3)], "{:?}", after.diags);
}
