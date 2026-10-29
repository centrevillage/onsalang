//! The shapes of a `use` line, all of them, against `onsa check`: the command ends as a check does for
//! every shape, and a candidate does what §18.1 promises of it (spec §15.1, §18.1, §2.2; S-37, S-594,
//! S-663, S-673, S-679; W4-03 U3a2/t2). The sweep moved here from the scripts of the break side
//! (`useshapes.py`, `odd.py`) that found an internal error in `use fx.{}` which the gate had passed.
//! The check runs in this process as the command runs it, with no file written (`check_input`, X-16):
//! the reading of a package from its directory, the exit code and the printing are the business of the
//! tests that run the command.
//!
//! What is fixed, and so what is checked, for every shape:
//! - the command ends with exit code 0 or 1 and no `internal error`, whatever the line is (a `use` that
//!   is empty, has a list of a name twice, names the package, a module, the module itself, a dependency
//!   that is not declared, ...), and ends in the time it is given;
//! - a candidate of a diagnostic, applied alone and checked again, takes away the diagnostic it was
//!   given for (the same code, file and message appear fewer times), and the stages after the names do
//!   not receive a diagnostic of the stage of the names that the text did not have before: no E0304,
//!   E0310 or E0303 that was not in the text before (§18.1: "a candidate leaves no diagnostic of the
//!   same stage or before in what it touches"). The number of the diagnostics of the names stage is
//!   not compared: one diagnostic is reported for a unit, so the next one a candidate lets through was
//!   hidden before and is no new fault (the count `na >= nb` of the script counted it as one).
//!
//! The shapes (a row of the tables below is a `use` line, put in each of three files, with a body that
//! names the head by its path):
//! - `shapes_*`: the head is the own package name, a module, a module in a directory, the module of the
//!   file itself, `std`, a name that is nothing, a dependency that is not declared, or a path of these;
//!   the tail is nothing, an empty list, a list of one or two names (the name twice, the name with a
//!   trailing `,`, with spaces), an item, a child module, the own package name, the module itself;
//!   with and without `pub`;
//! - `odd_*`: lines that break the syntax of a `use` in every way the script knew (a missing name, `..`,
//!   `{a b}`, a nested list, `self`, `*`, an alias, a keyword, a number, a string, a line break inside
//!   the list, two lists), before and after the body.
//!
//! The expected values are the two properties above only: the spec does not fix the diagnostic of every
//! shape, and the codes of the shapes (E0302, E0002, E0200, E0304, ...) are the business of the tests
//! of each of them (`use_paths.rs`, `use_cycles.rs`, `tests/spec/packages`). The sweep is the net under
//! them: a shape nobody wrote a test for still must not end the command or leave a candidate that adds
//! a fault.
//!
//! Size: 14 heads x 18 tails x 3 files for `use` and for `pub use` is 1512 packages, each run once and
//! once per candidate of its diagnostics; the six tests below run the files and the `pub` apart so the
//! tests of `cargo test` run side by side (a debug build, about a second each); `odd_*` is 55 lines x 2
//! files x 2 places = 220 packages.

mod test_support;

use std::collections::BTreeMap;

use test_support::sweep::*;

const HEADS: [&str; 14] = [
    "fx",
    "util",
    "main",
    "std",
    "dsp",
    "synth",
    "zz",
    "util.inner",
    "dsp.synth",
    "fx.util",
    "fx.dsp.synth",
    "fx.main",
    "std.math",
    "kp",
];

const TAILS: [&str; 18] = [
    "",
    ".{}",
    ".{a}",
    ".{a, b}",
    ".{util}",
    ".{synth}",
    ".{main}",
    ".{inner}",
    ".{abs}",
    ".a",
    ".inner",
    ".{inner, g}",
    ".g",
    ".{g,}",
    ".{ g }",
    ".{g, g}",
    ".{fx}",
    ".{std}",
];

/// The files of the package `fx` for the shapes. The file `where_` holds the line and the body.
fn shapes_package(where_: &str, line: &str, head: &str) -> Texts {
    let mut t = Texts::new();
    t.insert("main.onsa".into(), "pub fn k() -> I32 {\n  1\n}\n".into());
    t.insert("util.onsa".into(), "pub fn g() -> I32 {\n  1\n}\n".into());
    t.insert("util/inner.onsa".into(), "pub fn g() -> I32 {\n  1\n}\n".into());
    t.insert("dsp/synth.onsa".into(), "pub fn k() -> I32 {\n  1\n}\n".into());
    t.insert("dsp.onsa".into(), "pub fn g() -> I32 {\n  1\n}\n".into());
    let last = head.rsplit('.').next().unwrap();
    let body = format!("pub fn k() -> I32 {{\n  {head}.g() + {last}.g()\n}}\n");
    t.insert(where_.into(), format!("{line}\n{body}"));
    t
}

/// The names stage's codes of a later or equal stage that a candidate must not add.
const NEW_CODES: [&str; 3] = ["E0304", "E0310", "E0303"];

type Key = (String, String, String);

fn key(d: &Diag) -> Key {
    (d.code.clone(), d.file.clone(), d.message.clone())
}

fn count(diags: &[Diag], k: &Key) -> usize {
    diags.iter().filter(|d| &key(d) == k).count()
}

/// The problems of one package: it ends as a check does, and each candidate takes its diagnostic away and
/// adds no code of `NEW_CODES` that the text did not have.
fn probe(texts: &Texts, what: &str, problems: &mut Vec<String>) -> usize {
    let c = check_input(&input_of("fx", texts));
    if !ended_well(&c) {
        problems.push(format!("{what}: ended with code {} {:?}", c.code, c.stderr.lines().next().unwrap_or("")));
        return 0;
    }
    let mut applied_n = 0;
    let before_codes: Vec<&str> = c.diags.iter().map(|x| x.code.as_str()).collect();
    for diag in c.diags.iter().filter(|x| !x.fixes.is_empty()) {
        for (n, fix) in diag.fixes.iter().enumerate() {
            applied_n += 1;
            let mut applied = texts.clone();
            apply_fix_texts(&mut applied, fix);
            let after = check_input(&input_of("fx", &applied));
            if !ended_well(&after) {
                problems.push(format!(
                    "{what}: after candidate {n} of {} {:?}: ended with code {} {:?}",
                    diag.code,
                    diag.message,
                    after.code,
                    after.stderr.lines().next().unwrap_or("")
                ));
                continue;
            }
            let k = key(diag);
            if count(&after.diags, &k) >= count(&c.diags, &k) {
                problems.push(format!(
                    "{what}: candidate {n} {:?} of {} {:?} leaves the diagnostic",
                    fix["title"].as_str().unwrap_or(""),
                    diag.code,
                    diag.message
                ));
            }
            let new: Vec<&str> = after
                .diags
                .iter()
                .map(|x| x.code.as_str())
                .filter(|code| NEW_CODES.contains(code) && !before_codes.contains(code))
                .collect();
            if !new.is_empty() {
                problems.push(format!(
                    "{what}: candidate {n} {:?} of {} {:?} adds {new:?}",
                    fix["title"].as_str().unwrap_or(""),
                    diag.code,
                    diag.message
                ));
            }
        }
    }
    applied_n
}

fn shapes(where_: &str, prefix: &str) {
    let mut problems = Vec::new();
    let mut n = 0;
    let mut applied = 0;
    for head in HEADS {
        for tail in TAILS {
            let line = format!("{prefix}{head}{tail}");
            n += 1;
            let texts = shapes_package(where_, &line, head);
            applied += probe(&texts, &format!("{where_}: {line:?}"), &mut problems);
        }
    }
    assert!(problems.is_empty(), "{} of {n} shapes:\n{}", problems.len(), problems.join("\n"));
    // A sweep that applied no candidate would pass for nothing; 50 is under what each of the files gives.
    // A body path whose head is the name of a failed `use` is silent (S-462), so it gives no candidate.
    assert!(applied >= 50, "only {applied} candidates were applied in {n} packages: the sweep lost its subject");
}

/// §15.1: the shapes of `use` in the file of the root, `main.onsa`.
#[test]
fn shapes_use_in_a_root_module() {
    shapes("main.onsa", "use ");
}

/// §15.1: the shapes in a module below a module with a file (`dsp/synth.onsa`, its parent is `dsp.onsa`).
#[test]
fn shapes_use_in_a_module_below() {
    shapes("dsp/synth.onsa", "use ");
}

/// §15.1: the shapes in a module below a module in a directory (`util/inner.onsa`, parent `util.onsa`).
#[test]
fn shapes_use_in_a_module_of_a_directory() {
    shapes("util/inner.onsa", "use ");
}

/// §15.1: the same with `pub use`, which is E0200 in this version (the candidates, if any, are safe).
#[test]
fn shapes_pub_use_in_a_root_module() {
    shapes("main.onsa", "pub use ");
}

#[test]
fn shapes_pub_use_in_a_module_below() {
    shapes("dsp/synth.onsa", "pub use ");
}

#[test]
fn shapes_pub_use_in_a_module_of_a_directory() {
    shapes("util/inner.onsa", "pub use ");
}

const ODD: [&str; 55] = [
    "use",
    "use ",
    "use .a",
    "use a.",
    "use a..b",
    "use {a}",
    "use fx.",
    "use fx.{",
    "use fx.{a",
    "use fx.{a,",
    "use fx.{,}",
    "use fx.{a b}",
    "use fx.{a.b}",
    "use fx.{{a}}",
    "use fx . a",
    "use fx.\n{a}",
    "use fx.{\n}",
    "use fx.{ // c\n}",
    "use fx.{a} {b}",
    "use fx.a.{}",
    "use fx.{a,,b}",
    "use fx.{self}",
    "use fx.self",
    "use self",
    "use super.a",
    "use crate.a",
    "use fx.{a as b}",
    "use fx as g",
    "use fx.*",
    "use *",
    "use fx.{*}",
    "pub use fx.{}",
    "pub use fx",
    "use fx.util.{}",
    "use util.{}",
    "use main.{}",
    "use main",
    "use dsp.synth.{}",
    "use fx.{util}\nuse fx.{util}",
    "use ::a",
    "use fx::a",
    "use a-b",
    "use 1a",
    "use fx.1",
    "use fx.\"a\"",
    "use `a`",
    "use fx.a.b.c.d.e.f",
    "use fx.fx.fx",
    "use fx.{fx}",
    "use fx.{main}",
    "use fx.{dsp}",
    "use std",
    "use std.",
    "use std.{}",
    "use std.{std}",
];

/// The package of the odd lines: `fx` with a module in a directory, the line in `where_`, before or after
/// the body that names modules by their paths.
fn odd_package(where_: &str, line: &str, after: bool) -> Texts {
    let mut t = Texts::new();
    t.insert("main.onsa".into(), "pub fn k() -> I32 {\n  1\n}\n".into());
    t.insert("dsp/synth.onsa".into(), "pub fn s() -> I32 {\n  1\n}\n".into());
    t.insert("dsp.onsa".into(), "pub fn s() -> I32 {\n  1\n}\n".into());
    t.insert("util.onsa".into(), "pub fn s() -> I32 {\n  1\n}\n".into());
    let body = "pub fn q() -> I32 {\n  fx.util.s() + main.k() + dsp.synth.s()\n}\n";
    let text = if after { format!("{body}{line}\n") } else { format!("{line}\n{body}") };
    t.insert(where_.into(), text);
    t
}

fn odd(where_: &str) {
    let mut problems = Vec::new();
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut applied = 0;
    for line in ODD {
        for after in [false, true] {
            let texts = odd_package(where_, line, after);
            let what = format!("{where_}: {line:?} {}", if after { "after the body" } else { "before the body" });
            *seen.entry(what.clone()).or_default() += 1;
            applied += probe(&texts, &what, &mut problems);
        }
    }
    assert!(problems.is_empty(), "{} of {} packages:\n{}", problems.len(), seen.len(), problems.join("\n"));
    assert!(applied >= 50, "only {applied} candidates were applied: the sweep lost its subject");
}

/// §15.1, §18.1: the broken lines in `main.onsa`.
#[test]
fn odd_lines_in_a_root_module() {
    odd("main.onsa");
}

/// §15.1, §18.1: the broken lines in `dsp/synth.onsa`.
#[test]
fn odd_lines_in_a_module_below() {
    odd("dsp/synth.onsa");
}
