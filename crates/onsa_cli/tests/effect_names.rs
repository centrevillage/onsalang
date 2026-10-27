//! The names in an effect row, seen from the command line (spec §8.1, §8.2, §15.1, §18.1; S-74, R-129,
//! S-659, S-701, S-702, D-08; W4-03 U5b).
//!
//! What the spec fixes, and so what is checked here:
//! - an effect row is read like any other name, with the same result in every place a row is written: a
//!   signature, the type of a parameter, a type alias, a field, an anonymous function, the member of an
//!   `impl`. `Alloc` (and `core.Alloc` after `use std.core`) passes; a name that is not found is E0302;
//!   an effect that std declares and a `use` took is found, and in this version it is an E0200 (D-08);
//!   `Block` is found with no `use` and is an E0200 (S-702); a path is looked up through the module that
//!   a `use` bound (`fs.Fs`, S-659 (4));
//! - the six standard effects are in the modules of the table of §8.2 (`std.fs`, `std.io`, `std.time`,
//!   `std.random`, `std.log`), and in no other: the table is the mapping (S-659 (B)). The module of the
//!   prelude names is `std.core`, and there is no `std.prelude`;
//! - an effect of std written with no `use` is E0302 with one candidate, the `use` of it (§8.1, S-659
//!   (3)); after it the name is found. A name that no module declares has no candidate (§15.1);
//! - what a `use` takes in a module is not seen from another module.
//!
//! The text of the candidate is not promised (§18.1); what is checked is the number of the candidates and
//! what the program is after one is applied. The same cases with the places of the marks are under
//! `tests/spec/effects/names_*` and `tests/spec/packages/effect_names_modules`.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause.

mod test_support;

use std::path::Path;

use serde_json::Value;
use test_support::*;

fn check_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

fn offset(text: &str, line: u64, col: u64) -> usize {
    let mut start = 0;
    for (i, l) in text.split_inclusive('\n').enumerate() {
        if i as u64 + 1 == line {
            let in_line = l.char_indices().nth(col as usize - 1).map(|(b, _)| b).unwrap_or(l.len());
            return start + in_line;
        }
        start += l.len();
    }
    text.len()
}

/// Apply every edit of one candidate to `file` of `d` (all edits together, from the end).
fn apply(d: &Dir, file: &str, fix: &Value) {
    let mut text = std::fs::read_to_string(d.root().join(file)).unwrap();
    let mut edits: Vec<(usize, usize, String)> = array_of(fix, "edits")
        .iter()
        .map(|e| {
            let sp = span_of(&e["span"]);
            assert_eq!(sp.file, file, "a candidate edits the file of the diagnostic: {fix}");
            (offset(&text, sp.line, sp.col), offset(&text, sp.end_line, sp.end_col), str_of(e, "replace").to_string())
        })
        .collect();
    edits.sort_by(|x, y| y.0.cmp(&x.0));
    for (a, b, rep) in edits {
        text.replace_range(a..b, &rep);
    }
    d.write(file, &text);
}

/// The places an effect row is written. Each is a unit of its own, and `row` is the text of the row
/// (`Alloc`, `fs.Fs`). Returns the source and the line of each row.
fn places(prefix: &str, row: &str) -> (String, Vec<u64>) {
    let units = [
        format!("pub fn p_sig() uses {{{row}}} {{}}\n"),
        format!("pub fn p_param(f: fn() -> U32 uses {{{row}}}) -> U32 {{\n  1\n}}\n"),
        format!("pub type PAlias = fn(U32) -> U32 uses {{{row}}}\n"),
        format!("pub struct PField {{\n  f: fn() -> U32 uses {{{row}}},\n}}\n"),
        format!("pub fn p_closure() -> U32 {{\n  let _ = fn(x: U32) -> U32 uses {{{row}}} {{ x }}\n  1\n}}\n"),
        format!(
            "pub struct PImpl {{\n  id: U32,\n}}\n\nimpl PImpl {{\n  pub fn read(self) -> U32 uses {{{row}}} {{\n    self.id\n  }}\n}}\n"
        ),
    ];
    let mut src = prefix.to_string();
    let mut lines = Vec::new();
    for u in &units {
        src.push('\n');
        let at = src.matches('\n').count() as u64 + 1;
        let row_line = u.lines().position(|l| l.contains("uses {")).unwrap() as u64;
        lines.push(at + row_line);
        src.push_str(u);
    }
    (src, lines)
}

/// The row `row` (after `prefix`, the `use` lines) in every place: no diagnostic when `want` is `None`, and
/// else exactly one diagnostic of the code `want` at each row.
fn row_is_read_the_same_everywhere(tag: &str, prefix: &str, row: &str, want: Option<&str>) {
    let d = Dir::pkg(tag);
    let (src, lines) = places(prefix, row);
    d.write("main.onsa", &src);
    let (out, doc) = check_json(d.root(), &["."]);
    let got: Vec<(String, u64)> =
        diagnostics(&doc).iter().map(|x| (str_of(x, "code").to_string(), span_of(&x["span"]).line)).collect();
    match want {
        None => {
            assert_eq!(out.code, 0, "{row}: {src}\n{doc}");
            assert!(got.is_empty(), "{row}: {doc}");
        }
        Some(code) => {
            assert_eq!(out.code, 1, "{row}: {doc}");
            let mut expect: Vec<(String, u64)> = lines.iter().map(|l| (code.to_string(), *l)).collect();
            let mut got = got;
            expect.sort();
            got.sort();
            assert_eq!(
                got, expect,
                "{row} (a row in a signature, a parameter type, an alias, a field, an anonymous function and a member): {doc}"
            );
        }
    }
}

// ---- the same result in every place ---------------------------------------------------------------------

/// §8.2, §15.1: `Alloc` is in the prelude, in every place of a row; `core.Alloc` is the same effect.
#[test]
fn alloc_passes_in_every_place() {
    row_is_read_the_same_everywhere("row_alloc", "", "Alloc", None);
}

#[test]
fn alloc_by_its_path_passes_in_every_place() {
    row_is_read_the_same_everywhere("row_core_alloc", "use std.core\n", "core.Alloc", None);
}

/// §8.1, §15.1 (S-74): a name that nothing binds is E0302 in every place of a row.
#[test]
fn a_name_that_is_not_found_is_e0302_in_every_place() {
    row_is_read_the_same_everywhere("row_nope", "", "Nope", Some("E0302"));
    row_is_read_the_same_everywhere("row_head_nothing", "", "zzz.Alloc", Some("E0302"));
}

/// §8.1, S-659: a standard effect with no `use` is not found (E0302) in every place; with its `use` it is
/// found and is an E0200 at the name (D-08).
#[test]
fn a_standard_effect_is_e0302_without_its_use_and_e0200_with_it() {
    row_is_read_the_same_everywhere("row_fs_bare", "", "Fs", Some("E0302"));
    row_is_read_the_same_everywhere("row_fs_use", "use std.fs.{Fs}\n", "Fs", Some("E0200"));
    row_is_read_the_same_everywhere("row_fs_module", "use std.fs\n", "fs.Fs", Some("E0200"));
    row_is_read_the_same_everywhere("row_fs_module_missing", "use std.fs\n", "fs.Nope", Some("E0302"));
    row_is_read_the_same_everywhere("row_fs_package", "use std\n", "std.fs.Fs", Some("E0200"));
}

/// §8.2, S-702: `Block` is found with no `use` (it is in the prelude), and is an E0200 as an effect other
/// than `Alloc`; also by its path through `std.core`.
#[test]
fn block_is_found_with_no_use_and_is_e0200() {
    row_is_read_the_same_everywhere("row_block", "", "Block", Some("E0200"));
}

#[test]
fn block_by_its_path_is_e0200() {
    row_is_read_the_same_everywhere("row_core_block", "use std.core\n", "core.Block", Some("E0200"));
}

// ---- the modules of the table of §8.2 ------------------------------------------------------------------

const TABLE: [(&str, &[&str]); 5] =
    [("fs", &["Fs"]), ("io", &["Stdout", "Stdin"]), ("time", &["Clock"]), ("random", &["Random"]), ("log", &["Log"])];

/// §8.2 (S-659 (B), S-701): each standard effect is taken from the module of the table, and only from it.
#[test]
fn each_standard_effect_is_in_the_module_of_the_table_and_in_no_other() {
    for (module, effects) in TABLE {
        for effect in effects {
            let d = Dir::pkg(&format!("table_{module}_{effect}"));
            d.write("main.onsa", &format!("use std.{module}.{{{effect}}}\nuse std.{module}\n"));
            let (out, doc) = check_json(d.root(), &["."]);
            assert_eq!(out.code, 0, "use std.{module}.{{{effect}}}: {doc}");
            for (other, _) in TABLE.iter().filter(|(m, _)| *m != module) {
                let d = Dir::pkg(&format!("table_{other}_{effect}"));
                d.write("main.onsa", &format!("use std.{other}.{{{effect}}}\n"));
                let (out, doc) = check_json(d.root(), &["."]);
                assert_eq!(out.code, 1, "use std.{other}.{{{effect}}}: {doc}");
                assert_eq!(diagnostics(&doc).len(), 1, "{doc}");
                assert_eq!(str_of(&diagnostics(&doc)[0], "code"), "E0302", "{doc}");
                assert!(array_of(&diagnostics(&doc)[0], "fixes").is_empty(), "no candidate: {doc}");
            }
        }
    }
    // The prelude names are in `std.core` (S-659 (B)); the module `std.prelude` is not (the user did not take it).
    let d = Dir::pkg("table_prelude");
    d.write("main.onsa", "use std.prelude.{Alloc}\n");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{doc}");
    assert_eq!(str_of(&diagnostics(&doc)[0], "code"), "E0302", "{doc}");
}

// ---- the candidate --------------------------------------------------------------------------------------

/// §8.1, S-659 (3): an effect of std with no `use` is E0302 with one candidate. After it the name is found:
/// the program has the one E0200 at the row and no E0302. The text of the candidate is not promised, but the
/// edit takes the module of the table.
#[test]
fn a_standard_effect_without_use_has_the_use_as_its_one_candidate() {
    for (module, effects) in TABLE {
        for effect in effects {
            for (place, src) in [
                ("sig", format!("pub fn f() uses {{{effect}}} {{}}\n")),
                (
                    "closure",
                    format!("pub fn f() -> U32 {{\n  let g = fn(x: U32) -> U32 uses {{{effect}}} {{ x }}\n  1\n}}\n"),
                ),
            ] {
                let d = Dir::pkg(&format!("cand_{module}_{effect}_{place}"));
                d.write("main.onsa", &src);
                let (out, doc) = check_json(d.root(), &["."]);
                assert_eq!(out.code, 1, "{effect}: {doc}");
                assert_eq!(diagnostics(&doc).len(), 1, "{effect} in {place}: {doc}");
                let x = &diagnostics(&doc)[0];
                assert_eq!(str_of(x, "code"), "E0302", "{effect} in {place}: {doc}");
                let fixes = array_of(x, "fixes");
                assert_eq!(fixes.len(), 1, "{effect} in {place}: one candidate, the `use` of it: {doc}");
                let edited: String =
                    array_of(&fixes[0], "edits").iter().map(|e| str_of(e, "replace")).collect::<Vec<_>>().join("");
                assert!(
                    edited.contains(&format!("std.{module}")) && edited.contains(effect),
                    "{effect} in {place}: the edit takes the module of the table: {edited:?}"
                );
                apply(&d, "main.onsa", &fixes[0]);
                let (out, doc) = check_json(d.root(), &["."]);
                assert_eq!(out.code, 1, "{effect} in {place} after the candidate: {doc}");
                assert_eq!(diagnostics(&doc).len(), 1, "after the candidate: {doc}");
                assert_eq!(str_of(&diagnostics(&doc)[0], "code"), "E0200", "after the candidate: {doc}");
            }
        }
    }
}

/// §15.1: a name that no module declares has no candidate, and neither does a near spelling of an effect
/// (`Fss`), a path whose head nothing binds, and `Block` (found).
#[test]
fn no_candidate_for_a_name_that_no_module_declares() {
    for row in ["Nope", "Fss", "zzz.Alloc", "fs.Nope"] {
        let d = Dir::pkg("cand_none");
        d.write("main.onsa", &format!("use std.fs\n\npub fn f() uses {{{row}}} {{}}\n"));
        let (_, doc) = check_json(d.root(), &["."]);
        assert_eq!(diagnostics(&doc).len(), 1, "{row}: {doc}");
        assert_eq!(str_of(&diagnostics(&doc)[0], "code"), "E0302", "{row}: {doc}");
        assert!(array_of(&diagnostics(&doc)[0], "fixes").is_empty(), "{row}: no candidate: {doc}");
    }
}

// ---- the modules ----------------------------------------------------------------------------------------

/// §15.1: what a `use` takes in one module is not seen from another. `a.onsa` takes `Fs` (found, E0200),
/// `b.onsa` takes nothing (E0302), and `Alloc` and `Block` are found in both.
#[test]
fn the_use_of_a_module_is_not_seen_from_another() {
    let d = Dir::pkg("modules");
    d.write("a.onsa", "use std.fs.{Fs}\n\npub fn read_a() uses {Fs} {}\n\npub fn alloc_a() uses {Alloc} {}\n");
    d.write(
        "b.onsa",
        "pub fn read_b() uses {Fs} {}\n\npub fn alloc_b() uses {Alloc} {}\n\npub fn block_b() uses {Block} {}\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{doc}");
    let mut got: Vec<(String, String, u64)> = diagnostics(&doc)
        .iter()
        .map(|x| {
            let sp = span_of(&x["span"]);
            (str_of(x, "code").to_string(), sp.file, sp.line)
        })
        .collect();
    got.sort();
    let want = vec![
        ("E0200".to_string(), "a.onsa".to_string(), 3),
        ("E0200".to_string(), "b.onsa".to_string(), 5),
        ("E0302".to_string(), "b.onsa".to_string(), 1),
    ];
    assert_eq!(got, want, "{doc}");
}
