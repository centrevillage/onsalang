//! The keys and values of the packages' table `[[plugin]]` that do not depend on the format (CLAP,
//! VST3, AU), and the E0320 of the names a `[[plugin]]` points at (spec §14.3, §15.3, §18.1, §2.3;
//! S-580, S-597, S-718, S-99, S-827; W4-02 U4).
//!
//! The cases in `tests/spec/manifest/` check which line carries which code (`e1104_plugin_*`,
//! `e1103_plugin_*`, `e0320_plugin_flow_*`). What a marker cannot check is here:
//!
//! - a missing key is one E1104 at the heading of its table, with no fix candidate (no value is
//!   known), and a wrong value is an E1103 at the value, with none either (S-597); the cases of
//!   `tests/spec/manifest/` hold the same lines, here one manifest holds a table for each form and
//!   the whole set of keys and values is swept in one run;
//! - the errors of one table are independent of each other (§18.1), and of the E1102 of a key the
//!   table does not list;
//! - the manifest's errors stop every command before the source is read, with exit code 2;
//! - what this version does not check: `au` of the plugin and the limit of 255 for the parts of
//!   `version` (an AU target exists, S-841, S-826), and the `flow` that names no flow or a flow with
//!   no `@export` (S-641, M10): `check` exits 0;
//! - S-718: the E0320 of a flow a `[[plugin]]` names has no fix candidate and a note whose position
//!   is in `onsa.toml`, at the `flow` value; the E0320 of a flow that is not named keeps its one
//!   candidate; so does the E0320 of every flow when the `flow` names nothing; the module in the path
//!   (the file's name, the directory's name) has none.
//!
//! The path of a `flow` is the module's path and the flow's name (`m.voice`, §15.1); its form is
//! settled with S-641 (M10) and the tests use that form. The position of the E1103 of a repeated
//! `id` (the value of the table written later) is a detail the spec leaves open; it is the form of
//! the design memo of W4-02, and the notes are not checked.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause.

use crate::test_support;

use serde_json::Value;
use test_support::*;

const FLOW_SOURCE: &str = "@export\npub flow voice(x: F32 at sample) -> F32 at sample { x }\n";

/// The flow of `FLOW_SOURCE` and a type error (E0401), so that a command that reads the source would
/// report the E0401, and the manifest's error must come first.
const ERROR_SOURCE: &str =
    "@export\npub flow voice(x: F32 at sample) -> F32 at sample { x }\n\npub fn f() -> I32 {\n  true\n}\n";

type Table = Vec<(String, String)>;

/// The six keys of a `[[plugin]]`, in the order of the spec's table, with a good value; the `id` is
/// the argument.
fn good(id: &str) -> Table {
    [
        ("flow", "\"m.voice\"".to_string()),
        ("id", format!("\"{id}\"")),
        ("name", "\"Voice\"".to_string()),
        ("vendor", "\"Example\"".to_string()),
        ("version", "\"1.0.0\"".to_string()),
        ("category", "\"effect\"".to_string()),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect()
}

/// `good(id)` with the value of `key` replaced.
fn with(id: &str, key: &str, value: &str) -> Table {
    good(id).into_iter().map(|(k, v)| if k == key { (k, value.to_string()) } else { (k, v) }).collect()
}

/// `good(id)` without `key`.
fn without(id: &str, key: &str) -> Table {
    good(id).into_iter().filter(|(k, _)| k != key).collect()
}

/// A manifest of a package `demo` with these tables, and `tail` (more tables) after them. The lines
/// of the tables are known: `headings[i]` is the line of the heading of the table `i` (from 1), and
/// `at(i, key)` the line of its key.
struct Built {
    text: String,
    headings: Vec<u64>,
    keys: Vec<Vec<(String, u64)>>,
}

impl Built {
    fn at(&self, table: usize, key: &str) -> u64 {
        self.keys[table].iter().find(|(k, _)| k == key).unwrap_or_else(|| panic!("no key `{key}` in table {table}")).1
    }
}

fn build(tables: &[Table], tail: &str) -> Built {
    let mut lines: Vec<String> = vec!["[package]".into(), "name = \"demo\"".into(), "edition = \"2026\"".into()];
    let mut headings = Vec::new();
    let mut keys = Vec::new();
    for t in tables {
        lines.push(String::new());
        lines.push("[[plugin]]".into());
        headings.push(lines.len() as u64);
        let mut ks = Vec::new();
        for (k, v) in t {
            lines.push(format!("{k} = {v}"));
            ks.push((k.clone(), lines.len() as u64));
        }
        keys.push(ks);
    }
    Built { text: lines.join("\n") + "\n" + tail, headings, keys }
}

/// A package with that manifest and these files, written to a scratch directory.
fn package(tag: &str, manifest: &str, files: &[(&str, &str)]) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    for (path, text) in files {
        d.write(path, text);
    }
    d
}

/// One diagnostic of `check --json`: code, file, line, the number of fix candidates, and the object.
struct Found {
    code: String,
    file: String,
    line: u64,
    fixes: usize,
    json: Value,
}

/// `onsa check --json` of the package: the exit code and the diagnostics in the order of the
/// document.
fn check(d: &Dir) -> (i32, Vec<Found>) {
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    let doc = doc_of(&out);
    let found = diagnostics(&doc)
        .iter()
        .map(|e| Found {
            code: str_of(e, "code").to_string(),
            file: str_of(&e["span"], "file").to_string(),
            line: int_of(&e["span"], "line"),
            fixes: array_of(e, "fixes").len(),
            json: e.clone(),
        })
        .collect();
    (out.code, found)
}

/// `(code, line)` of the diagnostics in `onsa.toml`, sorted.
fn manifest_places(found: &[Found]) -> Vec<(String, u64)> {
    let mut v: Vec<(String, u64)> =
        found.iter().filter(|f| f.file == "onsa.toml").map(|f| (f.code.clone(), f.line)).collect();
    v.sort();
    v
}

fn place(code: &str, line: u64) -> (String, u64) {
    (code.to_string(), line)
}

fn sorted(mut v: Vec<(String, u64)>) -> Vec<(String, u64)> {
    v.sort();
    v
}

/// The diagnostics are all in the manifest, and none has a fix candidate (S-597: no value is known).
fn only_manifest_without_candidates(found: &[Found], what: &str) {
    for f in found {
        assert_eq!(f.file, "onsa.toml", "{what}: a diagnostic outside the manifest: {} {}:{}", f.code, f.file, f.line);
        assert_eq!(f.fixes, 0, "{what}: {} at line {} has a fix candidate: {}", f.code, f.line, f.json);
    }
}

/// §15.3 `[[plugin]]` rows, §14.3 "全て必須", §18.1: a missing key is an E1104 at the heading of the
/// table that should hold it, one for each missing key, and the other tables are not reported. No
/// candidate, because no value is known for any of the keys. One manifest holds a table for each key
/// that is missing, a complete one, a table that lacks two, and a table with no key.
#[test]
fn a_missing_key_is_an_e1104_at_the_heading_without_a_candidate() {
    let keys = ["flow", "id", "name", "vendor", "version", "category"];
    let mut tables: Vec<Table> = keys.iter().map(|k| without(&format!("com.example.{k}"), k)).collect();
    tables.push(good("com.example.complete"));
    tables.push(without("com.example.two", "vendor").into_iter().filter(|(k, _)| k != "version").collect());
    tables.push(Vec::new());
    let b = build(&tables, "");
    let d = package("plugin_e1104_keys", &b.text, &[("m.onsa", FLOW_SOURCE)]);
    let (code, found) = check(&d);
    assert_eq!(code, 2, "{:?}", found.iter().map(|f| &f.json).collect::<Vec<_>>());
    let mut want: Vec<(String, u64)> = (0..6).map(|i| place("E1104", b.headings[i])).collect();
    want.extend(std::iter::repeat_with(|| place("E1104", b.headings[7])).take(2));
    want.extend(std::iter::repeat_with(|| place("E1104", b.headings[8])).take(6));
    assert_eq!(manifest_places(&found), sorted(want));
    only_manifest_without_candidates(&found, "missing keys");
    assert_eq!(found.len(), 6 + 2 + 6, "nothing but the E1104");
}

/// §15.3 `[[plugin]]` rows, §18.1: a value that is not a string, a `version` that is not
/// `major.minor.patch` and a `category` that is not one of the three are an E1103 at the value, with
/// no candidate. A key with a value of the wrong type is present, so it is not an E1104 as well. Each
/// wrong value is in a table of its own.
#[test]
fn a_wrong_value_is_an_e1103_at_the_value_without_a_candidate() {
    let wrong: [(&str, &str); 22] = [
        ("flow", "true"),
        ("flow", "1"),
        ("id", "1"),
        ("id", "[\"a\"]"),
        ("name", "1"),
        ("name", "2.5"),
        ("vendor", "true"),
        ("vendor", "{ a = 1 }"),
        ("version", "1"),
        ("category", "1"),
        ("version", "\"1.2\""),
        ("version", "\"1.2.3.4\""),
        ("version", "\"a.b.c\""),
        ("version", "\"1.0.0-beta\""),
        ("version", "\"\""),
        ("version", "\"1.2.x\""),
        ("category", "\"synth\""),
        ("category", "\"Effect\""),
        ("category", "\"note_effect\""),
        ("category", "\"\""),
        ("category", "\"instrument \""),
        ("category", "[\"effect\"]"),
    ];
    let tables: Vec<Table> =
        wrong.iter().enumerate().map(|(i, (k, v))| with(&format!("com.example.t{i}"), k, v)).collect();
    let b = build(&tables, "");
    let d = package("plugin_e1103_values", &b.text, &[("m.onsa", FLOW_SOURCE)]);
    let (code, found) = check(&d);
    assert_eq!(code, 2);
    let want: Vec<(String, u64)> = wrong.iter().enumerate().map(|(i, (k, _))| place("E1103", b.at(i, k))).collect();
    assert_eq!(manifest_places(&found), sorted(want), "{:?}", wrong);
    only_manifest_without_candidates(&found, "wrong values");
    assert_eq!(found.len(), wrong.len(), "nothing but the E1103 (no E1104 for a key that is there)");
}

/// §15.3 `version` and `category` rows: the values that are right are not reported. The limit of 255
/// for each part is AU's alone and this version does not check it (S-841, S-826).
#[test]
fn the_right_versions_and_categories_are_not_reported() {
    let mut tables: Vec<Table> = Vec::new();
    for (i, v) in ["0.1.0", "1.0.0", "10.20.30", "1.2.300", "255.255.255", "256.1.1"].iter().enumerate() {
        tables.push(with(&format!("com.example.v{i}"), "version", &format!("\"{v}\"")));
    }
    for (i, c) in ["instrument", "effect", "note-effect"].iter().enumerate() {
        tables.push(with(&format!("com.example.c{i}"), "category", &format!("\"{c}\"")));
    }
    let b = build(&tables, "");
    let d = package("plugin_right_values", &b.text, &[("m.onsa", FLOW_SOURCE)]);
    let (code, found) = check(&d);
    assert_eq!(code, 0, "{:?}", found.iter().map(|f| &f.json).collect::<Vec<_>>());
}

/// §15.3 `id` row, §14.3 ("同じ `id` の重複は誤り"), §18.1: a repeated `id` is an E1103 at the `id` value of the
/// table written later (one for each table after the first that has it); the first is not reported.
/// The position is a detail of the design memo of W4-02. Three groups: an `id` three times in a row,
/// an `id` twice with another between, and `id` that differ.
#[test]
fn a_repeated_id_is_an_e1103_at_the_later_tables() {
    let tables = vec![
        good("com.example.same"),
        good("com.example.same"),
        good("com.example.same"),
        good("com.example.x"),
        good("com.example.y"),
        good("com.example.x"),
        good("com.example.p"),
        good("com.example.q"),
    ];
    let b = build(&tables, "");
    let d = package("plugin_e1103_ids", &b.text, &[("m.onsa", FLOW_SOURCE)]);
    let (code, found) = check(&d);
    assert_eq!(code, 2);
    let want = vec![place("E1103", b.at(1, "id")), place("E1103", b.at(2, "id")), place("E1103", b.at(5, "id"))];
    assert_eq!(manifest_places(&found), sorted(want));
    only_manifest_without_candidates(&found, "repeated id");
}

/// §18.1 "互いに独立に全て": the errors of one table are independent of each other and of the E1102
/// of a key the table does not list, which does not stop the values from being read.
#[test]
fn the_errors_of_one_table_are_independent() {
    let mut t = with("com.example.voice", "name", "1");
    t = t.into_iter().map(|(k, v)| if k == "version" { (k, "\"1.2\"".to_string()) } else { (k, v) }).collect();
    t.retain(|(k, _)| k != "vendor");
    t.push(("colour".to_string(), "1".to_string()));
    // The second table repeats the `id` of the first.
    let b = build(&[t, good("com.example.voice")], "");
    let d = package("plugin_independent", &b.text, &[("m.onsa", FLOW_SOURCE)]);
    let (code, found) = check(&d);
    assert_eq!(code, 2);
    let want = vec![
        place("E1104", b.headings[0]),
        place("E1103", b.at(0, "name")),
        place("E1103", b.at(0, "version")),
        place("E1102", b.at(0, "colour")),
        place("E1103", b.at(1, "id")),
    ];
    assert_eq!(manifest_places(&found), sorted(want));
}

/// §18.1, §18.2: the other commands that read the manifest stop at the errors of `[[plugin]]` too, with
/// exit code 2, and report them only: the E0401 of the source is not reached. A missing key (E1104) and
/// a wrong value (E1103) are both there.
#[test]
fn every_command_stops_on_a_plugin_error_before_the_source() {
    let tail = "\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";
    let b = build(&[without("com.example.voice", "vendor"), with("com.example.other", "version", "\"1.2\"")], tail);
    let d = package("plugin_commands", &b.text, &[("m.onsa", ERROR_SOURCE)]);
    let dir = d.arg();
    let commands: [&[&str]; 5] = [
        &["check", &dir],
        &["test", &dir],
        &["interface", &dir],
        &["graph", "voice", &dir],
        &["build", "--target", "host", &dir],
    ];
    for args in commands {
        let out = run(d.root(), args);
        assert_eq!(out.code, 2, "onsa {args:?}: {}{}", out.stdout, out.stderr);
        let mut found: Vec<&str> = out
            .stdout
            .lines()
            .filter_map(|l| l.split_once(": error[").and_then(|(_, r)| r.split_once(']')).map(|(c, _)| c))
            .collect();
        found.sort();
        assert_eq!(found, vec!["E1103", "E1104"], "onsa {args:?}: {}{}", out.stdout, out.stderr);
    }
    // The document: both in `onsa.toml`, at the heading and at the value, and no candidate.
    let (code, found) = check(&d);
    assert_eq!(code, 2);
    assert_eq!(
        manifest_places(&found),
        sorted(vec![place("E1104", b.headings[0]), place("E1103", b.at(1, "version"))])
    );
    only_manifest_without_candidates(&found, "the document");
}

/// §15.3 `au` row and S-841, S-826: this version checks neither that `au` is there for an AU target,
/// nor the limit of 255 for each part of `version`, nor the value of `au`. `check` and `test` exit 0.
/// One table for each: no `au`, `version = "1.2.300"`, and `au = { subtype = 1 }`.
#[test]
fn the_rules_for_au_alone_are_not_checked() {
    let mut with_au = good("com.example.c");
    with_au.push(("au".to_string(), "{ subtype = 1 }".to_string()));
    let tables = vec![good("com.example.a"), with("com.example.b", "version", "\"1.2.300\""), with_au];
    let tail = "\n[export]\nprefix = \"p_\"\n\n[targets.t]\nkind = \"au\"\nplatform = \"host\"\n";
    let b = build(&tables, tail);
    let d = package("plugin_au_alone", &b.text, &[("m.onsa", FLOW_SOURCE)]);
    for cmd in ["check", "test"] {
        let out = run(d.root(), &[cmd, &d.arg()]);
        assert_eq!(out.code, 0, "onsa {cmd}: {}{}", out.stdout, out.stderr);
    }
}

/// §14.3, §15.3 `flow` row, S-641: a `flow` that names no flow of the package, or a flow with no
/// `@export`, is not an error of `check` in this version (the E1103 for it comes with the build of a
/// plugin target, M10).
#[test]
fn a_flow_that_names_nothing_or_has_no_export_is_not_reported_by_check() {
    let tables = vec![with("com.example.a", "flow", "\"nowhere.nothing\""), good("com.example.b")];
    let b = build(&tables, "");
    let d = package(
        "plugin_flow_unchecked",
        &b.text,
        &[("m.onsa", "pub flow voice(x: F32 at sample) -> F32 at sample { x }\n")],
    );
    let (code, found) = check(&d);
    assert_eq!(code, 0, "{:?}", found.iter().map(|f| &f.json).collect::<Vec<_>>());
}

// ---- S-718: the E0320 of the names a `[[plugin]]` points at ------------------------------------

/// Two flows with a name that breaks §2.3, and a flow that uses both; the line of each name.
const BAD_NAME_LINE: u64 = 2;
const BAD_OTHER_LINE: u64 = 5;
const E0320_SOURCE: &str = "@export\npub flow BadName(x: F32 at sample) -> F32 at sample { x }\n\n@export\npub flow BadOther(x: F32 at sample) -> F32 at sample { x }\n\npub flow uses_both(x: F32 at sample) -> F32 at sample {\n  BadName~(x) + BadOther~(x)\n}\n";

fn e0320_in<'a>(found: &'a [Found], file: &str, line: u64) -> &'a Found {
    found.iter().find(|f| f.code == "E0320" && f.file == file && f.line == line).unwrap_or_else(|| {
        panic!("no E0320 at {file}:{line}: {:?}", found.iter().map(|f| (&f.code, &f.file, f.line)).collect::<Vec<_>>())
    })
}

/// §2.3 ("マニフェストが経路で名指す名前"), §15.3 `flow` row, S-718: the E0320 of the flow a `[[plugin]]`
/// names has no fix candidate, although other flows use the name; the E0320 of the flow that is not
/// named keeps its one candidate. The exit code is 1: the E0320 is in the source and the manifest is
/// right.
#[test]
fn the_e0320_of_a_named_flow_has_no_candidate_and_the_other_keeps_it() {
    let b = build(&[with("com.example.voice", "flow", "\"m.BadName\"")], "");
    let d = package("plugin_e0320_named", &b.text, &[("m.onsa", E0320_SOURCE)]);
    let (code, found) = check(&d);
    assert_eq!(code, 1);
    assert_eq!(
        found.len(),
        2,
        "the two E0320 and nothing else: {:?}",
        found.iter().map(|f| (&f.code, f.line)).collect::<Vec<_>>()
    );
    assert_eq!(e0320_in(&found, "m.onsa", BAD_NAME_LINE).fixes, 0, "the named flow: no candidate (S-718)");
    assert_eq!(e0320_in(&found, "m.onsa", BAD_OTHER_LINE).fixes, 1, "the flow that is not named keeps its candidate");
}

/// §2.3, §15.3 `flow` row, S-718: the E0320 of the named flow has a note that shows the place in the
/// manifest, the `flow` value: the note's `span` is in `onsa.toml`, at the line of the key. The wording
/// is not fixed. The flow that is not named has no note in the manifest.
#[test]
fn the_e0320_of_a_named_flow_has_a_note_that_points_at_the_manifest() {
    let b = build(&[with("com.example.voice", "flow", "\"m.BadName\"")], "");
    let d = package("plugin_e0320_note", &b.text, &[("m.onsa", E0320_SOURCE)]);
    let (_, found) = check(&d);
    let in_manifest = |f: &Found| -> Vec<u64> {
        array_of(&f.json, "notes")
            .iter()
            .filter(|n| n.get("span").is_some_and(|s| str_of(s, "file") == "onsa.toml"))
            .map(|n| int_of(&n["span"], "line"))
            .collect()
    };
    assert_eq!(
        in_manifest(e0320_in(&found, "m.onsa", BAD_NAME_LINE)),
        vec![b.at(0, "flow")],
        "one note, at the `flow` line"
    );
    assert!(in_manifest(e0320_in(&found, "m.onsa", BAD_OTHER_LINE)).is_empty(), "the flow that is not named");
}

/// S-718: a `flow` that names nothing (no module of that path, a name that is spelt otherwise) does not
/// take the candidate away from any E0320. Three tables, each names nothing.
#[test]
fn a_flow_that_names_nothing_leaves_every_e0320_as_it_is() {
    let tables = vec![
        with("com.example.a", "flow", "\"m.nothing\""),
        with("com.example.b", "flow", "\"other.BadName\""),
        with("com.example.c", "flow", "\"m.badname\""),
    ];
    let b = build(&tables, "");
    let d = package("plugin_e0320_nothing", &b.text, &[("m.onsa", E0320_SOURCE)]);
    let (code, found) = check(&d);
    assert_eq!(code, 1);
    assert_eq!(found.len(), 2, "{:?}", found.iter().map(|f| (&f.code, f.line)).collect::<Vec<_>>());
    assert_eq!(e0320_in(&found, "m.onsa", BAD_NAME_LINE).fixes, 1);
    assert_eq!(e0320_in(&found, "m.onsa", BAD_OTHER_LINE).fixes, 1);
}

/// S-718: the path decides, not the name: `m.BadName` is named, and a flow of the same name in
/// another module is not, so it keeps its candidate. The same for `Match`, whose corrected name is a
/// reserved word: the named one has no `match_` (§2.3 "下の予約語の候補も出さない"), the other has.
#[test]
fn the_path_decides_which_flow_is_named() {
    let tables = vec![with("com.example.a", "flow", "\"m.BadName\""), with("com.example.b", "flow", "\"m.Match\"")];
    let b = build(&tables, "");
    let m = "@export\npub flow BadName(x: F32 at sample) -> F32 at sample { x }\n\n@export\npub flow Match(x: F32 at sample) -> F32 at sample { x }\n";
    let other = "pub flow BadName(x: F32 at sample) -> F32 at sample { x }\n\npub flow Match(x: F32 at sample) -> F32 at sample { x }\n";
    let d = package("plugin_e0320_same_name", &b.text, &[("m.onsa", m), ("other.onsa", other)]);
    let (code, found) = check(&d);
    assert_eq!(code, 1);
    assert_eq!(e0320_in(&found, "m.onsa", 2).fixes, 0, "m.BadName is named");
    assert_eq!(e0320_in(&found, "m.onsa", 5).fixes, 0, "m.Match is named: no `match_` either");
    assert_eq!(e0320_in(&found, "other.onsa", 1).fixes, 1, "other.BadName is not named");
    assert_eq!(e0320_in(&found, "other.onsa", 3).fixes, 1, "other.Match is not named: the candidate `match_`");
}

/// §2.3, §15.1: the module in the path of a named flow (the file's name, the directory's name) has an
/// E0320 with no candidate, as it has without a `[[plugin]]`, and the other flows' E0320 are not
/// changed. The note that shows the manifest's place is the next test.
#[test]
fn the_e0320_of_a_module_in_the_path_has_no_candidate() {
    let voice = "@export\npub flow voice(x: F32 at sample) -> F32 at sample { x }\n";
    let tables = vec![
        with("com.example.a", "flow", "\"BadMod.voice\""),
        with("com.example.b", "flow", "\"BadDir.synth.voice\""),
    ];
    let b = build(&tables, "");
    let d = package(
        "plugin_e0320_modules",
        &b.text,
        &[("m.onsa", E0320_SOURCE), ("BadMod.onsa", voice), ("BadDir/synth.onsa", voice)],
    );
    let (code, found) = check(&d);
    assert_eq!(code, 1);
    for file in ["BadMod.onsa", "BadDir/synth.onsa"] {
        let on_module: Vec<&Found> = found.iter().filter(|f| f.code == "E0320" && f.file == file).collect();
        assert_eq!(on_module.len(), 1, "{file}: one E0320 at the module");
        assert_eq!(on_module[0].fixes, 0, "{file}");
    }
    // The flows of m.onsa are not named: they keep their candidates.
    assert_eq!(e0320_in(&found, "m.onsa", BAD_NAME_LINE).fixes, 1);
    assert_eq!(e0320_in(&found, "m.onsa", BAD_OTHER_LINE).fixes, 1);
}

/// §2.3 line "マニフェストが経路で名指す名前（`flow` が指す flow と、その経路の途中のモジュール）": the E0320 of the
/// module in the path also has a note that shows the manifest's place, at the `flow` value. (The task
/// asked for the flow's note; the spec's sentence and the decision S-718 name the module too.)
#[test]
fn the_e0320_of_a_module_in_the_path_has_a_note_that_points_at_the_manifest() {
    let voice = "@export\npub flow voice(x: F32 at sample) -> F32 at sample { x }\n";
    let tables = vec![
        with("com.example.a", "flow", "\"BadMod.voice\""),
        with("com.example.b", "flow", "\"BadDir.synth.voice\""),
    ];
    let b = build(&tables, "");
    let d = package(
        "plugin_e0320_module_notes",
        &b.text,
        &[("m.onsa", "pub fn f() -> I32 {\n  1\n}\n"), ("BadMod.onsa", voice), ("BadDir/synth.onsa", voice)],
    );
    let (_, found) = check(&d);
    for (file, table) in [("BadMod.onsa", 0), ("BadDir/synth.onsa", 1)] {
        let e =
            found.iter().find(|f| f.code == "E0320" && f.file == file).unwrap_or_else(|| panic!("no E0320 at {file}"));
        let lines: Vec<u64> = array_of(&e.json, "notes")
            .iter()
            .filter(|n| n.get("span").is_some_and(|s| str_of(s, "file") == "onsa.toml"))
            .map(|n| int_of(&n["span"], "line"))
            .collect();
        assert_eq!(lines, vec![b.at(table, "flow")], "{file}: one note, at the `flow` line");
    }
}
