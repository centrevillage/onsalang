//! The names of the prelude and of `std.core`, seen from the command line (spec §6.3, §8.2, §15.1, §18.1;
//! S-107, S-659, S-702, S-703, S-611, R-278; W4-03 U5b).
//!
//! What the spec fixes, and so what is checked here:
//! - the prelude names that std declares (`Option`, `Result`, `Alloc`, `Block`, the operator traits and the
//!   standard traits of §6.3) are the items of `std.core`; taking one again from there is E0304 with no
//!   candidate (S-611, S-659 (1)); the other prelude names (an enumerator, `panic`, `Copy`, `Dup`, a
//!   built-in type) are not items of it, so the `use` is E0302;
//! - a `use` that fails in the names stage (E0302) and takes a name of the prelude gets a note that the
//!   name is written with no `use`, and no candidate (S-703, §15.1). The text of the note is not
//!   promised; what is checked is that there is one, for each name of the list of §15.1, in each form
//!   that fails (a module that is not there, a module that has no such name, a head that is not there, a
//!   path with no list, an enumerator of `std.core`), and that a name that is not of the prelude (an
//!   effect, a name nothing has, a clock name) gets none; and an E0304 is not E0302;
//! - in a list the note is for the elements that are names of the prelude (`Foo` of `{Option, Foo}` gets none);
//! - the user's items of the names of the prelude, and a `Block` of a clock position (`at Block`, §11.3) is not
//!   the effect: it stays E0302 (tests/spec/negative/flow_clock_names.onsa).
//!
//! The same forms with the marks are under `tests/spec/module/prelude_*`; here are the notes and the
//! candidates, which a mark cannot say.
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

const OPERATOR_TRAITS: [&str; 20] = [
    "Add",
    "Sub",
    "Mul",
    "Div",
    "Rem",
    "Neg",
    "PartialEq",
    "PartialOrd",
    "BitAnd",
    "BitOr",
    "BitXor",
    "Shl",
    "Shr",
    "Not",
    "WrappingAdd",
    "WrappingSub",
    "WrappingMul",
    "SaturatingAdd",
    "SaturatingSub",
    "SaturatingMul",
];
const STANDARD_TRAITS: [&str; 14] = [
    "Eq", "Ord", "Hash", "Show", "Default", "Iter", "IntoIter", "Drop", "AnyNum", "Num", "Float", "Int", "Unsigned",
    "Ordinal",
];

/// The names of the prelude that std declares: items of `std.core`.
fn core_items() -> Vec<&'static str> {
    let mut v = vec!["Option", "Result", "Alloc", "Block"];
    v.extend(OPERATOR_TRAITS);
    v.extend(STANDARD_TRAITS);
    v
}

/// The names of the prelude that the compiler gives: not items of `std.core`.
const COMPILER_NAMES: [&str; 14] =
    ["Some", "None", "Ok", "Err", "panic", "Copy", "Dup", "I32", "U8", "F32", "Bool", "Str", "Buf", "Array"];

fn notes_of(d: &Value) -> usize {
    d.get("notes").and_then(Value::as_array).map_or(0, Vec::len)
}

fn fixes_of(d: &Value) -> usize {
    d.get("fixes").and_then(Value::as_array).map_or(0, Vec::len)
}

/// One diagnostic per `use` line of `uses`, in order: (code, notes, fixes).
fn per_use(tag: &str, uses: &[String]) -> Vec<(String, usize, usize)> {
    let d = Dir::pkg(tag);
    d.write("main.onsa", &(uses.join("\n") + "\n"));
    let (_, doc) = check_json(d.root(), &["."]);
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), uses.len(), "one diagnostic for each `use`: {doc}");
    let mut by_line: Vec<(u64, (String, usize, usize))> = ds
        .iter()
        .map(|x| (span_of(&x["span"]).line, (str_of(x, "code").to_string(), notes_of(x), fixes_of(x))))
        .collect();
    by_line.sort_by_key(|x| x.0);
    by_line.into_iter().map(|x| x.1).collect()
}

// ---- std.core (S-659, S-611) -----------------------------------------------------------------------------

/// §15.1, S-611, S-659 (1): the items of `std.core` taken again are E0304 with no candidate.
#[test]
fn a_prelude_name_taken_again_from_std_core_is_e0304_with_no_candidate() {
    let uses: Vec<String> = core_items().iter().map(|n| format!("use std.core.{{{n}}}")).collect();
    for (i, (code, _, fixes)) in per_use("core_again", &uses).into_iter().enumerate() {
        assert_eq!((code.as_str(), fixes), ("E0304", 0), "use std.core.{{{}}}", core_items()[i]);
    }
}

/// §15.1, S-659 (1): the prelude names that the compiler gives are not items of `std.core`: E0302, no candidate.
#[test]
fn the_names_the_compiler_gives_are_not_items_of_std_core() {
    let uses: Vec<String> = COMPILER_NAMES.iter().map(|n| format!("use std.core.{{{n}}}")).collect();
    for (i, (code, _, fixes)) in per_use("core_missing", &uses).into_iter().enumerate() {
        assert_eq!((code.as_str(), fixes), ("E0302", 0), "use std.core.{{{}}}", COMPILER_NAMES[i]);
    }
}

// ---- the note of S-703 -----------------------------------------------------------------------------------

/// The forms of a `use` that fail in the names stage and take the name `n`.
fn failing_forms(n: &str) -> Vec<String> {
    vec![
        format!("use std.option.{{{n}}}"),
        format!("use std.math.{{{n}}}"),
        format!("use option.{{{n}}}"),
        format!("use std.option.{n}"),
    ]
}

/// §15.1, S-703: the E0302 of a `use` that takes a name of the prelude has a note and no candidate; for each
/// name of the list, in each form (a path that is not there, a module that has no such name, a head that is
/// not there, a path with no list).
#[test]
fn a_failed_use_of_a_prelude_name_has_a_note_and_no_candidate() {
    let mut names = core_items();
    names.extend(COMPILER_NAMES);
    let mut uses = Vec::new();
    let mut who = Vec::new();
    for n in &names {
        for u in failing_forms(n) {
            who.push(u.clone());
            uses.push(u);
        }
    }
    for (i, (code, notes, fixes)) in per_use("note_prelude", &uses).into_iter().enumerate() {
        assert_eq!((code.as_str(), fixes), ("E0302", 0), "{}", who[i]);
        assert!(notes >= 1, "{}: the note that the name is written with no `use`", who[i]);
    }
}

/// §15.1, S-703: the enumerators of `std.core` (`use std.core.{Some}`, S-659 (1)) too.
#[test]
fn the_failed_use_of_an_enumerator_of_std_core_has_the_note() {
    let uses: Vec<String> =
        ["Some", "None", "Ok", "Err", "panic", "Copy"].iter().map(|n| format!("use std.core.{{{n}}}")).collect();
    for (i, (code, notes, fixes)) in per_use("note_core", &uses).into_iter().enumerate() {
        assert_eq!((code.as_str(), fixes), ("E0302", 0), "{}", uses[i]);
        assert!(notes >= 1, "{}: a note", uses[i]);
    }
}

/// §15.1, S-703: no note when the name is not one of the prelude: a name nothing has, an effect of std (taken
/// from the wrong module, or from `std.core`), a clock name (§11.3).
#[test]
fn a_failed_use_of_a_name_that_is_not_of_the_prelude_has_no_note() {
    let uses: Vec<String> = [
        "use std.option.{Foo}",
        "use std.math.{Foo}",
        "use option.{Foo}",
        "use std.option.Foo",
        "use std.core.{Fs}",
        "use std.math.{Fs}",
        "use std.math.{sample}",
        "use std.core.{Nope}",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    for (i, (code, notes, fixes)) in per_use("note_none", &uses).into_iter().enumerate() {
        assert_eq!((code.as_str(), notes, fixes), ("E0302", 0, 0), "{}", uses[i]);
    }
}

/// §15.1, S-703: in a list the note is for the names of the prelude; `Foo` gets none, and a list of names
/// that are not of the prelude gets no note at all.
#[test]
fn the_note_is_for_the_prelude_names_of_a_list() {
    let uses: Vec<String> = [
        "use std.option.{Option, Foo}",
        "use std.option.{Foo, Option}",
        "use std.option.{Foo, Bar}",
        "use std.option.{Option, Result}",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    let got = per_use("note_list", &uses);
    assert_eq!(got[0].1, 1, "{{Option, Foo}}: one note, for `Option`");
    assert_eq!(got[1].1, 1, "{{Foo, Option}}: one note, for `Option`");
    assert_eq!(got[2].1, 0, "{{Foo, Bar}}: none");
    assert!(got[3].1 >= 1, "{{Option, Result}}: the notes of the two names");
    for (code, _, fixes) in got {
        assert_eq!((code.as_str(), fixes), ("E0302", 0));
    }
}

/// §15.1, S-703: the note is about a `use` of the prelude name, so the E0304 of a name taken again from
/// `std.core` is not an E0302 (no `use`-less note is asked for: it is a different diagnostic), and the right
/// forms (the name written with no `use`) have no diagnostic.
#[test]
fn the_prelude_names_written_with_no_use_pass() {
    let d = Dir::pkg("no_use_needed");
    d.write(
        "main.onsa",
        "pub fn f(o: Option[U32]) -> U32 {\n  match o {\n    Some(v) => v,\n    None => 0,\n  }\n}\n\n\
         pub fn g[T: PartialOrd](x: T) -> T {\n  x\n}\n\npub fn h() uses {Alloc} {}\n",
    );
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "{doc}");
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}
