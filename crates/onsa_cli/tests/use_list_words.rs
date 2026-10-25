//! A reserved word or a keyword in a list of `use` is the failed name of that element only, the elements
//! after it are read and taken, and a list that is really cut still silences its module (spec §15.1, §2.2,
//! §18.1; R-272, S-462, S-596; W4-03 U3d/t).
//!
//! What the spec fixes, and so what is checked here:
//! - the name a `use` takes (an element of a list, or the last name of a path) is read as the name of a
//!   declaration: a keyword is E0002, a reserved word is E0200. The word is the failed name of that
//!   element only (S-462, the 69th supplement): the other elements of the list are taken, wherever the word
//!   stands (first, in the middle, last), and the module is not silenced for the names that no `use` takes
//!   (`zzz` is E0302, as it is with the path form `use kp.clock`);
//! - one report for the `use`, whatever the number of its failed names (§18.1, one unit, the first error);
//! - a `pub use` with such a word in its list is one diagnostic (the word, a syntax-stage error, ends the
//!   unit before the E0200 of the `pub`), its names that were read are failed names for the other modules that
//!   take them (`use main.{g}` is silent), and the module is not silenced (`use main.{zzz}` is E0302);
//! - a list that is cut in the middle (`3` is no name) is the other kind (§18.1: the names it did not read are
//!   not known): the names read before the cut are failed names, and the module of the `use` is silenced for the
//!   names it did not find. A cut `pub use` is read as far as it was read: for the other modules the names
//!   before the cut are failed names and the names after it are not there (E0302, S-596).
//!
//! The same cases, with the places of the marks, are `tests/spec/packages/use_list_words`.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause.

mod test_support;

use std::collections::BTreeSet;
use std::path::Path;

use serde_json::Value;
use test_support::*;

fn check_json(cwd: &Path) -> (Out, Value) {
    let out = run(cwd, &["check", "--json", "."]);
    let doc = doc_of(&out);
    (out, doc)
}

/// `(file, line, code)` of every diagnostic.
fn found(doc: &Value) -> BTreeSet<(String, u64, String)> {
    diagnostics(doc)
        .iter()
        .map(|d| {
            let sp = span_of(&d["span"]);
            (sp.file, sp.line, str_of(d, "code").to_string())
        })
        .collect()
}

fn want(items: &[(&str, u64, &str)]) -> BTreeSet<(String, u64, String)> {
    items.iter().map(|(f, l, c)| (f.to_string(), *l, c.to_string())).collect()
}

const KP: &str = "pub fn g() -> I32 {\n  1\n}\n\npub fn h() -> I32 {\n  2\n}\n";

/// The words: a reserved word is E0200, a keyword is E0002 (§2.2, §15.1).
const WORDS: [(&str, &str); 9] = [
    ("clock", "E0200"),
    ("when", "E0200"),
    ("reset_if", "E0200"),
    ("ser", "E0200"),
    ("static", "E0200"),
    ("match", "E0002"),
    ("test", "E0002"),
    ("self", "E0002"),
    ("fn", "E0002"),
];

/// The body that follows the `use` of the first line: a name no `use` takes (line 4), and a call of `g` and of
/// `h` as a `Bool` (lines 8 and 12), which is E0401 when the name is bound to the function.
const BODY: &str = "\npub fn no_such_name() -> I32 {\n  zzz()\n}\n\npub fn bound_g() -> I32 {\n  let _: Bool = g()\n  0\n}\n\npub fn bound_h() -> I32 {\n  let _: Bool = h()\n  0\n}\n";

fn package(tag: &str, main: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("kp.onsa", KP);
    d.write("main.onsa", main);
    d
}

/// §15.1, §18.1, S-462 (the 69th supplement), R-272: the word is the failed name of its element only, wherever it
/// stands in the list: the line has the one diagnostic of the word, `g` and `h` are taken (E0401 at the calls
/// as `Bool`), and `zzz` is E0302.
#[test]
fn a_word_in_a_list_fails_its_own_name_only() {
    let mut problems = Vec::new();
    for (word, code) in WORDS {
        for (pos, list) in
            [("first", format!("{word}, g, h")), ("middle", format!("g, {word}, h")), ("last", format!("g, h, {word}"))]
        {
            let d = package(&format!("words_{word}_{pos}"), &format!("use kp.{{{list}}}\n{BODY}"));
            let (out, doc) = check_json(d.root());
            let expected = want(&[
                ("main.onsa", 1, code),
                ("main.onsa", 4, "E0302"),
                ("main.onsa", 8, "E0401"),
                ("main.onsa", 13, "E0401"),
            ]);
            if out.code != 1 || found(&doc) != expected {
                problems.push(format!("{word} {pos}: want {expected:?}, exit code 1: {}", doc["diagnostics"]));
            }
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1, §18.1: the path form with the same words (the last name of a path with no list) fails its name only
/// and the module is not silenced: the line has the diagnostic of the word and `zzz` is E0302.
#[test]
fn a_word_at_the_end_of_a_path_fails_its_name_and_silences_nothing() {
    let mut problems = Vec::new();
    for (word, code) in WORDS {
        let d = package(&format!("words_path_{word}"), &format!("use kp.{word}\n{BODY}"));
        let (out, doc) = check_json(d.root());
        let expected = want(&[("main.onsa", 1, code), ("main.onsa", 4, "E0302")]);
        // `g` and `h` are not taken here: they are not names of the module, so they are E0302 too.
        let got: BTreeSet<_> = found(&doc).into_iter().filter(|(_, l, _)| *l <= 4).collect();
        if out.code != 1 || got != expected {
            problems
                .push(format!("{word}: want {expected:?} on the lines 1 to 4, exit code 1: {}", doc["diagnostics"]));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1: two words in one list are one report for the `use` (one unit, the first error), and the elements
/// that are names are taken.
#[test]
fn two_words_in_one_list_are_one_report_and_the_names_are_taken() {
    for (tag, list) in [("a", "clock, g, match, h"), ("b", "match, g, clock, h"), ("c", "g, static, h, test")] {
        let d = package(&format!("words_two_{tag}"), &format!("use kp.{{{list}}}\n{BODY}"));
        let (out, doc) = check_json(d.root());
        assert_eq!(out.code, 1, "{tag}: {doc}");
        let on_line_1: Vec<_> = found(&doc).into_iter().filter(|(_, l, _)| *l == 1).collect();
        assert_eq!(on_line_1.len(), 1, "{tag}: one report for the use: {}", doc["diagnostics"]);
        assert!(matches!(on_line_1[0].2.as_str(), "E0200" | "E0002"), "{tag}: {}", doc["diagnostics"]);
        let rest: BTreeSet<_> = found(&doc).into_iter().filter(|(_, l, _)| *l > 1).collect();
        assert_eq!(
            rest,
            want(&[("main.onsa", 4, "E0302"), ("main.onsa", 8, "E0401"), ("main.onsa", 13, "E0401")]),
            "{tag}: {doc}"
        );
    }
}

/// §15.1, §18.1, S-462: the name taken after the word is a binding, so a later `use` of the same name clashes
/// with it (E0304 on the later `use`, whose line is the second), and so does an item of the module (the
/// `use` gets the E0304 whichever is written first, so the E0304 is on the line of the list: but that line
/// has the diagnostic of the word, one report for the `use`).
#[test]
fn a_name_after_the_word_is_a_binding_that_clashes() {
    let d = Dir::pkg("words_clash");
    d.write("kp.onsa", KP);
    d.write("other.onsa", "pub fn h() -> I32 {\n  3\n}\n");
    d.write("main.onsa", "use kp.{g, match, h}\nuse other.{h}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{doc}");
    assert_eq!(found(&doc), want(&[("main.onsa", 1, "E0002"), ("main.onsa", 2, "E0304")]), "{doc}");
}

/// §15.1, §18.1, S-596, S-462: a `pub use` with a word in its list is the one diagnostic of the word. The names it
/// read (`g`, `h`) are failed names for the module that takes them from here, so `use main.{h}` is silent,
/// and the module is not silenced, so `use main.{zzz}` is E0302.
#[test]
fn a_pub_use_with_a_word_in_its_list_has_failed_names_for_the_other_modules() {
    let mut problems = Vec::new();
    for (word, code) in WORDS {
        let d = Dir::pkg(&format!("words_pub_{word}"));
        d.write("kp.onsa", KP);
        d.write("main.onsa", &format!("pub use kp.{{g, {word}, h}}\n"));
        d.write("user.onsa", "use main.{g}\nuse main.{h}\nuse main.{zzz}\n\npub fn silent() -> I32 {\n  let _: Bool = g()\n  let _: Bool = h()\n  0\n}\n");
        let (out, doc) = check_json(d.root());
        let expected = want(&[("main.onsa", 1, code), ("user.onsa", 3, "E0302")]);
        if out.code != 1 || found(&doc) != expected || diagnostics(&doc).len() != 2 {
            problems.push(format!("{word}: want {expected:?}, exit code 1: {}", doc["diagnostics"]));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1, R-180: a list that is cut at `3` is one E0002, and the module is silenced for the names that no `use`
/// takes: the names read before the cut (`g`), the names after it (`h`) and `zzz` are silent at their uses.
#[test]
fn a_cut_list_silences_its_module() {
    let d = package(
        "cut_silences",
        "use kp.{g, 3, h}\n\npub fn silent() -> I32 {\n  let _: Bool = zzz()\n  let _: Bool = g()\n  let _: Bool = h()\n  0\n}\n",
    );
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{doc}");
    assert_eq!(found(&doc), want(&[("main.onsa", 1, "E0002")]), "{doc}");
}

/// §18.1, S-596: a `pub use` cut at `3`: for the other modules `g` (read before the cut) is a failed name and is
/// silent, and `h` (after the cut, not read) is not there, E0302.
#[test]
fn a_cut_pub_use_has_the_names_before_the_cut_for_the_other_modules() {
    let d = Dir::pkg("cut_pub");
    d.write("kp.onsa", KP);
    d.write("main.onsa", "pub use kp.{g, 3, h}\n");
    d.write("user.onsa", "use main.{g}\nuse main.{h}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1, "{doc}");
    assert_eq!(found(&doc), want(&[("main.onsa", 1, "E0002"), ("user.onsa", 2, "E0302")]), "{doc}");
}

/// §15.1, §2.2: the words before the taken name are names of modules (`use kp.clock.{tick}` takes `tick` of the
/// module `kp.clock` and is fine), the control of the words that are taken.
#[test]
fn a_word_before_the_taken_name_is_a_module_name_and_makes_no_diagnostic() {
    let d = Dir::pkg("words_module_names");
    d.write("kp/clock.onsa", "pub fn tick() -> U32 {\n  1\n}\n");
    d.write("main.onsa", "use kp.clock.{tick}\n\npub fn t() -> U32 {\n  tick()\n}\n");
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// The starts of an item that stand at the head of a line (§18.1), each a whole item. The `true` in a body
/// is an E0401 (it is not an `I32`).
const ITEM_STARTS: [(&str, &str); 8] = [
    ("fn", "fn m() -> I32 {\n  true\n}\n"),
    ("pub_fn", "pub fn m() -> I32 {\n  true\n}\n"),
    ("use", "use kp.{h}\n"),
    ("struct", "struct S {\n  a: I32,\n}\n"),
    ("enum", "enum E {\n  A,\n}\n"),
    ("test", "test \"t\" {\n  assert true\n}\n"),
    ("attribute", "@repr(c)\nstruct S {\n  a: I32,\n}\n"),
    ("doc_comment", "/// doc\nfn m() -> I32 {\n  true\n}\n"),
];

/// §18.1, R-272 (a regression of U3d): a list of a `use` that is not closed ends at the item that starts at the
/// head of the next line, whatever the item starts with (a keyword too: `fn`, `use`, `pub`, `struct`, `enum`,
/// `test`, an attribute, a doc comment). The diagnostic is the E0002 at the `{` that is never closed (line 1,
/// column 8), and the item is read, so the E0401 inside it is reported. The rule of R-272 (read on after a
/// keyword) is for the elements inside the list, not for the head of a line. The tail is one item, or two (the
/// second has an E0401 of its own), or nothing (the end of the file, with the newline or without).
#[test]
fn a_list_that_is_not_closed_ends_at_the_item_on_the_next_line() {
    let mut problems = Vec::new();
    for head in ["use kp.{g,", "use kp.{g"] {
        for (tag, item) in ITEM_STARTS {
            for (shape, tail) in
                [("one_item", item.to_string()), ("two_items", format!("{item}\npub fn bad() -> I32 {{\n  true\n}}\n"))]
            {
                let text = format!("{head}\n{tail}");
                let d = package(&format!("unclosed_{tag}_{shape}"), &text);
                let (out, doc) = check_json(d.root());
                let mut expected = vec![("main.onsa", 1, "E0002".to_string())];
                for l in text.lines().enumerate().filter(|(_, l)| *l == "  true").map(|(i, _)| i as u64 + 1) {
                    expected.push(("main.onsa", l, "E0401".to_string()));
                }
                let expected: BTreeSet<(String, u64, String)> =
                    expected.into_iter().map(|(f, l, c)| (f.to_string(), l, c)).collect();
                let at_brace = diagnostics(&doc)
                    .iter()
                    .find(|x| str_of(x, "code") == "E0002")
                    .map(|x| (span_of(&x["span"]).line, span_of(&x["span"]).col));
                if out.code != 1 || at_brace != Some((1, 8)) || found(&doc) != expected {
                    problems.push(format!(
                        "`{head}` then {tag} ({shape}): want {expected:?} with the E0002 at 1:8: {}",
                        doc["diagnostics"]
                    ));
                }
            }
        }
        for (shape, text) in [("eof_newline", format!("{head}\n")), ("eof", head.to_string())] {
            let d = package(&format!("unclosed_{shape}"), &text);
            let (out, doc) = check_json(d.root());
            let only = diagnostics(&doc)
                .first()
                .map(|x| (str_of(x, "code").to_string(), span_of(&x["span"]).line, span_of(&x["span"]).col));
            if out.code != 1 || diagnostics(&doc).len() != 1 || only != Some(("E0002".to_string(), 1, 8)) {
                problems.push(format!("`{head}` then {shape}: want one E0002 at 1:8: {}", doc["diagnostics"]));
            }
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1, R-272: the control is a list that is closed: a keyword inside it is the error of that element (the E0002
/// at the word, not at a `{`), the list is read on, and the items after it are read (the E0401 of `bad`;
/// `zzz`, which no `use` takes, is E0302, since the list was read to its end).
#[test]
fn a_keyword_inside_a_closed_list_is_read_on() {
    for word in ["fn", "use", "pub", "struct", "enum", "test", "match"] {
        let text = format!(
            "use kp.{{g, {word}, h}}\n\npub fn bad() -> I32 {{\n  true\n}}\n\npub fn none() -> I32 {{\n  zzz()\n}}\n"
        );
        let d = package(&format!("closed_{word}"), &text);
        let (out, doc) = check_json(d.root());
        assert_eq!(out.code, 1, "{word}: {doc}");
        assert_eq!(
            found(&doc),
            want(&[("main.onsa", 1, "E0002"), ("main.onsa", 4, "E0401"), ("main.onsa", 8, "E0302")]),
            "{word}: {}",
            doc["diagnostics"]
        );
        let e = diagnostics(&doc).iter().find(|x| str_of(x, "code") == "E0002").unwrap();
        assert_ne!(span_of(&e["span"]).col, 8, "{word}: the E0002 is at the word");
    }
}
