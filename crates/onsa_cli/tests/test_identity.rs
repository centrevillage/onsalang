//! How `onsa test` identifies a test, writes its name, selects it with `--filter`, and which names
//! a `test` may carry (spec §11.8, §18.2; `docs/onsa-tools.md` §4; S-55, S-215, S-233, S-242,
//! S-244; W2-10).
//!
//! What the spec fixes, and so what is checked here:
//! - a test is identified by the path of its module and its name, so the same name in two modules
//!   is two tests (§11.8). The module path is the path of the file from the package root with `.`
//!   between the parts (`dsp.voice` for `dsp/voice.onsa`, §15.1), and for a single file with no
//!   manifest it is the name of the file (`dsp` for `dsp.onsa`, §11.8);
//! - the result lines are `test <full name text> ok` and `test <full name text> failed at
//!   <file>:<line>: <message>`. The full name text is the module path, one space, and the name
//!   written as a string literal of Onsa: in quotes, with `\` as `\\`, `"` as `\"`, `{` as `{{` and
//!   `}` as `}}`, and every other character as it is (§11.8, S-244). The order of the lines, the
//!   summary line, and the lines of a diagnostic are not fixed, so only the lines that start with
//!   `test ` are read, as a set. The file in a `failed at` line is the one of `span.file` of the
//!   JSON record of the same run (the package-relative path with `/`, §18.1);
//! - `--filter <text>` runs the tests whose full name text contains `<text>` as a substring: by
//!   code points, case sensitive, no normalization, the empty text matches all, and no match at
//!   all is a usage error (exit code 2, nothing on the standard output, with `--json` too, §18.2);
//!   an empty `--filter` is the same as no filter, so a package without tests succeeds with it
//!   (the answer to S-286, (e2)); there can be one `--filter` only;
//! - the checks come first: a diagnostic of the package stops the command before the filter is
//!   matched, wherever the diagnostic is and whatever the filter selects (§18.2);
//! - the name of a `test` is a string literal with no interpolation, not empty, and with no control
//!   character (U+0000..U+001F and U+007F..U+009F, so no LF and no tab), no U+2028 / U+2029 and no
//!   bidirectional control (U+202A..U+202E, U+2066..U+2069) in its value, also when it is written
//!   with an escape. A name that breaks this is E0002 of the syntax stage with a note and no fix
//!   (the answer to S-244 in the W2/W3 gap notes). Written raw, those characters stay the E0001
//!   of §2.5 (a tab is allowed in a literal, so a raw tab is the E0002 of the name rule).
//!
//! Not written here: the JSON document (test_json_document.rs), the E0200 reached from the tests
//! that run (W2-13), nesting of tests (not in the language), the wording of a panic.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use test_support::*;

// ---------------------------------------------------------------- the module path in the lines

const OK_TEST: &str = "test \"decays\" {\n  assert 1 == 1\n}\n";

fn identity_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("top.onsa", OK_TEST);
    d.write("dsp.onsa", OK_TEST);
    d.write("dsp/voice.onsa", &format!("{OK_TEST}\ntest \"rings\" {{\n  assert 1 == 2\n}}\n"));
    d.write("dsp/filter.onsa", OK_TEST);
    d
}

/// Spec §11.8: the same name in four modules is four tests, each reported under its module.
#[test]
fn a_result_line_names_the_module_path() {
    let d = identity_package("lines");
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let lines = sorted_result_lines(&out);

    // The failed line carries a file, which is the `span.file` of the same run's JSON record.
    let (_, doc) = test_json(d.root(), &[&d.arg()]);
    let rec = record(&doc, "dsp.voice", "rings");
    let f = failure_of(rec);
    let sp = span_of(&f["span"]);
    assert_eq!(sp.file, "dsp/voice.onsa");
    assert_eq!(sp.line, 6);
    assert_eq!(str_of(f, "message"), "assert 1 == 2");

    let mut want = vec![
        "test top \"decays\" ok".to_string(),
        "test dsp \"decays\" ok".to_string(),
        "test dsp.filter \"decays\" ok".to_string(),
        "test dsp.voice \"decays\" ok".to_string(),
        format!("test dsp.voice \"rings\" failed at {}:6: assert 1 == 2", sp.file),
    ];
    want.sort();
    assert_eq!(lines, want, "{}", out.stdout);
}

/// Spec §11.8: for a single file with no manifest the module path is the file name (`dsp` for
/// `dsp.onsa`, wherever the file is), and the example line of `docs/onsa-tools.md` §4 shows the
/// file as `dsp.onsa:12`. The file in the line is the path as it was passed, with `/` (§18.1).
#[test]
fn a_single_file_is_a_module_of_its_file_name() {
    for (tag, rel) in [("single", "dsp.onsa"), ("single_sub", "sub/dsp.onsa")] {
        let d = Dir::bare(tag);
        d.write(
            rel,
            "pub fn gain() -> I32 {\n  2\n}\n\ntest \"decays\" {\n  assert gain() == 2\n}\n\ntest \"rings\" {\n  assert gain() == 3\n}\n",
        );
        let out = run(d.root(), &["test", rel]);
        assert_eq!(out.code, 1, "{rel}: {}{}", out.stdout, out.stderr);
        let mut want = vec![
            "test dsp \"decays\" ok".to_string(),
            format!("test dsp \"rings\" failed at {rel}:10: assert gain() == 3"),
        ];
        want.sort();
        assert_eq!(sorted_result_lines(&out), want, "{rel}: {}", out.stdout);

        let (_, doc) = test_json(d.root(), &[rel]);
        assert_eq!(
            identities(&doc),
            [("dsp".to_string(), "decays".to_string()), ("dsp".to_string(), "rings".to_string())],
            "{rel}"
        );
        let f = failure_of(record(&doc, "dsp", "rings"));
        assert_eq!(span_of(&f["span"]).file, rel);
    }
}

// ---------------------------------------------------------------- the name as a literal

/// `(the name as written between the quotes, the name in the text of a result line, the value)`.
/// The text escapes `\`, `"`, `{` and `}` and nothing else (§11.8, S-244); the value is the name
/// after the escapes of the literal are read (`name` of the JSON record).
const NAMES: &[(&str, &str, &str)] = &[
    (r#"q\"uote"#, r#"q\"uote"#, "q\"uote"),
    (r"back\\slash", r"back\\slash", "back\\slash"),
    ("braces {{x}}", "braces {{x}}", "braces {x}"),
    ("{{{{", "{{{{", "{{"),
    ("}}", "}}", "}"),
    ("it's", "it's", "it's"),
    (r"\'", "'", "'"),
    (" pad ", " pad ", " pad "),
    ("日本語 ✓", "日本語 ✓", "日本語 ✓"),
    (r"e\u{301}", "e\u{301}", "e\u{301}"),
    (r"\u{e9}", "é", "é"),
    (r"\u{1f600}", "\u{1f600}", "\u{1f600}"),
    (r"\u{22}", r#"\""#, "\""),
    (r"\u{5c}", r"\\", "\\"),
    ("a b", "a b", "a b"),
];

fn names_source() -> String {
    NAMES.iter().map(|(src, _, _)| format!("test \"{src}\" {{\n  assert true\n}}\n")).collect::<Vec<_>>().join("\n")
}

/// Spec §11.8, S-244: the text of a name is a string literal with four characters escaped, and
/// the JSON `name` is the value. Every name here is accepted and distinct.
#[test]
fn a_name_is_written_as_a_string_literal_in_the_text_and_as_its_value_in_json() {
    let d = Dir::bare("names");
    d.write("m.onsa", &names_source());
    let out = run(d.root(), &["test", "m.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let mut want: Vec<String> = NAMES.iter().map(|(_, text, _)| format!("test m \"{text}\" ok")).collect();
    want.sort();
    assert_eq!(sorted_result_lines(&out), want, "{}", out.stdout);

    let (out, doc) = test_json(d.root(), &["m.onsa"]);
    assert_eq!(out.code, 0, "{}", out.stdout);
    let mut got: Vec<String> = identities(&doc).into_iter().map(|(m, n)| format!("{m}|{n}")).collect();
    got.sort();
    let mut want: Vec<String> = NAMES.iter().map(|(_, _, v)| format!("m|{v}")).collect();
    want.sort();
    assert_eq!(got, want);
}

// ---------------------------------------------------------------- --filter

/// `(module, name value, full name text)` of the tests of the filter package.
const ENTRIES: &[(&str, &str, &str)] = &[
    ("top", "decays", "top \"decays\""),
    ("top", "Decays", "top \"Decays\""),
    ("dsp.voice", "decays", "dsp.voice \"decays\""),
    ("dsp.voice", "rings", "dsp.voice \"rings\""),
    ("dsp.voice", "q\"uote", r#"dsp.voice "q\"uote""#),
    ("dsp.voice", "a{b}", "dsp.voice \"a{{b}}\""),
    ("dsp.voice", "é", "dsp.voice \"é\""),
    ("dsp.voice", "日本語", "dsp.voice \"日本語\""),
];

fn filter_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    let t = |name: &str| format!("test \"{name}\" {{\n  assert true\n}}\n");
    d.write("top.onsa", &format!("{}\n{}", t("decays"), t("Decays")));
    d.write(
        "dsp/voice.onsa",
        &[t("decays"), t("rings"), t(r#"q\"uote"#), t("a{{b}}"), t(r"\u{e9}"), t("日本語")].join("\n"),
    );
    d
}

const ALL: &[usize] = &[0, 1, 2, 3, 4, 5, 6, 7];
const VOICE: &[usize] = &[2, 3, 4, 5, 6, 7];

/// Spec §18.2: a substring of the full name text, by code points, case sensitive; the empty text
/// matches all; the separator of module and name is exactly one space; the quotes and the escapes
/// are part of the text.
#[test]
fn filter_matches_a_substring_of_the_full_name_text() {
    let d = filter_package("filter");
    let table: &[(&str, &[usize])] = &[
        ("", ALL),
        ("decays", &[0, 2]),
        ("Decays", &[1]),
        ("ecays", &[0, 1, 2]),
        ("rings", &[3]),
        ("dsp.voice", VOICE),
        ("dsp", VOICE),
        ("voice \"", VOICE),
        ("top \"D", &[1]),
        ("\"decays\"", &[0, 2]),
        ("s\"", &[0, 1, 2, 3]),
        (" \"", ALL),
        ("\"", ALL),
        // The text of the name with a quote has a backslash before the quote.
        ("q\\\"u", &[4]),
        ("{{b}}", &[5]),
        ("é", &[6]),
        ("日本", &[7]),
        ("本語", &[7]),
    ];
    for (filter, picked) in table {
        let out = run(d.root(), &["test", "--filter", filter, &d.arg()]);
        assert_eq!(out.code, 0, "--filter {filter:?}: {}{}", out.stdout, out.stderr);
        let mut want: Vec<String> = picked.iter().map(|&i| format!("test {} ok", ENTRIES[i].2)).collect();
        want.sort();
        assert_eq!(sorted_result_lines(&out), want, "--filter {filter:?}: {}", out.stdout);

        let (jout, doc) = test_json(d.root(), &["--filter", filter, &d.arg()]);
        assert_eq!(jout.code, 0, "--filter {filter:?}: {}", jout.stdout);
        let mut got: Vec<(String, String)> = identities(&doc);
        got.sort();
        let mut want: Vec<(String, String)> =
            picked.iter().map(|&i| (ENTRIES[i].0.to_string(), ENTRIES[i].1.to_string())).collect();
        want.sort();
        assert_eq!(got, want, "--filter {filter:?} (json)");
    }
}

/// Spec §18.2: no match at all is a usage error, exit code 2, and §18.2 (`--json`): a code 2 with
/// no diagnostic prints nothing on the standard output, with `--json` too.
#[test]
fn a_filter_that_matches_nothing_is_a_usage_error() {
    let d = filter_package("nomatch");
    for filter in [
        "zzz",
        "DSP",
        "Rings",
        "É",
        // No normalization: the text has U+00E9, this is `e` and U+0301.
        "e\u{301}",
        // The name is quoted, and one space separates the module from it.
        "dsp.voice decays",
        "dsp voice",
        "top  \"decays",
        " top",
        // The result line starts with `test`, the full name text does not.
        "test top",
        // The quote of the name is escaped in the text, the brace too.
        "q\"u",
        "a{b}",
    ] {
        for json in [false, true] {
            let mut args = vec!["test"];
            if json {
                args.push("--json");
            }
            args.extend(["--filter", filter]);
            let root = d.arg();
            args.push(&root);
            let out = run(d.root(), &args);
            assert_eq!(out.code, 2, "{args:?}: {}{}", out.stdout, out.stderr);
            assert_eq!(out.stdout, "", "{args:?}: a usage error prints nothing on the standard output");
            assert!(!out.stderr.trim().is_empty(), "{args:?}: the reason goes to the standard error");
        }
    }
}

/// Spec §18.2: `--filter` can be written once. A second one is not something the command takes.
#[test]
fn two_filters_are_a_usage_error() {
    let d = filter_package("twice");
    let root = d.arg();
    let out = run(d.root(), &["test", "--filter", "rings", "--filter", "decays", &root]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout, "");
}

/// A filter that selects failing and passing tests exits with 1 (a failed test, §18.2) and reports
/// only the selected ones.
#[test]
fn filter_selects_among_failures_and_the_exit_code_follows_the_selected_tests() {
    let d = identity_package("filter_exit");
    let root = d.arg();
    let out = run(d.root(), &["test", "--filter", "dsp.filter", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(sorted_result_lines(&out), ["test dsp.filter \"decays\" ok"]);

    // The failing test of dsp.voice is not selected, so it does not fail the run.
    let out = run(d.root(), &["test", "--filter", "decays", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(result_lines(&out).len(), 4, "{}", out.stdout);

    let out = run(d.root(), &["test", "--filter", "rings", &root]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(result_lines(&out).len(), 1, "{}", out.stdout);
}

/// Spec §18.2 and the answer to S-286 ((e2), 2026-10-08): an empty `--filter` is the same as no
/// filter, so on a package without tests it runs nothing and succeeds (exit code 0, `tests` is an
/// empty array), as the run without `--filter`; it is not the usage error of a filter that selects
/// nothing.
#[test]
fn an_empty_filter_on_a_package_without_tests_is_no_filter() {
    let d = Dir::pkg("empty_filter_no_tests");
    d.write("a.onsa", "pub fn gain() -> I32 {\n  2\n}\n");
    let root = d.arg();
    for args in [vec!["test", "--filter", "", &root], vec!["test", &root]] {
        let out = run(d.root(), &args);
        assert_eq!(out.code, 0, "{args:?}: {}{}", out.stdout, out.stderr);
        assert!(result_lines(&out).is_empty(), "{args:?}: {}", out.stdout);
    }
    let (out, doc) = test_json(d.root(), &["--filter", "", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    assert!(tests_of(&doc).is_empty(), "{doc}");
}

// ---------------------------------------------------------------- a message of several lines

/// A failed `assert` whose expression is written on two lines (`assert (1 == 1) &&` and
/// `(2 == 3)`), next to a failed one on one line.
const MULTI_LINE: &str = "test \"multi\" {\n  assert (1 == 1) &&\n(2 == 3)\n}\n\ntest \"one\" {\n  assert 1 == 2\n}\n";

/// `docs/onsa-tools.md` §4 and the answer to S-284 ((t3), 2026-10-08): the message of a failed test
/// that has several lines puts its first line on the `failed at` line of the test and each of the
/// others on a line of its own that starts with a space, so the lines that start with `test` are
/// the lines of the tests. The lines are split at the line breaks of §2.5 (LF and CR LF), and the
/// width of the indentation is not fixed. The `message` of the JSON record stays the source of the
/// expression as written (§18.1, the answer (a)).
#[test]
fn a_message_of_several_lines_goes_on_indented_lines_after_the_line_of_the_test() {
    for (tag, newline) in [("lf", "\n"), ("crlf", "\r\n")] {
        let d = Dir::pkg(&format!("multi_line_{tag}"));
        d.write("m.onsa", &MULTI_LINE.replace('\n', newline));
        let root = d.arg();
        let out = run(d.root(), &["test", &root]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert!(!out.stdout.contains('\r'), "{tag}: {:?}", out.stdout);
        assert_eq!(
            sorted_result_lines(&out),
            [
                "test m \"multi\" failed at m.onsa:2: assert (1 == 1) &&",
                "test m \"one\" failed at m.onsa:7: assert 1 == 2"
            ],
            "{tag}: {}",
            out.stdout
        );
        let lines: Vec<&str> = out.stdout.lines().collect();
        let at = lines.iter().position(|l| l.starts_with("test m \"multi\"")).unwrap();
        let next = lines[at + 1];
        assert!(next.starts_with(' ') && next.trim() == "(2 == 3)", "{tag}: {:?}", out.stdout);
        assert!(lines[at + 2].starts_with("test ") || !lines[at + 2].starts_with(' '), "{tag}: {:?}", out.stdout);

        if tag == "lf" {
            let (_, doc) = test_json(d.root(), &[&root]);
            assert_eq!(
                str_of(failure_of(record(&doc, "m", "multi")), "message"),
                "assert (1 == 1) &&\n(2 == 3)",
                "{doc}"
            );
        }
    }
}

/// Spec §18.1, §2.5 and the answer to S-284 (2026-10-08): the line breaks of the `message` of a
/// failed `assert` are LF, also when the file has CR LF (a CR LF is one line break, as `onsa fmt`
/// makes it LF), so the message does not depend on the line breaks of the machine. The rest of the
/// source of the expression is as written.
#[test]
fn the_message_of_an_assert_in_a_file_with_cr_lf_has_lf_line_breaks() {
    let d = Dir::pkg("multi_line_crlf_message");
    d.write("m.onsa", &MULTI_LINE.replace('\n', "\r\n"));
    let root = d.arg();
    let (out, doc) = test_json(d.root(), &[&root]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(str_of(failure_of(record(&doc, "m", "multi")), "message"), "assert (1 == 1) &&\n(2 == 3)", "{doc}");
    assert_eq!(str_of(failure_of(record(&doc, "m", "one")), "message"), "assert 1 == 2", "{doc}");
}

// ---------------------------------------------------------------- the order of the checks

const BROKEN_FN: &str = "pub fn f() -> I32 {\n  y\n}\n";
const UNSUPPORTED: &str = "target fn open() -> I32\n";

/// Spec §18.2: the checks of the whole package come before the match of the filter, so a
/// diagnostic in a module the filter does not select still stops the run, with exit code 1 (not
/// the 2 of a filter without a match), and no test runs.
#[test]
fn diagnostics_of_the_package_come_before_the_filter() {
    for (tag, broken, code) in [("e0302", BROKEN_FN, "E0302"), ("e0200", UNSUPPORTED, "E0200")] {
        let d = Dir::pkg(tag);
        d.write("a.onsa", broken);
        d.write("b.onsa", "test \"fine\" {\n  assert true\n}\n");
        let root = d.arg();
        for filter in ["fine", "nomatch", "", "a"] {
            let out = run(d.root(), &["test", "--filter", filter, &root]);
            assert_eq!(out.code, 1, "{code} --filter {filter:?}: {}{}", out.stdout, out.stderr);
            assert!(out.stdout.contains(&format!("error[{code}]")), "{code} --filter {filter:?}: {}", out.stdout);
            assert!(result_lines(&out).is_empty(), "no test runs: {}", out.stdout);

            let (jout, doc) = test_json(d.root(), &["--filter", filter, &root]);
            assert_eq!(jout.code, 1);
            assert!(diagnostics(&doc).iter().any(|x| str_of(x, "code") == code), "{code} --filter {filter:?}: {doc}");
            assert!(tests_of(&doc).is_empty(), "{code} --filter {filter:?}: {doc}");
        }
    }
}

// ---------------------------------------------------------------- what a test name may be

/// Runs `onsa check --json` on one file `m.onsa` with `src` and returns the document.
fn check_one(d: &Dir, src: &str) -> (Out, serde_json::Value) {
    d.write("m.onsa", src);
    let out = run(d.root(), &["check", "--json", "m.onsa"]);
    let doc = doc_of(&out);
    (out, doc)
}

/// The names that break the rule, each as the text between the quotes. Every one is E0002 of the
/// syntax stage: no interpolation, not empty, and no control, line separator or bidirectional
/// control in the value, also when the character is written with an escape.
const BAD_NAMES: &[(&str, &str)] = &[
    ("empty", ""),
    ("interpolation", "a{p}b"),
    ("interpolation alone", "{p}"),
    ("interpolation of a field", "at {p.x}"),
    ("lf", r"a\nb"),
    ("tab", r"a\tb"),
    ("cr", r"a\rb"),
    ("nul", r"a\0b"),
    ("c0 first", r"a\u{1}b"),
    ("escape", r"esc \u{1b}[31mred"),
    ("c0 last", r"a\u{1f}b"),
    ("delete", r"a\u{7f}b"),
    ("c1 first", r"a\u{80}b"),
    ("next line", r"a\u{85}b"),
    ("c1 last", r"a\u{9f}b"),
    ("line separator", r"a\u{2028}b"),
    ("paragraph separator", r"a\u{2029}b"),
    ("embedding", r"a\u{202a}b"),
    ("override", r"a\u{202e}b"),
    ("isolate", r"a\u{2066}b"),
    ("pop isolate", r"a\u{2069}b"),
];

/// Spec §11.8 with S-244: each bad name is one E0002, on the line of the `test`, with a note that
/// states the rule and no fix candidate (the answer to S-244).
#[test]
fn a_name_that_breaks_the_rule_is_e0002_with_a_note_and_no_fix() {
    let d = Dir::bare("bad_names");
    for (what, name) in BAD_NAMES {
        let src = format!("pub fn keep() -> I32 {{\n  1\n}}\n\ntest \"{name}\" {{\n  assert true\n}}\n");
        let (out, doc) = check_one(&d, &src);
        assert_eq!(out.code, 1, "{what}: {}{}", out.stdout, out.stderr);
        let ds = diagnostics(&doc);
        assert_eq!(ds.len(), 1, "{what}: one diagnostic: {doc}");
        let x = &ds[0];
        assert_eq!(str_of(x, "code"), "E0002", "{what}: {x}");
        assert_eq!(span_of(&x["span"]).line, 5, "{what}: the diagnostic is on the line of the `test`: {x}");
        assert!(array_of(x, "fixes").is_empty(), "{what}: no fix candidate: {x}");
        assert!(!array_of(x, "notes").is_empty(), "{what}: a note states the rule: {x}");
    }
}

/// The names at the edges of the rule are accepted: the neighbours of the forbidden ranges (U+0020,
/// U+00A0, and the code points next to U+2028..U+2029, U+202A..U+202E and U+2066..U+2069), a name
/// of one space, and an escaped brace. Distinct names, so no E0306.
#[test]
fn names_next_to_the_forbidden_ones_are_accepted() {
    let d = Dir::bare("good_names");
    let names =
        [" ", r"\u{20}x", r"a\u{a0}b", r"a\u{2027}b", r"a\u{202f}b", r"a\u{2065}b", r"a\u{206a}b", "a{{b}}", r"\u{a1}"];
    let src: String =
        names.iter().map(|n| format!("test \"{n}\" {{\n  assert true\n}}\n")).collect::<Vec<_>>().join("\n");
    let (out, doc) = check_one(&d, &src);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// Spec §18.1 (a syntax-stage diagnostic of a unit hides the later stages of that unit and only
/// of that unit) and §18.2 (`fmt` leaves a file with a syntax-stage diagnostic alone, exit code 2):
/// the bad name is one error of the syntax stage, the error in the body of the same test is not
/// reported, another unit is still checked, and `fmt` does not rewrite the file.
#[test]
fn a_bad_name_is_an_error_of_the_syntax_stage() {
    let d = Dir::bare("stage");
    let src = "pub fn g() -> I32 {\n  y\n}\n\ntest \"\" {\n  let a = undefined_name\n  assert a == 1\n}\n";
    let (out, doc) = check_one(&d, src);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let got: Vec<(String, u64)> =
        diagnostics(&doc).iter().map(|x| (str_of(x, "code").to_string(), span_of(&x["span"]).line)).collect();
    assert_eq!(got, [("E0302".to_string(), 2), ("E0002".to_string(), 5)], "{doc}");

    for args in [&["fmt", "--check", "m.onsa"][..], &["fmt", "m.onsa"][..]] {
        let out = run(d.root(), args);
        assert_eq!(out.code, 2, "{args:?}: {}{}", out.stdout, out.stderr);
        assert!(
            out.stdout.contains("error[E0002]"),
            "{args:?}: the diagnostic goes to the standard output: {}",
            out.stdout
        );
        assert_eq!(std::fs::read_to_string(d.root().join("m.onsa")).unwrap(), src, "{args:?}: the file is not written");
    }
}

/// Spec §2.5 and S-244: a control character written raw in a literal is E0001 (a name too), except
/// the tab, which a literal may hold; a raw tab in a name is then the E0002 of the name rule.
#[test]
#[ignore = "W3-04"]
fn raw_characters_in_a_name() {
    let d = Dir::bare("raw");
    let with = |c: char| format!("test \"a{c}b\" {{\n  assert true\n}}\n");

    let (out, doc) = check_one(&d, &with('\t'));
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let codes: Vec<&str> = diagnostics(&doc).iter().map(|x| str_of(x, "code")).collect();
    assert_eq!(codes, ["E0002"], "a raw tab: {doc}");

    for (what, c) in [
        ("U+0001", '\u{1}'),
        ("escape", '\u{1b}'),
        ("delete", '\u{7f}'),
        ("next line", '\u{85}'),
        ("line separator", '\u{2028}'),
        ("override", '\u{202e}'),
        ("isolate", '\u{2066}'),
    ] {
        let (out, doc) = check_one(&d, &with(c));
        assert_eq!(out.code, 1, "{what}: {}{}", out.stdout, out.stderr);
        assert!(
            diagnostics(&doc).iter().any(|x| str_of(x, "code") == "E0001"),
            "{what} written raw in a literal is E0001: {doc}"
        );
        assert!(
            diagnostics(&doc).iter().any(|x| str_of(x, "code") == "E0001" && span_of(&x["span"]).line == 1),
            "{what}: the E0001 is on the line of the `test`: {doc}"
        );
    }
}

/// Spec §11.8: a name is a string literal. These are the E0002 of the name rule too (the
/// lone words and characters are not names), with one diagnostic and no fix.
#[test]
fn a_name_that_is_not_a_string_literal_is_e0002() {
    let d = Dir::bare("not_literal");
    for (what, header) in [("a word", "test decays"), ("a char", "test 'c'"), ("a number", "test 12"), ("none", "test")]
    {
        let (out, doc) = check_one(&d, &format!("{header} {{\n  assert true\n}}\n"));
        assert_eq!(out.code, 1, "{what}: {}{}", out.stdout, out.stderr);
        let ds = diagnostics(&doc);
        assert!(!ds.is_empty(), "{what}: {doc}");
        assert_eq!(str_of(&ds[0], "code"), "E0002", "{what}: {doc}");
        assert!(array_of(&ds[0], "fixes").is_empty(), "{what}: {doc}");
    }
}
