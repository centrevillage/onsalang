//! The position of a failure that `onsa test` reports, for the forms the test
//! ticket of W2-10 did not cover (spec §18.1: `span` is the position of the
//! expression that panicked).
//!
//! The text of a failure (`spec/tools.md` §4, S-299, W5-24 U8) writes the characters that spec §2.5 does not let a
//! source hold as `\u{…}`; `--json` keeps the message. The std helpers that fail with a `Show` of a value
//! (`assert_near`, `std.test.check`) show numbers only, so no test of them holds such a character yet.

use crate::test_support;

use test_support::*;

/// R-185: an index out of range in the target of an assignment panics at the
/// target `xs[i]`, not at the whole statement; the value's own panic is at the
/// value. The text line has the same line.
#[test]
fn an_index_out_of_range_in_an_assignment_is_at_the_target() {
    let src = "test \"write\" {
  var xs: [I32; 2] = [1, 2]
  let i: U32 = 2
  xs[i] = 3
  assert xs[0] == 1
}

test \"value\" {
  var xs: [I32; 2] = [1, 2]
  let i: U32 = 5
  xs[0] = xs[i] + 1
  assert xs[0] == 1
}
";
    let d = Dir::pkg("assign_target");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "write"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 4, 3, 4, 8), "{f}");
    assert!(array_of(f, "calls").is_empty(), "{f}");
    let f = failure_of(record(&doc, "m", "value"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 11, 11, 11, 16), "{f}");

    let text = run(d.root(), &["test", &d.arg()]);
    assert!(
        result_lines(&text).iter().any(|l| l.starts_with("test m \"write\" failed at m.onsa:4: ")),
        "{}",
        text.stdout
    );
}

/// R-188: in a chain of indices the panic is at the element that is out of
/// range: the inner `xs[i]` of `xs[i][0]`, read or written, and the whole
/// `xs[0][i]` when the outer index is the one out of range. A written `xs` is
/// read after the write (an unread binding is an E0309, §5.1), with no blank
/// line before the last test, so that the lines below stay.
#[test]
fn an_index_out_of_range_in_a_chain_is_at_its_own_element() {
    let src = "test \"read\" {
  var xs: [[I32; 2]; 2] = [[0, 0], [0, 0]]
  let i: U32 = 3
  let y = xs[i][0]
  assert y == 0
}

test \"write\" {
  var xs: [[I32; 2]; 2] = [[0, 0], [0, 0]]
  let i: U32 = 3
  xs[i][0] = 1
  assert xs[0][0] == 1
}
test \"write outer\" {
  var xs: [[I32; 2]; 2] = [[0, 0], [0, 0]]
  let i: U32 = 3
  xs[0][i] = 1
  assert xs[0][0] == 1
}
";
    let d = Dir::pkg("index_chain");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    for (name, want) in [
        ("read", span("m.onsa", 4, 11, 4, 16)),
        ("write", span("m.onsa", 11, 3, 11, 8)),
        ("write outer", span("m.onsa", 17, 3, 17, 11)),
    ] {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(span_of(&f["span"]), want, "{name}: {f}");
    }
}

/// The result line of the test `name` of the module `m`, with its `failed at <file>:<line>:` head.
fn failed_at(text: &Out, name: &str) -> String {
    let head = format!("test m \"{name}\" failed at ");
    let lines = result_lines(text);
    let line = lines.iter().find(|l| l.starts_with(&head));
    let line = line.unwrap_or_else(|| panic!("no failed line of {name}: {}", text.stdout));
    line[head.len()..].to_string()
}

/// S-893: the panic of `unwrap` is the `panic` in the body of std. The JSON has it as it is, with
/// the call first in `calls`; the text shows the innermost position out of std (`spec/tools.md`
/// §4). The lines of std are not fixed here.
#[test]
fn a_failed_unwrap_is_in_std_in_the_json_and_at_the_call_in_the_text() {
    let src = "fn get(o: Option[I32]) -> I32 {
  o.unwrap()
}

fn id[T](move o: Option[T]) -> T {
  o.unwrap()
}

fn nested() -> Option[Option[I32]] {
  Some(None)
}

test \"none\" {
  let o: Option[I32] = None
  assert o.unwrap() == 0
}

test \"err\" {
  let r: Result[I32, U32] = Err(1)
  assert r.unwrap() == 0
}

test \"helper\" {
  assert get(None) == 0
}

test \"generic\" {
  let o: Option[U32] = None
  assert id(o) == 0
}

test \"chain\" {
  assert nested().unwrap().unwrap() == 0
}
";
    let d = Dir::pkg("unwrap_std");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let text = run(d.root(), &["test", &d.arg()]);
    // The test, the message, the line of the text, and the start of each of `calls`.
    let none = "called `unwrap()` on `None`";
    let err = "called `unwrap()` on `Err`";
    let cases = [
        ("none", none, 15, &[(15u64, 10u64)][..]),
        ("err", err, 20, &[(20, 10)]),
        ("helper", none, 2, &[(2, 3), (24, 10)]),
        ("generic", none, 6, &[(6, 3), (29, 10)]),
        ("chain", none, 33, &[(33, 10)]),
    ];
    for (name, message, line, calls) in cases {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(span_of(&f["span"]).file, "std/core.onsa", "{name}: {f}");
        assert_eq!(str_of(f, "kind"), "panic", "{name}: {f}");
        let got: Vec<_> = call_spans(f).iter().map(|c| (c.file.clone(), c.line, c.col)).collect();
        let want: Vec<_> = calls.iter().map(|&(l, c)| ("m.onsa".to_string(), l, c)).collect();
        assert_eq!(got, want, "{name}: {f}");
        assert_eq!(failed_at(&text, name), format!("m.onsa:{line}: {message}"), "{name}");
    }
}

/// S-893: a failed `assert` in the Onsa body of std is shown at the call too, and of a helper
/// that calls std, at the call in the helper. The position in std stays in the JSON.
#[test]
fn a_failed_assert_in_the_body_of_std_is_shown_at_the_call() {
    let src = "use std.dsp.test.{impulse, energy}

fn past() -> F64 uses {Alloc} {
  let b = impulse(4)
  energy(b, 0, 9)
}

test \"direct\" {
  let b = impulse(4)
  assert energy(b, 0, 9) == 1.0
}

test \"helper\" {
  assert past() == 1.0
}
";
    let d = Dir::pkg("energy_std");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let text = run(d.root(), &["test", &d.arg()]);
    for (name, line) in [("direct", 10), ("helper", 5)] {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(span_of(&f["span"]).file, "std/dsp/test.onsa", "{name}: {f}");
        let shown = failed_at(&text, name);
        assert!(shown.starts_with(&format!("m.onsa:{line}: ")), "{name}: {shown}");
    }
}

/// S-893: what is out of std is told by the file, not by its name: a file of the user's in a
/// directory `std` (a package cannot have that module, E0304, but a file alone can be there) is
/// out of std, and the failure is shown there and not at the `panic` in `std/core.onsa`.
#[test]
fn a_file_in_a_directory_named_std_is_out_of_std() {
    let d = Dir::bare("own_std_dir");
    d.write("std/m.onsa", "test \"mine\" {\n  let o: Option[I32] = None\n  assert o.unwrap() == 0\n}\n");
    let text = run(d.root(), &["test", "std/m.onsa"]);
    assert_eq!(text.code, 1, "{}{}", text.stdout, text.stderr);
    assert_eq!(failed_at(&text, "mine"), "std/m.onsa:3: called `unwrap()` on `None`");
}

// ---- the unwritable characters in the text of a failure (S-299, W5-24 U8) -------------------------------

/// A character that spec §2.5 does not let a source text hold: a lone CR, a control character other
/// than the TAB and the LF (U+0000 to U+001F, U+007F to U+009F), U+2028, U+2029 and the bidirectional
/// controls (U+202A to U+202E, U+2066 to U+2069).
fn unwritable(c: char) -> bool {
    matches!(c,
        '\u{0}'..='\u{8}' | '\u{b}'..='\u{1f}' | '\u{7f}'..='\u{9f}'
        | '\u{2028}' | '\u{2029}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}')
}

/// The text with every `\u{…}` (1 to 6 hexadecimal digits, any case, any number of leading zeros) read as
/// the character it stands for (spec §2.4). What `onsa test` writes must read back to the message.
fn read_escapes(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(i) = rest.find("\\u{") {
        out.push_str(&rest[..i]);
        let after = &rest[i + 3..];
        let end = after.find('}').unwrap_or_else(|| panic!("an escape that is not closed: {text:?}"));
        let digits = &after[..end];
        assert!((1..=6).contains(&digits.len()), "1 to 6 digits in an escape: {text:?}");
        let value = u32::from_str_radix(digits, 16).unwrap_or_else(|_| panic!("not hexadecimal in {text:?}"));
        out.push(char::from_u32(value).unwrap_or_else(|| panic!("not a scalar value in {text:?}")));
        rest = &after[end + 1..];
    }
    out.push_str(rest);
    out
}

/// The message of the first result line of the test `name` of the module `m`, which is the text after
/// `failed at <file>:<line>: `.
fn failed_message(text: &Out, name: &str) -> String {
    let shown = failed_at(text, name);
    let (_position, message) = shown.split_once(": ").unwrap_or_else(|| panic!("no message in {shown:?}"));
    message.to_string()
}

/// A package `m.onsa` with one test per `(name, message in the source)`, each `panic("<message>")` on line 2
/// of its own three lines. The sources are written as they are in the file (`\u{1b}` is the six characters).
fn panic_tests(tag: &str, messages: &[(String, String)]) -> (Dir, String) {
    let mut src = String::new();
    for (name, message) in messages {
        src.push_str(&format!("test \"{name}\" {{\n  panic(\"{message}\")\n}}\n"));
    }
    let d = Dir::pkg(tag);
    d.write("m.onsa", &src);
    (d, src)
}

#[test]
fn the_text_of_a_failure_writes_the_unwritable_characters_as_an_escape_like_the_spec_example() {
    // S-299, spec/tools.md §4: `panic("a\u{1b}[31m")` is `a\u{1b}[31m` in the failed line: the ESC is the
    // escape and the rest of the text is as it was.
    let (d, _) = panic_tests("example", &[("esc".to_string(), "a\\u{1b}[31m".to_string())]);
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    assert!(out.stdout.lines().any(|l| l == "test m \"esc\" failed at m.onsa:2: a\\u{1b}[31m"), "{:?}", out.stdout);
    assert!(!out.stdout.chars().any(unwritable), "no unwritable character is on the output: {:?}", out.stdout);
    assert!(out.stdout.lines().any(|l| l == "0 passed, 1 failed"), "{:?}", out.stdout);
}

#[test]
fn every_kind_of_unwritable_character_in_a_message_is_an_escape_that_reads_back_to_it() {
    // S-299, §4 and spec §2.5: a lone CR, the controls other than the TAB and the LF (the ends of both
    // ranges and some inside), U+2028, U+2029 and every bidirectional control. Each is the only odd
    // character of the message `x<c>y`, so a line shows which kind is not escaped. The digits of the
    // escape (the case, the leading zeros) are not fixed: it has to read back to the character (§2.4).
    let code_points: [u32; 26] = [
        0x00, 0x01, 0x08, 0x0b, 0x0c, 0x0d, 0x0e, 0x1b, 0x1f, 0x7f, 0x80, 0x85, 0x9f, 0x2028, 0x2029, 0x202a, 0x202b,
        0x202c, 0x202d, 0x202e, 0x2066, 0x2067, 0x2068, 0x2069, 0x1a, 0x90,
    ];
    let messages: Vec<(String, String)> =
        code_points.iter().map(|c| (format!("u+{c:04x}"), format!("x\\u{{{c:x}}}y"))).collect();
    let (d, _) = panic_tests("kinds", &messages);
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    assert!(!out.stdout.chars().any(unwritable), "no unwritable character is on the output: {:?}", out.stdout);
    let mut wrong = Vec::new();
    for (name, _) in &messages {
        let c = char::from_u32(u32::from_str_radix(&name[2..], 16).unwrap()).unwrap();
        let shown = failed_message(&out, name);
        if !shown.contains("\\u{") || read_escapes(&shown) != format!("x{c}y") {
            wrong.push(format!("{name}: {shown:?}"));
        }
    }
    assert!(wrong.is_empty(), "{} of {}:\n{}", wrong.len(), messages.len(), wrong.join("\n"));
}

#[test]
fn the_other_spellings_of_a_lone_cr_and_a_nul_in_the_source_are_escaped_too() {
    // S-299: the value of the message is what is written, not the spelling in the source: `\r` and `\0`
    // (spec §2.4) are a CR and a NUL, and both are escaped.
    let (d, _) =
        panic_tests("spellings", &[("cr".to_string(), "x\\ry".to_string()), ("nul".to_string(), "x\\0y".to_string())]);
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    assert!(!out.stdout.chars().any(unwritable), "{:?}", out.stdout);
    assert_eq!(read_escapes(&failed_message(&out, "cr")), "x\ry");
    assert_eq!(read_escapes(&failed_message(&out, "nul")), "x\0y");
}

#[test]
fn a_message_with_several_unwritable_characters_is_escaped_everywhere_and_the_rest_is_kept() {
    // S-299, §4: an ESC and a RIGHT-TO-LEFT OVERRIDE in one message, and the
    // text round them stays; the escape does not touch `[31m`, nor the letters.
    let (d, _) =
        panic_tests("mixed", &[("mixed".to_string(), "a\\u{1b}[31mb\\u{202E}c\\u{2028}d\\u{7f}e".to_string())]);
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    assert!(!out.stdout.chars().any(unwritable), "{:?}", out.stdout);
    let shown = failed_message(&out, "mixed");
    assert_eq!(read_escapes(&shown), "a\u{1b}[31mb\u{202e}c\u{2028}d\u{7f}e", "{shown:?}");
    assert!(
        shown.starts_with('a') && shown.contains("[31mb") && shown.contains('c') && shown.ends_with('e'),
        "{shown:?}"
    );
}

#[test]
fn the_characters_that_are_writable_stay_as_they_are_in_the_text_of_a_failure() {
    // S-299: only the characters of the closed list are written as an escape. The TAB stays; the
    // neighbours of the ends of each range stay (U+0020, U+007E, U+00A0, U+2027, U+202F, U+2065, U+206A);
    // so do the other format characters (U+200B, U+200E, U+200F, U+FEFF), which are not in the list of the
    // bidirectional controls of §2.5, the letters of other scripts and an emoji.
    let kept: [u32; 15] =
        [0x09, 0x20, 0x7e, 0xa0, 0xe9, 0x2027, 0x202f, 0x2065, 0x206a, 0x200b, 0x200e, 0x200f, 0xfeff, 0x65e5, 0x1f600];
    let messages: Vec<(String, String)> =
        kept.iter().map(|c| (format!("u+{c:04x}"), format!("x\\u{{{c:x}}}y"))).collect();
    let (d, _) = panic_tests("kept", &messages);
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    let mut wrong = Vec::new();
    for (name, _) in &messages {
        let c = char::from_u32(u32::from_str_radix(&name[2..], 16).unwrap()).unwrap();
        let shown = failed_message(&out, name);
        if shown != format!("x{c}y") {
            wrong.push(format!("{name}: expected {:?}, got {shown:?}", format!("x{c}y")));
        }
    }
    assert!(wrong.is_empty(), "{} of {}:\n{}", wrong.len(), messages.len(), wrong.join("\n"));
}

#[test]
fn a_backslash_in_a_message_is_not_changed_and_the_written_text_of_an_assert_is_the_source() {
    // S-299: a backslash is a writable character, so a message that holds a backslash and an `n` as text
    // (`"a\\nb"`, the four characters `a`, `\`, `n`, `b`) stays as it is; the text of a failed `assert` is the
    // source of the expression as it was written (spec §18.1), the escapes included, with no unwritable
    // character in it to change.
    let src = "test \"backslash\" {\n  panic(\"a\\\\nb\")\n}\n\ntest \"assert\" {\n  assert 'a' == '\\u{001B}'\n}\n";
    let d = Dir::pkg("backslash");
    d.write("m.onsa", src);
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    assert_eq!(failed_message(&out, "backslash"), "a\\nb");
    assert_eq!(failed_message(&out, "assert"), "assert 'a' == '\\u{001B}'");
}

#[test]
fn a_new_line_in_a_message_splits_the_lines_and_the_unwritable_characters_of_every_line_are_escaped() {
    // S-299, §4: the LF of a message is not an unwritable character: it makes the next line, which is
    // indented and does not start with `test ` (§4). The TAB stays. The ESC of the second line is escaped.
    let (d, _) = panic_tests(
        "lines",
        &[("lf".to_string(), "one\\ntwo\\u{1b}three\\n\\nfour".to_string()), ("tab".to_string(), "p\\tq".to_string())],
    );
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    assert!(!out.stdout.chars().any(unwritable), "{:?}", out.stdout);
    let lines: Vec<&str> = out.stdout.lines().collect();
    let first = lines.iter().position(|l| l.starts_with("test m \"lf\" failed at m.onsa:2: ")).expect("the first line");
    assert!(lines[first].ends_with(": one"), "{:?}", lines[first]);
    let rest: Vec<&str> = lines[first + 1..first + 4].to_vec();
    assert!(rest[0].starts_with(char::is_whitespace) && !rest[0].trim().is_empty(), "{rest:?}");
    assert_eq!(read_escapes(rest[0].trim()), "two\u{1b}three", "{rest:?}");
    assert!(rest[1].trim().is_empty(), "the empty line of the message is a line: {rest:?}");
    assert_eq!(rest[2].trim(), "four", "{rest:?}");
    assert_eq!(failed_message(&out, "tab"), "p\tq");
}

#[test]
fn a_panic_that_is_called_from_a_function_is_escaped_in_the_text_and_the_json_has_the_message_as_it_is() {
    // S-299, §4: the text of `onsa test` escapes the message of any panic of the program, and `--json`
    // keeps it (`failure.message` is the message, spec §18.1): the characters themselves, not the escape.
    let src = "fn boom() {\n  panic(\"a\\u{1b}[31mb\\u{202E}c\")\n}\n\ntest \"call\" {\n  boom()\n}\n";
    let d = Dir::pkg("from_fn");
    d.write("m.onsa", src);
    let text = run(d.root(), &["test", &d.arg()]);
    assert_eq!(text.code, 1, "{:?}{:?}", text.stdout, text.stderr);
    assert!(!text.stdout.chars().any(unwritable), "{:?}", text.stdout);
    let shown = failed_message(&text, "call");
    assert_eq!(read_escapes(&shown), "a\u{1b}[31mb\u{202e}c", "{shown:?}");
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "call"));
    assert_eq!(str_of(f, "message"), "a\u{1b}[31mb\u{202e}c", "{f}");
    assert_eq!(str_of(f, "kind"), "panic", "{f}");
}

#[test]
fn the_json_message_is_the_message_for_every_kind_of_unwritable_character() {
    // S-299, spec §18.1: `failure.message` of `--json` is the message, whatever it holds.
    let code_points: [u32; 8] = [0x00, 0x0d, 0x1b, 0x7f, 0x85, 0x2028, 0x2029, 0x202e];
    let messages: Vec<(String, String)> =
        code_points.iter().map(|c| (format!("u+{c:04x}"), format!("x\\u{{{c:x}}}y"))).collect();
    let (d, _) = panic_tests("json_kinds", &messages);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    for (name, _) in &messages {
        let c = char::from_u32(u32::from_str_radix(&name[2..], 16).unwrap()).unwrap();
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(str_of(f, "message"), format!("x{c}y"), "{name}: {f}");
    }
}

#[test]
fn a_cr_lf_in_a_message_is_one_line_break_and_not_a_lone_cr() {
    // S-299, §4 and spec §2.5: the lines of a message are split at the line breaks of §2.5, and a CR LF is one
    // line break there; the CR of it is not a lone CR, so it is not written as an escape.
    let (d, _) = panic_tests("crlf", &[("crlf".to_string(), "a\\r\\nb".to_string())]);
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{:?}{:?}", out.stdout, out.stderr);
    assert!(!out.stdout.contains('\r'), "{:?}", out.stdout);
    assert!(!out.stdout.contains("\\u{d}") && !out.stdout.contains("\\u{D}"), "{:?}", out.stdout);
    let lines: Vec<&str> = out.stdout.lines().collect();
    let first =
        lines.iter().position(|l| l.starts_with("test m \"crlf\" failed at m.onsa:2: ")).expect("the first line");
    assert!(lines[first].ends_with(": a"), "{:?}", lines[first]);
    assert!(lines[first + 1].starts_with(char::is_whitespace) && lines[first + 1].trim() == "b", "{:?}", lines);
}
