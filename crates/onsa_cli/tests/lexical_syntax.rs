//! The lexical decisions as the commands show them (W3-04/t; spec §2.1, §2.3, §2.4, §2.5, §2.2,
//! §18.1 and §18.2; S-201, S-89, S-90, S-51, S-169, S-279, S-371, R-01, R-63, R-101, R-102).
//!
//! The cases of `tests/spec/` and `tests/cst/` hold the diagnostics of each form. What a case file
//! cannot show is here: what `fmt`, `fmt --check` and `diff --ast` do with a file that has a lexical
//! error (§18.2: no write, exit code 2), the exit codes of the inputs that used to end in an internal
//! error (R-01: exit code 101), CR LF as one newline (§2.5: `check` is clean, `fmt` writes LF, the
//! lines and columns of a diagnostic count a CR LF once and a character once, §18.1), and a `///`
//! that no declaration takes (E0004, which must stop `fmt` before it moves the comment to the next
//! declaration).
//!
//! What the spec says, in short:
//!
//! - §2.4: a string literal cannot span lines (E0001 when the line ends before the closing quote);
//!   the escapes are a closed list; `\u{…}` is a Unicode scalar value. §18.1: the columns of a
//!   span count characters (Unicode scalar values), the lines start at 1.
//! - §2.5: white space is U+0020 and the tab, the newline is LF, CR LF is one newline (`fmt` writes LF),
//!   and a lone CR, the controls, U+2028 and U+2029, and the bidirectional controls are E0001, comments
//!   and strings included.
//! - §2.1: a `///` with no declaration to document, and a `//!` after the first item, are E0004
//!   (syntax stage: `fmt` stops with the exit code 2, §18.2).
//! - §2.2: `clock`, `when`, `reset_if` and `ser` are E0200 where they stand as names (syntax stage).
//!
//! The reserved word's own fmt stop is also in `syntax_units.rs` (`fmt_stops_for_a_reserved_word`),
//! for `clock`.

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        // A helper is called from several tests at once, so the tag alone does not make a name.
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_lexical_syntax_{}_{n}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, bytes: &[u8]) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, bytes).unwrap();
        p.to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn onsa(args: &[&str]) -> Output {
    Command::new(ONSA).args(args).output().expect("run onsa")
}

fn code(out: &Output) -> i32 {
    out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"))
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn read(path: &str) -> Vec<u8> {
    std::fs::read(path).unwrap()
}

/// The `(code, line, col)` of each diagnostic of `check --json` (an array, or an object with a
/// `diagnostics` array: the top-level shape is W3-16's).
fn check_diagnostics(path: &str) -> (i32, Vec<(String, u64, u64)>) {
    let out = onsa(&["check", "--json", path]);
    let status = code(&out);
    let text = stdout(&out);
    if status == 101 || (status == 2 && text.trim().is_empty()) {
        return (status, Vec::new());
    }
    let doc: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("not JSON ({e}): {text}\n{out:?}"));
    let list = match &doc {
        Value::Array(a) => a.clone(),
        Value::Object(_) => doc["diagnostics"].as_array().cloned().unwrap_or_default(),
        _ => Vec::new(),
    };
    let found = list
        .iter()
        .map(|d| {
            (
                d["code"].as_str().unwrap_or("?").to_string(),
                d["span"]["line"].as_u64().unwrap_or(0),
                d["span"]["col"].as_u64().unwrap_or(0),
            )
        })
        .collect();
    (status, found)
}

// ---------------------------------------------------------------------------------------------
// CR LF is one newline (§2.5)
// ---------------------------------------------------------------------------------------------

const LF_SOURCE: &str = "pub fn f(a: I32) -> I32 {\n  let b = a\n  b\n}\n";

#[test]
fn a_crlf_file_checks_clean_and_fmt_writes_lf() {
    // §2.5: "CR LF も一つの改行として読み、`onsa fmt` が LF に揃える".
    let d = Dir::new("crlf_fmt");
    let crlf = LF_SOURCE.replace('\n', "\r\n");
    let path = d.file("crlf.onsa", crlf.as_bytes());

    let (status, diags) = check_diagnostics(&path);
    assert_eq!((status, diags.len()), (0, 0), "a CR LF file is a clean program: {diags:?}");

    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 1, "CR LF is not the normal form: {out:?}");
    assert_eq!(read(&path), crlf.as_bytes(), "`fmt --check` writes nothing");

    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&path), LF_SOURCE.as_bytes(), "`fmt` writes LF");

    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "the written file is the normal form: {out:?}");
}

#[test]
fn diff_ast_does_not_see_crlf() {
    // §18.2 and docs/onsa-tools.md §3.5: a rewrite of `fmt` is no difference of the programs.
    let d = Dir::new("crlf_diff");
    let lf = d.file("lf.onsa", LF_SOURCE.as_bytes());
    let crlf = d.file("crlf.onsa", LF_SOURCE.replace('\n', "\r\n").as_bytes());
    let out = onsa(&["diff", "--ast", &lf, &crlf]);
    assert_eq!(code(&out), 0, "the same program with CR LF line ends: {out:?}");
}

#[test]
fn the_lines_of_a_diagnostic_count_crlf_once() {
    // §18.1: a span has the line it stands on, from 1. `$` is on the third line.
    let d = Dir::new("crlf_lines");
    let src = "pub fn f(a: I32) -> I32 {\r\n  let b = a\r\n  b $ 1\r\n}\r\n";
    let path = d.file("crlf_lines.onsa", src.as_bytes());
    let (status, diags) = check_diagnostics(&path);
    assert_eq!(status, 1);
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!((diags[0].0.as_str(), diags[0].1, diags[0].2), ("E0001", 3, 5), "{diags:?}");
}

#[test]
fn a_crlf_file_with_a_lexical_error_is_not_rewritten() {
    // §18.2: `fmt` writes nothing for a file with a syntax-stage diagnostic (exit code 2).
    let d = Dir::new("crlf_error");
    let src = "pub fn f(a: I32) -> I32 {\r\n  a $ 1\r\n}\r\n";
    let path = d.file("crlf_error.onsa", src.as_bytes());
    for args in [&["fmt"][..], &["fmt", "--check"][..]] {
        let mut full = args.to_vec();
        full.push(&path);
        let out = onsa(&full);
        assert_eq!(code(&out), 2, "{args:?}: {out:?}");
        assert_eq!(read(&path), src.as_bytes(), "{args:?}: the file is not written");
    }
}

// ---------------------------------------------------------------------------------------------
// the columns count characters (§18.1)
// ---------------------------------------------------------------------------------------------

#[test]
fn the_column_after_multi_byte_text_counts_characters() {
    // `$` follows a string of four characters (12 bytes, one outside the BMP): the column is 18, the
    // number of characters before it plus one, not a byte or a UTF-16 offset.
    let d = Dir::new("columns");
    let src = "pub fn f() -> I32 {\n  let s = \"日本語😀\" $ 1\n  1\n}\n";
    let path = d.file("columns.onsa", src.as_bytes());
    let (status, diags) = check_diagnostics(&path);
    assert_eq!(status, 1);
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!((diags[0].0.as_str(), diags[0].1, diags[0].2), ("E0001", 2, 18), "{diags:?}");
}

// ---------------------------------------------------------------------------------------------
// a string does not span lines (§2.4)
// ---------------------------------------------------------------------------------------------

#[test]
fn a_string_that_does_not_close_on_its_line_is_e0001_on_that_line() {
    let d = Dir::new("string_lines");
    let src = "pub fn f() -> Str {\n  \"a\n  b\"\n}\n";
    let path = d.file("string_lines.onsa", src.as_bytes());
    let (status, diags) = check_diagnostics(&path);
    assert_eq!(status, 1);
    assert_eq!(diags.len(), 1, "one error in the unit: {diags:?}");
    assert_eq!((diags[0].0.as_str(), diags[0].1), ("E0001", 2), "{diags:?}");
    for args in [&["fmt"][..], &["fmt", "--check"][..]] {
        let mut full = args.to_vec();
        full.push(&path);
        let out = onsa(&full);
        assert_eq!(code(&out), 2, "{args:?}: {out:?}");
        assert_eq!(read(&path), src.as_bytes(), "{args:?}: the file is not written");
    }
}

// ---------------------------------------------------------------------------------------------
// R-01: multi-byte characters in strings never end in an internal error
// ---------------------------------------------------------------------------------------------

/// A string literal written as the body of a function (so the string is on the second line).
fn string_in_a_function(literal: &str) -> String {
    format!("pub fn f(a: U32) -> Str uses {{Alloc}} {{\n  {literal}\n}}\n")
}

#[test]
fn multi_byte_characters_in_strings_end_in_a_diagnostic_and_not_in_an_internal_error() {
    // Each literal has a character of two or more bytes where the lexer used to cut a character:
    // right after the `{` of a hole, after a `.`, after a backslash, inside `\u{…}`. The diagnostic
    // is E0001 (§2.4: a hole is a name path, and a name is ASCII, §2.3; the escapes are a closed
    // list), on the second line; the four commands end with the exit codes of a syntax error and
    // write nothing.
    let literals = [
        "\"{é}\"",
        "\"{日本}\"",
        "\"{a.é}\"",
        "\"{😀}\"",
        "\"{\u{feff}a}\"",
        "\"{\u{85}}\"",
        "\"{日本",
        "\"{a.日本}\"",
        "\"é{a}é{é}\"",
        "\"\\é\"",
        "\"\\音\"",
        "\"\\😀\"",
        "\"\\u{é}\"",
        "\"\\u{12é}\"",
        "\"{a}\\é\"",
        "'\\é'",
        "\"日本{{日本}}日本{é}\"",
    ];
    for literal in literals {
        let d = Dir::new("multibyte");
        let src = string_in_a_function(literal);
        let path = d.file("multibyte.onsa", src.as_bytes());

        let (status, diags) = check_diagnostics(&path);
        assert_eq!(status, 1, "{literal}: check ends with the exit code of a diagnostic ({diags:?})");
        assert!(
            diags.iter().any(|x| x.0 == "E0001" && x.1 == 2),
            "{literal}: expected an E0001 on line 2, got {diags:?}"
        );
        assert!(diags.iter().all(|x| x.0 != "E0000"), "{literal}: {diags:?}");

        for args in [&["fmt"][..], &["fmt", "--check"][..]] {
            let mut full = args.to_vec();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{literal}: {args:?} stops at the lexical error: {out:?}");
            assert_eq!(read(&path), src.as_bytes(), "{literal}: {args:?} writes nothing");
        }
        let out = onsa(&["diff", "--ast", &path, &path]);
        assert_eq!(code(&out), 2, "{literal}: diff --ast stops at the lexical error: {out:?}");
    }
}

// ---------------------------------------------------------------------------------------------
// S-201: the characters a source may not hold stop `fmt` (E0001 is of the syntax stage)
// ---------------------------------------------------------------------------------------------

#[test]
fn a_character_that_a_source_may_not_hold_stops_fmt_wherever_it_stands() {
    // §2.5: "単独の CR、タブと改行以外の制御文字 …、U+2028 / U+2029、双方向の制御文字 … は、コメントと
    // 文字列の中も含めて書けない（E0001）". The expected line is the one the character is on.
    let cases: [(&str, String, u64); 14] = [
        ("a lone CR in code", "pub fn f(a: I32) -> I32 {\n  a \r+ 1\n}\n".to_string(), 2),
        ("a lone CR in a comment", "pub fn f(a: I32) -> I32 {\n  // x\ry\n  a\n}\n".to_string(), 2),
        ("a lone CR in a string", "pub fn f() -> Str {\n  \"a\rb\"\n}\n".to_string(), 2),
        ("a lone CR at the end of the file", "pub fn f() -> I32 {\n  1\n}\r".to_string(), 3),
        ("CR CR LF", "pub fn f() -> I32 {\n  1 // x\r\r\n}\n".to_string(), 2),
        ("U+0001 in a string", "pub fn f() -> Str {\n  \"a\u{1}b\"\n}\n".to_string(), 2),
        ("U+0000 in a comment", "pub fn f() -> I32 {\n  // a\u{0}b\n  1\n}\n".to_string(), 2),
        ("U+007F in a string", "pub fn f() -> Str {\n  \"a\u{7f}b\"\n}\n".to_string(), 2),
        ("U+0085 in a comment", "pub fn f() -> I32 {\n  // a\u{85}b\n  1\n}\n".to_string(), 2),
        ("U+2028 in a comment", "pub fn f() -> I32 {\n  // a\u{2028}b\n  1\n}\n".to_string(), 2),
        ("U+2029 in a string", "pub fn f() -> Str {\n  \"a\u{2029}b\"\n}\n".to_string(), 2),
        ("U+202E in a string", "pub fn f() -> Str {\n  \"a\u{202e}b\"\n}\n".to_string(), 2),
        ("U+2066 in a comment", "pub fn f() -> I32 {\n  // a\u{2066}b\n  1\n}\n".to_string(), 2),
        ("U+2069 in code", "pub fn f(a: I32) -> I32 {\n  a \u{2069}+ 1\n}\n".to_string(), 2),
    ];
    for (what, src, line) in cases {
        let d = Dir::new("chars");
        let path = d.file("chars.onsa", src.as_bytes());
        let (status, diags) = check_diagnostics(&path);
        assert_eq!(status, 1, "{what}: {diags:?}");
        assert!(
            diags.iter().any(|x| x.0 == "E0001" && x.1 == line),
            "{what}: expected an E0001 on line {line}, got {diags:?}"
        );
        for args in [&["fmt"][..], &["fmt", "--check"][..]] {
            let mut full = args.to_vec();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what}: {args:?}: {out:?}");
            assert_eq!(read(&path), src.as_bytes(), "{what}: {args:?} writes nothing");
        }
    }
}

#[test]
fn a_tab_and_the_characters_outside_the_lists_are_fine_in_comments_and_strings() {
    // §2.5: only the listed characters are errors; everything else may stand in a comment or a string.
    let d = Dir::new("allowed");
    let src = "pub fn f() -> Str {\n  // a\tb \u{a0} \u{200e} \u{200f} \u{feff} \u{2060} \u{3000}\n  \"a\tb \u{a0} \u{200e} \u{feff} \u{2060} \u{3000} 日本\"\n}\n";
    let path = d.file("allowed.onsa", src.as_bytes());
    let (status, diags) = check_diagnostics(&path);
    assert_eq!((status, diags.len()), (0, 0), "{diags:?}");
}

// ---------------------------------------------------------------------------------------------
// S-51: E0004 stops `fmt` before it moves a doc comment
// ---------------------------------------------------------------------------------------------

#[test]
fn a_doc_comment_with_nothing_to_document_is_e0004_and_stops_fmt() {
    // The first source is the one that showed the trouble: `fmt` wrote `fn f() {} /// doc` and the
    // comment then documented the `const B` that follows. §2.1: "付ける宣言の無い `///`（… fn の引数の
    // 前 …）は E0004". The others: a statement, the end of a block, the end of the file, a `//!` after the
    // first item (which documents nothing of the module).
    let cases: [(&str, &str, u64); 7] = [
        ("before the closing parenthesis of a parameter list", "fn f(\n  /// doc\n) {\n}\nconst B: U32 = 2\n", 2),
        ("before a parameter", "fn f(\n  /// doc\n  a: I32,\n) {\n}\nconst B: U32 = 2\n", 2),
        ("before a statement", "pub fn f() -> I32 {\n  /// doc\n  1\n}\n", 2),
        ("at the end of a block", "pub fn f() -> I32 {\n  1\n  /// doc\n}\n", 3),
        ("at the end of the file", "pub fn f() -> I32 {\n  1\n}\n/// doc\n", 4),
        ("before a use", "/// doc\nuse std.math.{sqrt}\n", 1),
        (
            "a module comment after the first item",
            "pub fn f() -> I32 {\n  1\n}\n//! late\npub fn g() -> I32 {\n  2\n}\n",
            4,
        ),
    ];
    for (what, src, line) in cases {
        let d = Dir::new("e0004");
        let path = d.file("e0004.onsa", src.as_bytes());
        let (status, diags) = check_diagnostics(&path);
        assert_eq!(status, 1, "{what}: {diags:?}");
        assert!(
            diags.iter().any(|x| x.0 == "E0004" && x.1 == line),
            "{what}: expected E0004 on line {line}, got {diags:?}"
        );
        for args in [&["fmt"][..], &["fmt", "--check"][..]] {
            let mut full = args.to_vec();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what}: {args:?}: {out:?}");
            assert_eq!(read(&path), src.as_bytes(), "{what}: {args:?} writes nothing");
            assert!(stdout(&out).contains("E0004"), "{what}: {args:?} reports the E0004: {out:?}");
        }
        let out = onsa(&["diff", "--ast", &path, &path]);
        assert_eq!(code(&out), 2, "{what}: diff --ast stops: {out:?}");
    }
}

#[test]
fn doc_comments_on_the_declarations_that_take_them_are_not_errors() {
    // §2.1: the items (not `use` or `test`), the members of an `impl`, a struct's fields, an enum's
    // variants and a flow's inputs; `////` is an ordinary comment, also at the end of the file.
    let d = Dir::new("docs_ok");
    let src = "\
//! Module documentation.

/// A struct.
pub struct P {
  /// A field.
  x: F32,
}

/// An enum.
pub enum C {
  /// A variant.
  A,
  B,
}

/// An impl.
impl P {
  /// A method.
  pub fn get(self) -> F32 {
    self.x
  }
}

/// A flow.
pub flow g(
  /// An input.
  x: F32 at sample,
) -> F32 at sample {
  x
}

//// An ordinary comment.
pub fn h() -> I32 {
  //// Another one, before a statement.
  1
}

////
";
    let path = d.file("docs_ok.onsa", src.as_bytes());
    let (status, diags) = check_diagnostics(&path);
    assert_eq!((status, diags.len()), (0, 0), "{diags:?}");
    let out = onsa(&["fmt", "--check", &path]);
    assert!(matches!(code(&out), 0 | 1), "fmt accepts the file: {out:?}");
}

// ---------------------------------------------------------------------------------------------
// S-169, S-279, S-371: the reserved words are E0200 and stop `fmt`
// ---------------------------------------------------------------------------------------------

#[test]
fn a_reserved_word_where_a_name_stands_is_e0200_and_stops_fmt() {
    // §2.2: "宣言の名前には使えず、この版では構文としても受け付けない（現れた位置で E0200 …）"; §18.2: the
    // reserved word's E0200 is a diagnostic of the syntax stage, so `fmt` stops.
    for word in ["clock", "when", "reset_if", "ser"] {
        let cases: [(&str, String, u64); 6] = [
            ("a let", format!("pub fn f(a: I32) -> I32 {{\n  let {word} = a\n  a\n}}\n"), 2),
            ("a parameter", format!("pub fn f({word}: I32) -> I32 {{\n  1\n}}\n"), 1),
            ("a function", format!("pub fn {word}() -> I32 {{\n  1\n}}\n"), 1),
            ("a field", format!("pub struct S {{\n  {word}: I32,\n}}\n"), 2),
            ("an operand", format!("pub fn f() -> I32 {{\n  {word} + 1\n}}\n"), 2),
            ("a use list", format!("use kp.{{{word}}}\n"), 1),
        ];
        for (what, src, line) in cases {
            let d = Dir::new("reserved");
            let path = d.file("reserved.onsa", src.as_bytes());
            let (status, diags) = check_diagnostics(&path);
            assert_eq!(status, 1, "{word} as {what}: {diags:?}");
            assert!(
                diags.iter().any(|x| x.0 == "E0200" && x.1 == line),
                "{word} as {what}: expected E0200 on line {line}, got {diags:?}"
            );
            for args in [&["fmt"][..], &["fmt", "--check"][..]] {
                let mut full = args.to_vec();
                full.push(&path);
                let out = onsa(&full);
                assert_eq!(code(&out), 2, "{word} as {what}: {args:?}: {out:?}");
                assert_eq!(read(&path), src.as_bytes(), "{word} as {what}: {args:?} writes nothing");
            }
        }
    }
}

#[test]
fn names_that_start_with_a_reserved_word_are_ordinary_names() {
    // §2.2 reserves the four words, not the names that start with them.
    let d = Dir::new("prefix");
    let src = "\
pub fn clock_rate(serial: I32, whenever: I32) -> I32 {
  let reset_ifx = serial
  reset_ifx + whenever
}
";
    let path = d.file("prefix.onsa", src.as_bytes());
    let (status, diags) = check_diagnostics(&path);
    assert_eq!((status, diags.len()), (0, 0), "{diags:?}");
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
}

#[test]
fn a_reserved_word_after_a_dot_is_a_name_and_not_an_e0200() {
    // §2.2: "パスの `.` の直後 … は、他のキーワードと同じく名前として読む（`s.clock` は後の段の
    // E0413 …）". The syntax stage reads `s.clock`; the type stage says there is no such field.
    for word in ["clock", "when", "reset_if", "ser"] {
        let d = Dir::new("after_dot");
        let src = format!("pub struct S {{\n  a: I32,\n}}\n\npub fn f(s: S) -> I32 {{\n  s.{word}\n}}\n");
        let path = d.file("after_dot.onsa", src.as_bytes());
        let (status, diags) = check_diagnostics(&path);
        assert_eq!(status, 1, "{word}: {diags:?}");
        assert!(diags.iter().all(|x| x.0 != "E0200"), "{word} after a dot is not E0200: {diags:?}");
        assert!(diags.iter().any(|x| x.0 == "E0413" && x.1 == 6), "{word}: expected E0413 on line 6: {diags:?}");
    }
}
