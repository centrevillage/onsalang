//! What a `///` documents, as the commands show it (W3-24/t; spec §2.1, §6.5, §11.7, §18.1, §18.2;
//! S-431, S-432, S-442).
//!
//! The cases of `tests/spec/` hold the diagnostic and the text of each form (`lex/doc_comment_targets.onsa`,
//! `fixes/e0004_doc_after_attribute*.onsa`, ...). What a case file cannot show is here:
//!
//! - S-431: in `check` (not only in the parser) the members of an `effect`, a `handler`, an `extern`
//!   block and the inline form of a handler, and the `target` declarations, take a `///`: the only
//!   diagnostic of such a unit is the E0200 of this version, never an E0004 (§2.1: "この一覧は閉じて
//!   いる"; E0004 is of the syntax stage, so it would come before the E0200, §18.1).
//! - S-432: a `///` between the attributes and the declaration is one E0004 with exactly one candidate
//!   (§2.1: "その doc の行を最初の属性の前 … へ移す一つである"), that moves the line and nothing else
//!   (the comparison ignores the width of the white space, which the spec does not fix, and keeps the
//!   line breaks); `onsa fmt` stops at the syntax error and writes nothing, so it does not move the
//!   comment by itself (§18.2); the reverse order (`///` before the attribute) is attached.

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
        let d = std::env::temp_dir().join(format!("onsa_doc_targets_{}_{n}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, text).unwrap();
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

/// The diagnostics of `check --json` as JSON values, with the exit code.
fn check(path: &str) -> (i32, Vec<Value>) {
    let out = onsa(&["check", "--json", path]);
    let status = code(&out);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let doc: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("not JSON ({e}): {text}\n{out:?}"));
    let list = doc["diagnostics"].as_array().cloned().unwrap_or_default();
    (status, list)
}

fn codes(diags: &[Value]) -> Vec<String> {
    diags.iter().map(|d| d["code"].as_str().unwrap_or("?").to_string()).collect()
}

/// The byte offset of a 1-based line and column (the column counts characters).
fn offset(src: &str, line: u64, col: u64) -> usize {
    let mut off = 0;
    for (i, l) in src.split_inclusive('\n').enumerate() {
        if i as u64 + 1 == line {
            let chars: usize = l.chars().take(col as usize - 1).map(char::len_utf8).sum();
            return off + chars;
        }
        off += l.len();
    }
    src.len()
}

/// The source with the edits of one candidate applied.
fn apply(src: &str, fix: &Value) -> String {
    let mut edits: Vec<(usize, usize, String)> = fix["edits"]
        .as_array()
        .expect("a candidate has edits")
        .iter()
        .map(|e| {
            let s = &e["span"];
            (
                offset(src, s["line"].as_u64().unwrap(), s["col"].as_u64().unwrap()),
                offset(src, s["end_line"].as_u64().unwrap(), s["end_col"].as_u64().unwrap()),
                e["replace"].as_str().unwrap().to_string(),
            )
        })
        .collect();
    edits.sort();
    for w in edits.windows(2) {
        assert!(w[0].1 <= w[1].0, "the edits of one candidate overlap: {edits:?}");
    }
    let mut out = src.to_string();
    for (a, b, r) in edits.into_iter().rev() {
        out.replace_range(a..b, &r);
    }
    out
}

/// The lines of a text with the white space at the start and the end of each line dropped and the
/// runs of white space inside a line made one space: the width of the white space is not fixed by
/// the spec (the line breaks are kept, the blank lines too).
fn lines(text: &str) -> Vec<String> {
    text.split('\n').map(|l| l.split_whitespace().collect::<Vec<_>>().join(" ")).collect()
}

// ---------------------------------------------------------------------------------------------
// S-431: the closed list of what a `///` documents
// ---------------------------------------------------------------------------------------------

#[test]
fn a_doc_comment_of_a_member_of_an_effect_a_handler_or_an_extern_block_is_no_e0004() {
    // §2.1 (S-431): "`impl` / `trait` / `effect` / `handler` / `extern` のメンバ（関連定数、効果の操作、
    // extern の関数と不透明型を含む。インライン形式の handler のメンバも同じ）". This version does not
    // support effects, handlers, `extern` blocks and `target` declarations outside `std` (E0200,
    // §18.1), so a unit holds that E0200 and nothing else: the `///` is attached, not E0004.
    let sources: [(&str, &str); 8] = [
        ("an operation of an effect", "pub effect Ask {\n  /// op\n  fn ask() -> I32\n}\n"),
        (
            "an operation after another one",
            "pub effect Ask {\n  /// first\n  fn ask() -> I32\n  // plain\n\n  /// second\n  fn tell(v: I32)\n}\n",
        ),
        (
            "a member of a handler",
            "pub effect Ask {\n  fn ask() -> I32\n}\n\nhandler h: Ask {\n  /// member\n  fn ask() -> I32 { 1 }\n}\n",
        ),
        (
            "a member of the inline form of a handler",
            "pub effect Ask {\n  fn ask() -> I32\n}\n\npub fn f() -> I32 {\n  handle { 1 } with Ask {\n    /// member\n    fn ask() -> I32 { 1 }\n  }\n}\n",
        ),
        ("a function of an extern block", "extern \"C\" lib \"m\" {\n  /// sin\n  fn sin(x: F64) -> F64\n}\n"),
        ("an opaque type of an extern block", "extern \"C\" lib \"m\" {\n  /// raw\n  type Raw\n}\n"),
        ("a target type", "/// t\ntarget type Device\n"),
        ("a target function", "/// t\npub target fn close(d: I32)\n"),
    ];
    for (what, src) in sources {
        let d = Dir::new("s431");
        let path = d.file("s431.onsa", src);
        let (_, diags) = check(&path);
        let found = codes(&diags);
        assert!(!found.iter().any(|c| c == "E0004"), "{what}: the `///` is attached, not E0004: {diags:?}");
        assert!(
            found.iter().all(|c| c == "E0200"),
            "{what}: only the E0200 of this version may be reported: {found:?}"
        );
    }
}

#[test]
fn a_doc_comment_after_the_last_member_of_those_is_still_e0004() {
    // The list is closed (§2.1): a `///` after the last member documents nothing, wherever the
    // members are. The candidate is `//` (§2.1).
    let sources: [(&str, &str); 4] = [
        ("an effect", "pub effect Ask {\n  /// op\n  fn ask() -> I32\n  /// stray\n}\n"),
        (
            "a handler",
            "pub effect Ask {\n  fn ask() -> I32\n}\n\nhandler h: Ask {\n  /// member\n  fn ask() -> I32 { 1 }\n  /// stray\n}\n",
        ),
        ("an extern block", "extern \"C\" lib \"m\" {\n  /// sin\n  fn sin(x: F64) -> F64\n  /// stray\n}\n"),
        (
            "the inline form of a handler",
            "pub effect Ask {\n  fn ask() -> I32\n}\n\npub fn f() -> I32 {\n  handle { 1 } with Ask {\n    /// member\n    fn ask() -> I32 { 1 }\n    /// stray\n  }\n}\n",
        ),
    ];
    for (what, src) in sources {
        let d = Dir::new("s431_end");
        let path = d.file("s431_end.onsa", src);
        let (_, diags) = check(&path);
        let strays: Vec<&Value> = diags.iter().filter(|x| x["code"] == "E0004").collect();
        assert_eq!(strays.len(), 1, "{what}: one E0004: {diags:?}");
        let stray_line = src.lines().position(|l| l.trim() == "/// stray").unwrap() as u64 + 1;
        assert_eq!(strays[0]["span"]["line"].as_u64(), Some(stray_line), "{what}: at the stray line: {diags:?}");
        let fixes = strays[0]["fixes"].as_array().unwrap();
        assert_eq!(fixes.len(), 1, "{what}: one candidate: {diags:?}");
        let fixed = apply(src, &fixes[0]);
        assert_eq!(fixed, src.replace("/// stray", "// stray"), "{what}: the candidate is `//`");
    }
}

// ---------------------------------------------------------------------------------------------
// S-432: a `///` between the attributes and the declaration
// ---------------------------------------------------------------------------------------------

/// (what, source, the source with the doc comment moved; the width of the white space is not compared).
fn misplaced() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        (
            "after the attribute of a function",
            "@fp(relaxed)\n/// d\nfn f(x: F32) -> F32 {\n  x\n}\n",
            "/// d\n@fp(relaxed)\nfn f(x: F32) -> F32 {\n  x\n}\n",
        ),
        (
            "after the attribute of a public struct",
            "@repr(c)\n/// d\npub struct S {\n  a: I32,\n}\n",
            "/// d\n@repr(c)\npub struct S {\n  a: I32,\n}\n",
        ),
        (
            "after the `///` lines that stand before the attribute",
            "/// a\n/// b\n@fp(relaxed)\n/// c\nfn f(x: F32) -> F32 {\n  x\n}\n",
            "/// a\n/// b\n/// c\n@fp(relaxed)\nfn f(x: F32) -> F32 {\n  x\n}\n",
        ),
        (
            "a run of lines is one error and one candidate that moves all of them",
            "@fp(relaxed)\n/// d1\n/// d2\n/// d3\nfn f(x: F32) -> F32 {\n  x\n}\n",
            "/// d1\n/// d2\n/// d3\n@fp(relaxed)\nfn f(x: F32) -> F32 {\n  x\n}\n",
        ),
        (
            "plain comments and blank lines stay where they are",
            "@fp(relaxed)\n// c1\n\n/// d\n// c2\n\nfn f(x: F32) -> F32 {\n  x\n}\n",
            "/// d\n@fp(relaxed)\n// c1\n\n// c2\n\nfn f(x: F32) -> F32 {\n  x\n}\n",
        ),
        (
            "a method of an impl, with another indentation of the doc comment",
            "pub struct S {\n  a: F32,\n}\n\nimpl S {\n  @fp(relaxed)\n        /// d\n  pub fn m(self) -> F32 {\n    self.a\n  }\n}\n",
            "pub struct S {\n  a: F32,\n}\n\nimpl S {\n  /// d\n  @fp(relaxed)\n  pub fn m(self) -> F32 {\n    self.a\n  }\n}\n",
        ),
        (
            "an input of a flow, the attribute at the start of its line",
            "pub flow g(\n  x: F32 at sample,\n  @param(min: 0.0, max: 1.0, default: 0.5)\n  /// d\n  level: F32 at block,\n) -> F32 at sample {\n  x * level\n}\n",
            "pub flow g(\n  x: F32 at sample,\n  /// d\n  @param(min: 0.0, max: 1.0, default: 0.5)\n  level: F32 at block,\n) -> F32 at sample {\n  x * level\n}\n",
        ),
        (
            "an input of a flow, the attribute follows the parenthesis on its line",
            "pub flow g(@param(min: 0.0, max: 1.0, default: 0.5)\n  /// d\n  level: F32 at block,\n  x: F32 at sample,\n) -> F32 at sample {\n  x * level\n}\n",
            "pub flow g(\n/// d\n@param(min: 0.0, max: 1.0, default: 0.5)\nlevel: F32 at block,\nx: F32 at sample,\n) -> F32 at sample {\nx * level\n}\n",
        ),
        (
            "an input of a flow, the attribute follows an input on its line",
            "pub flow g(x: F32 at sample, @param(min: 0.0, max: 1.0, default: 0.5)\n  /// d\n  level: F32 at block,\n) -> F32 at sample {\n  x * level\n}\n",
            "pub flow g(x: F32 at sample,\n/// d\n@param(min: 0.0, max: 1.0, default: 0.5)\nlevel: F32 at block,\n) -> F32 at sample {\nx * level\n}\n",
        ),
    ]
}

#[test]
fn a_doc_comment_after_the_attributes_is_one_e0004_with_one_candidate_that_moves_the_line() {
    for (what, src, expected) in misplaced() {
        let d = Dir::new("s432");
        let path = d.file("s432.onsa", src);
        let (status, diags) = check(&path);
        assert_eq!(status, 1, "{what}: {diags:?}");
        assert_eq!(codes(&diags), vec!["E0004".to_string()], "{what}: one E0004: {diags:?}");
        let fixes = diags[0]["fixes"].as_array().unwrap();
        assert_eq!(fixes.len(), 1, "{what}: exactly one candidate (S-432): {diags:?}");
        let fixed = apply(src, &fixes[0]);
        assert_eq!(
            lines(&fixed),
            lines(expected),
            "{what}: the candidate moves the doc comment before the first attribute:\n{fixed}"
        );

        // Applied, it is a program with no error: the doc comment is before the attribute and takes it.
        let d2 = Dir::new("s432_fixed");
        let path2 = d2.file("s432_fixed.onsa", &fixed);
        let (status2, diags2) = check(&path2);
        assert_eq!((status2, codes(&diags2)), (0, Vec::new()), "{what}: after the candidate: {diags2:?}\n{fixed}");
    }
}

#[test]
fn the_forms_with_the_doc_comment_moved_are_programs_with_no_error() {
    // The expected texts above are free of any other error, so the test of the candidate cannot
    // fail for a reason that is not the candidate.
    for (what, src, expected) in misplaced() {
        let d = Dir::new("s432_expected");
        let path = d.file("s432_expected.onsa", expected);
        let (status, diags) = check(&path);
        assert_eq!((status, codes(&diags)), (0, Vec::new()), "{what}: {diags:?}\n{expected}");
        // and the misplaced source has no other error than the one E0004
        let path = d.file("s432_source.onsa", src);
        let (_, diags) = check(&path);
        assert_eq!(codes(&diags), vec!["E0004".to_string()], "{what}: {diags:?}");
    }
}

#[test]
fn fmt_stops_at_a_doc_comment_after_the_attributes_and_does_not_move_it() {
    // §18.2: `onsa fmt` does not write a file with a syntax error (exit code 2). S-432 rejects the
    // reading in which `fmt` moves the comment before the attribute by itself.
    for (what, src, _) in misplaced() {
        let d = Dir::new("s432_fmt");
        let path = d.file("s432_fmt.onsa", src);
        for args in [&["fmt"][..], &["fmt", "--check"][..]] {
            let mut full = args.to_vec();
            full.push(&path);
            let out = onsa(&full);
            assert_eq!(code(&out), 2, "{what}: {args:?}: {out:?}");
            assert_eq!(std::fs::read_to_string(&path).unwrap(), src, "{what}: {args:?} writes nothing");
        }
    }
}

#[test]
fn a_doc_comment_before_the_attributes_is_attached_and_fmt_keeps_it_there() {
    // The reverse order is attached (§2.1): no E0004, and `fmt` does not move the line.
    let src = "\
/// A function.
@fp(relaxed)
fn f(x: F32) -> F32 {
  x
}

/// A struct.
@repr(c)
pub struct S {
  a: I32,
}

/// A flow, and its input.
pub flow g(
  /// The signal.
  x: F32 at sample,
  /// The level, in two
  /// lines.
  @param(min: 0.0, max: 1.0, default: 0.5)
  level: F32 at block,
) -> F32 at sample {
  x * level
}
";
    let d = Dir::new("s432_ok");
    let path = d.file("s432_ok.onsa", src);
    let (status, diags) = check(&path);
    assert_eq!((status, codes(&diags)), (0, Vec::new()), "{diags:?}");
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "the source is in the normal form: {out:?}");
}
