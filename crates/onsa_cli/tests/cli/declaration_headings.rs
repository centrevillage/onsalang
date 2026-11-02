//! The heading of a declaration and the shape of an attribute (W3-08/t1: spec §4.6, §6.4, §6.5, §12.4, §15.1,
//! §18.1; S-34, S-36, S-412, S-417, S-420, S-463, R-193).
//!
//! The case files in `tests/spec/` pin which diagnostic is on which line and the text after a candidate. These
//! tests say what those cannot: the range of the main position (`found`, the source text of the form, §18.1),
//! that a form with no candidate has none and has a note, that the candidate of `<…>` is made only for a text
//! that reads as a list of type parameters or arguments (R-193), and that the right forms go through `fmt`
//! unchanged and through `check` with no error of the syntax stage.
//!
//! Every test uses only the binary (`onsa check --json`, `onsa fmt --check`).

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_headings_{}_{tag}", std::process::id()));
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

/// The exit code and the diagnostics of `onsa check --json <path>`.
fn check(path: &str) -> (i32, Vec<Value>) {
    let out = Command::new(ONSA).args(["check", "--json", path]).output().expect("run onsa");
    let code = out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"));
    assert!(
        code == 0 || code == 1,
        "onsa check {path}: exit code {code} (stderr: {})",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8(out.stdout).expect("utf-8 output");
    let diags = match serde_json::from_str::<Value>(&text) {
        Ok(v) => match v.get("diagnostics") {
            Some(Value::Array(a)) => a.clone(),
            _ => panic!("the document has no `diagnostics` array: {v}"),
        },
        Err(e) => panic!("onsa check --json printed no JSON ({e}): {text}"),
    };
    (code, diags)
}

fn code_of(d: &Value) -> &str {
    d["code"].as_str().expect("`code` is a string")
}

fn found_of(d: &Value) -> &str {
    d["found"].as_str().unwrap_or_else(|| panic!("no `found` in {d}"))
}

fn count(d: &Value, key: &str) -> usize {
    d.get(key).and_then(Value::as_array).map_or(0, Vec::len)
}

/// `onsa check` of `src` reports one diagnostic, and it is `code`.
fn one(d: &Dir, name: &str, src: &str, code: &str) -> Value {
    let path = d.file(&format!("{name}.onsa"), src);
    let (_, diags) = check(&path);
    assert_eq!(diags.len(), 1, "{name}: one diagnostic expected, got {diags:?}\n{src}");
    assert_eq!(code_of(&diags[0]), code, "{name}: {}", diags[0]);
    diags[0].clone()
}

// ---- the range of the main position of the forms before the name (spec §18.1, S-316, S-417) ------------

#[test]
fn the_range_of_a_form_before_the_name_is_the_whole_form() {
    // §18.1: the main range of an E0020 is the range of the foreign form, from its first token to its last;
    // S-417: the range of a restricted visibility is `pub` to `)`, and a space inside it is part of it.
    // `found` is the source text of that range.
    let forms: [(&str, &str, &str, &str); 17] = [
        ("hash_derive", "E0020", "#[derive(PartialEq)]\npub struct Key {\n  id: U32,\n}\n", "#[derive(PartialEq)]"),
        ("hash_repr", "E0020", "#[repr(c)]\npub struct P {\n  x: I32,\n}\n", "#[repr(c)]"),
        ("at_derive", "E0020", "@derive(PartialEq, Eq)\npub struct Key {\n  id: U32,\n}\n", "@derive(PartialEq, Eq)"),
        ("relaxed", "E0020", "@relaxed\npub fn f() -> F32 {\n  1.0\n}\n", "@relaxed"),
        (
            "bulk",
            "E0020",
            "pub flow g(x: F32 at sample) -> F32 at sample {\n  @bulk let d = delay~(x, 4800)\n  d\n}\n",
            "@bulk",
        ),
        (
            "mem_fast",
            "E0020",
            "pub flow g(x: F32 at sample) -> F32 at sample {\n  @mem(fast) let d = delay~(x, 64)\n  d\n}\n",
            "@mem(fast)",
        ),
        ("pub_pkg", "E0020", "pub(pkg) fn f() -> I32 {\n  1\n}\n", "pub(pkg)"),
        ("pub_pkg_spaced", "E0020", "pub (pkg) fn f() -> I32 {\n  1\n}\n", "pub (pkg)"),
        ("pub_crate", "E0020", "pub(crate) fn f() -> I32 {\n  1\n}\n", "pub(crate)"),
        ("pub_crate_spaced", "E0020", "pub (crate) fn f() -> I32 {\n  1\n}\n", "pub (crate)"),
        ("pub_super", "E0002", "pub(super) fn f() -> I32 {\n  1\n}\n", "pub(super)"),
        ("pub_in", "E0002", "pub(in crate::a) fn f() -> I32 {\n  1\n}\n", "pub(in crate::a)"),
        ("pub_empty", "E0002", "pub() fn f() -> I32 {\n  1\n}\n", "pub()"),
        ("pub_package", "E0002", "pub(package) fn f() -> I32 {\n  1\n}\n", "pub(package)"),
        ("pub_super_spaced", "E0002", "pub (super) fn f() -> I32 {\n  1\n}\n", "pub (super)"),
        ("field_crate", "E0002", "pub struct P {\n  pub(crate) x: I32,\n}\n", "pub(crate)"),
        ("copy_in_the_head", "E0020", "pub struct P: Copy {\n  x: I32,\n}\n", "Copy"),
    ];
    let d = Dir::new("ranges");
    for (name, code, src, found) in forms {
        let diag = one(&d, name, src, code);
        assert_eq!(found_of(&diag), found, "{name}: {diag}");
    }
}

// ---- a form with no candidate has none and has a note (spec §18.1, S-417, S-420, S-464) -------------

#[test]
fn a_restricted_visibility_and_a_pub_struct_field_have_no_candidate_and_have_a_note() {
    // §15.1: the visibility of another language with a range, and `pub(crate)` / `pub(pkg)` on the field of a
    // `pub struct` (a candidate that takes it out would widen the field), are E0002 with no candidate, and a note
    // that shows the three visibilities. The text of the note is not promised.
    let forms = [
        ("super", "pub(super) fn f() -> I32 {\n  1\n}\n"),
        ("self_", "pub(self) fn f() -> I32 {\n  1\n}\n"),
        ("in_path", "pub(in a.b) fn f() -> I32 {\n  1\n}\n"),
        ("in_crate", "pub(in crate::a) fn f() -> I32 {\n  1\n}\n"),
        ("empty", "pub() fn f() -> I32 {\n  1\n}\n"),
        ("package", "pub(package) struct P {\n  x: I32,\n}\n"),
        ("field_crate", "pub struct P {\n  pub(crate) x: I32,\n}\n"),
        ("field_pkg", "pub struct P {\n  pub(pkg) x: I32,\n}\n"),
        ("field_spaced", "pub struct P {\n  pub (crate) x: I32,\n}\n"),
        ("extern_c", "extern \"C\" fn f() -> I32 {\n  1\n}\n"),
        ("extern_bare", "extern fn f() -> I32 {\n  1\n}\n"),
        ("export_c", "export \"C\" fn f() -> I32 {\n  1\n}\n"),
        // The replacement is not accepted in that place (spec §6.5): no candidate (S-463).
        ("hash_inline", "#[inline]\npub fn f() -> I32 {\n  1\n}\n"),
        ("hash_repr_rust", "#[repr(rust)]\npub struct P {\n  x: I32,\n}\n"),
        ("hash_derive_on_fn", "#[derive(Eq)]\npub fn f() -> I32 {\n  1\n}\n"),
        ("old_relaxed_on_struct", "@relaxed\npub struct P {\n  x: F32,\n}\n"),
        ("old_bulk_on_fn", "@bulk\npub fn f() -> I32 {\n  1\n}\n"),
        ("old_derive_on_const", "@derive(PartialEq)\nconst K: I32 = 1\n"),
        // A tuple of two elements or more: the names of the fields are not made up (spec §4.4).
        ("tuple_of_two", "pub struct Pair(F32, F32)\n"),
    ];
    let d = Dir::new("nocandidate");
    for (name, src) in forms {
        let diag = one(&d, name, src, "E0002");
        assert_eq!(count(&diag, "fixes"), 0, "{name}: a form with no candidate has none: {diag}");
        assert!(count(&diag, "notes") >= 1, "{name}: a note that shows the Onsa form is expected: {diag}");
    }
}

#[test]
fn a_spelling_only_difference_and_a_tuple_of_one_keep_their_candidate() {
    // `#[repr(C)]` is written `@repr(c)` (the same concept spelled otherwise), and a
    // tuple of one element has one candidate, a struct with the field `value` (spec §4.4).
    let d = Dir::new("keepcandidate");
    for (name, src) in
        [("repr_upper_c", "#[repr(C)]\npub struct P {\n  x: I32,\n}\n"), ("tuple_of_one", "pub struct Hz(F32)\n")]
    {
        let diag = one(&d, name, src, "E0020");
        assert_eq!(count(&diag, "fixes"), 1, "{name}: one candidate: {diag}");
    }
}

#[test]
fn the_other_places_of_pub_crate_and_pub_pkg_keep_the_candidate_that_takes_it_out() {
    // §15.1: an item, a `use`, an `impl` member, and the field of a struct with no visibility word or with
    // `priv` keep the E0020 and the candidate that takes the visibility out (S-36, S-412, S-420).
    let forms = [
        ("item", "pub(crate) fn f() -> I32 {\n  1\n}\n"),
        ("use_", "pub(pkg) use std.math\n"),
        ("member", "pub struct P {\n  v: I32,\n}\n\nimpl P {\n  pub(pkg) fn get(self) -> I32 {\n    self.v\n  }\n}\n"),
        ("plain_struct_field", "struct P {\n  pub(crate) x: I32,\n}\n"),
        ("priv_struct_field", "priv struct P {\n  pub(pkg) x: I32,\n}\n"),
    ];
    let d = Dir::new("keepfix");
    for (name, src) in forms {
        let diag = one(&d, name, src, "E0020");
        assert_eq!(count(&diag, "fixes"), 1, "{name}: one candidate: {diag}");
    }
}

// ---- the candidate of `<…>` is made only for a list that reads (spec §4.5, §18.1, R-193) ---------------

#[test]
fn the_candidate_of_angle_brackets_is_made_only_for_a_list_that_reads() {
    // R-193: when the text between the brackets does not read as type parameters or type arguments, writing it
    // in `[ ]` leaves an error of the syntax stage, which the promise of §18.1 does not allow, so there is no
    // E0020 and no candidate: the general E0002.
    let d = Dir::new("angle");
    let unreadable = [
        ("two_names", "pub fn b<T q>(x: T) -> T {\n  x\n}\n"),
        ("number", "pub fn b<3>(x: I32) -> I32 {\n  x\n}\n"),
        ("mismatched", "pub fn b(x: Option<I32)>) -> I32 {\n  1\n}\n"),
        ("call", "pub fn b(x: I32) -> I32 {\n  let a = d<U)>(x)\n  a\n}\n"),
    ];
    for (name, src) in unreadable {
        let path = d.file(&format!("{name}.onsa"), src);
        let (_, diags) = check(&path);
        assert!(!diags.is_empty(), "{name}: an error is expected");
        assert_eq!(code_of(&diags[0]), "E0002", "{name}: {diags:?}");
        assert_eq!(count(&diags[0], "fixes"), 0, "{name}: no candidate: {}", diags[0]);
    }
    let readable = d.file("readable.onsa", "pub fn b(x: Option<I32>) -> I32 {\n  1\n}\n");
    let (_, diags) = check(&readable);
    assert_eq!(code_of(&diags[0]), "E0020", "{diags:?}");
    assert_eq!(count(&diags[0], "fixes"), 1, "{}", diags[0]);
}

// ---- the right forms (spec §6.4, §6.5, §12.4, §15.1) ----------------------------------------------------

const RIGHT_FORMS: &str = "\
pub struct Key: PartialEq + Eq {
  id: U32,
}

pub struct Pair[T]: PartialEq {
  a: T,
  b: T,
}

pub enum Mode: PartialEq + Eq {
  Off,
  On,
}

priv struct Hidden {
  a: I32,
  b: I32,
}

priv fn module_fn() -> I32 {
  1
}

@repr(c)
pub struct Frame {
  left: F32,
  right: F32,
}

@fp(relaxed)
pub fn fast(x: F32) -> F32 {
  x * 2.0
}

pub flow echo(x: F32 at sample) -> F32 at sample {
  @mem(bulk) let d = delay~(x, 4800)
  d
}
";

#[test]
fn the_right_forms_go_through_fmt_unchanged() {
    // `fmt --check` exits with 0 for a file that is in the canonical form already, so the heading with
    // `: trait + trait`, `priv`, the attributes, and `@mem(bulk)` in front of a `let` (on the line of the `let`,
    // `spec/tools.md` §3.2) all pass the syntax stage and `fmt` does not move them.
    let d = Dir::new("fmt");
    let path = d.file("right.onsa", RIGHT_FORMS);
    let out = Command::new(ONSA).args(["fmt", "--check", &path]).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "fmt --check: {out:?}");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), RIGHT_FORMS);
}

#[test]
fn mem_bulk_is_read_and_then_stopped_with_e0200_until_w9_06() {
    // S-43, §12.4: the syntax of `@mem(bulk)` is read; its meaning (the place of the state in the bulk area) is
    // not in this version, so the one error of the file is the E0200 of a later stage than the syntax (§18.1:
    // what the spec has and the compiler does not handle yet). W9-06 takes this test out.
    let d = Dir::new("bulk");
    let path = d.file("bulk.onsa", RIGHT_FORMS);
    let (code, diags) = check(&path);
    assert_eq!(code, 1, "{diags:?}");
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!(code_of(&diags[0]), "E0200", "{}", diags[0]);
    // The flow `echo` starts at line 35 and its `@mem(bulk) let` is on line 36: the error is inside the flow.
    let line = diags[0]["span"]["line"].as_u64().expect("a line");
    assert!((35..=38).contains(&line), "the E0200 is in the flow `echo`: {}", diags[0]);
}
