//! The names of a `use` that failed, seen from the command line: they are errors where they are used, so
//! the use reports nothing, they are no partner of an E0304, and a `use` that was cut or empty is read
//! as far as it was readable (spec §15.1, §18.1; S-462, R-180; W4-03 U3b1).
//!
//! What the spec fixes, and so what is checked here:
//! - a `use` that fails in the names stage (the name or a step of the path is not there, the head is not
//!   a module or a package, an enumerator cannot be taken, the name is not visible) is one diagnostic for
//!   the `use`, however many names it loses, with no candidate; the names it would have bound are errors
//!   where they are used (a call, a path, a value), so the uses report nothing (§18.1);
//! - a failed name binds nothing, so it makes no E0304 with a real `use` of the name (before or after
//!   it) or with an item, and the name goes to the real one (§18.1);
//! - a failed name where a name is read by its spelling (an effect row, a bound, a derive list) is silent
//!   too, and the effects read next to it in a row stay (S-691 (1));
//! - a `use` cut in the middle of its list (an element that is not a name) is a syntax error, and the
//!   names it read before the cut are failed names too (R-180); an empty list takes no name, so it
//!   silences nothing (§15.1: it is an E0002 whose candidate takes the whole `use` off).
//!
//! The same cases, with the places of the marks, are under `tests/spec/packages/failed_use_*`; here it is
//! the exit code, the number of diagnostics, the candidates and the text after a candidate.
//!
//! Not written here: what a cut `use` makes of the names after the cut and of the other names of its
//! module (the spec leaves it open, §18.1 speaks only of the names that were read); the E0200 of a
//! keyword or a reserved word taken by a `use` (R-266, U3b2).
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause.

mod test_support;

use std::collections::BTreeSet;
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

fn codes(doc: &Value) -> BTreeSet<String> {
    diagnostics(doc).iter().map(|d| str_of(d, "code").to_string()).collect()
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|c| c.to_string()).collect()
}

fn fixes_of(d: &Value) -> &Vec<Value> {
    array_of(d, "fixes")
}

/// The lines (from 1) of `main.onsa` that have a diagnostic, in the order of the document.
fn lines_of(doc: &Value) -> Vec<u64> {
    diagnostics(doc).iter().map(|d| span_of(&d["span"]).line).collect()
}

/// A form of a failed `use`: its tag, the line, the code of its diagnostic, and the (name, use) pairs.
type Form = (&'static str, &'static str, &'static str, Vec<(&'static str, &'static str)>);

const UTIL: &str = "pub fn double(x: I32) -> I32 {\n  x * 2\n}\n\npub enum Color {\n  Red,\n  Green,\n}\n";
const HIDDEN: &str = "priv fn hidden() -> I32 {\n  1\n}\n";

/// A function that gives the value of `expr`, so that a name used in it is a use.
fn user(name: &str, expr: &str) -> String {
    let name = name.to_lowercase();
    format!("\npub fn use_{name}() -> I32 {{\n  {expr}\n}}\n")
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

type FileEdits = (String, Vec<(usize, usize, String)>);

/// Apply every edit of one candidate to the files of `d` (all edits together, from the end of each file).
fn apply(d: &Dir, fix: &Value) {
    let mut by_file: Vec<FileEdits> = Vec::new();
    for e in array_of(fix, "edits") {
        let sp = span_of(&e["span"]);
        let text = std::fs::read_to_string(d.root().join(&sp.file)).unwrap();
        let (a, b) = (offset(&text, sp.line, sp.col), offset(&text, sp.end_line, sp.end_col));
        let rep = str_of(e, "replace").to_string();
        match by_file.iter_mut().find(|(f, _)| *f == sp.file) {
            Some((_, v)) => v.push((a, b, rep)),
            None => by_file.push((sp.file.clone(), vec![(a, b, rep)])),
        }
    }
    for (file, mut edits) in by_file {
        let mut text = std::fs::read_to_string(d.root().join(&file)).unwrap();
        edits.sort_by(|x, y| y.0.cmp(&x.0));
        for (a, b, rep) in edits {
            text.replace_range(a..b, &rep);
        }
        d.write(&file, &text);
    }
}

/// A package with `util.onsa` (the real `double`, and `Color`), `hidden.onsa` (a `priv fn`) and `main.onsa`.
fn with_main(tag: &str, main: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("util.onsa", UTIL);
    d.write("hidden.onsa", HIDDEN);
    d.write("main.onsa", main);
    d
}

// ---- the places that read a name by its spelling --------------------------------------------------

/// §18.1 (S-462, S-675): an effect row (of a function, of a function type, of a closure), a bound and the
/// list of derived traits name a trait or an effect by its spelling; a failed name or the name of an E0304
/// written there is silent too, so the package has the one diagnostic of the `use` or of the E0304. The
/// same forms with a name nothing binds keep their own diagnostic (E0302 in a row and in a bound: the name is not
/// found, §15.1, S-74, R-278; E0416 in a derive list).
#[test]
fn a_failed_name_is_silent_where_it_is_read_by_its_spelling() {
    // (tag, the form, the code of the form with a name nothing binds)
    let forms = [
        ("effects", "pub fn f() -> I32 uses {Fs, Alloc} {\n  1\n}\n", "E0302"),
        ("fn_type", "pub fn f(g: fn() -> I32 uses {Fs}) -> I32 {\n  1\n}\n", "E0302"),
        ("closure", "pub fn f() -> I32 {\n  let g = fn(x: I32) -> I32 uses {Fs} { x }\n  1\n}\n", "E0302"),
        ("bound", "pub fn f[T: Fs](x: T) -> I32 {\n  1\n}\n", "E0302"),
        ("derive", "pub struct S: Fs + PartialEq {\n  a: I32,\n}\n\npub enum E: Fs {\n  A,\n}\n", "E0416"),
    ];
    // (tag, the lines before the form, the code and line of their diagnostic)
    let heads = [
        ("failed", "use util.{Fs}\n\n", "E0302", 1),
        ("e0304", "pub struct Fs {\n  a: I32,\n}\n\npub enum Fs {\n  A,\n}\n\n", "E0304", 5),
    ];
    let mut problems: Vec<String> = Vec::new();
    for (tag, form, code) in forms {
        for (head_tag, head, head_code, line) in heads {
            let d = with_main(&format!("spelling_{tag}_{head_tag}"), &format!("{head}{form}"));
            let (out, doc) = check_json(d.root(), &["."]);
            if out.code != 1 || codes(&doc) != set(&[head_code]) || lines_of(&doc) != vec![line] {
                problems.push(format!(
                    "{tag} after {head_tag}: exit {}, want one {head_code} on line {line}: {doc}",
                    out.code
                ));
            }
        }
        let d = with_main(&format!("spelling_{tag}_unbound"), form);
        let (out, doc) = check_json(d.root(), &["."]);
        if out.code != 1 || codes(&doc) != set(&[code]) {
            problems.push(format!("{tag} with a name nothing binds: exit {}, want {code}: {doc}", out.code));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1, §8.1, §10: a failed name in an effect row is silent where it is written, and only there: the
/// effects read next to it stay. `f` needs `Alloc` whatever the place of `Gone`, so the rt `g` that calls it
/// is an E0901 that names `Alloc`, and `h`, whose row has no `Alloc`, is an E0601 (S-691 (1)).
#[test]
fn the_effects_read_next_to_a_failed_name_stay() {
    for (tag, row) in [("before", "Alloc, Gone"), ("after", "Gone, Alloc")] {
        let main = format!(
            "use util.{{Gone}}\n\npub fn f() -> I32 uses {{{row}}} {{\n  1\n}}\n\n\
             pub rt fn g() -> I32 {{\n  f()\n}}\n\npub fn h() -> I32 {{\n  f()\n}}\n"
        );
        let d = with_main(&format!("alloc_lost_{tag}"), &main);
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), set(&["E0302", "E0901", "E0601"]), "{tag}: {doc}");
        assert_eq!(diagnostics(&doc).len(), 3, "{tag}: {doc}");
        for d in diagnostics(&doc).iter().filter(|d| str_of(d, "code") != "E0302") {
            assert!(d.to_string().contains("Alloc"), "{tag}: the diagnostic names `Alloc`: {d}");
        }
    }
    // §10: an rt function has no `Alloc` in its row (E0902), with a failed name next to it.
    let main = "use util.{Gone}\n\npub rt fn f() -> I32 uses {Alloc, Gone} {\n  1\n}\n";
    let d = with_main("rt_alloc_sig", main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302", "E0902"]), "{doc}");
    assert_eq!(lines_of(&doc), vec![1, 3], "{doc}");
}

/// §18.1: the other names of a row with a failed name keep their own diagnostic, whatever their order
/// (`Nope` binds nothing, an E0302 in each of `f1` and `f2`); a row of a failed name and `Alloc` has none.
#[test]
fn the_other_names_of_a_row_with_a_failed_name_keep_their_diagnostic() {
    let main = "use util.{Gone}\n\npub fn f1() -> I32 uses {Gone, Nope} {\n  1\n}\n\n\
                pub fn f2() -> I32 uses {Nope, Gone} {\n  1\n}\n\n\
                pub fn f3() -> I32 uses {Gone, Alloc} {\n  1\n}\n";
    let d = with_main("multi_effect", main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_eq!(lines_of(&doc), vec![1, 3, 7], "{doc}");
    for d in diagnostics(&doc).iter().filter(|d| span_of(&d["span"]).line != 1) {
        assert!(d.to_string().contains("Nope"), "the E0302 is of `Nope`: {d}");
    }
}

/// §8.1, §15.1: a row of a closure is read as one of a signature. `util.Alloc` is not the `Alloc` of the
/// prelude (`util` has no `Alloc`), so it is an E0302 in a signature and in a closure alike (the name is not found); and the
/// effect variable `e` of the function is an effect variable in the row of a closure in its body.
#[test]
fn a_closure_reads_its_effect_row_as_a_signature_does() {
    let main = "use util\n\npub fn a() -> I32 uses {util.Alloc} {\n  1\n}\n\n\
                pub fn b() -> I32 uses {Alloc} {\n  let g = fn(x: I32) -> I32 uses {util.Alloc} { x }\n  1\n}\n";
    let d = with_main("alloc_path", main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_eq!(lines_of(&doc), vec![3, 8], "{doc}");
    let main = "pub fn apply[e](f: fn() -> I32 uses {e}) -> I32 uses {e} {\n  \
                let g = fn(h: fn() -> I32 uses {e}) -> I32 uses {e} { h() }\n  g(f)\n}\n";
    let d = with_main("closure_effect_var", main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "the row of the closure reads `e` as an effect variable: {doc}");
}

/// §18.1, S-689 (1): a failed name in a bound of the heading of an `impl` is a bound that is not known, so the
/// members are checked: the `<` and the `.foo()` of a `T` with that bound have no diagnostic (no E0401, no
/// E0413), and a real error of a member is reported. An `impl` whose bound is a name nothing binds has a
/// diagnostic of its heading (E0302), so its members are not checked: the `bad` is silent there.
#[test]
fn the_members_of_an_impl_whose_bound_is_a_failed_name_are_checked() {
    let members = "pub struct S[T] {\n  a: T,\n}\n\n\
                   impl[T: Gone] S[T] {\n  pub fn m(self) -> Bool {\n    self.a < self.a\n  }\n\n  \
                   pub fn n(self) -> I32 {\n    self.a.foo()\n  }\n\n  \
                   pub fn bad(self) -> I32 {\n    let a: I32 = true\n    a\n  }\n}\n";
    let d = with_main("impl_bound_chain", &format!("use util.{{Gone}}\n\n{members}"));
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302", "E0401"]), "{doc}");
    assert_eq!(diagnostics(&doc).len(), 2, "the `use` and the `bad`: {doc}");
    assert_eq!(lines_of(&doc), vec![1, 17], "{doc}");
    // The bound nothing binds: an E0302 of the heading, the members are not checked.
    let d = with_main("impl_bound_unbound", &members.replace("Gone", "Nope"));
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(
        codes(&doc),
        set(&["E0302"]),
        "a bound nothing binds is an E0302, and the members are not checked: {doc}"
    );
    assert_eq!(diagnostics(&doc).len(), 1, "{doc}");
}

// ---- the unit goes on after a failed name (S-692 (c), S-689, S-690, R-271) --------------------------------

/// The text without its marks, and the (line, code) of each mark. A mark ` @@E0401` at the end of a line says
/// that the line has a diagnostic of that code, as `//~ E0401` does in a case.
fn marked(text: &str) -> (String, Vec<(u64, String)>) {
    let mut out = String::new();
    let mut marks = Vec::new();
    for (i, l) in text.lines().enumerate() {
        match l.split_once(" @@") {
            Some((line, code)) => {
                marks.push((i as u64 + 1, code.trim().to_string()));
                out.push_str(line);
            }
            None => out.push_str(l),
        }
        out.push('\n');
    }
    (out, marks)
}

/// Check `text` as the `main.onsa` of a package: the diagnostics must be the marked ones, no more and no
/// fewer, and the command must end by 0 or 1. The problem, if there is one.
fn check_marked(tag: &str, text: &str) -> Option<String> {
    let (src, mut want) = marked(text);
    let d = with_main(tag, &src);
    let (out, doc) = check_json(d.root(), &["."]);
    let mut got: Vec<(u64, String)> =
        diagnostics(&doc).iter().map(|x| (span_of(&x["span"]).line, str_of(x, "code").to_string())).collect();
    got.sort();
    want.sort();
    let code = if want.is_empty() { 0 } else { 1 };
    if out.code != code || got != want {
        return Some(format!("{tag}: exit {} (want {code}); want {want:?}, got {got:?}\n{src}", out.code));
    }
    None
}

/// A kind of failed name: the text before the units, with the marks of its own diagnostics; the failed type
/// and the failed length (none for the cut member, which is no const).
struct Failed {
    tag: &'static str,
    head: &'static str,
    ty: &'static str,
    len: Option<&'static str>,
}

/// The three kinds: the names of a `use` that failed (§15.1), the names of an E0304 (two items of one name, the
/// later one is reported), and a member that a syntax error cut off (S-260: `E.Zed` is not read).
const FAILED: [Failed; 3] = [
    Failed { tag: "use", head: "use util.{Gone, LEN} @@E0302\n\n", ty: "Gone", len: Some("LEN") },
    Failed {
        tag: "clash",
        head: "pub struct D {\n  a: I32,\n}\n\npub enum D { @@E0304\n  A(I32),\n  B,\n}\n\n\
               pub const N: U32 = 4\n\npub const N: U32 = 8 @@E0304\n\n",
        ty: "D",
        len: Some("N"),
    },
    Failed { tag: "cut", head: "pub enum E {\n  A,\n  B( @@E0002\n\n", ty: "E.Zed", len: None },
];

/// The head of a kind and a unit of a template, with the kind's names put in. `None` when the template needs
/// a length and the kind has none.
fn build(k: &Failed, template: &str) -> Option<String> {
    let mut t = template.replace("{T}", k.ty);
    if t.contains("{L}") {
        t = t.replace("{L}", k.len?);
    }
    Some(format!("{}{t}", k.head))
}

const REAL: &str = "  let a: I32 = true @@E0401\n  a\n}\n";

/// §18.1 (S-692 (c), S-689 (1), S-690 (1)): a failed name written in a place of the types and declarations is
/// an error type and not a first error of the unit: the unit goes on, the value of that type has no
/// diagnostic (`x + 1`), and the real error after it is reported. One program for each place and each
/// kind of failed name; the diagnostics are the marked ones and nothing else.
#[test]
fn a_unit_goes_on_after_a_failed_name_in_a_type_place() {
    let real = REAL;
    let places: Vec<(&str, String)> = vec![
        ("sig_arg", format!("pub fn u(x: {{T}}) -> I32 {{\n  let b = x + 1\n{real}")),
        ("sig_ret", format!("pub fn u() -> {{T}} {{\n{real}")),
        ("type_arg", format!("pub fn u(o: Option[{{T}}]) -> I32 {{\n{real}")),
        ("type_arg_ret", "pub fn u() -> Option[{T}] {\n  let a: I32 = true @@E0401\n  None\n}\n".to_string()),
        ("fn_arg", format!("pub fn u(f: fn({{T}}) -> I32) -> I32 {{\n{real}")),
        ("fn_ret", format!("pub fn u(f: fn(I32) -> {{T}}) -> I32 {{\n{real}")),
        ("array_len", format!("pub fn u(xs: [I32; {{L}}]) -> I32 {{\n{real}")),
        (
            "const_arg",
            format!(
                "pub struct Ring[T, const CAP: U32] {{\n  data: [T; CAP],\n  head: U32,\n}}\n\n\
                 pub fn u(r: Ring[F32, {{L}}]) -> I32 {{\n{real}"
            ),
        ),
        ("const_type", "pub const K: {T} = 1 + true @@E0401\n".to_string()),
        ("flow_in", "pub flow u(x: {T} at sample) -> F32 at sample {\n  let a: I32 = true @@E0401\n  1.0\n}\n".to_string()),
        ("field", "pub struct S {\n  f: {T},\n  g: Nope, @@E0302\n}\n".to_string()),
        ("variant", "pub enum V {\n  A({T}),\n  B(Nope), @@E0302\n}\n".to_string()),
        ("read_field", format!("pub struct H {{\n  f: {{T}},\n}}\n\npub fn u(s: H) -> I32 {{\n  let v: I32 = s.f\n{real}")),
        (
            "impl_heading",
            "impl {T} {\n  pub fn m(self) -> I32 {\n    let b = self + 1\n    let a: I32 = true @@E0401\n    a\n  }\n}\n"
                .to_string(),
        ),
        (
            "impl_type_arg",
            "pub struct S[T] {\n  a: T,\n}\n\nimpl S[{T}] {\n  pub fn m(self) -> I32 {\n    let b = self.a + 1\n    \
             let a: I32 = true @@E0401\n    a\n  }\n}\n"
                .to_string(),
        ),
        ("local_ann", format!("pub fn u() -> I32 {{\n  let o: {{T}} = 1\n  let b = o + 1\n{real}")),
        ("local_arg_ann", format!("pub fn u() -> I32 {{\n  let o: Option[{{T}}] = None\n{real}")),
        ("local_len_ann", format!("pub fn u() -> I32 {{\n  let xs: [I32; {{L}}] = [1, 2]\n{real}")),
        ("closure_arg", format!("pub fn u() -> I32 {{\n  let g = fn(x: {{T}}) -> I32 {{ 1 }}\n{real}")),
    ];
    let mut problems = Vec::new();
    let mut ran = 0;
    for k in &FAILED {
        for (label, template) in &places {
            if let Some(text) = build(k, template) {
                ran += 1;
                problems.extend(check_marked(&format!("type_place_{}_{label}", k.tag), &text));
            }
        }
    }
    assert!(ran >= 3 * places.len() - 4, "only {ran} programs ran");
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// R-271, §18.1: the error type of a failed name, through an alias, an alias of an alias and written itself,
/// has no use that is checked against it: `None`, `[]` and `Some(1)` as its value are not undecided (no
/// E0406), a call of its value is no E0401, the `match` of its value misses no arm (no E0501), and a struct
/// literal, a path and an associated call through an alias are no E0401. The programs have no mark of their
/// own: the only diagnostics are the ones of the failed name.
#[test]
fn the_error_type_of_a_failed_name_has_no_use_that_is_checked_against_it() {
    let uses: [(&str, &str, bool); 12] = [
        ("none", "pub fn u() -> {X} {\n  None\n}\n", false),
        ("empty", "pub fn u() -> {X} {\n  []\n}\n", false),
        ("some", "pub fn u() -> {X} {\n  Some(1)\n}\n", false),
        ("call", "pub fn u(o: {X}) -> I32 {\n  o()\n}\n", false),
        ("call_args", "pub fn u(o: {X}) -> I32 {\n  o(1, 2)\n}\n", false),
        ("match", "pub fn u(x: {X}) -> I32 {\n  match x {\n    Some(v) => v,\n    None => 0,\n  }\n}\n", false),
        ("match_one_arm", "pub fn u(x: {X}) -> I32 {\n  match x {\n    Some(v) => v,\n  }\n}\n", false),
        ("match_tuple", "pub fn u(x: {X}) -> I32 {\n  match x {\n    (p, q) => p,\n  }\n}\n", false),
        (
            "in_option",
            "pub fn u(x: Option[{X}]) -> I32 {\n  match x {\n    Some(f) => f(),\n    None => 0,\n  }\n}\n",
            false,
        ),
        ("literal", "pub fn u() -> I32 {\n  let s = {X} { a: 1 }\n  1\n}\n", true),
        ("path", "pub fn u() -> I32 {\n  let p = {X}.V\n  1\n}\n", true),
        ("assoc", "pub fn u() -> I32 {\n  let p = {X}.make()\n  1\n}\n", true),
    ];
    let mut problems = Vec::new();
    let mut ran = 0;
    for k in &FAILED {
        for (label, template, alias_only) in uses {
            for (form, x) in [("alias", "A"), ("chain", "B"), ("direct", k.ty)] {
                if alias_only && form == "direct" {
                    continue;
                }
                ran += 1;
                let text =
                    format!("{}pub type A = {}\n\npub type B = A\n\n{}", k.head, k.ty, template.replace("{X}", x));
                problems.extend(check_marked(&format!("error_type_{}_{form}_{label}", k.tag), &text));
            }
        }
    }
    assert!(ran >= 3 * 12 - 6, "only {ran} programs ran");
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1 (S-692 A2, R-271): a part of the error type matches anything in the exhaustiveness of a `match`, and
/// the parts it does not cover elsewhere are reported (E0501); a scrutinee that is all of the error type is not
/// counted. A flow reads a part of the error type as a value it does not know: an element or a field of the
/// error type may cross the `sample` boundary, and the omitted `init` of a delay of it has no diagnostic; what
/// is wrong whatever the type is (a nested array, a tuple) is reported (E0810).
#[test]
fn a_part_of_the_error_type_is_not_known_and_the_rest_is_checked() {
    let units = [
        ("none_only", "pub fn u(o: Option[{X}]) -> I32 {\n  match o { @@E0501\n    None => 1,\n  }\n}\n"),
        ("some_only", "pub fn u(o: Option[{X}]) -> I32 {\n  match o { @@E0501\n    Some(v) => 1,\n  }\n}\n"),
        ("tuple", "pub fn u(o: (Bool, {X})) -> I32 {\n  match o { @@E0501\n    (true, v) => 1,\n  }\n}\n"),
        (
            "result",
            "pub fn u(o: Result[{X}, Bool]) -> I32 {\n  match o { @@E0501\n    Ok(1) => 1,\n    Err(true) => 2,\n  }\n}\n",
        ),
        ("covered_lit", "pub fn u(o: Option[{X}]) -> I32 {\n  match o {\n    Some(1) => 1,\n    None => 2,\n  }\n}\n"),
        (
            "covered_or",
            "pub fn u(o: ({X}, Bool)) -> I32 {\n  match o {\n    (1 | 2, true) => 1,\n    (_, false) => 2,\n  }\n}\n",
        ),
        ("all_error", "pub fn u(o: {X}) -> I32 {\n  match o {\n    1 => 1,\n  }\n}\n"),
        ("flow_in", "pub flow u(x: [{X}; 2] at sample) -> F32 at sample {\n  1.0\n}\n"),
        ("flow_out", "pub flow u(x: F32 at sample) -> [{X}; 2] at sample {\n  [x, x]\n}\n"),
        (
            "flow_field",
            "pub struct W {\n  a: {X},\n  b: F32,\n}\n\npub flow u(x: W at sample) -> F32 at sample {\n  1.0\n}\n",
        ),
        (
            "flow_delay",
            "pub flow u(x: {X} at sample) -> F32 at sample {\n  let p = prev~(x)\n  let q = delay~(x, 8)\n  1.0\n}\n",
        ),
        ("flow_nested", "pub flow u(x: [[{X}; 2]; 2] at sample) -> F32 at sample { @@E0810\n  1.0\n}\n"),
        ("flow_tuple", "pub flow u(x: F32 at sample) -> (F32, {X}) at sample { @@E0810\n  (x, x)\n}\n"),
    ];
    let mut problems = Vec::new();
    let mut ran = 0;
    for (label, template) in units {
        for (form, x) in [("alias", "A"), ("direct", "Gone")] {
            ran += 1;
            let text = format!("use util.{{Gone}} @@E0302\n\npub type A = Gone\n\n{}", template.replace("{X}", x));
            problems.extend(check_marked(&format!("error_part_{form}_{label}"), &text));
        }
    }
    assert_eq!(ran, 2 * units.len());
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1, S-689 (1): a failed name in a bound of a type parameter is a bound that is not known: the operators
/// and the methods that need a bound of that parameter have no diagnostic, in a function, a closure in it and
/// the members of an `impl`, and the unit goes on. The other parameter of the same function, a parameter with
/// no bound and the name nothing binds keep their diagnostics (the controls).
#[test]
fn a_bound_that_is_a_failed_name_is_not_known() {
    // (tag, the head with its marks, the name of the bound)
    let heads = [
        ("use", "use util.{Gone} @@E0302\n\n", "Gone"),
        ("clash", "pub struct Tr {\n  a: I32,\n}\n\npub enum Tr { @@E0304\n  A,\n}\n\n", "Tr"),
    ];
    let units = [
        ("cmp", "pub fn u[T: {B}](x: T) -> Bool {\n  x < x\n}\n"),
        ("eq", "pub fn u[T: {B}](x: T) -> Bool {\n  x == x\n}\n"),
        ("add", "pub fn u[T: {B}](x: T) -> T {\n  x + x\n}\n"),
        ("method", "pub fn u[T: {B}](x: T) -> I32 {\n  x.foo()\n}\n"),
        ("with_copy", "pub fn u[T: Copy + {B}](x: T) -> Bool {\n  x < x\n}\n"),
        ("copy_first", "pub fn u[T: {B} + Copy](x: T) -> I32 {\n  x.foo()\n}\n"),
        (
            "real_error",
            "pub fn u[T: {B}](x: T) -> I32 {\n  let b = x < x\n  let m = x.foo()\n  let a: I32 = true @@E0401\n  a\n}\n",
        ),
        (
            "closure",
            "pub fn u[T: {B}](x: T) -> I32 {\n  let g = fn(y: T) -> Bool { y < y }\n  let a: I32 = true @@E0401\n  a\n}\n",
        ),
        ("other_param", "pub fn u[T: {B}, U](x: T, y: U) -> Bool {\n  let b = x < x\n  y < y @@E0401\n}\n"),
        // S-692 A1: the operators of integers need a bound too.
        (
            "int_ops",
            "pub fn u[T: {B}](x: T, n: U32) -> T {\n  let a = x & x\n  let b = x | x\n  let c = x ^ x\n  \
             let d = x << n\n  let e = x >> n\n  let f = !x\n  let g: I32 = true @@E0401\n  x\n}\n",
        ),
        ("int_ops_num", "pub fn u[T: Num + {B}](x: T) -> T {\n  let a = x & x\n  !a\n}\n"),
        ("struct", "pub struct W[T: {B}] {\n  a: T,\n}\n\npub enum V[T: {B}] {\n  A(T),\n}\n"),
        (
            "impl_members",
            "pub struct W[T: {B}] {\n  a: T,\n}\n\nimpl[T: {B}] W[T] {\n  pub fn lt(self) -> Bool {\n    self.a < self.a\n  }\n\n  \
             pub fn foo(self) -> I32 {\n    self.a.foo()\n  }\n\n  pub fn bad(self) -> I32 {\n    let b = self.a < self.a\n    \
             let a: I32 = true @@E0401\n    a\n  }\n}\n",
        ),
    ];
    let mut problems = Vec::new();
    for (tag, head, name) in heads {
        for (label, unit) in units {
            let text = format!("{head}{}", unit.replace("{B}", name));
            problems.extend(check_marked(&format!("bound_{tag}_{label}"), &text));
        }
    }
    let controls = [
        ("plain_cmp", "pub fn u[T](x: T) -> Bool {\n  x < x @@E0401\n}\n"),
        ("plain_method", "pub fn u[T](x: T) -> I32 {\n  x.foo() @@E0413\n}\n"),
        ("plain_int_op", "pub fn u[T: Num](x: T) -> T {\n  x & x @@E0401\n}\n"),
        ("plain_not", "pub fn u[T: Num](x: T) -> T {\n  !x @@E0401\n}\n"),
        ("unbound", "pub fn u[T: Nope](x: T) -> Bool { @@E0302\n  x < x\n}\n"),
        ("unbound_body_not_checked", "pub fn u[T: Nope](x: T) -> I32 { @@E0302\n  let a: I32 = true\n  a\n}\n"),
        (
            "plain_impl",
            "pub struct P[T] {\n  a: T,\n}\n\nimpl[T] P[T] {\n  pub fn lt(self) -> Bool {\n    self.a < self.a @@E0401\n  }\n\n  \
             pub fn foo(self) -> I32 {\n    self.a.foo() @@E0413\n  }\n}\n",
        ),
    ];
    for (label, unit) in controls {
        problems.extend(check_marked(&format!("bound_control_{label}"), unit));
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1 (the unit paragraph, S-689): an `impl` whose heading has a diagnostic of its own (an E0302 of the type
/// or of a type argument, an E0302 of a bound, a syntax error) is one unit, and its members are not checked;
/// an `impl` whose heading is right has its members checked. The failed name in a heading is no diagnostic of
/// the heading (the test above and `a_unit_goes_on_after_a_failed_name_in_a_type_place`).
#[test]
fn an_impl_whose_heading_has_a_diagnostic_does_not_check_its_members() {
    let s = "pub struct S[T] {\n  a: T,\n}\n\n";
    let member = "  pub fn m(self) -> I32 {\n    let a: I32 = true\n    a\n  }\n}\n";
    let mut problems = Vec::new();
    for (tag, heading) in [
        ("type", "impl Nope { @@E0302"),
        ("type_arg", "impl S[Nope] { @@E0302"),
        ("bound", "impl[T: Nope] S[T] { @@E0302"),
        ("syntax_empty", "impl { @@E0002"),
        ("syntax_number", "impl 1 { @@E0002"),
        ("syntax_where", "impl S[T] where T { @@E0002"),
    ] {
        problems.extend(check_marked(&format!("heading_{tag}"), &format!("{s}{heading}\n{member}")));
    }
    let right = "impl[T] S[T] {\n  pub fn m(self) -> I32 {\n    let a: I32 = true @@E0401\n    a\n  }\n}\n";
    problems.extend(check_marked("heading_right", &format!("{s}{right}")));
    // after an `impl` whose heading cannot be read, the next items are read as always
    problems.extend(check_marked("heading_then_right", &format!("{s}impl {{ @@E0002\n{member}\n{right}")));
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1 (S-692 (b)): a failed name written as a path in an expression or a pattern stops its unit: a call, an
/// associated call, a path, the arms of a `match` (and the arm that is missing), the `~` of a call in a flow,
/// the length of a `delay~` and the range of a `par` have no diagnostic, and nothing after them in the unit
/// has one (the `let a: I32 = true` is silent). A real error before the failed name is the first error of the
/// unit and is reported. The diagnostics of the program are the marked ones and nothing else.
#[test]
fn a_failed_name_in_a_value_place_stops_the_unit() {
    // (tag, the head with the marks of its own diagnostics, the call, the associated call, the path, the two
    // arms of a `match`, the name of a function, the name of a length)
    let kinds = [
        (
            "use",
            "use util.{Gone, gone, LEN} @@E0302\n\n",
            "gone(1)",
            "Gone.make()",
            "Gone.A",
            ["Gone.A(v) => v", "Gone.B => 0"],
            "gone",
            "LEN",
        ),
        (
            "clash",
            "pub fn gone(x: I32) -> I32 {\n  x\n}\n\npub fn gone(x: I32) -> F32 { @@E0304\n  2.0\n}\n\n\
             pub struct D {\n  a: I32,\n}\n\npub enum D { @@E0304\n  A(I32),\n  B,\n}\n\n\
             pub const N: U32 = 4\n\npub const N: U32 = 8 @@E0304\n\n",
            "gone(1)",
            "D.make()",
            "D.A",
            ["D.A(v) => v", "D.B => 0"],
            "gone",
            "N",
        ),
    ];
    let end = "  let a: I32 = true\n  a\n}\n";
    let mut problems = Vec::new();
    for (tag, head, call, assoc, path, arms, func, len) in kinds {
        let units: Vec<(&str, String)> = vec![
            ("call", format!("pub fn u() -> I32 {{\n  let o = {call}\n  let b = o + 1\n{end}")),
            ("assoc", format!("pub fn u() -> I32 {{\n  let o = {assoc}\n{end}")),
            ("path", format!("pub fn u() -> I32 {{\n  let o = {path}\n  let r: Bool = o\n{end}")),
            (
                "branch",
                format!("pub fn u() -> I32 {{\n  let flag = true\n  let o = if flag {{ {call} }} else {{ 2 }}\n{end}"),
            ),
            (
                "closure",
                format!("pub fn u() -> I32 {{\n  let f = fn(x: I32) -> I32 {{ {call} }}\n  let o = f.(1)\n{end}"),
            ),
            (
                "pattern",
                format!(
                    "pub fn u(x: I32) -> I32 {{\n  let r = match x {{\n    {},\n    {},\n  }}\n{end}",
                    arms[0], arms[1]
                ),
            ),
            ("flow_tilde", format!("pub flow u(x: F32 at sample) -> F32 at sample {{\n  let y = {func}~(x)\n{end}")),
            ("flow_plain", format!("pub flow u(x: F32 at sample) -> F32 at sample {{\n  let y = {func}(x)\n{end}")),
            (
                "flow_delay",
                format!("pub flow u(x: F32 at sample) -> F32 at sample {{\n  let y = delay~(x, {len})\n{end}"),
            ),
            (
                "flow_par_range",
                format!(
                    "pub flow u(x: F32 at sample) -> F32 at sample {{\n  let ys = par i in 0 ..< {len} {{\n    x\n  }}\n{end}"
                ),
            ),
            // a real error before the failed name is reported
            ("error_before", format!("pub fn u() -> I32 {{\n  let a: I32 = true @@E0401\n  let o = {call}\n  a\n}}\n")),
        ];
        for (label, unit) in units {
            problems.extend(check_marked(&format!("value_place_{tag}_{label}"), &format!("{head}{unit}")));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// X-3, §18.1: the candidate of the E0302 of a failed `use` (the own package name taken off) makes the name
/// real, so the units that wrote it, and the units that take the values of those, report what they could not
/// report before. They are the units the failed name held back. Everything else stays as it was: the
/// command ends by 0 or 1 (no internal error), the `use` is no longer a diagnostic, and the unit that never
/// wrote the name (`ctl_unit`) has no diagnostic.
#[test]
fn the_candidate_of_a_failed_use_leaves_the_units_that_did_not_read_it_clean() {
    let uses = [
        ("sig_arg", "pub fn held_u(x: Color) -> I32 {\n  let b = x + 1\n  let a: I32 = true\n  a\n}\n"),
        (
            "sig_ret",
            "pub fn held_u() -> Color {\n  let a: I32 = true\n  a\n}\n\npub fn held_user() -> I32 {\n  let o = held_u()\n  let b = o + 1\n  1\n}\n",
        ),
        ("type_arg", "pub fn held_u(o: Option[Color]) -> I32 {\n  let a: I32 = true\n  a\n}\n"),
        ("fn_arg", "pub fn held_u(f: fn(Color) -> I32) -> I32 {\n  let a: I32 = true\n  a\n}\n"),
        ("const_type", "pub const HELD: Color = 1 + true\n\npub fn held_user() -> I32 {\n  HELD + 1\n}\n"),
        ("flow_in", "pub flow held_u(x: Color at sample) -> F32 at sample {\n  let a: I32 = true\n  1.0\n}\n"),
        ("field", "pub struct Holder {\n  f: Color,\n}\n\npub fn held_u(s: Holder) -> I32 {\n  s.f + 1\n}\n"),
        ("impl_heading", "impl Color {\n  pub fn m(self) -> I32 {\n    let a: I32 = true\n    a\n  }\n}\n"),
        ("local_ann", "pub fn held_u() -> I32 {\n  let o: Color = 1\n  let b = o + 1\n  let a: I32 = true\n  a\n}\n"),
        (
            "discarded_ann",
            "pub fn held_u() -> I32 {\n  let _: Color = held_v()\n  1\n}\n\npub fn held_v() -> Color {\n  1\n}\n",
        ),
        ("closure_arg", "pub fn held_u() -> I32 {\n  let g = fn(x: Color) -> I32 { 1 }\n  let a: I32 = true\n  a\n}\n"),
        ("bound", "pub fn held_u[T: Color](x: T) -> Bool {\n  x < x\n}\n"),
        (
            "value_call",
            "pub fn held_u() -> I32 {\n  let o = double(1, 2)\n  let b = o + 1\n  let a: I32 = true\n  a\n}\n",
        ),
        ("value_path", "pub fn held_u() -> I32 {\n  let o = Color.Red\n  let b = o + 1\n  let a: I32 = true\n  a\n}\n"),
        (
            "pattern",
            "pub fn held_u(x: Color) -> I32 {\n  let r = match x {\n    Color.Red => 1,\n  }\n  let a: I32 = true\n  a\n}\n",
        ),
        ("flow_call", "pub flow held_u(x: F32 at sample) -> F32 at sample {\n  let y = double~(x)\n  y\n}\n"),
        (
            "bound_impl",
            "pub struct W[T: Color] {\n  a: T,\n}\n\nimpl[T: Color] W[T] {\n  pub fn lt(self) -> Bool {\n    self.a < self.a\n  }\n}\n",
        ),
    ];
    let mut problems: Vec<String> = Vec::new();
    for (label, unit) in uses {
        let text = format!("use demo.util.{{Color, double}}\n\n{unit}\npub fn ctl_unit() -> I32 {{\n  1\n}}\n");
        let d = with_main(&format!("candidate_{label}"), &text);
        let (out, doc) = check_json(d.root(), &["."]);
        let uses_diag: Vec<&Value> = diagnostics(&doc).iter().filter(|x| str_of(x, "code") == "E0302").collect();
        if out.code != 1 || uses_diag.len() != 1 || fixes_of(uses_diag[0]).len() != 1 {
            problems.push(format!("{label}: want one E0302 with one candidate: exit {}: {doc}", out.code));
            continue;
        }
        apply(&d, &fixes_of(uses_diag[0])[0]);
        let (out, doc) = check_json(d.root(), &["."]);
        let ctl_line = std::fs::read_to_string(d.root().join("main.onsa"))
            .unwrap()
            .lines()
            .position(|l| l.starts_with("pub fn ctl_unit"))
            .unwrap() as u64
            + 1;
        let bad: Vec<&Value> = diagnostics(&doc)
            .iter()
            .filter(|x| str_of(x, "code") == "E0302" || span_of(&x["span"]).line >= ctl_line)
            .collect();
        if out.code > 1 || !bad.is_empty() {
            problems.push(format!(
                "{label}: after the candidate: exit {}, diagnostics of the `use` or of `ctl_unit`: {bad:?}",
                out.code
            ));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

// ---- a failed `use` is one diagnostic, and its names are silent -------------------------------------

/// §18.1 (S-462): each form of a `use` that fails in the names stage is one diagnostic on the line of the
/// `use`, with no candidate, whatever the number of names it loses, and each name it would have bound is
/// silent where it is used. The `use` is the first line of `main.onsa`; the uses follow.
#[test]
fn a_failed_use_is_one_diagnostic_and_its_names_are_silent() {
    // (tag, the `use` line, the code of the diagnostic, [(name, the expression that uses it)])
    let forms: Vec<Form> = vec![
        ("item", "use util.{n1}", "E0302", vec![("n1", "n1(1)")]),
        ("list", "use util.{n1, n2, n3}", "E0302", vec![("n1", "n1(1)"), ("n2", "n2(1)"), ("n3", "n3(1)")]),
        ("head", "use missing.{m1, m2}", "E0302", vec![("m1", "m1(1)"), ("m2", "m2(1)")]),
        ("step", "use util.nomod.{d1, d2}", "E0302", vec![("d1", "d1(1)"), ("d2", "d2(1)")]),
        ("module", "use util.nomod", "E0302", vec![("nomod", "nomod.f(1)")]),
        ("variants", "use util.Color.{Red, Green}", "E0302", vec![("Red", "Red"), ("Green", "Green")]),
        ("std", "use std.math.{sqrtt}", "E0302", vec![("sqrtt", "sqrtt(1)")]),
        ("not_visible", "use hidden.{hidden}", "E0303", vec![("hidden", "hidden()")]),
        ("one_of_two", "use util.{double, n1}", "E0302", vec![("n1", "n1(1)")]),
    ];
    let mut problems: Vec<String> = Vec::new();
    for (tag, line, code, uses) in forms {
        let mut main = format!("{line}\n");
        for (name, expr) in uses {
            main.push_str(&user(name, expr));
        }
        let d = with_main(&format!("failed_{tag}"), &main);
        let (out, doc) = check_json(d.root(), &["."]);
        let ok = out.code == 1
            && codes(&doc) == set(&[code])
            && lines_of(&doc) == vec![1]
            && fixes_of(&diagnostics(&doc)[0]).is_empty();
        if !ok {
            problems.push(format!("{tag}: exit {}, want one {code} on line 1, no candidate: {doc}", out.code));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §18.1: the module that has the failed `use` is the one that is silent; the names are not bound anywhere
/// else, so a call of the same name in another module is the E0302 of a name that no `use` took.
#[test]
fn the_failed_names_are_the_names_of_the_module_that_has_the_use() {
    let d = Dir::pkg("failed_local");
    d.write("util.onsa", UTIL);
    d.write("first.onsa", &format!("use util.{{n1}}\n{}", user("n1", "n1(1)")));
    d.write("second.onsa", &user("n1", "n1(1)"));
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let found: BTreeSet<(String, String)> =
        diagnostics(&doc).iter().map(|x| (str_of(x, "code").to_string(), span_of(&x["span"]).file)).collect();
    let want: BTreeSet<(String, String)> = [("E0302", "first.onsa"), ("E0302", "second.onsa")]
        .iter()
        .map(|(c, f)| (c.to_string(), f.to_string()))
        .collect();
    assert_eq!(found, want, "{doc}");
    assert_eq!(diagnostics(&doc).len(), 2, "one in each: {doc}");
}

/// §18.1: the diagnostics of a file are the ones of its own module, so `check` of the file that has the
/// failed `use` shows the `use`, and `check` of a file that only uses a name of another module's failed
/// `use` is clean (it has none of its own).
#[test]
fn check_of_one_file_shows_the_diagnostics_of_that_file() {
    let d = Dir::pkg("failed_one_file");
    d.write("util.onsa", UTIL);
    d.write("first.onsa", "use util.{n1}\n");
    d.write("second.onsa", "use util.{double}\n");
    let (out, doc) = check_json(d.root(), &["first.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(lines_of(&doc), vec![1], "{doc}");
    let (out, doc) = check_json(d.root(), &["second.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

// ---- a failed `use` is no partner of an E0304 ---------------------------------------------------------

/// §18.1 (S-462): a failed `use` binds nothing, so it is no E0304 with a real `use` of the name written
/// before or after it, with an item, or with another failed `use`; the diagnostics are the E0302 of each
/// failed `use` and nothing else. The calls say where the name goes: the real `double` returns `I32`, so a
/// `Bool` is E0401 whichever way the names are written, and a call that went to a failed name gives nothing.
#[test]
fn a_failed_use_makes_no_clash_and_the_name_goes_to_the_real_one() {
    let item = "pub fn double(x: I32) -> I32 {\n  x\n}\n";
    let call = "\npub fn calls() -> I32 {\n  let _: Bool = double(1)\n  0\n}\n";
    // (tag, the text before the call, the number of failed `use` lines)
    let forms: [(&str, String, usize); 6] = [
        ("failed_first", "use nomod.{double}\nuse util.{double}\n".to_string(), 1),
        ("failed_last", "use util.{double}\nuse nomod.{double}\n".to_string(), 1),
        ("failed_then_item", format!("use nomod.{{double}}\n{item}"), 1),
        ("item_then_failed", format!("{item}use nomod.{{double}}\n"), 1),
        ("two_failed_and_real", "use nomod.{double}\nuse util.{double}\nuse other.{double}\n".to_string(), 2),
        ("failed_in_the_middle_of_a_list", "use util.{double}\nuse nomod.{double, other}\n".to_string(), 1),
    ];
    for (tag, before, failed) in forms {
        let d = with_main(&format!("clash_{tag}"), &format!("{before}{call}"));
        let (out, doc) = check_json(d.root(), &["."]);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        let found: Vec<&str> = diagnostics(&doc).iter().map(|x| str_of(x, "code")).collect();
        let mut want = vec!["E0302"; failed];
        want.push("E0401");
        let mut got = found.clone();
        got.sort();
        want.sort();
        assert_eq!(got, want, "{tag}: no E0304, one E0302 for each failed use, one E0401 for the real name: {doc}");
    }
}

// ---- a `use` cut in the middle of its list, and an empty list (R-180) -------------------------------

/// R-180, §18.1: a `use` cut in the middle of its list is one E0002, and the names it read before the cut
/// are silent where they are used (they are not in `util`, so they would be E0302 as written). The
/// elements that cut the list: an integer, a missing comma, a path, an alias, `self`.
#[test]
fn the_names_a_cut_use_read_before_the_cut_are_silent() {
    // (tag, the `use` line, the name that it read before the cut)
    let forms = [
        ("integer", "use util.{gone, 3, other}", "gone"),
        ("comma", "use util.{gone other}", "gone"),
        ("path", "use util.{gone, other.x}", "gone"),
        ("alias", "use util.{gone as other}", "gone"),
        ("self", "use util.{gone, self}", "gone"),
    ];
    let mut problems: Vec<String> = Vec::new();
    for (tag, line, name) in forms {
        let main = format!("{line}\n{}", user(name, &format!("{name}(1)")));
        let d = with_main(&format!("cut_{tag}"), &main);
        let (out, doc) = check_json(d.root(), &["."]);
        if out.code != 1 || codes(&doc) != set(&["E0002"]) || lines_of(&doc) != vec![1] {
            problems.push(format!("{tag}: exit {}, want one E0002 on line 1: {doc}", out.code));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// R-180 (its `判断`), S-462: a `use` cut in the middle of its list may have taken any name after the cut,
/// so every name its module does not find is silent where it is used (the mark of the module): the name
/// after the cut (`gone_b`) and a name no `use` wrote (`other_unknown`). Each use is in a function of its
/// own, so that each is a unit of its own; the only diagnostic is the E0002 of the `use`.
#[test]
fn a_cut_use_silences_every_name_its_module_does_not_find() {
    let main = format!(
        "use util.{{gone_a, 3, gone_b}}\n{}{}{}",
        user("a", "gone_a(1)"),
        user("b", "gone_b(1)"),
        user("c", "other_unknown(1)")
    );
    let d = with_main("cut_module", &main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0002"]), "{doc}");
    assert_eq!(lines_of(&doc), vec![1], "{doc}");
    // The mark is of the module: another module still reports its own unknown name.
    d.write("other.onsa", &user("d", "other_unknown(1)"));
    let (_, doc) = check_json(d.root(), &["."]);
    assert_eq!(codes(&doc), set(&["E0002", "E0302"]), "{doc}");
}

/// §15.1, R-180: an empty list takes no name, so it silences nothing: `double(1)` is the E0302 of a name that
/// no `use` took. The E0002 of the empty list (S-515) is the next test's, and is left out here.
#[test]
fn an_empty_list_takes_no_name_and_silences_nothing() {
    let main = format!("use util.{{}}\n{}", user("double", "double(1)"));
    let d = with_main("empty_list_names", &main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let others: Vec<&Value> = diagnostics(&doc).iter().filter(|x| str_of(x, "code") != "E0002").collect();
    assert_eq!(others.len(), 1, "{doc}");
    assert_eq!(str_of(others[0], "code"), "E0302", "{doc}");
    assert!(span_of(&others[0]["span"]).line > 1, "the E0302 is of the use of `double`: {doc}");
}

/// §15.1, S-515: the empty list is an E0002 of the `use`. The candidate takes the whole `use` off (§15.1),
/// and after it only the E0302 is left. With a comment inside there is no candidate.
#[test]
#[ignore = "W5-11: the empty list of a use is not an E0002 yet (S-515)"]
fn an_empty_list_is_an_e0002_whose_candidate_takes_the_use_off() {
    let main = format!("use util.{{}}\n{}", user("double", "double(1)"));
    let d = with_main("empty_list", &main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0002", "E0302"]), "{doc}");
    let e0002 = diagnostics(&doc).iter().find(|x| str_of(x, "code") == "E0002").unwrap().clone();
    assert_eq!(span_of(&e0002["span"]).line, 1, "{doc}");
    let fixes = fixes_of(&e0002);
    assert_eq!(fixes.len(), 1, "the candidate takes the `use` off: {e0002}");
    apply(&d, &fixes[0]);
    let text = std::fs::read_to_string(d.root().join("main.onsa")).unwrap();
    assert!(!text.contains("use util"), "the `use` is taken off: {text:?}");
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "after the candidate: {doc}");
    // A comment inside the empty list: no candidate.
    let main = format!("use util.{{\n  // nothing\n}}\n{}", user("double", "double(1)"));
    let d = with_main("empty_list_comment", &main);
    let (_, doc) = check_json(d.root(), &["."]);
    let e0002: Vec<&Value> = diagnostics(&doc).iter().filter(|x| str_of(x, "code") == "E0002").collect();
    assert_eq!(e0002.len(), 1, "{doc}");
    assert!(fixes_of(e0002[0]).is_empty(), "a comment inside: no candidate: {doc}");
}
