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
//!   too, and the effects read next to it in a row stay (S-691, the reading (1) for now);
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
/// same forms with a name nothing binds keep their own diagnostic (E0200, E0416).
#[test]
fn a_failed_name_is_silent_where_it_is_read_by_its_spelling() {
    // (tag, the form, the code of the form with a name nothing binds)
    let forms = [
        ("effects", "pub fn f() -> I32 uses {Fs, Alloc} {\n  1\n}\n", "E0200"),
        ("fn_type", "pub fn f(g: fn() -> I32 uses {Fs}) -> I32 {\n  1\n}\n", "E0200"),
        ("closure", "pub fn f() -> I32 {\n  let g = fn(x: I32) -> I32 uses {Fs} { x }\n  1\n}\n", "E0200"),
        ("bound", "pub fn f[T: Fs](x: T) -> I32 {\n  1\n}\n", "E0200"),
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
/// is an E0901 that names `Alloc`, and `h`, whose row has no `Alloc`, is an E0601 (S-691, the reading (1)
/// it takes for now).
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
/// (`Nope` binds nothing, an E0200 in each of `f1` and `f2`); a row of a failed name and `Alloc` has none.
#[test]
fn the_other_names_of_a_row_with_a_failed_name_keep_their_diagnostic() {
    let main = "use util.{Gone}\n\npub fn f1() -> I32 uses {Gone, Nope} {\n  1\n}\n\n\
                pub fn f2() -> I32 uses {Nope, Gone} {\n  1\n}\n\n\
                pub fn f3() -> I32 uses {Gone, Alloc} {\n  1\n}\n";
    let d = with_main("multi_effect", main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302", "E0200"]), "{doc}");
    assert_eq!(lines_of(&doc), vec![1, 3, 7], "{doc}");
    for d in diagnostics(&doc).iter().filter(|d| str_of(d, "code") == "E0200") {
        assert!(d.to_string().contains("Nope"), "the E0200 is of `Nope`: {d}");
    }
}

/// §8.1, §15.1: a row of a closure is read as one of a signature. `util.Alloc` is not the `Alloc` of the
/// prelude (`util` has no `Alloc`), so it is an E0200 in a signature and in a closure alike; and the
/// effect variable `e` of the function is an effect variable in the row of a closure in its body.
#[test]
fn a_closure_reads_its_effect_row_as_a_signature_does() {
    let main = "use util\n\npub fn a() -> I32 uses {util.Alloc} {\n  1\n}\n\n\
                pub fn b() -> I32 uses {Alloc} {\n  let g = fn(x: I32) -> I32 uses {util.Alloc} { x }\n  1\n}\n";
    let d = with_main("alloc_path", main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0200"]), "{doc}");
    assert_eq!(lines_of(&doc), vec![3, 8], "{doc}");
    let main = "pub fn apply[e](f: fn() -> I32 uses {e}) -> I32 uses {e} {\n  \
                let g = fn(h: fn() -> I32 uses {e}) -> I32 uses {e} { h() }\n  g(f)\n}\n";
    let d = with_main("closure_effect_var", main);
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 0, "the row of the closure reads `e` as an effect variable: {doc}");
}

/// §18.1, §15.1: a failed name in a bound of the heading of an `impl` is an error of the heading, so the
/// members are not checked: no E0401 for the `<` of a `T` that has no `PartialOrd`, no E0413 for its `foo`
/// (S-689, the reading it takes for now). The `impl` with a bound nothing binds keeps its E0200.
#[test]
fn the_members_of_an_impl_whose_bound_is_a_failed_name_are_not_checked() {
    let members = "pub struct S[T] {\n  a: T,\n}\n\n\
                   impl[T: Gone] S[T] {\n  pub fn m(self) -> Bool {\n    self.a < self.a\n  }\n\n  \
                   pub fn n(self) -> I32 {\n    self.a.foo()\n  }\n}\n";
    let d = with_main("impl_bound_chain", &format!("use util.{{Gone}}\n\n{members}"));
    let (out, doc) = check_json(d.root(), &["."]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(codes(&doc), set(&["E0302"]), "{doc}");
    assert_eq!(lines_of(&doc), vec![1], "{doc}");
    let d = with_main("impl_bound_unbound", members);
    let (_, doc) = check_json(d.root(), &["."]);
    assert!(codes(&doc).contains("E0200"), "a bound nothing binds is an E0200: {doc}");
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
