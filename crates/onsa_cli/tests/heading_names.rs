//! The names written in the head of a declaration against how far the declaration reaches (spec §15.1,
//! §11.6; S-144, S-665, S-664, S-662; W4-03 U4b/t).
//!
//! What the spec fixes, and so what is checked:
//! - §15.1 (S-144, S-665): a name (a type, and the types inside a type) written in the head of a declaration
//!   that has a visibility, or takes one, cannot be narrower than what the declaration reaches: E0303 on the
//!   name that was written, with no candidate. The declaration reaches as far as its word says (`pub`, none,
//!   `priv`), a field as far as its struct unless it has `priv`, the contents of a variant as far as the enum,
//!   and a member of an `impl` as far as the narrower of itself and its type. The places: the arguments and the
//!   return type of a function, the right side of an alias, the type of a constant, a field, a variant, a
//!   member of an `impl` (a function and a constant), the inputs and the output of a flow. The oracle is
//!   written once here from that rule (`rank`), and a generated file of the products of the places, the
//!   shapes of a type, and the three visibilities of the declaration and of the type is checked against it;
//! - §15.1, §4.4 (S-700): an alias makes no new type and is judged by the type it stands for, whatever its
//!   own word; its right side is judged where it is declared; a generic type is as narrow as its narrowest part;
//! - §11.6 (S-664): a flow is checked at its head, once, whatever the number of narrow names in it;
//! - §15.1 (S-662): a `pub` on a member of an `impl` of a type with no word or `priv` is E0020 whose one
//!   candidate takes the word off, with a note; the programs that the candidate gives are clean.
//!
//! Not asked: the text of a message and of a note, the end of the span, and which of two narrow names is
//! the one that is reported in a head (the spec fixes the one error of a unit, §18.1, not the order).
//! The same forms, with the places of the marks, are under `tests/spec/module/heading_*`.

mod test_support;

use serde_json::Value;
use test_support::*;

/// The three visibilities, from the narrowest: `priv` (the module), none (the package), `pub` (outside).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Vis {
    Priv,
    Pkg,
    Pub,
}

const ALL: [Vis; 3] = [Vis::Priv, Vis::Pkg, Vis::Pub];

impl Vis {
    /// How far it reaches: a bigger number is further.
    fn rank(self) -> u8 {
        match self {
            Vis::Priv => 0,
            Vis::Pkg => 1,
            Vis::Pub => 2,
        }
    }

    /// The word and the space after it, as written in the source.
    fn word(self) -> &'static str {
        match self {
            Vis::Priv => "priv ",
            Vis::Pkg => "",
            Vis::Pub => "pub ",
        }
    }

    fn tag(self) -> &'static str {
        match self {
            Vis::Priv => "Priv",
            Vis::Pkg => "Pkg",
            Vis::Pub => "Pub",
        }
    }

    fn narrower_of(self, other: Vis) -> Vis {
        if self.rank() <= other.rank() { self } else { other }
    }

    /// The name of the struct of this visibility.
    fn ty(self) -> String {
        format!("Ty{}", self.tag())
    }
}

/// A shape of a type that has one type `T` in it: the text of the type and a value of it.
struct Shape {
    name: &'static str,
    ty: fn(&str) -> String,
    value: fn(&str) -> String,
}

const PLAIN: Shape = Shape { name: "plain", ty: |t| t.to_string(), value: |t| format!("{t} {{ x: 1.0 }}") };
const OPTION: Shape = Shape { name: "option", ty: |t| format!("Option[{t}]"), value: |_| "None".to_string() };
const ARRAY: Shape =
    Shape { name: "array", ty: |t| format!("[{t}; 2]"), value: |t| format!("[{t} {{ x: 1.0 }}, {t} {{ x: 2.0 }}]") };
const TUPLE: Shape =
    Shape { name: "tuple", ty: |t| format!("(I32, {t})"), value: |t| format!("(1, {t} {{ x: 1.0 }})") };
const FN_TYPE: Shape =
    Shape { name: "fn", ty: |t| format!("fn({t}) -> I32"), value: |t| format!("fn(q: {t}) -> I32 {{ 0 }}") };
/// A generic struct that is `pub` itself: the type is as narrow as the argument.
const WRAPPED: Shape =
    Shape { name: "wrapped", ty: |t| format!("WrapPub[{t}]"), value: |t| format!("WrapPub {{ v: {t} {{ x: 1.0 }} }}") };

/// The shapes that every place takes.
const SHAPES: [&Shape; 6] = [&PLAIN, &OPTION, &ARRAY, &TUPLE, &FN_TYPE, &WRAPPED];

/// A struct of each visibility.
fn types_prelude() -> String {
    let mut s = String::new();
    for v in ALL {
        s.push_str(&format!("{}struct {} {{ x: F32 }}\n", v.word(), v.ty()));
    }
    s
}

/// The prelude of the generated file: a struct of each visibility, and a generic one that is `pub`.
fn prelude() -> String {
    types_prelude() + "pub struct WrapPub[T] { v: T }\n"
}

/// One generated declaration: the line it is on (counted by the file), the type whose name is narrow or
/// not, and what the declaration reaches.
struct Case {
    line: usize,
    what: String,
    reach: Vis,
    ty: Vis,
}

struct Gen {
    text: String,
    lines: usize,
    cases: Vec<Case>,
    n: usize,
}

impl Gen {
    fn new() -> Gen {
        let text = prelude();
        let lines = text.lines().count();
        Gen { text, lines, cases: vec![], n: 0 }
    }

    /// Add a line `decl` (one line) whose head names `ty` and reaches `reach`.
    fn decl(&mut self, what: &str, decl: String, reach: Vis, ty: Vis) {
        self.text.push_str(&decl);
        self.text.push('\n');
        self.lines += 1;
        self.cases.push(Case { line: self.lines, what: what.to_string(), reach, ty });
    }

    /// Add a line that is no case (an owner of the members of an `impl`).
    fn aside(&mut self, line: String) {
        self.text.push_str(&line);
        self.text.push('\n');
        self.lines += 1;
    }

    fn id(&mut self) -> usize {
        self.n += 1;
        self.n
    }
}

/// The text of the type `T` with the shape, and a value of it.
fn shaped(shape: &Shape, t: Vis) -> (String, String) {
    let name = t.ty();
    ((shape.ty)(&name), (shape.value)(&name))
}

/// The types in a type reach as far as the narrowest part, and `WrapPub` is `pub`: the part that is narrow
/// is the argument.
fn generate() -> Gen {
    let mut g = Gen::new();
    for dv in ALL {
        let dw = dv.word();
        for tv in ALL {
            for shape in SHAPES {
                let (ty, value) = shaped(shape, tv);
                let sh = shape.name;
                let n = g.id();
                g.decl(&format!("fn argument {sh}"), format!("{dw}fn f{n}(a: {ty}) -> I32 {{ 0 }}"), dv, tv);
                let n = g.id();
                g.decl(&format!("fn return {sh}"), format!("{dw}fn f{n}() -> {ty} {{ {value} }}"), dv, tv);
                let n = g.id();
                g.decl(&format!("rt fn argument {sh}"), format!("{dw}rt fn f{n}(a: {ty}) -> I32 {{ 0 }}"), dv, tv);
                let n = g.id();
                g.decl(&format!("alias {sh}"), format!("{dw}type A{n} = {ty}"), dv, tv);
                if shape.name != "fn" {
                    let n = g.id();
                    g.decl(&format!("const {sh}"), format!("{dw}const C{n}: {ty} = {value}"), dv, tv);
                }
                let n = g.id();
                g.decl(&format!("field {sh}"), format!("{dw}struct S{n} {{ f: {ty} }}"), dv, tv);
                // A `priv` field reaches the module alone, whatever the struct is.
                let n = g.id();
                g.decl(&format!("priv field {sh}"), format!("{dw}struct S{n} {{ priv f: {ty} }}"), Vis::Priv, tv);
                let n = g.id();
                g.decl(&format!("variant {sh}"), format!("{dw}enum E{n} {{ A({ty}) }}"), dv, tv);
                if shape.name != "fn" {
                    let n = g.id();
                    g.decl(
                        &format!("flow block input {sh}"),
                        format!("{dw}flow g{n}(x: F32 at sample, k: {ty} at block) -> F32 at sample {{ x }}"),
                        dv,
                        tv,
                    );
                    let n = g.id();
                    g.decl(
                        &format!("flow init input {sh}"),
                        format!("{dw}flow g{n}(x: F32 at sample, k: {ty} at init) -> F32 at sample {{ x }}"),
                        dv,
                        tv,
                    );
                }
            }
        }
    }
    // The members of an `impl`: the member reaches as far as the narrower of itself and the type. A member
    // wider than its type is E0020 (S-662) and is left to another test.
    for tv in ALL {
        for shape in SHAPES {
            let (ty, value) = shaped(shape, tv);
            let sh = shape.name;
            for ov in ALL {
                for mv in ALL {
                    if mv.rank() > ov.rank() {
                        continue;
                    }
                    let reach = mv.narrower_of(ov);
                    let n = g.id();
                    g.aside(format!("{}struct Own{n} {{ x: F32 }}", ov.word()));
                    g.decl(
                        &format!("member fn {sh} of a {} type", ov.tag()),
                        format!("impl Own{n} {{ {}fn m() -> {ty} {{ {value} }} }}", mv.word()),
                        reach,
                        tv,
                    );
                    if shape.name != "fn" {
                        let n = g.id();
                        g.aside(format!("{}struct Own{n} {{ x: F32 }}", ov.word()));
                        g.decl(
                            &format!("member const {sh} of a {} type", ov.tag()),
                            format!("impl Own{n} {{ {}const K: {ty} = {value} }}", mv.word()),
                            reach,
                            tv,
                        );
                    }
                }
            }
        }
    }
    g
}

/// The column (from 1) of the first `name` as a whole word in `line`.
fn column_of(line: &str, name: &str) -> usize {
    let bytes = line.as_bytes();
    let mut from = 0;
    while let Some(i) = line[from..].find(name) {
        let at = from + i;
        let before = at == 0 || !(bytes[at - 1].is_ascii_alphanumeric() || bytes[at - 1] == b'_');
        let end = at + name.len();
        let after = end >= bytes.len() || !(bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_');
        if before && after {
            return at + 1;
        }
        from = at + 1;
    }
    panic!("no `{name}` in {line:?}")
}

/// `check --json` of one file in a scratch directory: the diagnostics.
fn check_file(tag: &str, text: &str) -> Vec<Value> {
    let d = Dir::bare(tag);
    d.write("m.onsa", text);
    let out = run(d.root(), &["check", "--json", "m.onsa"]);
    assert!(!out.stderr.contains("internal error"), "{tag}: {}", out.stderr);
    assert!(out.code == 0 || out.code == 1, "{tag}: exit {}: {}{}", out.code, out.stdout, out.stderr);
    let doc = doc_of(&out);
    assert_eq!(out.code == 0, diagnostics(&doc).is_empty(), "{tag}: exit code and diagnostics: {doc}");
    diagnostics(&doc).clone()
}

fn fixes_len(d: &Value) -> usize {
    d.get("fixes").and_then(Value::as_array).map_or(0, Vec::len)
}

// ---- the places and the shapes against the reach -------------------------------------------------

/// §15.1 (S-144, S-665): in every place, for every shape of a type and every pair of visibilities, the
/// E0303 is where the type is narrower than the reach and nowhere else: one on the line, at the name that
/// was written, with no candidate.
#[test]
fn every_place_and_shape_has_the_error_exactly_where_the_name_is_narrower_than_the_reach() {
    let g = generate();
    assert!(g.cases.len() > 500, "the file is a product of the places: {}", g.cases.len());
    let diags = check_file("sweep", &g.text);
    let lines: Vec<&str> = g.text.lines().collect();
    // What the declarations do not say about themselves: no other diagnostic at all.
    for d in &diags {
        assert_eq!(str_of(d, "code"), "E0303", "only E0303 is expected: {d}");
        assert_eq!(fixes_len(d), 0, "E0303 has no candidate: {d}");
    }
    let mut seen = std::collections::BTreeMap::new();
    for d in &diags {
        let s = span_of(&d["span"]);
        *seen.entry(s.line as usize).or_insert(0usize) += 1;
        let line = lines[s.line as usize - 1];
        assert_eq!(s.col as usize, column_of(line, &narrow_name_of(line)), "the name that was written: {d}\n{line}");
    }
    let mut wrong = Vec::new();
    for c in &g.cases {
        let narrow = c.ty.rank() < c.reach.rank();
        let want = usize::from(narrow);
        let got = seen.get(&c.line).copied().unwrap_or(0);
        if got != want {
            wrong.push(format!(
                "{}: {} (reach {:?}, type {:?}): {got} errors, want {want}\n    {}",
                c.line,
                c.what,
                c.reach,
                c.ty,
                lines[c.line - 1]
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} lines are wrong:\n{}",
        wrong.len(),
        wrong.iter().take(25).cloned().collect::<Vec<_>>().join("\n")
    );
    // A line that is not a case has no error.
    let case_lines: std::collections::BTreeSet<usize> = g.cases.iter().map(|c| c.line).collect();
    for l in seen.keys() {
        assert!(case_lines.contains(l), "an error on a line that is no case: {}", lines[l - 1]);
    }
}

/// The name of the struct on a generated line (a line has the one of `TyPriv`, `TyPkg`, `TyPub`; the value
/// in the body repeats it, and the first one is the one written in the head).
fn narrow_name_of(line: &str) -> String {
    for v in [Vis::Priv, Vis::Pkg, Vis::Pub] {
        let name = v.ty();
        if line.contains(&name) {
            return name;
        }
    }
    panic!("no type on {line:?}")
}

// ---- an alias is judged by the type it stands for ----------------------------------------------

/// §15.1, §4.4 (S-700): an alias makes no new type. A function that names the alias is E0303 when the type
/// the alias stands for is narrower than the function, whatever the word of the alias; the alias is E0303
/// itself where it names a type narrower than itself.
#[test]
fn an_alias_is_judged_by_the_type_it_stands_for_and_not_by_its_own_word() {
    let mut text = types_prelude();
    let mut want: Vec<(usize, bool)> = Vec::new();
    let mut line = text.lines().count();
    let mut n = 0;
    for av in ALL {
        for tv in ALL {
            n += 1;
            let alias = format!("Alias{n}");
            text.push_str(&format!("{}type {alias} = {}\n", av.word(), tv.ty()));
            line += 1;
            want.push((line, tv.rank() < av.rank()));
            for dv in ALL {
                n += 1;
                text.push_str(&format!("{}fn use{n}(a: {alias}) -> I32 {{ 0 }}\n", dv.word()));
                line += 1;
                want.push((line, tv.rank() < dv.rank()));
            }
        }
    }
    let diags = check_file("alias", &text);
    for d in &diags {
        assert_eq!(str_of(d, "code"), "E0303", "{d}");
        assert_eq!(fixes_len(d), 0, "{d}");
    }
    let got: Vec<usize> = diags.iter().map(|d| span_of(&d["span"]).line as usize).collect();
    let mut expect: Vec<usize> = want.iter().filter(|(_, e)| *e).map(|(l, _)| *l).collect();
    expect.sort();
    let mut got_sorted = got.clone();
    got_sorted.sort();
    assert_eq!(got_sorted, expect, "the lines with an error\n{text}");
}

/// §15.1, §4.4 (S-700): an alias is judged by the types within the type it stands for (the argument, the
/// element, the parameter), and an alias of an alias by the type at its end; the aliases here name a
/// narrow type of their own word, so they have no error themselves.
#[test]
fn an_alias_is_judged_by_the_types_within_the_type_it_stands_for() {
    let mut text = prelude();
    let mut line = text.lines().count();
    let mut expect: Vec<usize> = Vec::new();
    let mut n = 0;
    for tv in ALL {
        for shape in SHAPES {
            let (ty, _) = shaped(shape, tv);
            n += 1;
            text.push_str(&format!("{}type B{n} = {ty}\n{}type C{n} = B{n}\n", tv.word(), tv.word()));
            line += 2;
            for (alias, dv) in ALL.iter().flat_map(|&dv| [(format!("B{n}"), dv), (format!("C{n}"), dv)]) {
                line += 1;
                let f = format!("use_{}_{}", alias.to_lowercase(), dv.tag().to_lowercase());
                text.push_str(&format!("{}fn {f}(a: {alias}) -> I32 {{ 0 }}\n", dv.word()));
                if tv.rank() < dv.rank() {
                    expect.push(line);
                }
            }
        }
    }
    let diags = check_file("alias_within", &text);
    for d in &diags {
        assert_eq!(str_of(d, "code"), "E0303", "{d}");
        assert_eq!(fixes_len(d), 0, "{d}");
    }
    let mut got: Vec<usize> = diags.iter().map(|d| span_of(&d["span"]).line as usize).collect();
    got.sort();
    assert_eq!(got, expect, "the lines with an error\n{text}");
}

/// §15.1: a generic type is as narrow as its narrowest part: `Wrap[T]` names the generic struct and `T`.
#[test]
fn a_generic_type_is_as_narrow_as_the_struct_and_the_argument() {
    let mut text = types_prelude();
    let mut line = text.lines().count();
    for wv in ALL {
        line += 1;
        text.push_str(&format!("{}struct Wrap{}[T] {{ v: T }}\n", wv.word(), wv.tag()));
    }
    let mut expect: Vec<usize> = Vec::new();
    let mut n = 0;
    for wv in ALL {
        for tv in ALL {
            for dv in ALL {
                n += 1;
                line += 1;
                text.push_str(&format!("{}fn f{n}(a: Wrap{}[{}]) -> I32 {{ 0 }}\n", dv.word(), wv.tag(), tv.ty()));
                if wv.narrower_of(tv).rank() < dv.rank() {
                    expect.push(line);
                }
            }
        }
    }
    let diags = check_file("generic", &text);
    for d in &diags {
        assert_eq!(str_of(d, "code"), "E0303", "{d}");
        assert_eq!(fixes_len(d), 0, "{d}");
    }
    let mut got: Vec<usize> = diags.iter().map(|d| span_of(&d["span"]).line as usize).collect();
    got.sort();
    assert_eq!(got, expect, "the lines with an error\n{text}");
}

// ---- a flow is checked at its head, once --------------------------------------------------------

/// §11.6 (S-664): the inputs and the output of a flow are in its head; a `pub` flow with narrow names in
/// them (`Pair`, `Hid`; the aliases of `F32` are judged by `F32`, S-700) has the one error, and the items
/// that the flow generates (`State`, `Params`, `Config`, `Out`, `init`, `process`, `render`) have none of
/// their own.
#[test]
fn a_flow_with_narrow_names_in_all_its_inputs_and_its_output_has_the_one_error() {
    let text = "struct Pair { a: F32 }\n\
                priv struct Hid { a: F32 }\n\
                type Gain = F32\n\
                priv type Level = F32\n\
                pub flow f(p: Pair at sample, g: Gain at block, k: Level at init) -> Hid at sample { Hid { a: p.a } }\n\
                pub flow split(x: F32 at sample) -> Pair at sample { Pair { a: x } }\n\
                flow fine(x: F32 at sample, g: Gain at block) -> Pair at sample { Pair { a: x * g } }\n";
    let diags = check_file("flow_once", text);
    let lines: Vec<(String, u64)> =
        diags.iter().map(|d| (str_of(d, "code").to_string(), span_of(&d["span"]).line)).collect();
    assert_eq!(lines, [("E0303".to_string(), 5), ("E0303".to_string(), 6)], "{diags:?}");
    for d in &diags {
        assert_eq!(fixes_len(d), 0, "{d}");
    }
}

/// §11.6, §15.1: the items of a flow that has no error are fine in the head of a `pub` function of the
/// module when the flow is `pub` (they take its visibility), and are narrower than it when the flow is
/// not: `State` of a flow with no word is a name of the package.
#[test]
fn the_items_of_a_flow_take_its_word_in_a_head() {
    let text = "pub flow open(x: F32 at sample) -> F32 at sample { x }\n\
                flow shared(x: F32 at sample) -> F32 at sample { x }\n\
                priv flow hidden(x: F32 at sample) -> F32 at sample { x }\n\
                pub fn takes_open(move s: open.State) -> open.State { s }\n\
                pub fn takes_shared(move s: shared.State) -> I32 { 0 }\n\
                pub fn takes_hidden(move s: hidden.State) -> I32 { 0 }\n\
                fn shared_takes_shared(move s: shared.State) -> shared.State { s }\n\
                fn shared_takes_hidden(move s: hidden.State) -> I32 { 0 }\n\
                priv fn hidden_takes_hidden(move s: hidden.State) -> hidden.State { s }\n";
    let diags = check_file("flow_items", text);
    let mut lines: Vec<u64> = diags.iter().map(|d| span_of(&d["span"]).line).collect();
    lines.sort();
    assert_eq!(lines, [5, 6, 8], "{diags:?}");
    for d in &diags {
        assert_eq!(str_of(d, "code"), "E0303", "{d}");
    }
}

// ---- the word that is wider than the type (S-662) -----------------------------------------------

/// §15.1 (S-662): a `pub` on a member of an `impl` of a type with no word or `priv` is E0020, one candidate
/// that takes the word off, and a note. The program the candidate gives is clean, and the member is as it was
/// without the word.
#[test]
fn a_pub_member_of_a_narrower_type_is_e0020_and_its_candidate_takes_the_word_off() {
    for (tag, owner) in [("pkg", ""), ("priv", "priv ")] {
        for member in
            ["fn get(self) -> I32 {\n    self.x\n  }", "rt fn get(self) -> I32 {\n    self.x\n  }", "const K: I32 = 1"]
        {
            let src = format!("{owner}struct S {{\n  x: I32,\n}}\n\nimpl S {{\n  pub {member}\n}}\n");
            let diags = check_file(&format!("e0020_{tag}"), &src);
            assert_eq!(diags.len(), 1, "{src}\n{diags:?}");
            let d = &diags[0];
            assert_eq!(str_of(d, "code"), "E0020", "{d}");
            let s = span_of(&d["span"]);
            assert_eq!((s.line, s.col), (6, 3), "at the word: {d}");
            let notes = d.get("notes").and_then(Value::as_array).map_or(0, Vec::len);
            assert!(notes >= 1, "a note says that the member does not reach past its type: {d}");
            let fixes = d["fixes"].as_array().unwrap_or_else(|| panic!("no fixes: {d}"));
            assert_eq!(fixes.len(), 1, "the one candidate: {d}");
            let edits = fixes[0]["edits"].as_array().expect("edits");
            assert_eq!(edits.len(), 1, "{d}");
            let e = &edits[0];
            let (l, c) = (int_of(&e["span"], "line"), int_of(&e["span"], "col"));
            assert_eq!((l, c), (6, 3), "the edit starts at the word: {d}");
            assert_eq!(str_of(e, "replace"), "", "the word is taken off: {d}");
            // Apply it: the word, and the spaces after it up to the next token if the edit takes them.
            let lines: Vec<&str> = src.lines().collect();
            let el = int_of(&e["span"], "end_line") as usize;
            let ec = int_of(&e["span"], "end_col") as usize;
            assert_eq!(el, 6, "{d}");
            let line = lines[5];
            let fixed_line = format!("{}{}", &line[..2], &line[ec - 1..]);
            let mut fixed: Vec<String> = lines.iter().map(|x| x.to_string()).collect();
            fixed[5] = fixed_line;
            let fixed = fixed.join("\n") + "\n";
            let after = check_file(&format!("e0020_{tag}_fixed"), &fixed);
            assert!(after.is_empty(), "{fixed}\n{after:?}");
            assert_eq!(
                fixed.split_whitespace().collect::<Vec<_>>(),
                src.replacen("pub ", "", 1).split_whitespace().collect::<Vec<_>>()
            );
        }
    }
}

/// §15.1 (S-662): the members that need no word taken off are clean for every type: no word, `priv`, and
/// `pub` on a `pub` type.
#[test]
fn the_words_that_are_not_wider_than_the_type_are_clean_for_every_type() {
    let mut text = String::new();
    let mut n = 0;
    for ov in ALL {
        for mv in ALL {
            n += 1;
            text.push_str(&format!(
                "{}struct S{n} {{\n  x: I32,\n}}\n\nimpl S{n} {{\n  {}fn get(self) -> I32 {{\n    self.x\n  }}\n}}\n\n",
                ov.word(),
                mv.word()
            ));
        }
    }
    let diags = check_file("words_clean", &text);
    let codes: Vec<(String, u64)> =
        diags.iter().map(|d| (str_of(d, "code").to_string(), span_of(&d["span"]).line)).collect();
    // Only the two `pub` members of a type that is not `pub`: (priv, pub) and (none, pub). A member with no
    // word or `priv` is written on any type (§15.1, S-662), `fn` of a `priv` type too.
    assert_eq!(codes.len(), 2, "{codes:?}\n{text}");
    for (code, _) in &codes {
        assert_eq!(code, "E0020");
    }
}
