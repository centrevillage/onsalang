//! A drawn sweep of the names of the items generated for a flow (spec §11.6, §15.1, §18.1; S-694 (1)): the
//! order of `use` lines that take them, and the places where a name of that kind is written. The model is
//! written from the spec; it is not a copy of the full sweeps of the breaking side (the full sweep has the
//! orders of every length and every place with every kind, and is run by hand).
//!
//! What the spec fixes, and the model uses:
//! - Each `use` is decided by its own line, wherever it is written and whatever the other lines are (§15.1:
//!   "各 `use` は、書く位置にも他の `use` にもよらずに決まる"), so the diagnostics of a set of `use` lines do
//!   not depend on their order.
//! - A name that the namespace of a flow does not have (`nosuch`, and `process_inplace` of a flow whose sample
//!   inputs and outputs differ in number or types, S-694) is E0302 at the `use`; the places that write the name
//!   afterwards are silent (§18.1, failed names).
//! - A name written where a type is read is E0308 when it is a function (`reset`, and `process_inplace`
//!   whether the flow has it or not, S-694), a flow (`gain`) or a path to a function (`gain.reset`); a type of
//!   the namespace (`Params`, `gain.Params`) is a type there; a name the namespace does not have (`gain.nosuch`)
//!   is E0302 (§15.1: "名前が見つからなければ E0302").
//!
//! Not in the model: what the spec leaves open (the code of `src.process_inplace` written as a path where a
//! type is read when the flow has none; two failed names of one name in a module), and the items that are
//! made only for some inputs (`Config`, `Params`, `Out`, `Event`: they depend on the clocks and the types of
//! the flow, R-264, W7-03).
//!
//! The seed is fixed. A failing run prints every mismatch with the program that was checked.

mod test_support;

use std::collections::BTreeMap;

use test_support::sweep::{Rng, Texts, check_package, ended_well, package};

/// The module with the flows. `gain` has `process_inplace` (its sample input and output are both `F32`);
/// `src` has no sample input; `cvt`'s output is `I32` through an alias; `pass`'s input is `F32` through one.
const SYNTH: &str = "\
pub flow gain(x: F32 at sample, g: F32 at block) -> F32 at sample {
  x * g
}

pub flow src(g: F32 at block) -> F32 at sample {
  g
}

pub flow cvt(x: F32 at sample) -> Count at sample {
  x.trunc_i32()
}

pub flow pass(x: Level at sample) -> F32 at sample {
  x
}

pub type Level = F32

pub type Count = I32

pub fn helper() -> I32 {
  1
}
";

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    /// `use dsp.synth.gain.{Params}`: a type of the namespace.
    Ty,
    /// `use dsp.synth.gain.{reset}`: a function of the namespace.
    Func,
    /// `use dsp.synth.src.{process_inplace}`: the flow has no sample input.
    AbsentNoInput,
    /// `use dsp.synth.cvt.{process_inplace}`: the types differ through an alias.
    AbsentAlias,
    /// `use dsp.synth.pass.{process_inplace}`: the types are the same through an alias.
    PresentAlias,
    /// `use dsp.synth.{gain}`, `gain` written: a flow.
    Flow,
    /// `use dsp.synth.{nosuch}`: a failed name.
    Failed,
    /// `use dsp.synth.{gain}`, `gain.Params` written.
    PathTy,
    /// `gain.reset` written.
    PathFunc,
    /// `gain.nosuch` written.
    PathMissing,
}

/// What a kind is: the line that takes it, the code of that line, the text written in a place, the code of
/// that place when a type is read there, and whether the name is a type (it is then fine where a value type
/// is read, and not where the spec asks for another kind of type).
struct Shape {
    use_line: &'static str,
    use_code: Option<&'static str>,
    hole: &'static str,
    hole_code: Option<&'static str>,
    is_type: bool,
}

fn shape(k: Kind) -> Shape {
    let s = |use_line, use_code, hole, hole_code, is_type| Shape { use_line, use_code, hole, hole_code, is_type };
    match k {
        Kind::Ty => s("use dsp.synth.gain.{Params}", None, "Params", None, true),
        Kind::Func => s("use dsp.synth.gain.{reset}", None, "reset", Some("E0308"), false),
        Kind::AbsentNoInput => {
            s("use dsp.synth.src.{process_inplace}", Some("E0302"), "process_inplace", Some("E0308"), false)
        }
        Kind::AbsentAlias => {
            s("use dsp.synth.cvt.{process_inplace}", Some("E0302"), "process_inplace", Some("E0308"), false)
        }
        Kind::PresentAlias => s("use dsp.synth.pass.{process_inplace}", None, "process_inplace", Some("E0308"), false),
        Kind::Flow => s("use dsp.synth.{gain}", None, "gain", Some("E0308"), false),
        Kind::Failed => s("use dsp.synth.{nosuch}", Some("E0302"), "nosuch", None, false),
        Kind::PathTy => s("use dsp.synth.{gain}", None, "gain.Params", None, true),
        Kind::PathFunc => s("use dsp.synth.{gain}", None, "gain.reset", Some("E0308"), false),
        Kind::PathMissing => s("use dsp.synth.{gain}", None, "gain.nosuch", Some("E0302"), false),
    }
}

/// A place where a type is read. `{H}` is on exactly one line. `data` is true where a value type of a
/// `Copy` struct is fine; the places of the headings of a flow and of an `impl` ask for something else, so
/// a type of the namespace is not written there. `control` is a text that makes the place correct.
struct Place {
    name: &'static str,
    lines: &'static [&'static str],
    data: bool,
    control: &'static str,
}

const PLACES: &[Place] = &[
    Place { name: "fn param", lines: &["pub fn p01(x: {H}) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place { name: "fn result", lines: &["pub fn p02() -> {H} {", "  p02()", "}"], data: true, control: "I32" },
    Place { name: "fn inout", lines: &["pub fn p03(inout x: {H}) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place { name: "fn move", lines: &["pub fn p04(move x: {H}) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place { name: "priv fn", lines: &["priv fn p05(x: {H}) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place { name: "plain fn", lines: &["fn p06(x: {H}) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place { name: "struct field", lines: &["pub struct S07 {", "  a: {H},", "}"], data: true, control: "I32" },
    Place {
        name: "struct 2nd field",
        lines: &["pub struct S08 {", "  a: I32,", "  b: {H},", "}"],
        data: true,
        control: "I32",
    },
    Place { name: "priv struct", lines: &["priv struct S09 {", "  a: {H},", "}"], data: true, control: "I32" },
    Place { name: "plain struct", lines: &["struct S10 {", "  a: {H},", "}"], data: true, control: "I32" },
    Place { name: "enum payload", lines: &["pub enum E11 {", "  A({H}),", "  B,", "}"], data: true, control: "I32" },
    Place { name: "alias", lines: &["type A12 = {H}"], data: true, control: "I32" },
    Place { name: "pub alias", lines: &["pub type A13 = {H}"], data: true, control: "I32" },
    Place {
        name: "option arg",
        lines: &["pub fn p14(x: Option[{H}]) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "result ok",
        lines: &["pub fn p15(x: Result[{H}, I32]) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "result err",
        lines: &["pub fn p16(x: Result[I32, {H}]) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place { name: "tuple", lines: &["pub fn p17(x: (I32, {H})) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place { name: "array", lines: &["pub fn p18(x: [{H}; 2]) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place { name: "span", lines: &["pub fn p19(x: Span[{H}]) -> I32 {", "  1", "}"], data: true, control: "I32" },
    Place {
        name: "fn type param",
        lines: &["pub fn p20(f: fn({H}) -> I32) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "fn type result",
        lines: &["pub fn p21(f: fn(I32) -> {H}) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "let annotation in option",
        lines: &["pub fn p23() -> I32 {", "  let _: Option[{H}] = None", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "field of fn type",
        lines: &["pub struct S24 {", "  f: fn({H}) -> I32,", "}"],
        data: true,
        control: "I32",
    },
    Place { name: "field of array", lines: &["pub struct S25 {", "  a: [{H}; 2],", "}"], data: true, control: "I32" },
    Place {
        name: "field of option",
        lines: &["pub struct S26 {", "  a: Option[{H}],", "}"],
        data: true,
        control: "I32",
    },
    Place { name: "alias of tuple", lines: &["type A27 = (I32, {H})"], data: true, control: "I32" },
    Place { name: "alias of array", lines: &["type A28 = [{H}; 2]"], data: true, control: "I32" },
    Place { name: "alias of option", lines: &["type A29 = Option[{H}]"], data: true, control: "I32" },
    Place { name: "alias of fn type", lines: &["type A30 = fn({H}) -> I32"], data: true, control: "I32" },
    Place {
        name: "user generic arg",
        lines: &["pub struct W31[T] {", "  a: T,", "}", "", "pub fn p31(x: W31[{H}]) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "flow input",
        lines: &["pub flow f32(x: {H} at sample) -> F32 at sample {", "  1.0", "}"],
        data: false,
        control: "F32",
    },
    Place {
        name: "flow output",
        lines: &["pub flow f33(x: F32 at sample) -> {H} at sample {", "  x", "}"],
        data: false,
        control: "F32",
    },
    Place {
        name: "flow block input",
        lines: &["pub flow f34(g: {H} at block) -> F32 at sample {", "  1.0", "}"],
        data: false,
        control: "F32",
    },
    Place {
        name: "flow init input",
        lines: &["pub flow f35(g: {H} at init) -> F32 at sample {", "  1.0", "}"],
        data: false,
        control: "F32",
    },
    Place { name: "impl target", lines: &["impl {H} {", "}"], data: false, control: "S36" },
    Place {
        name: "nested span",
        lines: &["pub fn p37(x: Span[Span[{H}]]) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "nested option",
        lines: &["pub fn p38(x: Option[Option[{H}]]) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "option result",
        lines: &["pub fn p39() -> Option[{H}] {", "  None", "}"],
        data: true,
        control: "I32",
    },
    Place { name: "array result", lines: &["pub fn p40() -> [{H}; 1] {", "  p40()", "}"], data: true, control: "I32" },
    Place { name: "tuple field", lines: &["pub struct S41 {", "  a: (I32, {H}),", "}"], data: true, control: "I32" },
    Place {
        name: "second param",
        lines: &["pub fn p42(x: I32, y: {H}) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place { name: "alias of result", lines: &["type A43 = Result[{H}, I32]"], data: true, control: "I32" },
    Place { name: "pub alias of tuple", lines: &["pub type A44 = (I32, {H})"], data: true, control: "I32" },
    Place {
        name: "fn type nested",
        lines: &["pub fn p45(f: fn(fn({H}) -> I32) -> I32) -> I32 {", "  1", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "enum second variant",
        lines: &["pub enum E46 {", "  A,", "  B(I32, {H}),", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "alias in a struct of a struct",
        lines: &["pub struct S47 {", "  inner: Option[(I32, {H})],", "}"],
        data: true,
        control: "I32",
    },
    Place {
        name: "flow output array",
        lines: &["pub flow f48(x: F32 at sample) -> [{H}; 2] at sample {", "  [x, x]", "}"],
        data: false,
        control: "F32",
    },
    Place {
        name: "flow input array",
        lines: &["pub flow f49(x: [{H}; 2] at sample) -> F32 at sample {", "  1.0", "}"],
        data: false,
        control: "F32",
    },
    Place {
        name: "second flow input",
        lines: &["pub flow f50(a: F32 at sample, b: {H} at sample) -> F32 at sample {", "  1.0", "}"],
        data: false,
        control: "F32",
    },
];

/// The text of `main.onsa`: the `use` lines, a blank line, the place with `hole` written. Returns it with the
/// line of the hole and the number of times the hole is written on that line.
fn program(uses: &[&str], place: &Place, hole: &str) -> (String, u64, usize) {
    let mut text = String::new();
    for u in uses {
        text.push_str(u);
        text.push('\n');
    }
    text.push('\n');
    let (mut hole_line, mut times) = (0, 0);
    for (n, l) in place.lines.iter().enumerate() {
        if l.contains("{H}") {
            hole_line = uses.len() as u64 + 2 + n as u64;
            times = l.matches("{H}").count();
            text.push_str(&l.replace("{H}", hole));
        } else {
            text.push_str(l);
        }
        text.push('\n');
    }
    if place.name == "impl target" {
        // The control of an `impl` is a struct of the module.
        text.push_str("\nstruct S36 {\n  a: I32,\n}\n");
    }
    assert!(hole_line > 0, "no hole in the place {}", place.name);
    (text, hole_line, times)
}

fn texts(main: String) -> Texts {
    let mut t: Texts = BTreeMap::new();
    t.insert("dsp/synth.onsa".to_string(), SYNTH.to_string());
    t.insert("main.onsa".to_string(), main);
    t
}

/// One program checked: the diagnostics as sorted (code, line) pairs against `expect`; on a mismatch the
/// program is added to `problems`.
fn run_one(tag: &str, main: &str, expect: &[(&str, u64)], problems: &mut Vec<String>) {
    let d = package(tag, "demo", &texts(main.to_string()));
    let c = check_package(d.root());
    let mut got: Vec<(String, u64)> = c.diags.iter().map(|x| (format!("{}@{}", x.code, x.file), x.line)).collect();
    got.sort();
    let mut want: Vec<(String, u64)> = expect.iter().map(|(c, l)| (format!("{c}@main.onsa"), *l)).collect();
    want.sort();
    let code_ok = c.code == if want.is_empty() { 0 } else { 1 };
    if !ended_well(&c) || got != want || !code_ok {
        problems.push(format!(
            "{tag}: expected {want:?}, got {got:?} (exit {}) {}\n{main}",
            c.code,
            c.diags.iter().map(|x| x.message.clone()).collect::<Vec<_>>().join(" | ")
        ));
    }
}

/// The kinds whose name is not a value written where a type is read.
const KINDS_OF_TYPES: [Kind; 4] = [Kind::Ty, Kind::Failed, Kind::PathTy, Kind::PathMissing];

/// The kinds whose name is a value (a function, a flow, a path to a function) written where a type is read:
/// the code of that is E0308 (S-103), which W4-04 U7 gives (now E0302).
const KINDS_OF_VALUES: [Kind; 6] =
    [Kind::Func, Kind::AbsentNoInput, Kind::AbsentAlias, Kind::PresentAlias, Kind::Flow, Kind::PathFunc];

/// The controls: every place written with a correct text has no diagnostic, so a mismatch of the sweep is
/// the name, not the place.
#[test]
fn the_places_are_correct_with_a_correct_type() {
    let mut problems = Vec::new();
    for (i, p) in PLACES.iter().enumerate() {
        let (text, _, _) = program(&[], p, p.control);
        run_one(&format!("gen_ctl_{i}"), &text, &[], &mut problems);
    }
    assert!(problems.is_empty(), "{} places failed:\n{}", problems.len(), problems.join("\n---\n"));
}

/// Each place once, with the next kind of `kinds` that fits the place (a type of the namespace does not fit
/// where the heading of a flow wants another type): the diagnostics are the E0302 of the `use` for a name the
/// namespace does not have, and the code of the place.
fn each_place_once(kinds: &[Kind], tag: &str) {
    let mut problems = Vec::new();
    let mut next = 0usize;
    let mut used = vec![0usize; kinds.len()];
    for (i, p) in PLACES.iter().enumerate() {
        let kind = loop {
            let k = kinds[next % kinds.len()];
            next += 1;
            if p.data || !shape(k).is_type {
                break k;
            }
        };
        used[kinds.iter().position(|x| *x == kind).unwrap()] += 1;
        let sh = shape(kind);
        let (text, hole_line, times) = program(&[sh.use_line], p, sh.hole);
        let mut expect: Vec<(&str, u64)> = Vec::new();
        if let Some(c) = sh.use_code {
            expect.push((c, 1));
        }
        if let Some(c) = sh.hole_code {
            for _ in 0..times {
                expect.push((c, hole_line));
            }
        }
        run_one(&format!("{tag}_{i}_{kind:?}"), &text, &expect, &mut problems);
    }
    assert!(used.iter().all(|n| *n >= 4), "a kind was used too seldom: {used:?}");
    assert!(problems.is_empty(), "{} programs failed:\n{}", problems.len(), problems.join("\n---\n"));
}

#[test]
fn a_name_of_a_type_or_a_failed_name_in_each_place() {
    each_place_once(&KINDS_OF_TYPES, "gen_pos_ty");
}

#[test]
#[ignore = "W4-04 U7: a value (a function, a flow) written where a type is read is E0308 (S-103); now E0302"]
fn a_name_of_a_value_in_each_place() {
    each_place_once(&KINDS_OF_VALUES, "gen_pos_val");
}

/// A set of `use` lines of two to four names that are different in the module (the slot of the bound name
/// decides: `Params`, `reset`, `process_inplace`, `gain`, `nosuch`), each with a place that writes its name
/// (when `values` is false, no place for a name that is a value, which is the subject of the other test); the
/// lines in a drawn order. The diagnostics do not depend on the order.
fn use_lines_in_any_order(values: bool, tag: &str) {
    // The slots: the kinds that bind the same name cannot be in one module together.
    let slots: [&[Kind]; 5] = [
        &[Kind::Ty],
        &[Kind::Func],
        &[Kind::AbsentNoInput, Kind::AbsentAlias, Kind::PresentAlias],
        &[Kind::Flow, Kind::PathTy, Kind::PathFunc, Kind::PathMissing],
        &[Kind::Failed],
    ];
    let data_places: Vec<&Place> = PLACES.iter().filter(|p| p.data).collect();
    let mut rng = Rng::new(0x5eed_u64);
    let mut problems = Vec::new();
    for trial in 0..20 {
        let n = rng.range(2, 4);
        let mut chosen: Vec<usize> = (0..slots.len()).collect();
        rng.shuffle(&mut chosen);
        chosen.truncate(n);
        let kinds: Vec<Kind> = chosen.iter().map(|s| *rng.pick(slots[*s])).collect();
        // The `use` lines: one per distinct line (the kinds of the slot `gain` share one line).
        let mut lines: Vec<&str> = Vec::new();
        for k in &kinds {
            let l = shape(*k).use_line;
            if !lines.contains(&l) {
                lines.push(l);
            }
        }
        rng.shuffle(&mut lines);
        let mut text = String::new();
        for l in &lines {
            text.push_str(l);
            text.push('\n');
        }
        text.push('\n');
        let mut line_no = lines.len() as u64 + 1;
        let mut expect: Vec<(&str, u64)> = Vec::new();
        for (e, k) in kinds.iter().enumerate() {
            let sh = shape(*k);
            if let Some(c) = sh.use_code {
                let at = lines.iter().position(|l| *l == sh.use_line).unwrap() as u64 + 1;
                expect.push((c, at));
            }
            let is_value = sh.hole_code == Some("E0308");
            if is_value != values && is_value {
                continue;
            }
            let place = data_places[(trial * 5 + e) % data_places.len()];
            for l in place.lines {
                line_no += 1;
                if l.contains("{H}") {
                    if let Some(c) = sh.hole_code {
                        for _ in 0..l.matches("{H}").count() {
                            expect.push((c, line_no));
                        }
                    }
                    text.push_str(&l.replace("{H}", sh.hole));
                } else {
                    text.push_str(l);
                }
                text.push('\n');
            }
            text.push('\n');
            line_no += 1;
        }
        run_one(&format!("{tag}_{trial}"), &text, &expect, &mut problems);
    }
    assert!(problems.is_empty(), "{} programs failed:\n{}", problems.len(), problems.join("\n---\n"));
}

#[test]
fn the_use_lines_decide_alone_in_any_order() {
    use_lines_in_any_order(false, "gen_ord");
}

#[test]
#[ignore = "W4-04 U7: a value (a function, a flow) written where a type is read is E0308 (S-103); now E0302"]
fn the_use_lines_decide_alone_in_any_order_with_values_in_places() {
    use_lines_in_any_order(true, "gen_ord_val");
}
