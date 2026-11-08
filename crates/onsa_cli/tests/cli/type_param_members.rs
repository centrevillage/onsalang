//! A name after a type parameter, a const parameter or an effect row variable and a `.` in a heading, a type
//! and a body (spec §15.1, §5.1, §8.1, §18.1; R-370, R-404, R-406; W5-11 U10a/i, U10e/i, U10f/i).
//!
//! What is checked: a member that the bounds of the type parameter do not give is the name not found, in
//! the message and at the place, in the three places that are no body (a type `-> T.K`, a bound `U: T.x`,
//! an effect row `uses {T.e}`) and in the type of a local of a body, as it is in a body (`T.f()`). The type
//! parameter itself is found, so no message says it is not. A member the bounds give is the E0308 of its kind
//! at the place, as `F32.PI` is; after a const parameter, a value, the `.` is the E0308 of a name with no
//! members, as after a local (`x.K`); so is it after an effect row variable, a name that is no namespace, in
//! each place and in a body (`e.x`, `let y: e.K`, `e.K { a: 1 }`). After a parameter whose bounds are unknown (a contradiction, a bound not
//! found) the `.` gets no diagnostic, and the error of the bound is the one of the unit. A parameter is seen in
//! the whole heading (§5.1): in a bound before it, in its own bound and in the type of a const parameter.
//! The text of a message is not promised by the spec (§18.1): this holds the one of the implementation.
//! The `use` a candidate adds is in the form fmt writes (S-598): fmt leaves the file with it as it is.

use crate::test_support;

use test_support::fmt::{Fmt, format};
use test_support::sweep::{Texts, apply_fix_texts, check_input, ended_well, input_of};

/// A function of `main.onsa`, and the line in it (from 1), the name and the column (from 1) of its E0302.
const CASES: [(&str, u64, &str, u64); 5] = [
    ("fn a[T](x: T) -> T.K {\n  x\n}\n", 1, "K", 20),
    ("fn b[T, U: T.x](x: U) -> U {\n  x\n}\n", 1, "x", 14),
    ("fn c[T](x: T) -> U32 uses {T.e} {\n  1\n}\n", 1, "e", 30),
    ("fn d[T: Float](x: T) -> T.NOPE {\n  x\n}\n", 1, "NOPE", 27),
    ("fn e[T](x: T) {\n  let y: T.K = x\n}\n", 2, "K", 12),
];

/// An item of `main.onsa`, and the line in it (from 1), the code and the message and the column (from 1) of
/// the one diagnostic of its unit.
const KINDS: [(&str, u64, &str, u64); 12] = [
    ("fn a[T: Float](x: T) -> T.PI {\n  x\n}\n", 1, "E0308 `T.PI` is a constant, not a type (§15.1)", 25),
    (
        "fn b[T: Float, U: T.PI](x: U) -> U {\n  x\n}\n",
        1,
        "E0308 `T.PI` is a constant, not a trait or a kind constraint (§15.1)",
        19,
    ),
    ("fn c[T: Float](x: T) -> U32 uses {T.PI} {\n  1\n}\n", 1, "E0308 `T.PI` is a constant, not an effect (§15.1)", 35),
    ("fn d[T: Float](x: T) {\n  let y: T.PI = x\n}\n", 2, "E0308 `T.PI` is a constant, not a type (§15.1)", 10),
    (
        "fn e[const N: U32](x: F32) -> N.K {\n  x\n}\n",
        1,
        "E0308 `N` is a const parameter, which has no members (§15.1)",
        33,
    ),
    (
        "fn f[const N: U32, U: N.x](x: U) -> U {\n  x\n}\n",
        1,
        "E0308 `N` is a const parameter, which has no members (§15.1)",
        25,
    ),
    (
        "fn g[T: Copy + ?Dup](x: T) -> T.K {\n  x\n}\n",
        1,
        "E0416 `?Dup` and `Copy` contradict: `?Dup` lifts the implicit `Dup`, and the other requires it (§4.5)",
        17,
    ),
    ("fn h[T: Gone](x: T) -> T.K {\n  x\n}\n", 1, "E0302 cannot find `Gone`", 9),
    ("fn i[U: T.x, T: Show](x: U) -> U {\n  x\n}\n", 1, "E0302 cannot find `x`", 11),
    ("fn j[T: T.x](x: T) -> T {\n  x\n}\n", 1, "E0302 cannot find `x`", 11),
    ("fn k[const N: T.K, T](x: T) -> T {\n  x\n}\n", 1, "E0302 cannot find `K`", 17),
    (
        "fn l[U: T.PI, T: Float](x: U) -> U {\n  x\n}\n",
        1,
        "E0308 `T.PI` is a constant, not a trait or a kind constraint (§15.1)",
        9,
    ),
];

/// An item of `main.onsa` with a `.` after its effect row variable `e`, and the line in it (from 1) and the
/// column (from 1) of the name after the `.`, where its one diagnostic is.
const EFFECT_VARS: [(&str, u64, u64); 6] = [
    ("fn a[e](f: fn(F32) -> F32 uses {e}, x: F32) -> e.K uses {e} {\n  x\n}\n", 1, 50),
    ("fn b[e, U: e.x](f: fn(U) -> U uses {e}, x: U) -> U uses {e} {\n  x\n}\n", 1, 14),
    ("fn c[e](f: fn(F32) -> F32 uses {e}, x: F32) -> F32 uses {e.x} {\n  x\n}\n", 1, 60),
    ("fn d[e](f: fn(F32) -> F32 uses {e}, x: F32) -> F32 uses {e} {\n  e.x\n}\n", 2, 5),
    ("fn g[e](f: fn(F32) -> F32 uses {e}, x: F32) -> F32 uses {e} {\n  let y: e.K = x\n  y\n}\n", 2, 12),
    ("fn h[e](f: fn(F32) -> F32 uses {e}, x: F32) -> F32 uses {e} {\n  let q = e.K { a: 1 }\n  x\n}\n", 2, 13),
];

/// The diagnostics of the package of the one file `main.onsa` holding the items `items`, against the line, the
/// message (with its code) and the column of each.
fn expect(items: &[(&str, u64, String, u64)]) {
    let (mut text, mut want) = (String::new(), Vec::new());
    for (src, line, message, col) in items {
        want.push((text.lines().count() as u64 + line, message.clone(), *col));
        text.push_str(src);
    }
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), text.clone());
    let checked = check_input(&input_of("demo", &texts));
    assert!(ended_well(&checked), "check did not end as a check does:\n{}", checked.stderr);
    let got: Vec<(u64, String, u64)> =
        checked.diags.iter().map(|d| (d.line, format!("{} {}", d.code, d.message), d.col)).collect();
    assert_eq!(got, want, "in:\n{text}");
}

#[test]
fn a_member_the_bounds_do_not_give_is_the_name_not_found() {
    let items: Vec<_> =
        CASES.iter().map(|&(src, line, name, col)| (src, line, format!("E0302 cannot find `{name}`"), col)).collect();
    expect(&items);
}

#[test]
fn a_member_the_bounds_give_and_a_const_parameter_are_of_another_kind_and_unknown_bounds_hold_the_name() {
    let items: Vec<_> = KINDS.iter().map(|&(src, line, message, col)| (src, line, message.to_string(), col)).collect();
    expect(&items);
}

#[test]
fn an_effect_row_variable_has_no_members_in_each_place_and_is_no_value_in_a_body() {
    let message = "E0308 `e` is an effect row variable, which has no members (§15.1)";
    let items = EFFECT_VARS.iter().map(|&(src, line, col)| (src, line, message.to_string(), col));
    // The variable alone at the place of a value and of a callee (R-411).
    let alone = [
        ("fn i[e](f: fn(F32) -> F32 uses {e}, x: F32) -> F32 uses {e} {\n  let v = e\n  x\n}\n", "value", 11),
        ("fn j[e](f: fn(F32) -> F32 uses {e}, x: F32) -> F32 uses {e} {\n  e(x)\n}\n", "function", 3),
    ];
    let alone = alone
        .map(|(src, want, col)| (src, 2, format!("E0308 `e` is an effect row variable, not a {want} (§15.1)"), col));
    expect(&items.chain(alone).collect::<Vec<_>>());
}

/// The head of a `.` after an effect row variable is a use of it, in a heading and in a body: the E0320 of its
/// name renames it there too (§2.3).
#[test]
fn the_rename_of_an_effect_row_variable_reaches_its_name_before_a_dot() {
    let mut texts = Texts::new();
    let text = "pub fn n1[_e, U: _e.x](f: fn(U) -> U uses {_e}, x: U) -> _e.K uses {_e.y} {\n  _e.z\n}\n";
    texts.insert("main.onsa".to_string(), text.to_string());
    let checked = check_input(&input_of("demo", &texts));
    let renames: Vec<_> = checked.of_code("E0320").iter().flat_map(|d| &d.fixes).cloned().collect();
    assert_eq!(renames.len(), 1, "one rename:\n{}", checked.stderr);
    apply_fix_texts(&mut texts, &renames[0]);
    let want = "pub fn n1[e, U: e.x](f: fn(U) -> U uses {e}, x: U) -> e.K uses {e.y} {\n  e.z\n}\n";
    assert_eq!(texts["main.onsa"], want);
}

/// The head of a `.` after a const parameter is a use of it: the E0320 of its name renames it there too (§2.3).
#[test]
fn the_rename_of_a_const_parameter_reaches_its_name_before_a_dot() {
    let mut texts = Texts::new();
    let text = "pub fn n1[const n: U32, U: n.x](x: U) -> n.K uses {n.y} {\n  x\n}\n";
    texts.insert("main.onsa".to_string(), text.to_string());
    let checked = check_input(&input_of("demo", &texts));
    let renames: Vec<_> = checked.of_code("E0320").iter().flat_map(|d| &d.fixes).cloned().collect();
    assert_eq!(renames.len(), 1, "one rename:\n{}", checked.stderr);
    apply_fix_texts(&mut texts, &renames[0]);
    let want = "pub fn n1[const N: U32, U: N.x](x: U) -> N.K uses {N.y} {\n  x\n}\n";
    assert_eq!(texts["main.onsa"], want);
}

#[test]
fn the_use_a_candidate_adds_is_as_fmt_writes_it() {
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), "fn f() -> U32 uses {Fs} {\n  1\n}\n".to_string());
    let checked = check_input(&input_of("demo", &texts));
    let fixes: Vec<_> = checked.diags.iter().flat_map(|d| &d.fixes).collect();
    assert_eq!(fixes.len(), 1, "one candidate:\n{}", checked.stderr);
    assert_eq!(fixes[0]["title"], "add `use std.fs.Fs`");
    apply_fix_texts(&mut texts, fixes[0]);
    let fixed = texts["main.onsa"].clone();
    assert_eq!(format("main.onsa", &fixed), Fmt::Text(fixed.clone()), "fmt changes the candidate's `use`");
}
