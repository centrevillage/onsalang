//! `onsa diff --ast` does not report the order of a list read as a set (`spec/tools.md` §3.5, S-750):
//! the bounds of a type parameter, a derive list and an effect row; the order of the other lists (the
//! parameters, the fields, the type parameters, the type arguments) it reports. The pairs and what is
//! expected of them are of the tests of W5-24 U3b/t: the exit code and the keys of the items reported
//! (`~ <kind> <name>`, the head of the line, `spec/tools.md` §3.5), with no file written (X-16).

use onsa_diag::SourceMap;
use onsa_driver::AstDiff;
use onsa_syntax::diff::Change;

/// `onsa diff --ast` of `old` and `new`, as the command reports it: the exit code and the lines
/// without the positions (`~ fn f`).
fn reported(old: &str, new: &str) -> (i32, Vec<String>) {
    let mut sources = SourceMap::default();
    let (a, b) = (sources.add("old.onsa", old), sources.add("new.onsa", new));
    match onsa_diag::stack::run(|| onsa_driver::diff_ast(&sources, a, b)) {
        Ok(AstDiff::Items(d)) => {
            let sign = |c: Change| match c {
                Change::Added => "+",
                Change::Removed => "-",
                Change::Changed => "~",
            };
            let lines: Vec<String> = d.iter().map(|d| format!("{} {}", sign(d.change), d.key)).collect();
            (if lines.is_empty() { 0 } else { 1 }, lines)
        }
        Ok(AstDiff::Syntax(ds)) => (2, vec![onsa_diag::to_text(&sources, &ds)]),
        Err(e) => (101, vec![e.render(&sources)]),
    }
}

/// The name of a pair, the old and the new file, the exit code and the items changed (`~`).
type Pair = (&'static str, &'static str, &'static str, i32, &'static [&'static str]);

#[test]
fn the_order_of_a_set_is_no_difference_and_of_another_list_is() {
    let mut wrong = Vec::new();
    for &(name, old, new, code, keys) in PAIRS {
        let want: Vec<String> = keys.iter().map(|k| format!("~ {k}")).collect();
        let got = reported(old, new);
        if got != (code, want.clone()) {
            wrong.push(format!("{name}: expected {code} {want:?}, got {got:?}"));
        }
    }
    assert!(wrong.is_empty(), "{} of {} pairs:\n{}", wrong.len(), PAIRS.len(), wrong.join("\n"));
    assert_eq!(PAIRS.len(), 15);
}

const PAIRS: &[Pair] = &[
    (
        "bounds_order",
        r#"pub fn show_eq[T: PartialEq + Show](x: T) -> T {
  x
}

pub fn three_bounds[T: Num + Show + PartialEq](x: T) -> T {
  x
}

pub fn maybe_dup[T: ?Dup + Show](x: T) -> U32 {
  0
}

pub struct Wrap[T: Num + Show] {
  a: T,
}

pub enum Choice[T: Eq + Hash] {
  A(T),
  B,
}

impl[T: Eq + Hash] Choice[T] {
  pub fn method[U: Show + PartialEq](self, u: U) -> U {
    u
  }
}
"#,
        r#"pub fn show_eq[T: Show + PartialEq](x: T) -> T {
  x
}

pub fn three_bounds[T: PartialEq + Num + Show](x: T) -> T {
  x
}

pub fn maybe_dup[T: Show + ?Dup](x: T) -> U32 {
  0
}

pub struct Wrap[T: Show + Num] {
  a: T,
}

pub enum Choice[T: Hash + Eq] {
  A(T),
  B,
}

impl[T: Hash + Eq] Choice[T] {
  pub fn method[U: PartialEq + Show](self, u: U) -> U {
    u
  }
}
"#,
        0,
        &[],
    ),
    (
        "derive_order",
        r#"pub struct P: PartialEq + Eq + Hash {
  n: U32,
}

pub struct Chain: PartialEq + Eq + PartialOrd + Ord {
  n: U32,
}

pub enum Mode: Eq + Ordinal {
  Off,
  On,
}

pub struct W[T]: PartialEq + Eq {
  a: T,
}
"#,
        r#"pub struct P: Hash + PartialEq + Eq {
  n: U32,
}

pub struct Chain: Ord + PartialOrd + Eq + PartialEq {
  n: U32,
}

pub enum Mode: Ordinal + Eq {
  Off,
  On,
}

pub struct W[T]: Eq + PartialEq {
  a: T,
}
"#,
        0,
        &[],
    ),
    (
        "effect_row_order",
        r#"pub fn alloc_then_variable[e](f: fn() -> U32 uses {e}) -> U32 uses {Alloc, e} {
  f.()
}

pub fn two_variables[d, e](f: fn() -> U32 uses {d}, g: fn() -> U32 uses {e}) -> U32 uses {d, e} {
  f.() + g.()
}

pub fn three_elements[d, e](f: fn() -> U32 uses {d}, g: fn() -> U32 uses {e}) -> U32 uses {Alloc, d, e} {
  f.() + g.()
}

pub fn in_a_function_type[d, e](f: fn(fn() -> U32 uses {d, e}) -> U32 uses {Alloc, e}) -> U32 {
  0
}

pub fn closure[e](f: fn() -> U32 uses {e}) -> U32 uses {e} {
  let _ = fn(x: U32) -> U32 uses {Alloc, e} { x }
  f.()
}

pub struct Holder {
  id: U32,
}

impl Holder {
  pub fn method[e](self, f: fn() -> U32 uses {e}) -> U32 uses {Alloc, e} {
    f.()
  }
}
"#,
        r#"pub fn alloc_then_variable[e](f: fn() -> U32 uses {e}) -> U32 uses {e, Alloc} {
  f.()
}

pub fn two_variables[d, e](f: fn() -> U32 uses {d}, g: fn() -> U32 uses {e}) -> U32 uses {e, d} {
  f.() + g.()
}

pub fn three_elements[d, e](f: fn() -> U32 uses {d}, g: fn() -> U32 uses {e}) -> U32 uses {e, Alloc, d} {
  f.() + g.()
}

pub fn in_a_function_type[d, e](f: fn(fn() -> U32 uses {e, d}) -> U32 uses {e, Alloc}) -> U32 {
  0
}

pub fn closure[e](f: fn() -> U32 uses {e}) -> U32 uses {e} {
  let _ = fn(x: U32) -> U32 uses {e, Alloc} { x }
  f.()
}

pub struct Holder {
  id: U32,
}

impl Holder {
  pub fn method[e](self, f: fn() -> U32 uses {e}) -> U32 uses {e, Alloc} {
    f.()
  }
}
"#,
        0,
        &[],
    ),
    (
        "all_three_order",
        r#"pub struct P: PartialEq + Eq {
  n: U32,
}

pub fn n[T: PartialEq + Show, e](x: T, f: fn() -> U32 uses {e}) -> U32 uses {Alloc, e} {
  f.()
}
"#,
        r#"pub struct P: Eq + PartialEq {
  n: U32,
}

pub fn n[T: Show + PartialEq, e](x: T, f: fn() -> U32 uses {e}) -> U32 uses {e, Alloc} {
  f.()
}
"#,
        0,
        &[],
    ),
    (
        "item_order_only",
        r#"pub fn first(x: U32) -> U32 {
  x
}

pub fn second(x: U32) -> U32 {
  x
}
"#,
        r#"pub fn second(x: U32) -> U32 {
  x
}

pub fn first(x: U32) -> U32 {
  x
}
"#,
        0,
        &[],
    ),
    (
        "bounds_order_one_more",
        r#"pub fn n[T: PartialEq + Show](x: T) -> T {
  x
}
"#,
        r#"pub fn n[T: Show + PartialEq + Eq](x: T) -> T {
  x
}
"#,
        1,
        &["fn n"],
    ),
    (
        "derive_order_one_more",
        r#"pub struct P: PartialEq + Eq {
  n: U32,
}
"#,
        r#"pub struct P: Eq + PartialEq + Hash {
  n: U32,
}
"#,
        1,
        &["struct P"],
    ),
    (
        "effect_row_order_one_more",
        r#"pub fn n[d, e](f: fn() -> U32 uses {d}, g: fn() -> U32 uses {e}) -> U32 uses {Alloc, e} {
  f.() + g.()
}
"#,
        r#"pub fn n[d, e](f: fn() -> U32 uses {d}, g: fn() -> U32 uses {e}) -> U32 uses {e, d, Alloc} {
  f.() + g.()
}
"#,
        1,
        &["fn n"],
    ),
    (
        "order_only_next_to_a_real_change",
        r#"pub fn only_order[T: PartialEq + Show](x: T) -> T {
  x
}

pub fn real_change(x: U32) -> U32 {
  x + 1
}

pub struct SameOrderOnly: PartialEq + Eq {
  n: U32,
}
"#,
        r#"pub fn only_order[T: Show + PartialEq](x: T) -> T {
  x
}

pub fn real_change(x: U32) -> U32 {
  x + 2
}

pub struct SameOrderOnly: Eq + PartialEq {
  n: U32,
}
"#,
        1,
        &["fn real_change"],
    ),
    (
        "argument_order",
        r#"pub fn f(a: U32, b: Bool) -> U32 {
  a
}
"#,
        r#"pub fn f(b: Bool, a: U32) -> U32 {
  a
}
"#,
        1,
        &["fn f"],
    ),
    (
        "field_order",
        r#"pub struct P {
  a: U32,
  b: Bool,
}
"#,
        r#"pub struct P {
  b: Bool,
  a: U32,
}
"#,
        1,
        &["struct P"],
    ),
    (
        "type_parameter_order",
        r#"pub fn f[T, U](a: T, b: U) -> T {
  a
}
"#,
        r#"pub fn f[U, T](a: T, b: U) -> T {
  a
}
"#,
        1,
        &["fn f"],
    ),
    (
        "bounds_of_two_parameters_order",
        r#"pub fn f[T: PartialEq, U: Show](a: T, b: U) -> T {
  a
}
"#,
        r#"pub fn f[U: Show, T: PartialEq](a: T, b: U) -> T {
  a
}
"#,
        1,
        &["fn f"],
    ),
    (
        "type_argument_order",
        r#"pub struct Pair[A, B] {
  a: A,
  b: B,
}

pub fn f(p: Pair[U32, Bool]) -> U32 {
  0
}
"#,
        r#"pub struct Pair[A, B] {
  a: A,
  b: B,
}

pub fn f(p: Pair[Bool, U32]) -> U32 {
  0
}
"#,
        1,
        &["fn f"],
    ),
    (
        "derive_and_field_order",
        r#"pub struct P: PartialEq + Eq {
  a: U32,
  b: Bool,
}
"#,
        r#"pub struct P: Eq + PartialEq {
  b: Bool,
  a: U32,
}
"#,
        1,
        &["struct P"],
    ),
];
