//! Sweeps of the places that use an error type or an unknown bound (spec §18.1, S-692 (b) with the readings
//! A1 and A2, S-689, S-690, R-271; W4-03 U3c/t2).
//!
//! A name that failed in the names stage (a failed `use`, the name of an E0304, a member that a syntax error
//! cut off) is read as an error type where a type is written, and as an unknown bound where a bound is
//! written. Whatever uses that type has no diagnostic, and the unit goes on, so a real error after it is
//! reported (§18.1). Every later stage meets the error type again (W4-04 the names of a body, W5 the types,
//! W7 the delays), and each time a place that was not thought of can report a false error or lose a real one.
//! These tests build the combinations from tables, so a new place is one more row:
//!
//! - `error_type_in_every_body_form`: forms of a body (an operator, a comparison, a method, a field, an
//!   index, `?`, a call, every form of a pattern, `match`, the conditions, an assignment, `move` and `inout`
//!   arguments, a closure, a literal, `as`, an interpolation) × the ways to make an error type (a failed
//!   name, its alias, the alias of the alias, the name of an E0304 and its alias, a member that a syntax
//!   error cut off and its alias). Every form is a function of its own with a real error (`let a: I32 =
//!   true`) after it, which is the only diagnostic the function has, and the same form without the real
//!   error, which has none.
//! - `unknown_bound_silences_what_depends_on_the_trait`: a bound that is a failed name (alone, with a known
//!   bound before and after it, with `?Dup`) × the forms that depend on a type parameter meeting a trait (every
//!   operator, the methods, the bounds of other functions, `[x; 3]`, a move). What does not depend on the trait
//!   (a type parameter where another type is wanted, a field) stays an error, and so do the forms of the
//!   parameters whose bounds are all known.
//! - `exhaustiveness_takes_the_error_type_as_everything`: the part of a pattern whose type is an error type
//!   matches anything, the other parts that are missing are E0501 (A2).
//! - `flow_with_error_types`: the inputs and outputs of a flow and the delays of a value of an error type.
//!
//! Not written: what the spec leaves open. A form is in a table only when the spec says what its diagnostics
//! are, so the tables have no form whose first error depends on the order of two checks of one stage, nor
//! one with an error that does not depend on the error type (a name that is nowhere, a `?` in a function
//! that returns `I32`, a type parameter that nothing decides).
//!
//! The tests are in their own file (a binary of its own), so that they run beside the others: each makes a
//! few packages of hundreds of functions and runs `check` once on each.

mod test_support;

use std::collections::BTreeMap;

use test_support::sweep::{Texts, check_package, ended_well, package};

// ---- the source with its marks ---------------------------------------------------------------------------

/// A source text under construction. A mark ` @@E0401` at the end of a line says that the line has a
/// diagnostic of that code (as `//~ E0401` does in a case); the units are named, so that a problem is
/// reported by the name of the function.
struct Src {
    text: String,
    marks: Vec<(u64, String)>,
    units: Vec<(u64, String)>,
    lines: u64,
}

impl Src {
    fn new() -> Src {
        Src { text: String::new(), marks: Vec::new(), units: Vec::new(), lines: 0 }
    }

    fn raw(&mut self, chunk: &str) {
        for l in chunk.lines() {
            self.lines += 1;
            match l.split_once(" @@") {
                Some((line, code)) => {
                    self.marks.push((self.lines, code.trim().to_string()));
                    self.text.push_str(line);
                }
                None => self.text.push_str(l),
            }
            self.text.push('\n');
        }
    }

    /// A chunk that is one unit (one function); its marks are the ones that unit is expected to have.
    fn unit(&mut self, name: &str, chunk: &str) {
        self.units.push((self.lines + 1, name.to_string()));
        self.raw(chunk);
    }

    fn unit_at(&self, line: u64) -> &str {
        self.units.iter().rev().find(|(start, _)| *start <= line).map(|(_, n)| n.as_str()).unwrap_or("(head)")
    }
}

const UTIL: &str = "pub fn double(x: I32) -> I32 {\n  x * 2\n}\n";

/// Check `src` as the `main.onsa` of a package, with `util.onsa` beside it: the diagnostics must be the
/// marked ones, no more and no fewer, and the command must end by 0 or 1 without an internal error. The
/// problems, one for each unit that differs, with what was wanted and what was reported.
fn verify(tag: &str, src: &Src) -> Vec<String> {
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), src.text.clone());
    texts.insert("util.onsa".to_string(), UTIL.to_string());
    let d = package(tag, "demo", &texts);
    // `SWEEP_DUMP=<dir>` keeps the packages, to run them with another build or to read a failing one
    if let Ok(dump) = std::env::var("SWEEP_DUMP") {
        let dir = std::path::Path::new(&dump).join(tag);
        std::fs::create_dir_all(&dir).expect("the directory of the dump");
        for (f, t) in &texts {
            std::fs::write(dir.join(f), t).expect("a file of the dump");
        }
        std::fs::write(dir.join("onsa.toml"), "[package]\nname = \"demo\"\nedition = \"2026\"\n").unwrap();
    }
    let checked = check_package(d.root());
    let want_code = if src.marks.is_empty() { 0 } else { 1 };
    let mut problems = Vec::new();
    if !ended_well(&checked) || checked.code != want_code {
        problems.push(format!("{tag}: exit {} (want {want_code}); {}", checked.code, checked.stderr));
        return problems;
    }
    let mut by_unit: BTreeMap<String, (Vec<String>, Vec<String>)> = BTreeMap::new();
    for (line, code) in &src.marks {
        by_unit.entry(src.unit_at(*line).to_string()).or_default().0.push(format!("{code}@{line}"));
    }
    for dg in &checked.diags {
        by_unit
            .entry(src.unit_at(dg.line).to_string())
            .or_default()
            .1
            .push(format!("{}@{} ({})", dg.code, dg.line, dg.message));
    }
    for (unit, (want, got)) in by_unit {
        let plain: Vec<String> = got.iter().map(|g| g.split(" (").next().unwrap().to_string()).collect();
        let (mut a, mut b) = (want.clone(), plain);
        a.sort();
        b.sort();
        if a != b {
            problems.push(format!("{tag}/{unit}: want {want:?}, got {got:?}"));
        }
    }
    problems
}

fn finish(problems: Vec<String>) {
    let n = problems.len();
    let limit = std::env::var("SWEEP_SHOW").ok().and_then(|v| v.parse().ok()).unwrap_or(40);
    let shown: Vec<String> = problems.into_iter().take(limit).collect();
    assert!(n == 0, "{n} problem(s):\n{}", shown.join("\n"));
}

// ---- 1. an error type in every form of a body --------------------------------------------------------------

/// A way to make an error type: the text before the items (with the marks of its own diagnostics), the
/// items every body uses are put after it, and the type that is written for `x` and `y`.
struct Kind {
    tag: &'static str,
    head: &'static str,
    ty: &'static str,
}

const USE: &str = "use util.{Gone} @@E0302\n\n";
const CLASH: &str = "pub struct D {\n  a: I32,\n}\n\npub enum D { @@E0304\n  A(I32),\n  B,\n}\n\n";
const CUT: &str = "pub enum E {\n  A,\n  B( @@E0002\n\n";

const KINDS: [Kind; 7] = [
    Kind { tag: "use", head: USE, ty: "Gone" },
    Kind { tag: "use_alias", head: "use util.{Gone} @@E0302\n\npub type A = Gone\n\n", ty: "A" },
    Kind { tag: "use_chain", head: "use util.{Gone} @@E0302\n\npub type A = Gone\n\npub type B = A\n\n", ty: "B" },
    Kind { tag: "clash", head: CLASH, ty: "D" },
    Kind {
        tag: "clash_alias",
        head: "pub struct D {\n  a: I32,\n}\n\npub enum D { @@E0304\n  A(I32),\n  B,\n}\n\npub type AD = D\n\n",
        ty: "AD",
    },
    Kind { tag: "cut", head: CUT, ty: "E.Zed" },
    Kind { tag: "cut_alias", head: "pub enum E {\n  A,\n  B( @@E0002\n\npub type AC = E.Zed\n\n", ty: "AC" },
];

/// The items the bodies use. `{T}` is the error type of the kind.
const COMMON: &str = "pub struct S {
  a: I32,
  b: I32,
}

pub enum En {
  P,
  Q(I32),
}

impl En {
  pub fn make(v: I32) -> I32 {
    v
  }
}

fn id[U](v: U) -> U { v }
fn put(inout v: {T}) { }
fn put2(inout v: {T}, move w: {T}) { }
fn eat[U](move v: U) -> U { v }
fn lo(a: I32, b: I32) -> I32 { a }
fn same(a: I32, b: I32) { }
fn apply(f: fn(I32) -> I32) -> I32 { f.(1) }
fn gid[U](v: U) -> U { v }
fn gadd[U: Num](p: U, q: U) -> U { p + q }
fn gnum[U: Num](p: U) -> U { p }
fn gdup[U: Dup](p: U) -> U { p }
fn geq[U: Eq](p: U, q: U) -> Bool { p == q }
fn gord[U: Ord](p: U, q: U) -> Bool { p < q }
fn garr[U](p: U) -> [U; 2] { [p, p] }
fn gn[U, const N: U32](p: [U; N]) -> U32 { N }
fn gopt[U](p: Option[U], q: U) -> U { q }
fn gnone[U]() -> Option[U] { None }
fn gnone2[U](p: U) -> Option[U] { None }
fn gnone3[U](p: U, q: Option[U]) -> Option[U] { q }

";

/// A form of a body: its name, its statements (`{T}` is the error type), and how its function is made.
/// `x` and `y` are of the error type. `Shape::Plain` is `-> I32` with the statements, `let a: I32 = <v>`
/// and `a`; `Shape::Opt` returns `Option[I32]` (a `?` can be written); `Shape::Alloc` has `uses {Alloc}`
/// (an interpolated string is made on the heap, §12.2).
#[derive(Clone, Copy, PartialEq)]
enum Shape {
    Plain,
    Opt,
    Alloc,
}

use Shape::{Alloc, Opt, Plain};

/// The forms. The spec says for each that a value of an error type, used as it is used there, has no diagnostic
/// of its own (§18.1) and that nothing else in the statements is an error. A form is not here when the
/// statements have an error that does not depend on the type of `x` (a name that is nowhere, a `?` in a
/// function that returns `I32`, a closure that captures and is bound by a `let`, an effect that the function
/// does not have, a type parameter that nothing decides), or when the spec leaves the diagnostic open.
const BODIES: &[(&str, &str, Shape)] = &[
    // operators
    ("add", "let _ = x + 1", Plain),
    ("add2", "let _ = x + y", Plain),
    ("sub_rev", "let _ = 1 - x", Plain),
    ("neg", "let _ = -x", Plain),
    ("not", "let _ = !x", Plain),
    ("mulf", "let _ = x * 2.0", Plain),
    ("rem", "let _ = x % 3", Plain),
    ("div0", "let _ = x / 0", Plain),
    ("wrap", "let _ = x +% y", Plain),
    ("sat", "let _ = x *| 2", Plain),
    ("bitand", "let _ = x & 1", Plain),
    ("bitor", "let _ = x | y", Plain),
    ("bitxor", "let _ = x ^ y", Plain),
    ("shl", "let _ = x << 2", Plain),
    ("shr", "let _ = 1 >> x", Plain),
    ("lit_float", "let _ = x + 1.5", Plain),
    ("lit_hex", "let _ = 0xFF + x", Plain),
    ("lit_big", "let _ = x + 99999999999", Plain),
    // comparison and logic
    ("lt", "let _ = x < y", Plain),
    ("eq", "let _ = x == y", Plain),
    ("ne", "let _ = x != 1", Plain),
    ("and", "let _ = x && true", Plain),
    ("or", "let _ = true || x", Plain),
    ("cmp_chain", "let _ = (x < 1) == (y > 2)", Plain),
    ("eq_none", "let _ = x == None", Plain),
    ("eq_empty", "let _ = x == []", Plain),
    ("eq_tuple", "let _ = x == (1, 2)", Plain),
    ("eq_array", "let _ = x == [1, 2]", Plain),
    // conversions
    ("as_i32", "let _ = x as I32", Plain),
    ("as_f32", "let _ = x as F32", Plain),
    ("as_u8", "let _ = (x + 1) as U8", Plain),
    // methods
    ("m_foo", "let _ = x.foo()", Plain),
    ("m_len", "let _ = x.len()", Plain),
    ("m_chain", "let _ = x.abs().foo(1)", Plain),
    ("m_args", "let _ = x.foo(1, true, y)", Plain),
    ("m_unwrap", "let _ = x.unwrap()", Plain),
    ("m_unwrap_or", "let _ = x.unwrap_or(0)", Plain),
    // fields, elements, indexes, `?`, calls
    ("f_a", "let _ = x.a", Plain),
    ("f_ab", "let _ = x.a.b", Plain),
    ("f_0", "let _ = x.0", Plain),
    ("idx", "let _ = x[0]", Plain),
    ("idx_y", "let _ = x[y]", Plain),
    ("try", "let _ = x?", Opt),
    ("call", "let _ = x(1)", Plain),
    ("call_dot", "let _ = x.(1, 2)", Plain),
    ("call_inout_arg", "let _ = x(inout y)", Plain),
    // patterns of a `let`
    ("let_tuple", "let (_, _) = x", Plain),
    ("let_tuple3", "let (_, _, _) = x", Plain),
    ("let_struct", "let S { a: _, b: _ } = x", Plain),
    ("let_nested", "let ((_, _), _) = x", Plain),
    // `match`: the patterns, the guards, the missing arms (the scrutinee is an error type, so nothing is missing)
    ("m_some", "let _ = match x { Some(v) => v, None => 0 }", Plain),
    ("m_ok", "let _ = match x { Ok(v) => v, Err(_) => 0 }", Plain),
    ("m_lit", "let _ = match x { 1 => 1, 2 => 2, _ => 0 }", Plain),
    ("m_or", "let _ = match x { 1 | 2 => 1, _ => 0 }", Plain),
    ("m_bind", "let _ = match x { m => m }", Plain),
    ("m_wild", "let _ = match x { _ => 0 }", Plain),
    ("m_tuple", "let _ = match x { (p, _) => p }", Plain),
    ("m_tuple_nested", "let _ = match x { ((p, _), _) => p }", Plain),
    ("m_struct", "let _ = match x { S { a: p, b: _ } => p }", Plain),
    ("m_struct_lit", "let _ = match x { S { a: 1, b: q } => q, S { a: p, b: _ } => p }", Plain),
    ("m_enum", "let _ = match x { En.P => 0, En.Q(v) => v }", Plain),
    ("m_enum_miss", "let _ = match x { En.P => 0 }", Plain),
    ("m_none_only", "let _ = match x { None => 0 }", Plain),
    ("m_some_only", "let _ = match x { Some(v) => v }", Plain),
    ("m_guard", "let _ = match x { Some(v) if v > 0 => v, _ => 0 }", Plain),
    ("m_bool", "let _ = match x { true => 1, false => 0 }", Plain),
    ("m_str", "let _ = match x { \"a\" => 1, _ => 0 }", Plain),
    ("m_two_scrut", "let _ = match (x, y) { (1, 2) => 0, _ => 1 }", Plain),
    ("m_two_scrut_miss", "let _ = match (x, y) { (Some(_), None) => 0, (None, _) => 1 }", Plain),
    ("m_tuple_all", "let _ = match (x, y) { (_, _) => 0 }", Plain),
    ("m_move", "let _ = match move x { Some(_) => 0, None => 1 }", Plain),
    ("m_in_arm", "let _ = match true { true => x + 1, false => 0 }", Plain),
    // conditions and loops
    ("if1", "if x { }", Plain),
    ("if_else", "let _ = if x { 1 } else { 2 }", Plain),
    ("if_cmp", "let _ = if x < y { 1 } else { 2 }", Plain),
    ("if_return", "if true { return x }", Plain),
    ("while1", "var k = 0\n  while x { k = k + 1 }", Plain),
    ("while_cmp", "var k = 0\n  while k < x { k = k + 1 }", Plain),
    ("for1", "for _ in x { }", Plain),
    ("for_range", "for _ in 0 ..< x { }", Plain),
    ("for_range2", "for _ in x ..< y { }", Plain),
    ("for_tuple", "for (_, _) in x { }", Plain),
    ("for_move", "for _ in move x { }", Plain),
    ("while_break", "while true { break }", Plain),
    ("nested", "if true { while x { break } }", Plain),
    ("block", "let _ = {\n    let w = x + 1\n    w\n  }", Plain),
    // assignment
    ("assign", "var z = 0\n  z = x\n  let _ = z", Plain),
    ("assign_op", "var z = 0\n  z = z + x", Plain),
    ("assign_var", "var v = x\n  v = y\n  let _ = v", Plain),
    ("assign_var2", "var v = x\n  v = 1\n  let _ = v", Plain),
    ("assign_var3", "var v = 1\n  v = x\n  v = v + 1", Plain),
    ("assign_field", "var v = x\n  v.a = 1\n  let _ = v", Plain),
    ("assign_idx", "var v = x\n  v[0] = 1\n  let _ = v", Plain),
    ("assign_idx_op", "var v = x\n  v[0] = v[0] + 1", Plain),
    ("assign_tuple", "var v = x\n  v.0 = 1\n  let _ = v", Plain),
    // `move` and `inout` arguments
    ("move_let", "let _ = move x", Plain),
    ("move_arg", "let _ = eat(move x)", Plain),
    ("move_twice", "let _ = eat(move x)\n  let _ = eat(move x)", Plain),
    ("move_then_use", "let _ = move x\n  let _ = x", Plain),
    ("inout_arg", "var v = x\n  put(inout v)", Plain),
    ("inout_arg2", "var v = x\n  put2(inout v, move y)", Plain),
    ("inout_field", "var v = x\n  put(inout v.a)", Plain),
    ("inout_idx", "var v = x\n  put(inout v[0])", Plain),
    ("borrow_use", "let _ = id(x)", Plain),
    ("borrow2", "let _ = id(x)\n  let _ = id(x)", Plain),
    // closures
    ("clos_cap", "let _ = apply(fn(p: I32) -> I32 { p + x })", Plain),
    ("clos_cap2", "let _ = apply(fn(p: I32) -> I32 { x })", Plain),
    ("clos_param", "let f = fn(p: {T}) -> I32 { 0 }\n  let _ = f.(x)", Plain),
    ("clos_ret", "let f = fn(p: I32) -> {T} { None }\n  let _ = f.(1)", Plain),
    ("clos_ret2", "let f = fn(p: I32) -> {T} { None }\n  let _ = f.(1) + 1", Plain),
    ("clos_ret_arr", "let f = fn(p: I32) -> {T} { [] }\n  let _ = f.(1)", Plain),
    // literals
    ("struct_lit", "let _ = S { a: x, b: y }", Plain),
    ("struct_lit2", "let _ = S { a: x, b: 1 }.a", Plain),
    ("struct_lit3", "let _ = S { a: 1, b: 1 + x }", Plain),
    ("arr_lit", "let _ = [x, y]", Plain),
    ("arr_lit_mixed", "let _ = [x, 1]", Plain),
    ("arr_rep", "let _ = [x; 3]", Plain),
    ("arr_idx", "let _ = [x, y][0]", Plain),
    ("tuple_lit", "let _ = (x, 1)", Plain),
    ("tuple_lit_idx", "let _ = (x, 1).0", Plain),
    ("interp", "let _ = \"v={x}\"", Alloc),
    // the type of a local and of a value
    ("ann_var", "let _: {T} = x\n  let _: {T} = y", Plain),
    ("ann_other", "let _: Bool = x", Plain),
    ("ann_i32", "let _: I32 = x", Plain),
    ("ann_opt", "let _: Option[I32] = x", Plain),
    ("ret_none", "let _: {T} = None", Plain),
    ("opt_wrap", "let _ = Some(x)", Plain),
    ("opt_none", "let _ = if true { None } else { x }", Plain),
    ("opt_none2", "let _ = if true { x } else { None }", Plain),
    ("empty_arr", "let _ = if true { [] } else { x }", Plain),
    ("empty_arr2", "let _ = [x, []]", Plain),
    ("none_arr", "let _ = [None, x]", Plain),
    // calls of a function (the generic ones: a type variable that meets an error type is decided)
    ("g_call", "let _ = gid(x)", Plain),
    ("g_call_add", "let _ = gid(x) + 1", Plain),
    ("g_call2", "let _ = gadd(x, y)", Plain),
    ("g_call3", "let _ = gadd(x, 1)", Plain),
    ("g_num", "let _ = gnum(x)", Plain),
    ("g_dup", "let _ = gdup(x)", Plain),
    ("g_eq", "let _ = geq(x, y)", Plain),
    ("g_ord", "let _ = gord(x, 1)", Plain),
    ("g_arr", "let _ = garr(x)", Plain),
    ("g_arr2", "let _ = garr([x, y])", Plain),
    ("g_n", "let _ = gn([x, y])", Plain),
    ("g_opt", "let _ = gopt(None, x)", Plain),
    ("g_opt2", "let _ = gopt(x, None)", Plain),
    ("g_unres_ann", "let _: {T} = gnone2(1)", Plain),
    ("g_unres_ann2", "let _: {T} = gnone()", Plain),
    ("g_unres_x", "let _ = gnone2(x)", Plain),
    ("g_unres_x2", "let _ = gnone3(x, None)", Plain),
    ("assoc_fn", "let _ = En.make(x)", Plain),
    ("lo", "let _ = lo(x, y)", Plain),
    ("same", "same(x, 1)", Plain),
    ("sum_calls", "let _ = id(x) + id(y)", Plain),
];

fn function(prefix: &str, name: &str, shape: Shape, stmts: &str, ty: &str, real: bool) -> String {
    let uses = if shape == Alloc { " uses {Alloc}" } else { "" };
    let (ret, tail) = if shape == Opt { ("Option[I32]", "Some(a)") } else { ("I32", "a") };
    let last = if real { "let a: I32 = true @@E0401" } else { "let a: I32 = 1" };
    let stmts = stmts.replace("{T}", ty);
    format!("pub fn {prefix}_{name}(x: {ty}, y: {ty}) -> {ret}{uses} {{\n  {stmts}\n  {last}\n  {tail}\n}}\n\n")
}

/// §18.1: a value of an error type is used in every form of a body, and nothing is reported on the use. The
/// functions with a real error report that and nothing else; the ones without report nothing.
#[test]
fn error_type_in_every_body_form() {
    let mut problems = Vec::new();
    let mut units = 0;
    for k in &KINDS {
        let mut src = Src::new();
        src.raw(k.head);
        src.raw(&COMMON.replace("{T}", k.ty));
        for (name, stmts, shape) in BODIES {
            src.unit(&format!("r_{name}"), &function("r", name, *shape, stmts, k.ty, true));
            src.unit(&format!("c_{name}"), &function("c", name, *shape, stmts, k.ty, false));
            units += 2;
        }
        // the controls: an error type that is only a part of the type keeps the errors of the rest
        let part = k.ty;
        src.unit(
            "ctl_part_field",
            &format!("pub fn ctl_part_field(x: Option[{part}]) -> I32 {{\n  let r = x.a @@E0413\n  0\n}}\n\n"),
        );
        src.unit(
            "ctl_part_ann",
            &format!("pub fn ctl_part_ann(x: Option[{part}]) -> I32 {{\n  let r: Bool = x @@E0401\n  0\n}}\n\n"),
        );
        src.unit(
            "ctl_part_as",
            &format!("pub fn ctl_part_as(x: Option[{part}]) -> I32 {{\n  let r = x as I32 @@E0411\n  0\n}}\n\n"),
        );
        problems.extend(verify(&format!("body_{}", k.tag), &src));
    }
    assert!(units >= 7 * 2 * 100, "only {units} functions were checked");
    finish(problems);
}

// ---- 2. an unknown bound ---------------------------------------------------------------------------------------

/// The items the generic bodies use.
const GENERIC_COMMON: &str = "fn id[U](v: U) -> U { v }
fn eat[U](move v: U) -> U { v }
fn gplain[U](p: U) -> U { p }
fn gadd[U: Num](p: U, q: U) -> U { p + q }
fn geq[U: Eq](p: U, q: U) -> Bool { p == q }
fn gord[U: Ord](p: U, q: U) -> Bool { p < q }
fn gdup[U: Dup](p: U) -> U { p }
fn gnodup[U: ?Dup](p: U) -> I32 { 0 }

";

/// The forms that depend on the type parameter meeting a trait: no diagnostic when a bound is not known.
/// `x` and `y` are of the type parameter `T`, `n` is a `U32`.
const BOUND_SILENT: &[(&str, &str)] = &[
    ("add", "let _ = x + y"),
    ("sub", "let _ = x - y"),
    ("mul", "let _ = x * y"),
    ("div", "let _ = x / y"),
    ("rem", "let _ = x % y"),
    ("wrap_add", "let _ = x +% y"),
    ("wrap_sub", "let _ = x -% y"),
    ("wrap_mul", "let _ = x *% y"),
    ("sat_add", "let _ = x +| y"),
    ("sat_sub", "let _ = x -| y"),
    ("sat_mul", "let _ = x *| y"),
    ("neg", "let _ = -x"),
    ("not", "let _ = !x"),
    ("bitand", "let _ = x & y"),
    ("bitor", "let _ = x | y"),
    ("bitxor", "let _ = x ^ y"),
    ("shl", "let _ = x << n"),
    ("shr", "let _ = x >> n"),
    ("lt", "let _ = x < y"),
    ("le", "let _ = x <= y"),
    ("gt", "let _ = x > y"),
    ("ge", "let _ = x >= y"),
    ("eq", "let _ = x == y"),
    ("ne", "let _ = x != y"),
    ("m0", "let _ = x.foo()"),
    ("m1", "let _ = x.foo(y)"),
    ("m_chain", "let _ = x.foo().bar(1)"),
    ("call_num", "let _ = gadd(x, y)"),
    ("call_eq", "let _ = geq(x, y)"),
    ("call_ord", "let _ = gord(x, y)"),
    ("call_dup", "let _ = gdup(x)"),
    ("call_nodup", "let _ = gnodup(x)"),
    ("call_plain", "let _ = gplain(x)"),
    ("arr_rep", "let _ = [x; 3]"),
    ("arr_lit", "let _ = [x, y]"),
    ("move_twice", "let _ = eat(move x)\n  let _ = eat(move x)"),
    ("use_twice", "let _ = x\n  let _ = x"),
    ("clos", "let f = fn(p: T) -> T { p + p }\n  let _ = f.(x)"),
    ("clos_ord", "let f = fn(p: T, q: T) -> Bool { p < q }\n  let _ = f.(x, y)"),
    ("if_cmp", "let _ = if x < y { 1 } else { 2 }"),
];

/// The forms that stay errors, whatever the bounds are, with the code of the error: the first error of the
/// function is the line, and nothing is reported after it. `ret` is the type the function returns.
const BOUND_REAL: &[(&str, &str, &str)] = &[
    ("field", "let r = x.a", "E0413"),
    ("ann_u32", "let r: U32 = x", "E0401"),
    ("and", "let r = x && y", "E0401"),
    ("pass_bool", "let r = gadd(true, true)", "E0416"),
    ("pass_bool_ord", "let r = gord(true, 1)", "E0401"),
];

/// A bound list with the failed name in it (`{G}`), as it is written after `T:`.
const BOUNDS: [(&str, &str); 5] = [
    ("alone", "{G}"),
    ("num_before", "Num + {G}"),
    ("num_after", "{G} + Num"),
    ("nodup", "?Dup + {G}"),
    ("eq_before", "Eq + {G}"),
];

/// A name that fails in the names stage, and the text before the items.
const FAILED_BOUND: [(&str, &str, &str); 2] = [
    ("use", "use util.{Gone} @@E0302\n\n", "Gone"),
    ("clash", "pub struct Tr {\n  a: I32,\n}\n\npub enum Tr { @@E0304\n  A,\n}\n\n", "Tr"),
];

/// §18.1, S-689, S-692 A1: a failed name in a bound is an unknown bound. The forms that depend on the type
/// parameter meeting a trait (operators, methods, the bounds of other functions, the `Dup` of `[x; 3]` and of
/// a move) have no diagnostic, and the forms that do not depend on it keep theirs.
#[test]
fn unknown_bound_silences_what_depends_on_the_trait() {
    let mut problems = Vec::new();
    let mut units = 0;
    for (tag, head, name) in FAILED_BOUND {
        let mut src = Src::new();
        src.raw(head);
        src.raw(GENERIC_COMMON);
        for (btag, bound) in BOUNDS {
            let bound = bound.replace("{G}", name);
            for (fname, stmts) in BOUND_SILENT {
                for (suffix, last) in [("r", "let a: I32 = true @@E0401"), ("c", "let a: I32 = 1")] {
                    let unit = format!("{suffix}_{btag}_{fname}");
                    src.unit(
                        &unit,
                        &format!(
                            "pub fn {unit}[T: {bound}](x: T, y: T, n: U32) -> I32 {{\n  {stmts}\n  {last}\n  a\n}}\n\n"
                        ),
                    );
                    units += 1;
                }
            }
            for (fname, stmts, code) in BOUND_REAL {
                let unit = format!("e_{btag}_{fname}");
                src.unit(
                    &unit,
                    &format!(
                        "pub fn {unit}[T: {bound}](x: T, y: T, n: U32) -> I32 {{\n  {stmts} @@{code}\n  let a: I32 = true\n  a\n}}\n\n"
                    ),
                );
                units += 1;
            }
            // a type parameter where another type is wanted
            let unit = format!("e_{btag}_ret");
            src.unit(&unit, &format!("pub fn {unit}[T: {bound}](x: T, y: T, n: U32) -> U32 {{\n  x @@E0401\n}}\n\n"));
            units += 1;
        }
        // the controls: bounds that are all known
        src.unit("ctl_plain_cmp", "pub fn ctl_plain_cmp[T](x: T, y: T) -> Bool {\n  x < y @@E0401\n}\n\n");
        src.unit("ctl_plain_method", "pub fn ctl_plain_method[T](x: T) -> I32 {\n  x.foo() @@E0413\n}\n\n");
        src.unit("ctl_plain_call", "pub fn ctl_plain_call[T](x: T, y: T) -> T {\n  gadd(x, y) @@E0416\n}\n\n");
        src.unit("ctl_nodup_arr", "pub fn ctl_nodup_arr[T: ?Dup](x: T) -> I32 {\n  let r = [x; 3] @@E0416\n  0\n}\n\n");
        src.unit("ctl_num_method", "pub fn ctl_num_method[T: Num](x: T) -> I32 {\n  x.foo() @@E0413\n}\n\n");
        src.unit(
            "ctl_other_param",
            "pub fn ctl_other_param[T: Gone2, U](x: T, y: U) -> Bool {\n  let b = x < x\n  y < y @@E0401\n}\n\n"
                .replace("Gone2", name)
                .as_str(),
        );
        // a bound nothing binds is E0302 and the body is not checked
        src.unit("ctl_unbound", "pub fn ctl_unbound[T: Nope](x: T) -> I32 { @@E0302\n  let a: I32 = true\n  a\n}\n\n");
        problems.extend(verify(&format!("bound_{tag}"), &src));
    }
    assert!(units >= 2 * 5 * 60, "only {units} functions were checked");
    finish(problems);
}

/// The callees of [`NO_KIND`] (`{G}` the type parameters of a function, `{X}` the type with no kind).
const NO_KIND_CALLEES: &str = "fn two{G}(move a: {X}, b: {X}) {}
fn two_mv{G}(move a: {X}, move b: {X}) {}
rt fn keep{G}(move p: (Buf[F32], {X})) -> (Buf[F32], {X}) { p }
fn keep_n{G}(move p: (Buf[F32], {X})) -> (Buf[F32], {X}) { p }

";

/// The forms whose diagnostics depend on the kind of a value of no known kind (§18.1, §4.6): whether it
/// moves (E0702 of a `move` argument and another, the E0703 of `move`, S-609), and of an aggregate with an
/// Affine part, which is Affine whatever the other part is (its drop, E0901 and E0601; E0704).
const NO_KIND: &[(&str, &str)] = &[
    ("move_and_read", "pub fn NAME{G}(move x: {X}) {\n  two(move x, x)\n}\n\n"),
    ("move_twice", "pub fn NAME{G}(move x: {X}) {\n  two_mv(move x, move x)\n}\n\n"),
    ("no_marks", "pub fn NAME{G}(move x: {X}) {\n  two_mv(x, x)\n}\n\n"),
    ("rt_return", "pub rt fn NAME{G}(move p: (Buf[F32], {X})) -> (Buf[F32], {X}) {\n  p\n}\n\n"),
    ("rt_pass", "pub rt fn NAME{G}(move p: (Buf[F32], {X})) -> (Buf[F32], {X}) {\n  keep(move p)\n}\n\n"),
    (
        "rt_let",
        "pub rt fn NAME{G}(move p: (Buf[F32], {X})) -> (Buf[F32], {X}) {\n  let q = move p\n  keep(move q)\n}\n\n",
    ),
    ("plain_return", "pub fn NAME{G}(move p: (Buf[F32], {X})) -> (Buf[F32], {X}) {\n  p\n}\n\n"),
    ("plain_pass", "pub fn NAME{G}(move p: (Buf[F32], {X})) -> (Buf[F32], {X}) {\n  keep_n(move p)\n}\n\n"),
    (
        "moved_twice",
        "pub fn NAME{G}(move p: (Buf[F32], {X})) -> U32 {\n  let q = move p\n  let r = move p @@E0704\n  1\n}\n\n",
    ),
];

/// §18.1, §4.6: a value of an unknown bound or of the error type has no kind, so what depends on whether it
/// moves has no diagnostic; an aggregate with an Affine part is Affine (W4-07 U4b-2).
#[test]
fn a_value_of_no_kind() {
    let mut problems = Vec::new();
    for (tag, generics, ty) in [("bound", "[T: Gone]", "T"), ("error", "", "Gone")] {
        let fill = |t: &str| t.replace("{G}", generics).replace("{X}", ty);
        let mut src = Src::new();
        src.raw(USE);
        src.raw(&fill(NO_KIND_CALLEES));
        for (name, form) in NO_KIND {
            src.unit(name, &fill(form).replace("NAME", name));
        }
        problems.extend(verify(&format!("no_kind_{tag}"), &src));
    }
    finish(problems);
}

// ---- 3. the exhaustiveness ---------------------------------------------------------------------------------

/// §18.1, S-692 A2: the part of a pattern whose type is an error type matches anything, and a part that is
/// missing in the other parts is E0501. The receiver itself an error type has nothing missing. `{X}` is the
/// error type of the kind. The unit has the mark on the line of the `match`.
const EXHAUST_TYPES: &str = "pub struct W {\n  b: Bool,\n  g: {X},\n}\n\npub enum V {\n  A({X}),\n  B,\n}\n\n";

const EXHAUST: &[(&str, &str, bool)] = &[
    ("opt_none_only", "pub fn NAME(o: Option[{X}]) -> I32 {\n  match o { @@E0501\n    None => 1,\n  }\n}\n\n", true),
    ("opt_some_only", "pub fn NAME(o: Option[{X}]) -> I32 {\n  match o { @@E0501\n    Some(v) => 1,\n  }\n}\n\n", true),
    (
        "opt_both",
        "pub fn NAME(o: Option[{X}]) -> I32 {\n  match o {\n    Some(_) => 1,\n    None => 2,\n  }\n}\n\n",
        false,
    ),
    (
        "opt_some_wild",
        "pub fn NAME(o: Option[{X}]) -> I32 {\n  match o {\n    Some(_) => 1,\n    _ => 2,\n  }\n}\n\n",
        false,
    ),
    (
        "opt_opt_miss",
        "pub fn NAME(o: Option[Option[{X}]]) -> I32 {\n  match o { @@E0501\n    Some(Some(v)) => 1,\n    None => 2,\n  }\n}\n\n",
        true,
    ),
    (
        "opt_opt_all",
        "pub fn NAME(o: Option[Option[{X}]]) -> I32 {\n  match o {\n    Some(Some(_)) => 1,\n    Some(None) => 2,\n    None => 3,\n  }\n}\n\n",
        false,
    ),
    (
        "tuple_true_only",
        "pub fn NAME(o: (Bool, {X})) -> I32 {\n  match o { @@E0501\n    (true, v) => 1,\n  }\n}\n\n",
        true,
    ),
    (
        "tuple_both",
        "pub fn NAME(o: (Bool, {X})) -> I32 {\n  match o {\n    (true, _) => 1,\n    (false, _) => 2,\n  }\n}\n\n",
        false,
    ),
    (
        "tuple_first_error",
        "pub fn NAME(o: ({X}, Bool)) -> I32 {\n  match o { @@E0501\n    (v, true) => 1,\n  }\n}\n\n",
        true,
    ),
    (
        "tuple_first_error_all",
        "pub fn NAME(o: ({X}, Bool)) -> I32 {\n  match o {\n    (_, true) => 1,\n    (_, false) => 2,\n  }\n}\n\n",
        false,
    ),
    (
        "struct_true_only",
        "pub fn NAME(o: W) -> I32 {\n  match o { @@E0501\n    W { b: true, g: v } => 1,\n  }\n}\n\n",
        true,
    ),
    (
        "struct_both",
        "pub fn NAME(o: W) -> I32 {\n  match o {\n    W { b: true, g: _ } => 1,\n    W { b: false, g: _ } => 2,\n  }\n}\n\n",
        false,
    ),
    ("enum_payload_miss", "pub fn NAME(o: V) -> I32 {\n  match o { @@E0501\n    V.A(p) => 1,\n  }\n}\n\n", true),
    ("enum_payload_all", "pub fn NAME(o: V) -> I32 {\n  match o {\n    V.A(_) => 1,\n    V.B => 2,\n  }\n}\n\n", false),
    // the receiver itself is an error type: nothing is missing
    ("recv_none", "pub fn NAME(o: {X}) -> I32 {\n  match o {\n    None => 1,\n  }\n}\n\n", false),
    ("recv_some", "pub fn NAME(o: {X}) -> I32 {\n  match o {\n    Some(v) => v,\n  }\n}\n\n", false),
    ("recv_bool", "pub fn NAME(o: {X}) -> I32 {\n  match o {\n    true => 1,\n  }\n}\n\n", false),
    ("recv_tuple", "pub fn NAME(o: {X}) -> I32 {\n  match o {\n    (_, _) => 1,\n  }\n}\n\n", false),
    (
        "recv_pair_of_errors",
        "pub fn NAME(o: ({X}, {X})) -> I32 {\n  match o {\n    (Some(_), None) => 1,\n  }\n}\n\n",
        false,
    ),
];

/// §18.1, S-692 A2, R-271.
#[test]
fn exhaustiveness_takes_the_error_type_as_everything() {
    let mut problems = Vec::new();
    let mut units = 0;
    for k in &KINDS {
        let mut src = Src::new();
        src.raw(k.head);
        src.raw(&EXHAUST_TYPES.replace("{X}", k.ty));
        for (name, template, _) in EXHAUST {
            let unit = format!("x_{name}");
            src.unit(&unit, &template.replace("NAME", &unit).replace("{X}", k.ty));
            units += 1;
        }
        problems.extend(verify(&format!("exhaust_{}", k.tag), &src));
    }
    assert!(units >= 7 * 15, "only {units} functions were checked");
    finish(problems);
}

// ---- 4. flows ---------------------------------------------------------------------------------------------------

/// §11, §18.1: the inputs and outputs of a flow whose type is an error type (or has one in it), and a delay of
/// a value of an error type, whose omitted `init` is `T.default()` of a type that is not known (§11.4): no
/// diagnostic. The real error after the use is the one `E0401` of the flow.
const FLOWS: &[(&str, &str)] = &[
    ("in_plain", "x: {X} at sample) -> F32 at sample {\n  STMTS1.0\n}"),
    ("in_array", "x: [{X}; 2] at sample) -> F32 at sample {\n  STMTS1.0\n}"),
    ("in_block", "x: {X} at block) -> F32 at sample {\n  STMTS1.0\n}"),
    ("in_init", "x: {X} at init) -> F32 at sample {\n  STMTS1.0\n}"),
    ("in_array_block", "x: [{X}; 2] at block) -> F32 at sample {\n  STMTS1.0\n}"),
    ("out_plain", "x: F32 at sample) -> {X} at sample {\n  STMTSx\n}"),
    ("out_array", "x: F32 at sample) -> [{X}; 2] at sample {\n  STMTS[x, x]\n}"),
    ("io_same", "x: {X} at sample) -> {X} at sample {\n  STMTSx\n}"),
    ("prev_init_omitted", "x: {X} at sample) -> F32 at sample {\n  let z = prev~(x)\n  STMTS1.0\n}"),
    ("prev_out", "x: {X} at sample) -> {X} at sample {\n  let z = prev~(x)\n  STMTSz\n}"),
    ("delay_init_omitted", "x: {X} at sample) -> F32 at sample {\n  let z = delay~(x, 8)\n  STMTS1.0\n}"),
    ("delay_out", "x: {X} at sample) -> {X} at sample {\n  STMTSdelay~(x, 8)\n}"),
    // The `init` is written: the omitted one of an array is an E0200 of this version whatever its elements are.
    ("prev_array", "x: [{X}; 2] at sample) -> F32 at sample {\n  let z = prev~(x, [0.0, 0.0])\n  STMTS1.0\n}"),
    ("prev_local", "x: F32 at sample) -> F32 at sample {\n  let y: {X} = x\n  let z = prev~(y)\n  STMTS1.0\n}"),
    ("prev_init_given", "x: {X} at sample, n: {X} at init) -> F32 at sample {\n  let z = prev~(x, n)\n  STMTS1.0\n}"),
];

#[test]
fn flow_with_error_types() {
    let mut problems = Vec::new();
    let mut units = 0;
    for k in &KINDS {
        let mut src = Src::new();
        src.raw(k.head);
        for (name, template) in FLOWS {
            for (suffix, stmts) in [("r", "let a: I32 = true @@E0401\n  "), ("c", "")] {
                let unit = format!("{suffix}_{name}");
                let body = template.replace("{X}", k.ty).replace("STMTS", stmts);
                src.unit(&unit, &format!("pub flow {unit}({body}\n\n"));
                units += 1;
            }
        }
        problems.extend(verify(&format!("flow_{}", k.tag), &src));
    }
    assert!(units >= 7 * 2 * 15, "only {units} flows were checked");
    finish(problems);
}

// ---- 5. the interpolation of a failed name --------------------------------------------------------------------

/// §18.1, R-270 (W4-04 makes the names of a body be resolved): a failed name written in the braces of an
/// interpolated string is an error where it is used, so the string has no diagnostic of its own, as the
/// local of an error type has none. The only diagnostics are the ones of the failed names.
#[test]
fn the_interpolation_of_a_failed_name_is_silent() {
    let heads = [
        ("use_upper", "use util.{KK} @@E0302\n\n", ["KK", "KK.a"]),
        ("use_lower", "use util.{gone} @@E0302\n\n", ["gone", "gone.a"]),
        ("clash_const", "pub const KK: U32 = 4\n\npub const KK: U32 = 8 @@E0304\n\n", ["KK", "KK.a"]),
    ];
    let mut problems = Vec::new();
    for (tag, head, names) in heads {
        let mut src = Src::new();
        src.raw(head);
        for (i, name) in names.iter().enumerate() {
            let unit = format!("interp_{i}");
            src.unit(
                &unit,
                &format!("pub fn {unit}() -> I32 uses {{Alloc}} {{\n  let s = \"v={{{name}}}\"\n  1\n}}\n\n"),
            );
        }
        problems.extend(verify(&format!("interp_{tag}"), &src));
    }
    finish(problems);
}
