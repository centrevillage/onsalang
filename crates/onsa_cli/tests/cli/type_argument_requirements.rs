//! The requirement a type argument fails first, written in a type and used as a value (spec §4.5, S-1013 (i),
//! S-862; W5-13 U5b/t).
//!
//! §4.5: a type argument that meets none of the requirements of a type parameter is reported with the first it
//! does not meet "in the same order as a value is used: the implicit `Escape`, the implicit `Dup`, the bound
//! written". A type written in a signature, a field, the right side of an alias, an annotation, a `N::[…].K` of
//! a body and a constant expression of a type is judged by the requirements of the type parameters of `N`; a
//! value use is `mk(x)` for a `fn mk[T…](x: T)`. The two must give the same code (E0416, or E0710 for the
//! implicit `Escape`) and name the same requirement (`T: Dup`, `T: Eq`, … in the message; E0710 is `Escape`).
//!
//! The grid: six type parameters (`T`, `T: Eq`, `T: Copy`, `T: Num`, `T: ?Dup + Eq`, `T: ?Escape + Eq`) against
//! seven arguments (`Buf[F32]`, an Affine struct, `Option[Buf[F32]]`, `Span[F32]`, `I32`, `Bool`, `Str`) in the
//! seven places above, and against the three type parameters `U`, `U: ?Dup`, `U: ?Dup + Eq` as the argument of an
//! `impl` heading, of a signature and of a value use (the arguments of an `impl` heading are the parameters of
//! the `impl` only, §6.2).
//!
//! The oracle (`unmet`) is written from §4.5, §4.6, §6.3: the kinds and the traits of the arguments are the
//! tables of those sections; nothing is read from the output of the command. It judges a cell as the spec
//! reads: the implicit `Escape` first (a second-class argument to a parameter without `?Escape`), then the
//! implicit `Dup` (not for a second-class argument given to `?Escape`, whose kind requirements count as met,
//! §4.5), then the bound. What the message names is read as the text between backticks that begins with `T: `.
//!
//! The cells split into three kinds of tests, so that a decision that moves one kind does not hide the others:
//! - settled by the spec: the code and the requirement of every cell whose first unmet requirement is not a
//!   `Dup` that the bound also asks for;
//! - S-1021 (OPEN, provisional reading (1)): a bound that itself needs `Dup` (`T: Copy`, `T: Num`) and an argument
//!   that is not `Dup`: the first requirement reported is the implicit `Dup`, as the value use does today. If
//!   S-1021 is decided as (3) the bound is reported instead, in both places, and these cells change together;
//! - S-1020 (OPEN, provisional reading (2)): two type arguments of one type that each fail a requirement.
//!
//! Every input is checked in this process (`check_file`), nothing is written to the disk.

use std::sync::OnceLock;

use crate::test_support::sweep::{Checked, check_file, ended_well, quoted};

#[derive(Clone, Copy, PartialEq)]
enum Bound {
    None,
    Eq,
    Copy,
    Num,
}

/// A type parameter of `N` and `mk`: what is written in `[ ]`, and what it asks.
struct Param {
    decl: &'static str,
    /// The implicit `Escape` is asked (no `?Escape`).
    escape: bool,
    /// The implicit `Dup` is asked (no `?Dup`).
    dup: bool,
    bound: Bound,
}

const PARAMS: &[Param] = &[
    Param { decl: "T", escape: true, dup: true, bound: Bound::None },
    Param { decl: "T: Eq", escape: true, dup: true, bound: Bound::Eq },
    Param { decl: "T: Copy", escape: true, dup: true, bound: Bound::Copy },
    Param { decl: "T: Num", escape: true, dup: true, bound: Bound::Num },
    Param { decl: "T: ?Dup + Eq", escape: true, dup: false, bound: Bound::Eq },
    Param { decl: "T: ?Escape + Eq", escape: false, dup: true, bound: Bound::Eq },
];

/// A type argument: how it is written, and what it is (§4.1 the kinds, §4.6, §6.3 the table of traits).
struct Arg {
    label: &'static str,
    /// The type as written; for a type parameter of the item, its name.
    ty: &'static str,
    /// The `[ ]` of the item that declares the type parameter `U` (a type parameter as the argument), or "".
    declares: &'static str,
    /// Not second-class (`Span` is).
    first_class: bool,
    dup: bool,
    copy: bool,
    eq: bool,
    num: bool,
}

const fn arg(
    label: &'static str,
    ty: &'static str,
    first_class: bool,
    dup: bool,
    copy: bool,
    eq: bool,
    num: bool,
) -> Arg {
    Arg { label, ty, declares: "", first_class, dup, copy, eq, num }
}

const fn type_param(label: &'static str, declares: &'static str, dup: bool, eq: bool) -> Arg {
    Arg { label, ty: "U", declares, first_class: true, dup, copy: false, eq, num: false }
}

/// `Buf` is Affine and has no `Eq`; `B` (declared below) is an Affine struct with no derive; `Option[Buf[F32]]` is
/// Affine and has `Eq` only when its content has it; `Span` is second-class and has no trait; `Str` is Shared.
const ARGS: &[Arg] = &[
    arg("Buf[F32]", "Buf[F32]", true, false, false, false, false),
    arg("Affine struct", "B", true, false, false, false, false),
    arg("Option[Buf[F32]]", "Option[Buf[F32]]", true, false, false, false, false),
    arg("Span[F32]", "Span[F32]", false, false, false, false, false),
    arg("I32", "I32", true, true, true, true, true),
    arg("Bool", "Bool", true, true, true, true, false),
    arg("Str", "Str", true, true, false, true, false),
];

/// A type parameter has the implicit `Dup` unless `?Dup`, `Eq` only when it says so, and no `Copy` or `Num`.
const PARAM_ARGS: &[Arg] = &[
    type_param("U", "U", true, false),
    type_param("U: ?Dup", "U: ?Dup", false, false),
    type_param("U: ?Dup + Eq", "U: ?Dup + Eq", false, true),
];

#[derive(Clone, Copy, PartialEq, Debug)]
enum Place {
    /// `fn f(x: N[A])`.
    Signature,
    /// `struct M { n: N[A] }`.
    Field,
    /// `type Al = N[A]`, and `fn u(x: Al)` that uses it.
    Alias,
    /// `let _: Option[N[A]] = None` in a body.
    Annotation,
    /// `N::[A].K` in a body.
    BodyConst,
    /// `[F32; N::[A].K]` in a type.
    TypeConst,
    /// `mk(b)` for a `b: A`.
    Value,
    /// `impl[U…] N[U]`.
    Heading,
    /// `fn f[U…](x: N[U])`.
    SignatureParam,
    /// `fn g[U…](x: U)` that calls `mk(x)`.
    ValueParam,
}

impl Place {
    fn is_value(self) -> bool {
        matches!(self, Place::Value | Place::ValueParam)
    }
}

const PLACES: [Place; 7] =
    [Place::Signature, Place::Field, Place::Alias, Place::Annotation, Place::BodyConst, Place::TypeConst, Place::Value];

const PARAM_PLACES: [Place; 3] = [Place::Heading, Place::SignatureParam, Place::ValueParam];

/// The first requirement the argument does not meet, in the order of §4.5: the implicit `Escape`, the implicit
/// `Dup`, the bound. The second-class argument given to `?Escape` is taken to meet the kind requirements (§4.5).
fn unmet(p: &Param, a: &Arg) -> Option<&'static str> {
    if p.escape && !a.first_class {
        return Some("Escape");
    }
    if p.dup && a.first_class && !a.dup {
        return Some("Dup");
    }
    bound_unmet(p, a)
}

/// The bound written, alone.
fn bound_unmet(p: &Param, a: &Arg) -> Option<&'static str> {
    match p.bound {
        Bound::Eq if !a.eq => Some("Eq"),
        Bound::Copy if !a.copy => Some("Copy"),
        Bound::Num if !a.num => Some("Num"),
        _ => None,
    }
}

/// The argument fails the implicit `Dup` and the bound written together: the cell that §4.5 (S-1013 (i)) moves
/// from the bound, which a type written reports today, to the implicit `Dup`, which a value use reports.
fn dup_and_bound_unmet(p: &Param, a: &Arg) -> bool {
    unmet(p, a) == Some("Dup") && bound_unmet(p, a).is_some()
}

/// S-1021: the first requirement is the implicit `Dup` although the bound written asks for `Dup` itself.
fn depends_on_s1021(p: &Param, a: &Arg) -> bool {
    unmet(p, a) == Some("Dup") && matches!(p.bound, Bound::Copy | Bound::Num)
}

fn expected(p: &Param, a: &Arg) -> String {
    match unmet(p, a) {
        None => "no diagnostic".to_string(),
        Some("Escape") => "E0710 Escape".to_string(),
        Some(need) => format!("E0416 {need}"),
    }
}

// ---- the programs ------------------------------------------------------------------------------

const HEAD: &str = "pub struct B {\n  b: Buf[F32],\n}\n\n";
const N_DECL: &str = "pub struct N[@P] {\n  @FIELD,\n}\n\n";
const IMPL_K: &str = "impl[@P] N[T] {\n  pub const K: U32 = 1\n}\n\n";
const MK: &str = "fn mk[@P](x: T) -> U32 {\n  0\n}\n\n";

/// The program of one cell: only the place gives the diagnostic (one error per unit, §18.1, and one unit that
/// fails at most). A `T: ?Escape` parameter cannot be a field (§4.5), so its struct holds a function.
fn source(p: &Param, a: &Arg, place: Place) -> String {
    let field = if p.escape { "a: T" } else { "f: fn(T) -> F32" };
    let n = N_DECL.replace("@P", p.decl).replace("@FIELD", field);
    let impl_k = IMPL_K.replace("@P", p.decl);
    let mk = MK.replace("@P", p.decl);
    let ty = a.ty;
    let tail = match place {
        Place::Signature => format!("{n}pub fn f(x: N[{ty}]) -> U32 {{\n  0\n}}\n"),
        Place::Field => format!("{n}pub struct M {{\n  n: N[{ty}],\n}}\n"),
        Place::Alias => format!("{n}pub type Al = N[{ty}]\n\npub fn u(x: Al) -> U32 {{\n  0\n}}\n"),
        Place::Annotation => format!("{n}pub fn f() -> U32 {{\n  let _: Option[N[{ty}]] = None\n  0\n}}\n"),
        Place::BodyConst => format!("{n}{impl_k}pub fn f() -> U32 {{\n  N::[{ty}].K\n}}\n"),
        Place::TypeConst => format!("{n}{impl_k}pub fn f(x: [F32; N::[{ty}].K]) -> U32 {{\n  0\n}}\n"),
        Place::Value => format!("{mk}pub fn g(b: {ty}) -> U32 {{\n  mk(b)\n}}\n"),
        Place::Heading => {
            let u = a.declares;
            format!("{n}impl[{u}] N[U] {{\n  pub fn k(self) -> U32 {{\n    0\n  }}\n}}\n")
        }
        Place::SignatureParam => {
            let u = a.declares;
            format!("{n}pub fn f[{u}](x: N[U]) -> U32 {{\n  0\n}}\n")
        }
        Place::ValueParam => {
            let u = a.declares;
            format!("{mk}pub fn g[{u}](x: U) -> U32 {{\n  mk(x)\n}}\n")
        }
    };
    format!("{HEAD}{tail}")
}

/// What the check said, in the words of `expected`: the code and what the message names (`E0416 Dup`).
fn said(c: &Checked) -> String {
    said_with(c, "T")
}

struct Seen {
    param: &'static Param,
    arg: &'static Arg,
    place: Place,
    want: String,
    got: String,
}

impl Seen {
    fn label(&self) -> String {
        format!(
            "[{}] x [{}] at {:?}: want {}, got {}",
            self.param.decl, self.arg.label, self.place, self.want, self.got
        )
    }
}

/// Every cell, checked once for the tests of this file.
fn grid() -> &'static Vec<Seen> {
    static GRID: OnceLock<Vec<Seen>> = OnceLock::new();
    GRID.get_or_init(|| {
        let mut seen = Vec::new();
        for param in PARAMS {
            for (args, places) in [(ARGS, &PLACES[..]), (PARAM_ARGS, &PARAM_PLACES[..])] {
                for arg in args {
                    for &place in places {
                        let got = said(&check_file("main.onsa", &source(param, arg, place)));
                        seen.push(Seen { param, arg, place, want: expected(param, arg), got });
                    }
                }
            }
        }
        seen
    })
}

fn report(what: &str, failed: &[&Seen]) -> String {
    let mut text = format!("{what}: {} cell(s) differ from §4.5\n", failed.len());
    for s in failed.iter().take(40) {
        text.push_str(&format!("  {}\n", s.label()));
    }
    text
}

/// The cells of `grid()` that satisfy `keep` and that differ from the order of §4.5.
fn differing(keep: impl Fn(&Seen) -> bool) -> Vec<&'static Seen> {
    grid().iter().filter(|s| keep(s) && s.want != s.got).collect()
}

// ---- tests -------------------------------------------------------------------------------------

#[test]
fn the_grid_has_every_kind_of_answer() {
    // The oracle must not agree with a command that says nothing for want of cells.
    let cells = grid().len();
    let per_param = ARGS.len() * PLACES.len() + PARAM_ARGS.len() * PARAM_PLACES.len();
    assert_eq!(cells, PARAMS.len() * per_param, "the number of cells");
    for kind in ["no diagnostic", "E0710 Escape", "E0416 Dup", "E0416 Eq", "E0416 Copy", "E0416 Num"] {
        let n = grid().iter().filter(|s| s.want == kind).count();
        assert!(n >= 10, "the grid has {n} cells that want `{kind}`");
    }
}

#[test]
fn a_value_use_names_the_first_unmet_requirement() {
    // Settled (§4.5, S-862): `mk(b)` with a `b: A` for each parameter and argument, and for an argument that is a
    // type parameter of the function. The value use does this today; it is the side that the type written has to
    // agree with.
    let failed = differing(|s| s.place.is_value() && !depends_on_s1021(s.param, s.arg));
    assert!(failed.is_empty(), "{}", report("a value use", &failed));
}

#[test]
fn s1021_a_value_use_names_the_implicit_dup_first_for_a_bound_that_needs_dup() {
    // S-1021 (OPEN), provisional reading (1): `T: Copy` and `T: Num` with an argument that is not `Dup` (`Buf[F32]`,
    // an Affine struct, `Option[Buf[F32]]`, and `U: ?Dup`, `U: ?Dup + Eq`) report `T: Dup` as §4.5 lists the
    // requirements: the implicit `Dup` before the bound written. The value use does so today. If S-1021 is decided
    // as (3) the bound is reported instead, here and in the type written, and these cells change together.
    let cells: Vec<&Seen> = grid().iter().filter(|s| s.place.is_value() && depends_on_s1021(s.param, s.arg)).collect();
    assert_eq!(cells.len(), 2 * (3 + 2), "the number of S-1021 value uses");
    let failed: Vec<&Seen> = cells.into_iter().filter(|s| s.want != s.got).collect();
    assert!(failed.is_empty(), "{}", report("the S-1021 value uses", &failed));
}

#[test]
fn a_type_written_names_the_first_unmet_requirement_where_the_bound_is_not_also_unmet() {
    // Settled (§4.5) and right today: the six places and the three of a type parameter as the argument, for every
    // cell but those that fail the implicit `Dup` and the bound written together (the next test).
    let failed = differing(|s| !s.place.is_value() && !dup_and_bound_unmet(s.param, s.arg));
    assert!(failed.is_empty(), "{}", report("a type written", &failed));
}

#[test]
#[ignore = "W5-13 U5b: S-1013 (i), a type written names the implicit Dup before the bound written (E0416 names the bound today)"]
fn a_type_written_names_the_implicit_dup_before_a_bound_written() {
    // S-1013 (i): the cells that fail the implicit `Dup` and the bound written together (`T: Eq` and a `Buf[F32]`,
    // `T: ?Escape + Eq` and an Affine struct, `T: Eq` and `U: ?Dup`) have to name `Dup`, as a value use does; a type
    // written names the bound today. Without the cells that S-1021 moves (the next test).
    let cells: Vec<&Seen> =
        grid().iter().filter(|s| !s.place.is_value() && dup_and_bound_unmet(s.param, s.arg)).collect();
    assert!(!cells.is_empty(), "no cell");
    let failed =
        differing(|s| !s.place.is_value() && dup_and_bound_unmet(s.param, s.arg) && !depends_on_s1021(s.param, s.arg));
    assert!(failed.is_empty(), "{}", report("a type written", &failed));
}

#[test]
#[ignore = "W5-13 U5b: S-1013 (i) with S-1021 provisional (1), a type written names the implicit Dup before a bound that needs Dup"]
fn s1021_a_type_written_names_the_implicit_dup_first_for_a_bound_that_needs_dup() {
    // S-1021 (OPEN), provisional reading (1): as the value use above, in the six places and the two of a type
    // parameter as the argument (`impl` heading and signature).
    let cells: Vec<&Seen> = grid().iter().filter(|s| !s.place.is_value() && depends_on_s1021(s.param, s.arg)).collect();
    assert_eq!(cells.len(), 2 * (3 * 6 + 2 * 2), "the number of S-1021 cells of a type written");
    let failed: Vec<&Seen> = cells.into_iter().filter(|s| s.want != s.got).collect();
    assert!(failed.is_empty(), "{}", report("the S-1021 cells", &failed));
}

#[test]
#[ignore = "W5-13 U5b: S-1013 (i), a type written and a value use name the same requirement"]
fn a_type_written_and_a_value_use_name_the_same_requirement() {
    // The property of S-1013 itself, with no oracle: for a parameter and an argument the places of a type written
    // and the value use give one answer. It holds for the S-1021 cells too, whichever way S-1021 is read.
    let mut failed = Vec::new();
    for s in grid().iter().filter(|s| !s.place.is_value()) {
        let value = grid()
            .iter()
            .find(|v| v.place.is_value() && std::ptr::eq(v.param, s.param) && v.arg.label == s.arg.label)
            .expect("the value use of the same parameter and argument");
        if value.got != s.got {
            failed.push(format!(
                "[{}] x [{}]: {:?} says {}, the value use says {}",
                s.param.decl, s.arg.label, s.place, s.got, value.got
            ));
        }
    }
    assert!(failed.is_empty(), "{} place(s) differ from the value use:\n  {}", failed.len(), failed.join("\n  "));
}

// ---- S-1020: two type arguments that each fail ---------------------------------------------------

const TWO: &str = "pub struct P[A, B: @BOUND] {\n  a: A,\n  b: B,\n}\n\n";
const TWO_MK: &str = "fn mk[A, B: @BOUND](x: A, y: B) -> U32 {\n  0\n}\n\n";

fn two_written(bound: &str, second: &str) -> Checked {
    let src = TWO.replace("@BOUND", bound) + &format!("pub fn f(x: P[Span[F32], {second}]) -> U32 {{\n  0\n}}\n");
    check_file("main.onsa", &src)
}

fn two_value(bound: &str, second: &str) -> Checked {
    let src =
        TWO_MK.replace("@BOUND", bound) + &format!("pub fn g(s: Span[F32], b: {second}) -> U32 {{\n  mk(s, b)\n}}\n");
    check_file("main.onsa", &src)
}

#[test]
fn s1020_the_type_written_reports_the_outer_requirement_before_a_second_class_argument_before_it() {
    // S-1020 (OPEN), provisional reading (2): `P[Span[F32], Bool]` with `P[A, B: Num]`: the first argument is
    // second-class for `A` (E0710) and the second fails `B: Num` (E0416). The type written reports the
    // requirement of the outer type first, so E0416 and no E0710 (the value use `mk(s, b)` reports the first
    // argument: E0710). The reading (1) would make the type written E0710 too.
    let written = two_written("Num", "Bool");
    assert_eq!(said_with(&written, "B"), "E0416 Num", "the type written");
    let value = two_value("Num", "Bool");
    assert_eq!(said(&value), "E0710 Escape", "the value use");
}

#[test]
#[ignore = "W5-13 U5b: S-1013 (i) with S-1020 provisional (2), the second argument names the implicit Dup"]
fn s1020_with_the_implicit_dup_of_the_second_argument() {
    // The same with a second argument `Buf[F32]` that also fails the implicit `Dup` (S-1013 (i): the implicit
    // `Dup` is named before the bound `B: Eq`), and S-1020 (2): E0416 and no E0710 for the first argument.
    let written = two_written("Eq", "Buf[F32]");
    assert_eq!(said_with(&written, "B"), "E0416 Dup", "the type written");
    let value = two_value("Eq", "Buf[F32]");
    assert_eq!(said(&value), "E0710 Escape", "the value use");
}

/// `said` for a parameter named `name` (`A`, `B`) instead of `T`.
fn said_with(c: &Checked, name: &str) -> String {
    if !ended_well(c) {
        return format!("the command did not end well: {}", c.stderr);
    }
    let prefix = format!("{name}: ");
    let names: Vec<String> = c
        .diags
        .iter()
        .map(|d| match d.code.as_str() {
            "E0710" => "E0710 Escape".to_string(),
            "E0416" => {
                let need = quoted(&d.message).into_iter().find_map(|q| q.strip_prefix(&prefix).map(str::to_string));
                format!("E0416 {}", need.unwrap_or_else(|| format!("(no `{prefix}…` in: {})", d.message)))
            }
            other => format!("{other} ({})", d.message),
        })
        .collect();
    if names.is_empty() { "no diagnostic".to_string() } else { names.join("; ") }
}
