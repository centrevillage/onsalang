//! A drawn sweep of the sameness of a type written and the same type named by an alias (spec §4.4: "元の型と
//! 同じに使える", and its item of the errors of the right side, S-757; §4.5, §5.3, §18.1; W4-05 U4a/i2).
//!
//! For each drawn type `t` (depth 3, a fixed seed) and a drawn wrapper `w` (`W[_]`, `Option[_]`, …), one
//! file has the aliases `type Z = t` and `type Y = w[Z]` and five functions, each one line and one unit:
//! `a(p: t)`, `b(p: Z)`, `c(p: w[t])`, `d(p: Y)` and `e(p: w[Z])`, each with the same mode of `p` and the
//! body `{ p }` against `-> U32`. The body shows the type `p` is read as, in the message of its E0401 (or
//! none where it is the error type). What the spec fixes, and the model uses:
//! - An alias with an error of its right side (E0416, §4.5) has it at its declaration and is the error type:
//!   the places that name it are silent (§4.4, S-757). So when `Z` has a diagnostic, `b` has none and `a`
//!   has one (the same error, written there), and `Y` has none (`w[Z]` holds the error type, which meets
//!   every requirement, §18.1); when `Y` has one, `d` has none and `e` has one.
//! - Otherwise an alias is the same as its right side, where it is named (§4.4): `b` has the diagnostics of
//!   `a`, `d` those of `e`, and `e` those of `c`, by line and code, and the E0401 of the body by its message
//!   too (the type `p` is read as). Whether a second-class part stands in its place is judged where the alias
//!   is named (§4.4, §5.3), so `move p: Z` with `Z = Span[F32]` is the E0710 of `move p: Span[F32]`. The
//!   messages of a signature are not compared: they show the type written, with an alias with an error in it
//!   as written (`Span[N[Bool]]`) or as read (`Span[_]`), which the spec does not fix.
//!
//! The leaves have aliases of their own (`SpA`, `Pl`, `WS`) and aliases with an error (`Bad`, `BadBuf`), so
//! an alias inside an alias, written and named, is drawn too. The seed is fixed; a failing run prints every
//! mismatch with its lines.

mod test_support;

use std::collections::BTreeMap;

use test_support::sweep::{Rng, Texts, check_package, ended_well, package};

const HEAD: &str = "\
pub struct W[T] { a: T }
pub struct N[T: Num] { a: T }
pub struct C[T: Copy] { a: T }
pub struct D[T: ?Dup] { a: T }
pub struct F[T: Float] { a: T }
pub struct P { a: F32 }
pub struct R { s: Str }
pub struct Q { b: Buf[F32] }
type SpA = Span[F32]
type Pl = [Span[F32]; 2]
type WS = W[Str]
type Bad = N[Bool] @@
type BadBuf = Buf[Str] @@
pub fn main() {}
";

const LEAVES: &[&str] = &["F32", "I32", "Bool", "Str", "P", "R", "Q", "SpA", "Pl", "WS", "Bad", "BadBuf"];

/// The constructors and their counts of arguments; `Fn` is a function type, `Tup` a pair, `Arr` `[_; 2]`.
const CTORS: &[(&str, usize)] = &[
    ("W", 1),
    ("N", 1),
    ("C", 1),
    ("D", 1),
    ("F", 1),
    ("Option", 1),
    ("Result", 2),
    ("Tup", 2),
    ("Arr", 1),
    ("Buf", 1),
    ("Span", 1),
    ("Array", 1),
    ("Set", 1),
    ("Map", 2),
    ("Ptr", 1),
    ("Fn", 2),
];

const MODES: &[&str] = &["", "", "inout ", "move "];

const WRAPS: &[&str] = &["W[{}]", "Option[{}]", "({}, F32)", "[{}; 2]", "Array[{}]", "Buf[{}]", "fn({}) -> F32"];

fn draw(r: &mut Rng, depth: usize) -> String {
    if depth == 0 || r.chance(30) {
        return r.pick(LEAVES).to_string();
    }
    let &(c, n) = r.pick(CTORS);
    let args: Vec<String> = (0..n).map(|_| draw(r, depth - 1)).collect();
    match c {
        "Fn" => format!("fn({}{}) -> {}", r.pick(MODES), args[0], args[1]),
        "Tup" => format!("({}, {})", args[0], args[1]),
        "Arr" => format!("[{}; 2]", args[0]),
        _ => format!("{c}[{}]", args.join(", ")),
    }
}

/// The diagnostics of each line, as their codes, with the message of an E0401.
type ByLine = BTreeMap<u64, Vec<String>>;

#[test]
fn an_alias_is_the_type_it_names_and_an_alias_with_an_error_is_silent_where_named() {
    const CASES: usize = 300;
    let mut r = Rng::new(0x5757_0405);
    let mut text = HEAD.to_string();
    let mut lines = Vec::new();
    for i in 0..CASES {
        let (t, m, w) = (draw(&mut r, 3), *r.pick(MODES), *r.pick(WRAPS));
        let first = text.lines().count() as u64 + 1;
        let f = |name: &str, ty: &str| format!("pub fn {name}{i}({m}p: {ty}) -> U32 {{ p }}\n");
        text.push_str(&format!("type Z{i} = {t}\ntype Y{i} = {}\n", w.replace("{}", &format!("Z{i}"))));
        text.push_str(&f("a", &t));
        text.push_str(&f("b", &format!("Z{i}")));
        text.push_str(&f("c", &w.replace("{}", &t)));
        text.push_str(&f("d", &format!("Y{i}")));
        text.push_str(&f("e", &w.replace("{}", &format!("Z{i}"))));
        lines.push(first);
    }
    // The aliases with an error of the head are marked `@@`.
    let marked: Vec<u64> = (1..).zip(text.lines()).filter(|(_, l)| l.ends_with(" @@")).map(|(n, _)| n).collect();
    let text = text.replace(" @@\n", "\n");
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), text.clone());
    let d = package("alias_sameness", "demo", &texts);
    let checked = check_package(d.root());
    assert!(ended_well(&checked), "check did not end as a check does:\n{}", checked.stderr);
    let mut got = ByLine::new();
    for x in &checked.diags {
        let message = if x.code == "E0401" { x.message.as_str() } else { "" };
        got.entry(x.line).or_default().push(format!("{} {message}", x.code));
    }
    let at = |n: u64| got.get(&n).cloned().unwrap_or_default();
    let mut bad = Vec::new();
    for n in marked {
        if at(n).is_empty() {
            bad.push(format!("line {n}: the alias with an error has no diagnostic"));
        }
    }
    let mut decl_errors = 0;
    for (i, &z) in lines.iter().enumerate() {
        let [y, a, b, c, d, e] = [z + 1, z + 2, z + 3, z + 4, z + 5, z + 6];
        let mut want = |ok: bool, what: &str| {
            if !ok {
                let show = |n: u64| format!("  {}\n    {:?}", text.lines().nth(n as usize - 1).unwrap(), at(n));
                let all: Vec<String> = [z, y, a, b, c, d, e].into_iter().map(show).collect();
                bad.push(format!("case {i}: {what}\n{}", all.join("\n")));
            }
        };
        if at(z).is_empty() {
            want(at(b) == at(a), "`b(p: Z)` is not `a(p: t)`");
            want(at(e) == at(c), "`e(p: w[Z])` is not `c(p: w[t])`");
        } else {
            decl_errors += 1;
            want(at(b).is_empty() && !at(a).is_empty(), "`Z` has an error: `b` is not silent or `a` is");
            want(at(y).is_empty(), "`Z` has an error: `Y = w[Z]` is not silent");
        }
        if at(y).is_empty() {
            want(at(d) == at(e), "`d(p: Y)` is not `e(p: w[Z])`");
        } else {
            want(at(d).is_empty() && !at(e).is_empty(), "`Y` has an error: `d` is not silent or `e` is");
        }
    }
    // The draw makes both sides of each rule: aliases with an error and without.
    assert!((CASES / 10..CASES * 9 / 10).contains(&decl_errors), "{decl_errors} of {CASES} aliases have an error");
    assert!(bad.is_empty(), "{} mismatches:\n{}", bad.len(), bad.join("\n"));
}
