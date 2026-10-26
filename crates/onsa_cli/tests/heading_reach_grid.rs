//! The names in the head of a declaration against how far it reaches, over types that are built up (aliases
//! of aliases, a type in a type, generic structs) and members of an `impl` that are wider than their type
//! (spec §15.1, §4.4; S-662, S-665, S-698, S-699, S-700; W4-03 U4b). The sweep moved here from the grid of
//! the break side (`grid2.py`) that found, after U4b, that a `pub fn` which names an alias was judged by
//! the word of the alias and not by the type it stands for, which the gate had passed.
//!
//! The oracle is written here from the rule, not from the script (`Ty::narrowest`, `expect`):
//! - §15.1 (S-665): a name written in the head of a declaration cannot be narrower than what the declaration
//!   reaches: E0303, no candidate. A declaration reaches as far as its word (`pub` > none > `priv`); a
//!   `priv` field only the module; a member of an `impl` as far as the narrower of itself and its type;
//! - §15.1, §4.4 (S-700): an alias makes no new type and is judged by the types it stands for, whatever its
//!   own word; a generic struct is as narrow as the narrower of itself and its argument; `Option`, an array,
//!   a tuple and a function type are as narrow as the narrowest type in them. The right side of an alias is
//!   judged at the reach of the alias, so the aliases of the support are written with a word no wider than
//!   what they stand for (and the declaration `type D = …` of a case is where a wide word is E0303);
//! - §15.1 (S-662, S-698): a `pub` on a member of an `impl` of a type that is not `pub` is E0020, one
//!   candidate that takes the word off; the unit is read no further, so the narrow name in the same member
//!   has no E0303 (it comes when the candidate is applied, which `candidate_headings.rs` looks at);
//! - §15.1 (S-699): the name of a constant in an array length or a constant argument is not a name of the
//!   head.
//!
//! The grid of `heading_names.rs` is every place against every shape of one type; this one draws, from a
//! fixed seed, a pool of types of three kinds of struct and thirty built-up types and aliases, and 70
//! declarations of the places and the words each, in three packages (three seeds, one file each: the
//! declarations are units of their own, §18.1). Not asked: the text of a message, the end of a span.

mod test_support;

use test_support::sweep::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Vis {
    Priv,
    Pkg,
    Pub,
}

const VISES: [Vis; 3] = [Vis::Priv, Vis::Pkg, Vis::Pub];

impl Vis {
    fn rank(self) -> u8 {
        self as u8
    }

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

    fn narrower(self, o: Vis) -> Vis {
        if self.rank() <= o.rank() { self } else { o }
    }
}

/// A type of the head, built up from the three structs `SPriv`, `SPkg`, `SPub` and the generic structs
/// `GPriv`, `GPkg`, `GPub`.
#[derive(Clone)]
enum Ty {
    Plain(Vis),
    Option(Box<Ty>),
    Array(Box<Ty>),
    Tuple(Box<Ty>, Box<Ty>),
    Fn(Box<Ty>),
    Generic(Vis, Box<Ty>),
    /// The alias `Al<n>` and the type it stands for.
    Alias(usize, Box<Ty>),
}

impl Ty {
    fn text(&self) -> String {
        match self {
            Ty::Plain(v) => format!("S{}", v.tag()),
            Ty::Option(t) => format!("Option[{}]", t.text()),
            Ty::Array(t) => format!("[{}; 2]", t.text()),
            Ty::Tuple(a, b) => format!("({}, {})", a.text(), b.text()),
            Ty::Fn(t) => format!("fn({}) -> I32", t.text()),
            Ty::Generic(v, t) => format!("G{}[{}]", v.tag(), t.text()),
            Ty::Alias(n, _) => format!("Al{n}"),
        }
    }

    /// How far the narrowest name in the type reaches (S-700: an alias by what it stands for).
    fn narrowest(&self) -> Vis {
        match self {
            Ty::Plain(v) => *v,
            Ty::Option(t) | Ty::Array(t) | Ty::Fn(t) | Ty::Alias(_, t) => t.narrowest(),
            Ty::Tuple(a, b) => a.narrowest().narrower(b.narrowest()),
            Ty::Generic(v, t) => v.narrower(t.narrowest()),
        }
    }

    /// A value of the type, when the sweep can write one.
    fn value(&self) -> Option<String> {
        match self {
            Ty::Plain(v) => Some(format!("S{} {{ x: 1 }}", v.tag())),
            Ty::Option(_) => Some("None".to_string()),
            Ty::Array(t) => t.value().map(|v| format!("[{v}, {v}]")),
            Ty::Tuple(a, b) => Some(format!("({}, {})", a.value()?, b.value()?)),
            Ty::Fn(_) => None,
            Ty::Generic(v, t) => t.value().map(|x| format!("G{} {{ v: {x} }}", v.tag())),
            Ty::Alias(_, t) => t.value(),
        }
    }

    fn depth(&self) -> usize {
        match self {
            Ty::Plain(_) | Ty::Alias(..) => 1,
            Ty::Option(t) | Ty::Array(t) | Ty::Fn(t) | Ty::Generic(_, t) => 1 + t.depth(),
            Ty::Tuple(a, b) => 1 + a.depth().max(b.depth()),
        }
    }
}

/// The support of a file (the structs and the aliases) and the pool of types that the aliases and the
/// plain ones make up.
fn pool(rng: &mut Rng) -> (Vec<String>, Vec<Ty>) {
    let mut lines = Vec::new();
    let mut pool = Vec::new();
    for v in VISES {
        lines.push(format!("{}struct S{} {{ x: I32 }}", v.word(), v.tag()));
        lines.push(format!("{}struct G{}[T] {{ v: T }}", v.word(), v.tag()));
        pool.push(Ty::Plain(v));
    }
    let mut aliases = 0;
    while pool.len() < 36 {
        let a = Box::new(rng.pick(&pool).clone());
        let b = Box::new(rng.pick(&pool).clone());
        let t = match rng.below(8) {
            0 => Ty::Option(a),
            1 => Ty::Array(a),
            2 => Ty::Tuple(a, b),
            3 => Ty::Fn(a),
            4 | 5 => Ty::Generic(*rng.pick(&VISES), a),
            _ => {
                // An alias whose word is no wider than what it stands for (its right side is judged there).
                let reach = a.narrowest();
                let words: Vec<Vis> = VISES.iter().copied().filter(|v| v.rank() <= reach.rank()).collect();
                aliases += 1;
                lines.push(format!("{}type Al{aliases} = {}", rng.pick(&words).word(), a.text()));
                Ty::Alias(aliases, a)
            }
        };
        if t.depth() <= 4 {
            pool.push(t);
        }
    }
    (lines, pool)
}

/// The text of a type in the place of a flow input, where a function type needs its brackets.
fn flow_ty(t: &Ty) -> String {
    match t {
        Ty::Fn(_) => format!("({})", t.text()),
        _ => t.text(),
    }
}

struct Case {
    line: usize,
    what: String,
    e0303: bool,
    e0020: bool,
}

/// One package: the support, then 70 declarations drawn from the seed, each on a line of its own.
fn generate(seed: u64) -> (Vec<String>, Vec<Case>) {
    let mut rng = Rng::new(seed);
    let (mut lines, pool) = pool(&mut rng);
    let mut cases = Vec::new();
    let mut n = 0;
    while cases.len() < 70 {
        n += 1;
        let t = rng.pick(&pool).clone();
        let (ty, need) = (t.text(), t.narrowest());
        let dv = *rng.pick(&VISES);
        let w = dv.word();
        // (what, text, how far it reaches, an E0020 for the word)
        let (what, text, reach, e20) = match rng.below(11) {
            0 => ("fn argument", format!("{w}fn d{n}(a: {ty}) -> I32 {{ 0 }}"), dv, false),
            1 => ("rt fn argument", format!("{w}rt fn d{n}(a: {ty}) -> I32 {{ 0 }}"), dv, false),
            2 => match t.value() {
                Some(v) => ("fn return", format!("{w}fn d{n}() -> {ty} {{ {v} }}"), dv, false),
                None => continue,
            },
            3 => ("alias", format!("{w}type D{n} = {ty}"), dv, false),
            4 => match t.value() {
                Some(v) => ("const", format!("{w}const D{n}: {ty} = {v}"), dv, false),
                None => continue,
            },
            5 => ("field", format!("{w}struct D{n} {{ f: {ty} }}"), dv, false),
            6 => ("priv field", format!("{w}struct D{n} {{ priv f: {ty} }}"), Vis::Priv, false),
            7 => ("variant", format!("{w}enum D{n} {{ A({ty}) }}"), dv, false),
            8 => (
                "flow block input",
                format!("{w}flow d{n}(x: F32 at sample, g: {} at block) -> F32 at sample {{ x }}", flow_ty(&t)),
                dv,
                false,
            ),
            9 => (
                "flow init input",
                format!("{w}flow d{n}(x: F32 at sample, g: {} at init) -> F32 at sample {{ x }}", flow_ty(&t)),
                dv,
                false,
            ),
            _ => {
                // A member of an `impl`: as far as the narrower of the member and the type of the impl.
                let (tv, mv) = (*rng.pick(&VISES), *rng.pick(&VISES));
                lines.push(format!("{}struct H{n} {{ x: I32 }}", tv.word()));
                let (kind, member) = if rng.chance(50) || t.value().is_none() {
                    ("impl fn", format!("{}fn m(a: {ty}) -> I32 {{ 0 }}", mv.word()))
                } else {
                    ("impl const", format!("{}const K: {ty} = {}", mv.word(), t.value().unwrap()))
                };
                (kind, format!("impl H{n} {{ {member} }}"), mv.narrower(tv), mv == Vis::Pub && tv != Vis::Pub)
            }
        };
        lines.push(text);
        cases.push(Case {
            line: lines.len(),
            what: format!("{what} (reach {reach:?}, narrowest {need:?})"),
            e0303: !e20 && need.rank() < reach.rank(),
            e0020: e20,
        });
    }
    (lines, cases)
}

/// §15.1, §4.4 (S-662, S-665, S-698, S-700): in each package, each declaration has the E0303 when the
/// narrowest name in its head is narrower than its reach, the E0020 when a member is wider than its type
/// (and then no E0303), and nothing else; the support has nothing; the E0303 has no candidate and the E0020
/// the one.
fn sweep(seed: u64, problems: &mut Vec<String>) -> (usize, usize, usize) {
    let (lines, cases) = generate(seed);
    let texts = Texts::from([("m.onsa".to_string(), lines.join("\n") + "\n")]);
    let d = package("heading_grid", "demo", &texts);
    let c = check_package(d.root());
    assert!(ended_well(&c), "seed {seed}: code {} {}", c.code, c.stderr);
    let case_lines: std::collections::BTreeSet<usize> = cases.iter().map(|c| c.line).collect();
    for x in &c.diags {
        let line = x.line as usize;
        if !case_lines.contains(&line) || !(x.code == "E0303" || x.code == "E0020") {
            problems.push(format!(
                "seed {seed}: {} on line {line}, which has no such case: {}\n    {}",
                x.code,
                x.message,
                lines[line - 1]
            ));
        } else if (x.code == "E0303" && !x.fixes.is_empty()) || (x.code == "E0020" && x.fixes.len() != 1) {
            problems.push(format!("seed {seed}: {} on line {line} has {} candidates", x.code, x.fixes.len()));
        }
    }
    for case in &cases {
        let on_line = |code: &str| c.diags.iter().filter(|x| x.line as usize == case.line && x.code == code).count();
        let (got303, got20) = (on_line("E0303"), on_line("E0020"));
        if got303 != usize::from(case.e0303) || got20 != usize::from(case.e0020) {
            problems.push(format!(
                "seed {seed}: line {}: {}: E0303 {got303} (want {}), E0020 {got20} (want {})\n    {}",
                case.line,
                case.what,
                case.e0303,
                case.e0020,
                lines[case.line - 1]
            ));
        }
    }
    assert_eq!(c.code == 0, c.diags.is_empty(), "seed {seed}: exit code {} and {} diagnostics", c.code, c.diags.len());
    (
        cases.iter().filter(|c| c.e0303).count(),
        cases.iter().filter(|c| c.e0020).count(),
        cases.iter().filter(|c| !c.e0303 && !c.e0020).count(),
    )
}

#[test]
fn built_up_types_and_wide_members_have_the_errors_the_rule_gives_and_no_others() {
    let (mut narrow, mut wide, mut fine) = (0, 0, 0);
    let mut problems = Vec::new();
    for seed in [0x6F1, 0x6F2, 0x6F3] {
        let (a, b, c) = sweep(seed, &mut problems);
        narrow += a;
        wide += b;
        fine += c;
    }
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
    // The sample must have all three kinds of subject.
    assert!(narrow >= 20 && wide >= 5 && fine >= 20, "narrow {narrow}, wide {wide}, fine {fine}");
}

/// §15.1 (S-699): the name of a constant in the length of an array or in a constant argument is not a name
/// of the head: a `pub` declaration that names a `priv` constant there has no E0303, and a narrow type next
/// to it still has.
#[test]
fn the_constant_in_a_length_is_no_name_of_the_head() {
    let text = "priv const N: U32 = 2\n\
                const M: U32 = 3\n\
                priv struct Hid { x: I32 }\n\
                pub fn a(v: [I32; N]) -> I32 { 0 }\n\
                pub type Row = [I32; M]\n\
                pub struct Ring[T, const K: U32] { v: [T; K] }\n\
                pub fn b(r: Ring[I32, N]) -> I32 { 0 }\n\
                pub fn c(v: [Hid; N]) -> I32 { 0 }\n";
    let d = package("heading_len", "demo", &Texts::from([("m.onsa".to_string(), text.to_string())]));
    let c = check_package(d.root());
    assert!(ended_well(&c), "{} {}", c.code, c.stderr);
    let got: Vec<(&str, u64)> = c.diags.iter().map(|x| (x.code.as_str(), x.line)).collect();
    assert_eq!(got, [("E0303", 8)], "{:?}", c.diags);
}
