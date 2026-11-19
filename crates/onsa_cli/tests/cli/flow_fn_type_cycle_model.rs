//! A drawn sweep of the declarations that hold a function type, through cycles, against the least fixed point of the spec
//! (§11.3, S-372, S-1151; W7-14 U6b/t, from the sweep of the break side of U6, `gen_cycle.py`).
//!
//! §11.3: "入出力の値型と、本体の式（部分式を含む）の型は…関数型を含まない（E0810）。含むかは型の構造で決め、配列とタプルの要素、
//! struct のフィールド（`priv` も）、enum の列挙子の要素、型引数、別名の中の関数型も含む". So a type holds a function type when it is one,
//! or an element of a tuple or an array, a field of a struct, an element of a variant, a type argument (a phantom one too: `Ph[T]` has no
//! field of `T`), or the right of an alias, that holds one; and a declaration that is read through itself (a cycle through the type arguments of
//! the phantom `Ph[T]`, the only way a declaration reads itself: a field of its own type is E0311) holds one when the least fixed point of the
//! table of the declarations says so.
//!
//! The generator draws 3 to 7 declarations (a struct, an enum or an alias each) of fields and variants of a function, a number, a tuple, an array,
//! an earlier declaration, `W[T]` (a field `T`), `Q[T]` (a field `Ph[T]`) and `Ph[T]`, whose argument may be any declaration (an alias only an earlier
//! one), so that the declarations read each other. The flows read a constant of each type asked (every declaration, and the wrappers `Ph`, a tuple, an
//! array, `W`, `Q` of three of them) in the body (as an argument of an `rt fn`, or in a `let _`) or as an input at `block`. The model says: a flow has
//! one E0810 when the type it reads holds a function type, and no diagnostic at all when it does not (so a type that holds none is never taken for one,
//! and one that does is never missed or told twice), for the declarations in the module of the flow and in another module (`use`). Fixed seeds, the
//! texts kept in memory (`check_input`, no file written: `rules/common.md` 3.7).

use crate::test_support;

use std::collections::BTreeMap;

use test_support::sweep::{Rng, Texts, check_input, ended_well, input_of};

#[derive(Clone, Debug)]
enum Ty {
    Fn,
    F32,
    Tuple(Vec<Ty>),
    Arr(Box<Ty>),
    /// A declaration of the package, by its place.
    Decl(usize),
    /// `Ph[T]`, `W[T]` or `Q[T]`: the name and the argument.
    Gen(&'static str, Box<Ty>),
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Struct,
    Enum,
    Alias,
}

/// The declarations: the kind and, for each, the types it is made of (the fields, the element of each variant, or the right of the alias).
struct Decls {
    kinds: Vec<Kind>,
    parts: Vec<Vec<Ty>>,
}

fn draw(rng: &mut Rng, d: &Decls, i: usize, depth: usize) -> Ty {
    let n = d.kinds.len();
    // Few functions and many edges and tuples, as the sweep of the break side of U6b (`gen_cycle3.py`): a declaration entered first that
    // rests on one entered after it, whose other field is a tuple of the first, is asked by a later flow (W7-14 U6c).
    let r = if depth > 2 { rng.below(40) } else { rng.below(100) };
    if r < 6 {
        Ty::Fn
    } else if r < 12 {
        Ty::F32
    } else if (12..38).contains(&r) && i > 0 {
        Ty::Decl(rng.below(i))
    } else if r < 72 {
        // An edge through the phantom: any declaration, an alias only an earlier one.
        let mut j = rng.below(n);
        if d.kinds[j] == Kind::Alias && j >= i {
            if i == 0 {
                return Ty::F32;
            }
            j = rng.below(i);
        }
        Ty::Gen("Ph", Box::new(Ty::Decl(j)))
    } else if r < 86 {
        Ty::Tuple(vec![draw(rng, d, i, depth + 1), draw(rng, d, i, depth + 1)])
    } else if r < 90 {
        Ty::Arr(Box::new(draw(rng, d, i, depth + 1)))
    } else if r < 94 {
        Ty::Gen("W", Box::new(draw(rng, d, i, depth + 1)))
    } else {
        Ty::Gen("Q", Box::new(draw(rng, d, i, depth + 1)))
    }
}

/// Whether each declaration holds a function type: the least fixed point of the table. With `phantom` false the type argument of `Ph[T]`
/// is left out (the table of what a declaration holds without the argument that no field of it reads).
fn table(d: &Decls, phantom: bool) -> Vec<bool> {
    let mut h = vec![false; d.kinds.len()];
    loop {
        let mut changed = false;
        for i in 0..h.len() {
            if !h[i] && d.parts[i].iter().any(|t| holds(t, &h, phantom)) {
                h[i] = true;
                changed = true;
            }
        }
        if !changed {
            return h;
        }
    }
}

fn holds(t: &Ty, h: &[bool], phantom: bool) -> bool {
    match t {
        Ty::Fn => true,
        Ty::F32 => false,
        Ty::Tuple(ts) => ts.iter().any(|t| holds(t, h, phantom)),
        Ty::Gen("Ph", _) if !phantom => false,
        Ty::Arr(t) | Ty::Gen(_, t) => holds(t, h, phantom),
        Ty::Decl(j) => h[*j],
    }
}

fn show(t: &Ty) -> String {
    match t {
        Ty::Fn => "rt fn(F32) -> F32".to_string(),
        Ty::F32 => "F32".to_string(),
        Ty::Tuple(ts) => format!("({})", ts.iter().map(show).collect::<Vec<_>>().join(", ")),
        Ty::Arr(t) => format!("[{}; 2]", show(t)),
        Ty::Decl(j) => format!("D{j}"),
        Ty::Gen(n, t) => format!("{n}[{}]", show(t)),
    }
}

/// A closed value of the type (the declarations read themselves only through `Ph`, so it ends).
fn value(t: &Ty, d: &Decls) -> String {
    match t {
        Ty::Fn => "dbl".to_string(),
        Ty::F32 => "1.0".to_string(),
        Ty::Tuple(ts) => format!("({})", ts.iter().map(|t| value(t, d)).collect::<Vec<_>>().join(", ")),
        Ty::Arr(t) => format!("[{}, {}]", value(t, d), value(t, d)),
        Ty::Gen("Ph", t) => format!("Ph::[{}] {{ n: 0.0 }}", show(t)),
        Ty::Gen("W", t) => format!("W::[{}] {{ t: {} }}", show(t), value(t, d)),
        Ty::Gen(_, t) => format!("Q::[{}] {{ p: Ph::[{}] {{ n: 0.0 }} }}", show(t), show(t)),
        Ty::Decl(j) => match d.kinds[*j] {
            Kind::Alias => value(&d.parts[*j][0], d),
            Kind::Enum => format!("D{j}.V0({})", value(&d.parts[*j][0], d)),
            Kind::Struct => {
                let fields: Vec<String> =
                    d.parts[*j].iter().enumerate().map(|(k, t)| format!("f{k}: {}", value(t, d))).collect();
                format!("D{j} {{ {} }}", fields.join(", "))
            }
        },
    }
}

fn declarations(d: &Decls) -> String {
    let mut out = String::from("pub rt fn dbl(x: F32) -> F32 {\n  x * 2.0\n}\n");
    for i in 0..d.kinds.len() {
        match d.kinds[i] {
            Kind::Alias => out.push_str(&format!("\npub type D{i} = {}\n", show(&d.parts[i][0]))),
            Kind::Struct => {
                out.push_str(&format!("\npub struct D{i} {{\n"));
                for (k, t) in d.parts[i].iter().enumerate() {
                    out.push_str(&format!("  f{k}: {},\n", show(t)));
                }
                out.push_str("}\n");
            }
            Kind::Enum => {
                out.push_str(&format!("\npub enum D{i} {{\n"));
                for (k, t) in d.parts[i].iter().enumerate() {
                    out.push_str(&format!("  V{k}({}),\n", show(t)));
                }
                out.push_str("}\n");
            }
        }
    }
    out.push_str(
        "\npub struct Ph[T] {\n  n: F32,\n}\n\npub struct W[T] {\n  t: T,\n}\n\npub struct Q[T] {\n  p: Ph[T],\n}\n",
    );
    out
}

/// One program: the declarations, the flows, whether each flow holds a function type in what it reads, and whether the declarations are in another module.
struct Program {
    texts: Texts,
    /// For each flow, `fl<k>`: whether its type holds a function type.
    expect: BTreeMap<String, bool>,
    /// How many declarations hold a function type only through the type argument of a `Ph` (a cycle, or a type that is read through it).
    through_phantom: usize,
    seed: u64,
}

fn program(seed: u64, modules: bool) -> Program {
    let mut rng = Rng::new(seed * 2 + modules as u64);
    let n = rng.range(3, 7);
    let mut d = Decls { kinds: Vec::new(), parts: vec![Vec::new(); n] };
    for _ in 0..n {
        d.kinds.push(*rng.pick(&[Kind::Struct, Kind::Struct, Kind::Enum, Kind::Alias]));
    }
    for i in 0..n {
        let count = match d.kinds[i] {
            Kind::Alias => 1,
            Kind::Struct => rng.range(1, 3),
            Kind::Enum => rng.range(1, 2),
        };
        let mut parts = Vec::new();
        for _ in 0..count {
            parts.push(draw(&mut rng, &d, i, 0));
        }
        d.parts[i] = parts;
    }
    // The types asked: every declaration, the wrappers of three of them, and each type a declaration is made of.
    let mut asked: Vec<Ty> = (0..n).map(Ty::Decl).collect();
    let mut order: Vec<usize> = (0..n).collect();
    rng.shuffle(&mut order);
    for &j in order.iter().take(3.min(n)) {
        let t = Ty::Decl(j);
        asked.push(Ty::Gen("Ph", Box::new(t.clone())));
        asked.push(Ty::Tuple(vec![Ty::F32, t.clone()]));
        asked.push(Ty::Arr(Box::new(t.clone())));
        asked.push(Ty::Gen("W", Box::new(t.clone())));
        asked.push(Ty::Gen("Q", Box::new(t)));
    }
    for t in d.parts.iter().flatten().filter(|t| !matches!(t, Ty::Fn | Ty::F32)) {
        if !asked.iter().any(|a| show(a) == show(t)) {
            asked.push(t.clone());
        }
    }
    rng.shuffle(&mut asked);
    let forms: Vec<usize> = asked.iter().map(|_| rng.below(4)).collect();
    package(&d, &asked, &forms, modules, seed)
}

/// The program of the declarations `d` whose flows `fl<k>` read the types `asked` in this order, each in its form: an input at `block` (0), a
/// `let _` (1) or an argument of an `rt fn` (2, 3).
fn package(d: &Decls, asked: &[Ty], forms: &[usize], modules: bool, seed: u64) -> Program {
    let h = table(d, true);
    let without = table(d, false);
    let through_phantom = h.iter().zip(&without).filter(|(a, b)| **a && !**b).count();
    let mut flows = Vec::new();
    let mut expect = BTreeMap::new();
    for (k, t) in asked.iter().enumerate() {
        let ts = show(t);
        let mut s = format!("pub rt fn k{k}(v: {ts}) -> F32 {{\n  1.0\n}}\n\nconst C{k}: {ts} = {}\n\n", value(t, d));
        s.push_str(&match forms[k] {
            0 => format!("pub flow fl{k}(x: F32 at sample, v: {ts} at block) -> F32 at sample {{\n  x\n}}\n"),
            1 => format!("pub flow fl{k}(x: F32 at sample) -> F32 at sample {{\n  let _ = C{k}\n  x\n}}\n"),
            _ => format!("pub flow fl{k}(x: F32 at sample) -> F32 at sample {{\n  x * k{k}(C{k})\n}}\n"),
        });
        flows.push(s);
        expect.insert(format!("fl{k}"), holds(t, &h, true));
    }
    let mut texts = Texts::new();
    if modules {
        texts.insert("dsp.onsa".to_string(), declarations(d));
        let mut names: Vec<String> = ["dbl", "Ph", "W", "Q"].iter().map(|s| s.to_string()).collect();
        names.extend((0..d.kinds.len()).map(|i| format!("D{i}")));
        texts.insert("main.onsa".to_string(), format!("use dsp.{{{}}}\n\n{}", names.join(", "), flows.join("\n")));
    } else {
        texts.insert("main.onsa".to_string(), format!("{}\n{}", declarations(d), flows.join("\n")));
    }
    Program { texts, expect, through_phantom, seed }
}

/// A type written as [`show`] writes it.
fn parse(s: &str) -> Ty {
    fn eat(s: &mut &str, p: &str) -> bool {
        s.strip_prefix(p).map(|r| *s = r).is_some()
    }
    fn ty(s: &mut &str) -> Ty {
        if eat(s, "rt fn(F32) -> F32") {
            Ty::Fn
        } else if eat(s, "F32") {
            Ty::F32
        } else if eat(s, "(") {
            let mut ts = vec![ty(s)];
            while eat(s, ", ") {
                ts.push(ty(s));
            }
            assert!(eat(s, ")"), "a tuple ends at {s}");
            Ty::Tuple(ts)
        } else if eat(s, "[") {
            let t = ty(s);
            assert!(eat(s, "; 2]"), "an array ends at {s}");
            Ty::Arr(Box::new(t))
        } else if let Some(name) = ["Ph", "W", "Q"].into_iter().find(|n| eat(s, &format!("{n}["))) {
            let t = ty(s);
            assert!(eat(s, "]"), "a generic ends at {s}");
            Ty::Gen(name, Box::new(t))
        } else {
            assert!(eat(s, "D"), "a type at {s}");
            let digits = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
            let j = s[..digits].parse().unwrap();
            *s = &s[digits..];
            Ty::Decl(j)
        }
    }
    let mut rest = s;
    let t = ty(&mut rest);
    assert!(rest.is_empty(), "{s}: left {rest}");
    t
}

/// The flow of a line of `main.onsa`: the last `pub flow fl<k>` at or before it.
fn flow_of(text: &str, line: u64) -> Option<String> {
    let mut found = None;
    for (i, l) in text.lines().enumerate() {
        if i as u64 + 1 > line {
            break;
        }
        if let Some(rest) = l.strip_prefix("pub flow ") {
            found = Some(rest.split('(').next().unwrap().to_string());
        }
    }
    found
}

fn run(programs: impl IntoIterator<Item = Program>) -> (usize, usize, usize) {
    let (mut flows, mut holding, mut phantom) = (0, 0, 0);
    let mut bad = Vec::new();
    for p in programs {
        let (seed, modules) = (p.seed, p.texts.contains_key("dsp.onsa"));
        phantom += p.through_phantom;
        let checked = check_input(&input_of("demo", &p.texts));
        assert!(ended_well(&checked), "seed {seed}: check did not end as a check does:\n{}", checked.stderr);
        let main = &p.texts["main.onsa"];
        let mut got: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for x in &checked.diags {
            let flow = if x.file == "main.onsa" { flow_of(main, x.line) } else { None };
            let key = flow.unwrap_or_else(|| format!("{}:{}", x.file, x.line));
            got.entry(key).or_default().push(format!("{} at {}:{}", x.code, x.line, x.col));
        }
        for (f, holds) in &p.expect {
            flows += 1;
            holding += *holds as usize;
            let g = got.remove(f).unwrap_or_default();
            let ok = if *holds { g.len() == 1 && g[0].starts_with("E0810") } else { g.is_empty() };
            if !ok {
                bad.push(format!("seed {} ({}): {f} holds a function type: {holds}; got {g:?}", p.seed, modules));
            }
        }
        for (k, g) in got {
            bad.push(format!("seed {seed} ({modules}): diagnostics outside the flows, at {k}: {g:?}"));
        }
    }
    assert!(bad.is_empty(), "{} mismatches:\n{}", bad.len(), bad.join("\n"));
    (flows, holding, phantom)
}

#[test]
fn declaration_cycles_hold_a_function_type_by_the_least_fixed_point() {
    let (flows, holding, phantom) = run((0..200).map(|seed| program(seed, false)));
    // The draw has both sides: types that hold one and types that do not, and declarations that hold one only through a phantom argument.
    assert!(
        flows > 3500 && holding > 1500 && flows - holding > 1000,
        "{flows} flows, {holding} of them hold a function type"
    );
    assert!(phantom > 100, "{phantom} declarations hold a function type only through a phantom argument");
}

#[test]
fn declaration_cycles_in_another_module_hold_a_function_type_by_the_least_fixed_point() {
    let (flows, holding, phantom) = run((0..100).map(|seed| program(seed, true)));
    assert!(
        flows > 1800 && holding > 800 && flows - holding > 600,
        "{flows} flows, {holding} of them hold a function type"
    );
    assert!(phantom >= 30, "{phantom} declarations hold a function type only through a phantom argument");
}

/// The shapes the sweep of the break side of U6b found (`gen_cycle3.py`, the seeds 544, 2438, 783 and 1798, as their declarations are numbered): the declarations, by `D<j>` (a
/// struct `s`, an enum `e` of one element a variant, an alias `a`), and the types asked in order, the first of which, asked first, walked a
/// declaration being entered from one entered after it, and was taken to tell the others: each also asked in the reverse order.
const SHAPES: [Shape; 4] = [
    (
        &[
            ('e', &["Ph[D3]"]),
            ('s', &["Ph[D0]", "D0", "(F32, Ph[D0])"]),
            ('e', &["Ph[D5]"]),
            ('e', &["W[(Ph[D5], Ph[D5])]", "Q[(D2, (D0, D2))]"]),
            ('s', &["(D3, rt fn(F32) -> F32)", "Ph[D2]"]),
            ('s', &["D3", "Ph[D1]", "D4"]),
            ('a', &["Ph[D1]"]),
            ('a', &["Q[D5]"]),
            ('a', &["((D1, Ph[D4]), D0)"]),
        ],
        &["D5", "D6", "[D6; 2]", "Ph[D6]", "Ph[D1]", "(F32, D6)", "Q[D6]"],
    ),
    (
        &[
            ('s', &["Ph[D0]", "(Ph[D6], Ph[D1])", "Ph[D6]"]),
            ('s', &["D0"]),
            ('a', &["rt fn(F32) -> F32"]),
            ('s', &["Ph[D0]"]),
            ('s', &["D1"]),
            ('a', &["((Ph[D3], D4), rt fn(F32) -> F32)"]),
            ('s', &["Q[F32]", "((Ph[D4], (D5, D0)), Ph[D1])"]),
        ],
        &["D6", "D3"],
    ),
    (SEED_783, &["(Ph[D5], ((D3, D4), (Ph[D2], D0)))", "D1"]),
    (
        &[
            ('s', &["Ph[D4]", "Ph[D3]", "(rt fn(F32) -> F32, F32)"]),
            ('s', &["F32", "W[(D0, D0)]"]),
            ('s', &["(Q[(D1, D0)], rt fn(F32) -> F32)", "Ph[D4]", "D1"]),
            ('e', &["Ph[D4]"]),
            ('s', &["(D3, D0)"]),
            ('a', &["Ph[D3]"]),
            ('s', &["F32", "Ph[D4]", "Ph[D4]"]),
        ],
        &["[D2; 2]", "[D5; 2]", "(F32, D5)", "Ph[D5]", "Q[D5]", "Ph[D3]", "W[D5]"],
    ),
];

/// The declarations of a shape and the types asked.
type Shape = (&'static [Decl], &'static [&'static str]);

/// A declaration of a shape: its kind and the types it is made of.
type Decl = (char, &'static [&'static str]);

const SEED_783: &[Decl] = &[
    ('s', &["F32", "(Q[F32], Ph[D6])", "F32"]),
    ('s', &["Ph[D4]"]),
    ('a', &["rt fn(F32) -> F32"]),
    ('a', &["Ph[D0]"]),
    ('e', &["Ph[D4]", "Ph[D5]"]),
    ('s', &["D4", "(Ph[D1], W[W[D4]])", "(Ph[D5], ((D3, D4), (Ph[D2], D0)))"]),
    ('s', &["rt fn(F32) -> F32", "Ph[D5]"]),
    ('s', &["(Q[(D2, D3)], (Ph[D1], Ph[D7]))", "rt fn(F32) -> F32"]),
];

#[test]
fn the_shapes_the_break_side_found_hold_a_function_type_whichever_flow_asks_first() {
    let mut programs = Vec::new();
    for (k, (decls, asked)) in SHAPES.iter().enumerate() {
        let kind = |c: char| match c {
            's' => Kind::Struct,
            'e' => Kind::Enum,
            _ => Kind::Alias,
        };
        let d = Decls {
            kinds: decls.iter().map(|&(c, _)| kind(c)).collect(),
            parts: decls.iter().map(|(_, ts)| ts.iter().map(|t| parse(t)).collect()).collect(),
        };
        let mut asked: Vec<Ty> = asked.iter().map(|t| parse(t)).collect();
        for modules in [false, true] {
            for _ in 0..2 {
                // The first in the body: the input of a flow is asked before the declarations are lowered, and its answers are not kept.
                let forms: Vec<usize> = (0..asked.len()).map(|i| if i == 0 { 1 } else { (i + k) % 3 }).collect();
                programs.push(package(&d, &asked, &forms, modules, k as u64));
                asked.reverse();
            }
        }
    }
    let (flows, holding, _) = run(programs);
    assert_eq!((flows, holding), (72, 72), "every type asked holds a function type");
}
