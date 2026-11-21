//! A drawn sweep of the clocks of flows against a model of the rules of the clock algebra (§11.3, §11.4, S-1077, S-1078,
//! S-1079, S-567; W7-09 U2r2/t, moved from `sweep/model.py` of the break side of U2r1).
//!
//! Each drawn flow has the inputs `p` (`block`), `q` (`init`) and `x` (`sample`) and up to seven `let`s of the forms `a`,
//! `a + b`, `prev~(a)` and `if a > F32.ONE { b } else { c }`, where an atom is a name (an input or a `let` before), the constant
//! `F32.ONE`, or a name with an `at` (`p at (sample / 4)`, `(x at block)`). The model, from the spec:
//! - A value of a periodic tick meets another of another ratio, or a value of the parameter kinds, as follows: two ticks of
//!   different ratios are E0815, one tick with the parameter kinds is that tick, and without one the later of the parameter kinds
//!   holds (a constant is below `init`). The clock of a part in error is an error, which no other part reports (§18.1 gives one
//!   error to a flow).
//! - `e at k` takes the clock `k`, and it is E0815 when `k` is slower than the clock of `e` (a constant takes `k`).
//! - The first argument of `prev~` has the clock of a tick, else E0813 (§11.4, a state is counted in ticks).
//!
//! The flow whose first error is at a `let` has one diagnostic of that code on the line, and a clean one has none. The sweep is
//! shown to catch three errors of the model (a slower `at` is allowed, ticks of two ratios meet, a delay of the parameter kinds is
//! allowed): the same drawn flows, read with each, differ from the result.

use crate::test_support::sweep::{Rng, Texts, check_input, ended_well, input_of};

#[derive(Clone, Copy, PartialEq, Debug)]
enum Clk {
    Const,
    Init,
    Block,
    /// A periodic tick: 0 is `sample`, -2 is `sample / 4`.
    Tick(i32),
    Error,
}

fn rank(c: Clk) -> i32 {
    match c {
        Clk::Const => 0,
        Clk::Init => 1,
        Clk::Block => 2,
        Clk::Tick(k) => 6 + k,
        Clk::Error => 99,
    }
}

/// The model's rules; the three flags are what the mutants turn off.
#[derive(Clone, Copy)]
struct Rules {
    slower_at_is_error: bool,
    two_ratios_clash: bool,
    prev_of_a_parameter_kind_is_error: bool,
}

const TRUE_RULES: Rules =
    Rules { slower_at_is_error: true, two_ratios_clash: true, prev_of_a_parameter_kind_is_error: true };

/// The texts after `at` and their clocks (`K4` is the constant 4, so `(sample / K4)` is `(sample / 4)`).
const KS: [(&str, Clk); 8] = [
    ("sample", Clk::Tick(0)),
    ("(sample / 2)", Clk::Tick(-1)),
    ("(sample / 4)", Clk::Tick(-2)),
    ("(sample / 8)", Clk::Tick(-3)),
    ("(sample / K4)", Clk::Tick(-2)),
    ("(sample / (8))", Clk::Tick(-3)),
    ("block", Clk::Block),
    ("init", Clk::Init),
];

/// An atom: the constant, or the name of index `.0` (0 `p`, 1 `q`, 2 `x`, 3 + i `l<i>`) with the `at` `KS[.1]`.
#[derive(Clone, Copy)]
enum Atom {
    One,
    Name(usize, Option<usize>),
}

#[derive(Clone, Copy)]
enum Form {
    Atom(Atom),
    Plus(Atom, Atom),
    Prev(Atom),
    If(Atom, Atom, Atom),
}

fn name_of(i: usize) -> String {
    ["p".to_string(), "q".to_string(), "x".to_string()].get(i).cloned().unwrap_or_else(|| format!("l{}", i - 3))
}

fn atom_text(a: Atom) -> String {
    match a {
        Atom::One => "F32.ONE".to_string(),
        Atom::Name(i, None) => name_of(i),
        Atom::Name(i, Some(k)) => format!("({} at {})", name_of(i), KS[k].0),
    }
}

fn form_text(f: Form) -> String {
    match f {
        Form::Atom(a) => atom_text(a),
        Form::Plus(a, b) => format!("{} + {}", atom_text(a), atom_text(b)),
        Form::Prev(a) => format!("prev~({})", atom_text(a)),
        Form::If(a, b, c) => {
            format!("if {} > F32.ONE {{ {} }} else {{ {} }}", atom_text(a), atom_text(b), atom_text(c))
        }
    }
}

fn atom_clock(a: Atom, clocks: &[Clk], r: Rules) -> (Clk, bool) {
    match a {
        Atom::One => (Clk::Const, false),
        Atom::Name(i, None) => (clocks[i], false),
        Atom::Name(i, Some(k)) => {
            let (c, k) = (clocks[i], KS[k].1);
            match c {
                Clk::Error => (Clk::Error, false),
                Clk::Const => (k, false),
                _ => (k, r.slower_at_is_error && rank(k) < rank(c)),
            }
        }
    }
}

/// The clock of the meeting of clocks, and whether two ratios meet.
fn join(cs: &[Clk], r: Rules) -> (Clk, bool) {
    if cs.contains(&Clk::Error) {
        return (Clk::Error, false);
    }
    let ticks: Vec<Clk> = cs.iter().copied().filter(|c| matches!(c, Clk::Tick(_))).collect();
    if let Some(&t) = ticks.first() {
        let clash = ticks.iter().any(|&u| u != t);
        return (
            if clash && !r.two_ratios_clash {
                t
            } else if clash {
                Clk::Error
            } else {
                t
            },
            clash && r.two_ratios_clash,
        );
    }
    (cs.iter().copied().max_by_key(|&c| rank(c)).unwrap_or(Clk::Const), false)
}

/// The clock of a `let` and its error.
fn eval(f: Form, clocks: &[Clk], r: Rules) -> (Clk, Option<&'static str>) {
    let atom = |a| atom_clock(a, clocks, r);
    let one = |c: (Clk, bool)| (c.0, c.1.then_some("E0815"));
    match f {
        Form::Atom(a) => one(atom(a)),
        Form::Plus(a, b) => {
            let (x, y) = (atom(a), atom(b));
            let (c, clash) = join(&[x.0, y.0], r);
            (c, (x.1 || y.1 || clash).then_some("E0815"))
        }
        Form::If(a, b, c) => {
            let (x, y, z) = (atom(a), atom(b), atom(c));
            let (c, clash) = join(&[x.0, y.0, z.0], r);
            (c, (x.1 || y.1 || z.1 || clash).then_some("E0815"))
        }
        Form::Prev(a) => match atom(a) {
            (Clk::Error, _) => (Clk::Error, None),
            (c @ Clk::Tick(_), e) => (c, e.then_some("E0815")),
            (c, _) if !r.prev_of_a_parameter_kind_is_error => (c, None),
            _ => (Clk::Error, Some("E0813")),
        },
    }
}

struct Flow {
    first_line: u64,
    lets: Vec<Form>,
}

fn draw_atom(rng: &mut Rng, names: usize) -> Atom {
    if rng.chance(12) {
        return Atom::One;
    }
    let i = rng.below(names);
    Atom::Name(i, rng.chance(43).then(|| rng.below(KS.len())))
}

fn draw_form(rng: &mut Rng, names: usize) -> Form {
    let r = rng.below(100);
    let mut atom = || draw_atom(rng, names);
    match r {
        0..=24 => Form::Atom(atom()),
        25..=59 => Form::Plus(atom(), atom()),
        60..=79 => Form::Prev(atom()),
        _ => Form::If(atom(), atom(), atom()),
    }
}

/// The flows of one seed, from the line `line` on; 70% of them are drawn again until each `let` has no error.
fn draw_flows(seed: u64, n: usize, start: u64) -> Vec<Flow> {
    let mut rng = Rng::new(seed);
    let mut flows = Vec::new();
    let mut line = start;
    for _ in 0..n {
        let valid = rng.chance(70);
        let mut clocks = vec![Clk::Block, Clk::Init, Clk::Tick(0)];
        let mut lets = Vec::new();
        for _ in 0..rng.range(1, 7) {
            let mut form = draw_form(&mut rng, clocks.len());
            for _ in 0..30 {
                if !valid || eval(form, &clocks, TRUE_RULES).1.is_none() {
                    break;
                }
                form = draw_form(&mut rng, clocks.len());
            }
            clocks.push(eval(form, &clocks, TRUE_RULES).0);
            lets.push(form);
        }
        let n = lets.len() as u64;
        flows.push(Flow { first_line: line, lets });
        line += n + 4;
    }
    flows
}

/// The line and code of the first error of a flow, read with `r`.
fn first_error(f: &Flow, r: Rules) -> Option<(u64, &'static str)> {
    let mut clocks = vec![Clk::Block, Clk::Init, Clk::Tick(0)];
    for (i, &form) in f.lets.iter().enumerate() {
        let (c, e) = eval(form, &clocks, r);
        if let Some(code) = e {
            return Some((f.first_line + 1 + i as u64, code));
        }
        clocks.push(c);
    }
    None
}

#[test]
fn the_clocks_of_drawn_flows_are_those_the_rules_of_the_algebra_give() {
    let mut text = String::from("const K4: U32 = 4\n\n");
    let mut flows: Vec<Flow> = Vec::new();
    for seed in [0x0709_2201, 0x0709_2202, 0x0709_2203] {
        let start = text.lines().count() as u64 + 1;
        for (j, f) in draw_flows(seed, 100, start).into_iter().enumerate() {
            let id = flows.len();
            text.push_str(&format!(
                "pub flow f{id}(p: F32 at block, q: F32 at init, x: F32 at sample) -> F32 at sample {{\n"
            ));
            for (i, &form) in f.lets.iter().enumerate() {
                text.push_str(&format!("  let l{i} = {}\n", form_text(form)));
            }
            let reads: Vec<String> = (0..f.lets.len()).map(|i| format!("(l{i} at sample)")).collect();
            text.push_str(&format!(
                "  {}\n}}\n\n",
                std::iter::once("x".to_string()).chain(reads).collect::<Vec<_>>().join(" + ")
            ));
            assert_eq!(
                f.first_line,
                text.lines().count() as u64 - f.lets.len() as u64 - 3,
                "the line of flow {j} of seed {seed}"
            );
            flows.push(f);
        }
    }
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), text);
    let checked = check_input(&input_of("demo", &texts));
    assert!(ended_well(&checked), "check did not end as a check does:\n{}", checked.stderr);

    // What the checker says of each flow: the diagnostics on the lines of its `let`s.
    let got: Vec<Vec<(u64, String)>> = flows
        .iter()
        .map(|f| {
            let (lo, hi) = (f.first_line, f.first_line + f.lets.len() as u64 + 3);
            checked.diags.iter().filter(|d| (lo..=hi).contains(&d.line)).map(|d| (d.line, d.code.clone())).collect()
        })
        .collect();
    let mismatches = |r: Rules| {
        flows
            .iter()
            .zip(&got)
            .filter(|(f, g)| match first_error(f, r) {
                None => !g.is_empty(),
                Some((line, code)) => g.as_slice() != [(line, code.to_string())],
            })
            .count()
    };
    let bad = mismatches(TRUE_RULES);
    assert_eq!(bad, 0, "{bad} of {} flows differ from the model", flows.len());

    // The draw has both of the kinds of an error, and the clean flows.
    let errors: Vec<_> = flows.iter().filter_map(|f| first_error(f, TRUE_RULES)).collect();
    let (e815, e813) =
        (errors.iter().filter(|e| e.1 == "E0815").count(), errors.iter().filter(|e| e.1 == "E0813").count());
    assert!(
        e815 > 40 && e813 > 20 && errors.len() + 60 < flows.len(),
        "the draw: {e815} E0815, {e813} E0813 of {}",
        flows.len()
    );

    // The sweep catches an error of the model: each of the three changes of the rules is read as a difference.
    for (name, r) in [
        ("a slower at is allowed", Rules { slower_at_is_error: false, ..TRUE_RULES }),
        ("ticks of two ratios meet", Rules { two_ratios_clash: false, ..TRUE_RULES }),
        ("a delay of a parameter kind is allowed", Rules { prev_of_a_parameter_kind_is_error: false, ..TRUE_RULES }),
    ] {
        assert!(mismatches(r) >= 5, "{name}: the sweep does not tell it from the spec ({} differ)", mismatches(r));
    }
}
