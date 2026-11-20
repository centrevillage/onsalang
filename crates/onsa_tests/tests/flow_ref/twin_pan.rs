//! Panics by stage (W7-20 U3, the family P): a flow `fa` of `if~` and `match~` with divisions (by `k`, `ki`, `n` or a binding of
//! an arm) in the conditions, the guards, the bodies and the plain `if`s of the arms, run only on the evaluator and in the
//! interpreter, one `test` for each scene: `init` alone for `n` = 0, 1, 2, and `init` then one `process` for `n`, `k` = 0, 1, 3,
//! `ki` = 0, 2 and 0 or 2 frames. A panic stops a test, so a scene is a test of its own; the panic is taken as what the program
//! does (`Expect::Evaluator`), and the plan tells what may happen: a program that panics where no division can divide by zero,
//! panics earlier than any division can be evaluated, or does not panic where a division that is surely evaluated (§11.5: a
//! body and the first condition are, the others are chosen by what comes before) divides by zero, or panics later than that
//! division can, is the failure. What the plan cannot say (which of the divisions that may be reached is, and the frame of a
//! `sample` panic) is what the evaluator and the interpreter are compared on (`compare_case`: the same call and the same stage).

use std::collections::BTreeSet;

use onsa_diag::stack;
use onsa_driver::PackageInput;
use onsa_tests::flow_ref::flow::PanicAt;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Expect, Panic, Verdict, run_case_with};

use super::compare::compare_case;
use super::shrink::{LIMITS, MISSING_PANIC, OUT_OF_STAGES, UNEXPECTED_PANIC, class_of, shrink};
use super::twin::{HEADER, Rng, SIGNATURE, report};

/// What a division reads (`100 / d`): an input (`k` and `ki` of `block`, `n` of `init`), or the binding `b<i>` of an arm.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum D {
    K,
    N,
    Ki,
    B(usize),
}

/// A condition: `x > c` (`sample`), `d == 0`, `d < 2` (true for 0), `d != 0`, a division `100 / d > 3`, or the guarded one.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Cond {
    X(&'static str),
    Eq0(D),
    Lt2(D),
    Ne(D),
    Div(D),
    Gdiv(D),
    /// A short circuit whose right side divides: `l && 100 / d > 3` (`true`) or `l || 100 / d > 3`, where `l` is `x > 0.0` (`None`)
    /// or a test of another input, `g != 0` or `g == 0`; it is the right side that is evaluated only where `l` does not decide.
    Short(bool, Option<D>, D),
    /// A text, for a form written by hand.
    Raw(&'static str),
}

/// A branch or an arm that is not a chain or a `match~`: a state, a division, or a plain `if` of a condition and a division.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Leaf {
    X,
    State,
    /// A state of an argument that divides: `acc~(x * F32.round_from(100 / d))`.
    StateDiv(D),
    /// A state of an argument of `block` that divides: `scale~(x, F32.round_from(100 / d))`.
    Block(D),
    Div(D),
    If(Cond, D),
    Raw(&'static str),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Scr {
    K,
    N,
    Ku,
    /// The binding `b<i>` of an arm around the `match~`.
    B(usize),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Pat {
    Lit(u8),
    Bind,
    Wild,
}

#[derive(Clone, Debug)]
pub struct Arm {
    pat: Pat,
    guard: Option<Cond>,
    body: Node,
}

/// The plan of the body of `fa`: a leaf, a chain of `if~` (a condition for each branch but the last), a `match~`.
#[derive(Clone, Debug)]
pub enum Node {
    Leaf(Leaf),
    If(Vec<Cond>, Vec<Node>),
    Match(Scr, Vec<Arm>),
}

impl D {
    fn text(self) -> String {
        match self {
            D::K => "k".into(),
            D::N => "n".into(),
            D::Ki => "ki".into(),
            D::B(i) => format!("b{i}"),
        }
    }

    /// Whether the scene gives 0 (a binding may: the arm that is not taken has the default).
    fn zero(self, s: &Scene) -> bool {
        match self {
            D::K => s.k == 0,
            D::N => s.n == 0,
            D::Ki => s.ki == 0,
            D::B(_) => true,
        }
    }

    /// The stage (0 `init`, 1 `block`, 2 `sample`) of the clock a division that reads it has at the earliest.
    fn rank(self) -> u8 {
        u8::from(matches!(self, D::K | D::Ki))
    }
}

impl Cond {
    fn text(&self) -> String {
        match self {
            Cond::X(c) => format!("x > {c}"),
            Cond::Eq0(d) => format!("{} == 0", d.text()),
            Cond::Lt2(d) => format!("{} < 2", d.text()),
            Cond::Ne(d) => format!("{} != 0", d.text()),
            Cond::Div(d) => format!("100 / {} > 3", d.text()),
            Cond::Gdiv(d) => format!("{0} != 0 && 100 / {0} > 3", d.text()),
            &Cond::Short(and, g, d) => {
                let left =
                    g.map_or("x > 0.0".to_string(), |g| format!("{} {} 0", g.text(), if and { "!=" } else { "==" }));
                format!("{left} {} 100 / {} > 3", if and { "&&" } else { "||" }, d.text())
            }
            Cond::Raw(t) => t.to_string(),
        }
    }

    fn d(&self) -> Option<D> {
        match *self {
            Cond::X(_) | Cond::Raw(_) => None,
            Cond::Eq0(d) | Cond::Lt2(d) | Cond::Ne(d) | Cond::Div(d) | Cond::Gdiv(d) | Cond::Short(_, _, d) => Some(d),
        }
    }

    /// The division that may be by 0 and whether it is surely evaluated with the condition (`Div`; a short circuit evaluates it
    /// where its left does not decide; the guarded ones never divide by 0).
    fn div(&self) -> Option<(D, bool)> {
        match *self {
            Cond::Div(d) => Some((d, true)),
            Cond::Short(_, g, d) if g != Some(d) => Some((d, false)),
            _ => None,
        }
    }

    /// Whether it reads the sample (`x`, or a binding of that clock: `slow` has a bit for each binding).
    fn sample(&self, slow: u32) -> bool {
        let b = |d: Option<D>| matches!(d, Some(D::B(i)) if slow >> i & 1 == 1);
        match *self {
            Cond::X(_) | Cond::Raw(_) | Cond::Short(_, None, _) => true,
            Cond::Short(_, g, d) => b(g) || b(Some(d)),
            _ => b(self.d()),
        }
    }

    fn tag(&self) -> &'static str {
        match self {
            Cond::X(_) => "c_x",
            Cond::Eq0(_) => "c_eq0",
            Cond::Lt2(_) => "c_lt2",
            Cond::Ne(_) => "c_ne",
            Cond::Div(_) => "c_div",
            Cond::Gdiv(_) => "c_gdiv",
            &Cond::Short(and, g, d) if g != Some(d) => {
                [["c_or_x", "c_and_x"], ["c_or_clk", "c_and_clk"]][usize::from(g.is_some())][usize::from(and)]
            }
            Cond::Short(..) => "c_gdiv",
            Cond::Raw(_) => "c_raw",
        }
    }
}

fn dtag(d: D) -> &'static str {
    ["d_n", "d_k", "d_b"][match d {
        D::N => 0,
        D::K | D::Ki => 1,
        D::B(_) => 2,
    }]
}

impl Leaf {
    fn text(&self) -> String {
        let div = |d: &D| format!("x * F32.round_from(100 / {})", d.text());
        match self {
            Leaf::X => "x".into(),
            Leaf::State => "acc~(x)".into(),
            Leaf::StateDiv(d) => format!("acc~({})", div(d)),
            Leaf::Block(d) => format!("scale~(x, F32.round_from(100 / {}))", d.text()),
            Leaf::Div(d) => div(d),
            Leaf::If(c, d) => format!("if {} {{ {} }} else {{ x }}", c.text(), div(d)),
            Leaf::Raw(t) => t.to_string(),
        }
    }

    /// The divisions that may be by 0, and whether each is surely evaluated (when the leaf is).
    fn divs(&self) -> Vec<(D, bool)> {
        match *self {
            Leaf::Div(d) | Leaf::StateDiv(d) | Leaf::Block(d) => vec![(d, true)],
            Leaf::If(c, d) => (c.div().into_iter()).chain((c != Cond::Ne(d)).then_some((d, false))).collect(),
            _ => Vec::new(),
        }
    }
}

impl Node {
    /// As `fa` writes it, where `scope` bindings (`b0`, ...) of the arms around it are named.
    fn text(&self, scope: usize) -> String {
        match self {
            Node::Leaf(l) => l.text(),
            Node::If(conds, arms) => {
                let chain: String = (conds.iter().zip(arms).enumerate())
                    .map(|(i, (c, a))| {
                        format!("if{} {} {{ {} }} else ", if i == 0 { "~" } else { "" }, c.text(), a.text(scope))
                    })
                    .collect();
                format!("{chain}{{ {} }}", arms[arms.len() - 1].text(scope))
            }
            Node::Match(scr, arms) => {
                let name = format!("b{scope}");
                let arm = |a: &Arm| {
                    let bind = a.pat == Pat::Bind;
                    let pat = match a.pat {
                        Pat::Lit(v) => v.to_string(),
                        Pat::Bind => name.clone(),
                        Pat::Wild => "_".into(),
                    };
                    let (guard, body) = (
                        a.guard.map_or(String::new(), |g| format!(" if {}", g.text())),
                        a.body.text(scope + usize::from(bind)),
                    );
                    // A binding that neither the guard nor the body reads is read by the body (`0.0 *` it).
                    let read = !bind || guard.contains(&name) || body.contains(&name);
                    let body = if read { body } else { format!("({body}) + 0.0 * F32.round_from({name})") };
                    format!("{pat}{guard} => {body}")
                };
                let scr = match scr {
                    Scr::K => "k".to_string(),
                    Scr::N => "n".into(),
                    Scr::Ku => "ku".into(),
                    Scr::B(i) => format!("b{i}"),
                };
                format!("match~ {scr} {{ {} }}", arms.iter().map(arm).collect::<Vec<_>>().join(", "))
            }
        }
    }

    fn block_b(&self) -> bool {
        match self {
            Node::Leaf(l) => matches!(l, Leaf::Block(D::B(_))),
            Node::If(_, arms) => arms.iter().any(Node::block_b),
            Node::Match(_, arms) => arms.iter().any(|a| a.body.block_b()),
        }
    }

    fn uses_ku(&self) -> bool {
        match self {
            Node::Leaf(_) => false,
            Node::If(_, arms) => arms.iter().any(Node::uses_ku),
            Node::Match(scr, arms) => *scr == Scr::Ku || arms.iter().any(|a| a.body.uses_ku()),
        }
    }

    /// The divisions that may be by 0, and whether each is surely evaluated: a body, the first condition of a chain and the
    /// condition of a plain `if` are (§11.3: not a position of a condition); the other conditions and the guards are chosen by
    /// what comes before, and the branch of a plain `if` by its condition.
    fn divs(&self, out: &mut Vec<(D, bool)>) {
        match self {
            Node::Leaf(l) => out.extend(l.divs()),
            Node::If(conds, arms) => {
                out.extend(conds.iter().enumerate().filter_map(|(i, c)| c.div().map(|(d, sure)| (d, sure && i == 0))));
                arms.iter().for_each(|a| a.divs(out));
            }
            Node::Match(_, arms) => {
                for a in arms {
                    out.extend(a.guard.iter().filter_map(Cond::div).map(|(d, _)| (d, false)));
                    a.body.divs(out);
                }
            }
        }
    }

    /// The forms the plan holds (the gate asserts its seeds hold the forms of `COVER`).
    fn tags(&self, scope: usize, depth: usize, t: &mut BTreeSet<&'static str>) {
        let cond = |c: &Cond, t: &mut BTreeSet<&'static str>| {
            t.insert(c.tag());
            t.extend(c.div().map(|(d, _)| dtag(d)));
        };
        match self {
            Node::Leaf(l) => match *l {
                Leaf::Div(d) => t.extend(["body_div", dtag(d)]),
                Leaf::StateDiv(d) => t.extend(["state_div", dtag(d)]),
                Leaf::Block(d) => t.extend(["block_div", dtag(d)]),
                Leaf::If(c, d) => {
                    cond(&c, t);
                    t.insert(if c == Cond::Ne(d) { "plain_guarded" } else { "plain_bad" });
                    t.insert(dtag(d));
                }
                _ => {}
            },
            Node::If(conds, arms) => {
                t.insert(["if", "nested_if"][depth.min(1)]);
                for (i, c) in conds.iter().enumerate() {
                    cond(c, t);
                    t.extend((i > 0 && c.div().is_some()).then_some("late_cond_div"));
                    t.extend(matches!(c.d(), Some(D::B(_))).then_some("if_cond_b"));
                }
                t.extend(
                    (conds.len() == 2
                        && conds[0] == Cond::Eq0(conds[1].d().unwrap_or(D::K))
                        && matches!(conds[1], Cond::Div(_)))
                    .then_some("guard_chain"),
                );
                arms.iter().for_each(|a| a.tags(scope, depth + 1, t));
            }
            Node::Match(scr, arms) => {
                t.insert(["match", "nested_match"][depth.min(1)]);
                t.insert(match scr {
                    Scr::K => "scr_k",
                    Scr::N => "scr_n",
                    Scr::Ku => "scr_ku",
                    Scr::B(_) => "scr_b",
                });
                // The arms are chosen from the outside in: a scrutinee that is a binding of the outside, read by a division
                // in an argument of `block`, is what an order that is not that is seen by.
                t.extend((matches!(scr, Scr::B(_)) && arms.iter().any(|a| a.body.block_b())).then_some("block_arg_b"));
                let mut sample_before = false;
                for (i, a) in arms.iter().enumerate() {
                    if let Some(g) = &a.guard {
                        cond(g, t);
                        t.extend((g.div().is_some() && i > 0).then_some("late_guard_div"));
                        t.extend((g.div().is_some() && sample_before).then_some("sample_then_div"));
                        t.extend(matches!(g.d(), Some(D::B(b)) if b < scope).then_some("outer_guard"));
                        sample_before |= matches!(g, Cond::X(_));
                    }
                    a.body.tags(scope + usize::from(a.pat == Pat::Bind), depth + 1, t);
                }
            }
        }
    }
}

/// A scene: `init` with `n` (when `frames` is `None`), or `init` then a `process` of `frames` frames of `k` and `ki`.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Scene {
    n: u32,
    k: u32,
    ki: i32,
    frames: Option<usize>,
}

impl Scene {
    fn name(&self) -> String {
        match self.frames {
            None => format!("n{}_init", self.n),
            Some(f) => format!("n{}_k{}_ki{}_f{f}", self.n, self.k, self.ki),
        }
    }

    fn text(&self, xs: &str) -> String {
        let init = format!("fa.init(fa.Config {{ n: {} }}, 8.0)", self.n);
        let Some(f) = self.frames else { return format!("test \"{}\" {{\n  let _ = {init}\n}}\n", self.name()) };
        let params = format!("fa.Params {{ k: {}, ki: {} }}", self.k, self.ki);
        format!(
            "test \"{}\" {{\n  let xs: [F32; 2] = {xs}\n  var o: [F32; 2] = [0.0; 2]\n  var st = {init}\n  fa.process(inout st, {params}, xs.slice(0, {f}), inout o.slice(0, {f}))\n}}\n",
            self.name()
        )
    }
}

/// The scenes of `frames` (3 of `init` alone, and a `process` of each number of frames).
pub fn scenes(frames: &[usize]) -> Vec<Scene> {
    let mut all: Vec<_> = (0..3).map(|n| Scene { n, k: 0, ki: 0, frames: None }).collect();
    for (n, k, ki, f) in (0..3)
        .flat_map(|n| [0, 1, 3].map(|k| (n, k)))
        .flat_map(|(n, k)| [0, 2].map(|ki| (n, k, ki)))
        .flat_map(|(n, k, ki)| frames.iter().map(move |f| (n, k, ki, *f)))
    {
        all.push(Scene { n, k, ki, frames: Some(f) });
    }
    all
}

/// What each scene of a form written by hand does: the panic (at which call and stage), or none.
pub type Hand = fn(&Scene) -> Option<PanicAt>;

/// A program of the family: the plan of `fa`, the samples `xs` of its two frames, its scenes, and for a form that is written
/// by hand what each scene does (the panic, none or at which call and stage), where the plan is not asked.
#[derive(Clone)]
pub struct Prog {
    pub plan: Node,
    pub xs: &'static str,
    pub scenes: Vec<Scene>,
    pub hand: Option<Hand>,
}

impl Prog {
    pub fn src(&self) -> String {
        let ku = if self.plan.uses_ku() { "  let ku: U32 = if x > 0.0 { 2 } else { 0 }\n" } else { "" };
        let flow = format!("pub flow fa{SIGNATURE} -> F32 at sample {{\n{ku}  {}\n}}\n", self.plan.text(0));
        HEADER.to_string() + &flow + &self.scenes.iter().map(|s| s.text(self.xs)).collect::<String>()
    }
}

fn gen_d(rng: &mut Rng, scope: usize) -> D {
    let mut ds = vec![D::K, D::K, D::N, D::Ki];
    ds.extend((0..scope).flat_map(|b| [D::B(b); 3]));
    rng.pick(&ds)
}

fn gen_cond(rng: &mut Rng, scope: usize) -> Cond {
    let d = gen_d(rng, scope);
    match rng.below(10) {
        0 => Cond::X(rng.pick(&["0.0", "0.5"])),
        1 => Cond::Eq0(d),
        2 => Cond::Lt2(d),
        3 | 4 => Cond::Div(d),
        5 => Cond::Gdiv(d),
        6 => Cond::Ne(d),
        _ => {
            let left = [None, None, Some(gen_d(rng, scope))][rng.below(3)];
            Cond::Short(rng.chance(50), left, d)
        }
    }
}

/// A leaf, where `slow` has a bit for each binding that is of the clock `sample` (`block` takes no such division), and `late` tells
/// that a scrutinee or a guard of `sample` is before it in a `match~` (the evaluator has no value then for a binding of an arm outside that
/// is read in an argument of `block`: `Internal("a local with no value")`, which the interpreter does not have; the form is
/// not made until the evaluator takes it).
fn gen_leaf(rng: &mut Rng, scope: usize, slow: u32, late: bool, need: bool) -> Leaf {
    let d = gen_d(rng, scope);
    let fast = if matches!(d, D::B(i) if slow >> i & 1 == 1 || late) { D::Ki } else { d };
    match rng.below(9) {
        _ if need => [Leaf::State, Leaf::StateDiv(d)][rng.below(2)],
        0 => Leaf::State,
        1 => Leaf::X,
        2 | 3 => Leaf::Div(d),
        4 => Leaf::If(Cond::Ne(d), d),
        5 | 6 if scope > 0 && !late && slow >> (scope - 1) & 1 == 0 && rng.chance(80) => Leaf::Block(D::B(scope - 1)),
        5 | 6 => Leaf::Block(fast),
        _ => Leaf::If(gen_cond(rng, scope), d),
    }
}

/// A node at `depth` (the root is a chain or a `match~`, and nothing is nested below depth 1) with `scope` bindings around it
/// (the bits of `slow` are those of the clock `sample`: a binding has the clock of its scrutinee and of the guards up to its arm,
/// S-1131), and with a state when `need`: a chain and a `match~` have one in an arm of their own, for they are E0812 else.
fn gen_node(rng: &mut Rng, depth: usize, scope: usize, (slow, late): (u32, bool), need: bool) -> Node {
    if depth > 0 && (depth > 1 || rng.chance(55)) {
        return Node::Leaf(gen_leaf(rng, scope, slow, late, need));
    }
    if depth == 0 && rng.chance(10) {
        // The nest that the order of choosing the arms is seen by: the arm of `b0` takes `k`, the arm of `b1` in it takes `b0` and
        // an argument of `block` divides by it, where an order from the inside out (or the innermost only) takes the arm of 0.
        let arm = |pat, guard, leaf| Arm { pat, guard, body: Node::Leaf(leaf) };
        let inner =
            Node::Match(Scr::B(0), vec![arm(Pat::Lit(0), None, Leaf::X), arm(Pat::Bind, None, Leaf::Block(D::B(1)))]);
        let mut arms = vec![arm(Pat::Lit(0), None, Leaf::State)];
        arms.extend(
            rng.chance(50).then(|| {
                arm(Pat::Wild, Some(rng.pick(&[Cond::Eq0(D::N), Cond::Lt2(D::Ki), Cond::Div(D::K)])), Leaf::X)
            }),
        );
        arms.push(Arm { pat: Pat::Bind, guard: None, body: inner });
        return Node::Match(Scr::K, arms);
    }
    if rng.chance(50) {
        let n = rng.pick(&[2, 3, 3]);
        let mut conds: Vec<_> = (1..n).map(|_| gen_cond(rng, scope)).collect();
        if n == 3 && rng.chance(40) {
            let d = gen_d(rng, scope);
            conds = vec![Cond::Eq0(d), Cond::Div(d)];
        }
        let with_state = rng.below(n);
        return Node::If(
            conds,
            (0..n).map(|i| gen_node(rng, depth + 1, scope, (slow, late), i == with_state)).collect(),
        );
    }
    let scr = if scope > 0 && rng.chance(60) {
        Scr::B(rng.below(scope))
    } else {
        rng.pick(&[Scr::K, Scr::K, Scr::N, Scr::Ku])
    };
    if let Scr::B(j) = scr
        && !late
        && slow >> j & 1 == 0
        && rng.chance(50)
    {
        // The arms are chosen from the outside in (a mutant that chooses the inner arms first takes the arm of 0 here, and the
        // division of the other is by a binding that is not bound): the inner arm takes the outer binding, an argument of `block`
        // divides by it, and a state is in the other arm (or the node of the outside has it).
        let (first, second) = (if need { Leaf::State } else { Leaf::X }, Leaf::Block(D::B(scope)));
        let arm = |pat, leaf| Arm { pat, guard: None, body: Node::Leaf(leaf) };
        return Node::Match(scr, vec![arm(Pat::Lit(0), first), arm(Pat::Bind, second)]);
    }
    let n = rng.pick(&[2, 3, 3, 4]);
    let (with_state, mut lits, mut arms) = (rng.below(n), vec![0, 1, 2], Vec::new());
    let (scr_slow, mut guards_slow) = (matches!(scr, Scr::Ku) || matches!(scr, Scr::B(i) if slow >> i & 1 == 1), false);
    for i in 0..n {
        let last = i == n - 1;
        let pat = match rng.below(10) {
            _ if last => rng.pick(&[Pat::Bind, Pat::Wild]),
            0..=3 if !lits.is_empty() => Pat::Lit(lits.remove(rng.below(lits.len()))),
            4..=7 => Pat::Bind,
            _ => Pat::Wild,
        };
        let bind = usize::from(pat == Pat::Bind);
        let guarded = !last && (!matches!(pat, Pat::Lit(_)) || rng.chance(30));
        let guard = guarded.then(|| gen_cond(rng, scope + bind));
        let own = slow | u32::from(scr_slow) << scope;
        guards_slow |= guard.is_some_and(|g| g.sample(own));
        let body_slow = slow | u32::from(scr_slow || guards_slow) << scope;
        arms.push(Arm {
            pat,
            guard,
            body: gen_node(rng, depth + 1, scope + bind, (body_slow, late || scr_slow || guards_slow), i == with_state),
        });
    }
    Node::Match(scr, arms)
}

/// The program of a seed and the forms it holds.
pub fn make(seed: u64) -> (Prog, BTreeSet<&'static str>) {
    let mut rng = Rng::new(seed ^ 0x9A71C);
    let plan = gen_node(&mut rng, 0, 0, (0, false), true);
    let xs = rng.pick(&["[1.0, -1.0]", "[-1.0, 1.0]", "[0.5, 0.25]", "[-0.5, -1.0]"]);
    let mut tags = BTreeSet::new();
    plan.tags(0, 0, &mut tags);
    (Prog { plan, xs, scenes: scenes(&[0, 2]), hand: None }, tags)
}

/// The forms that are written by hand (the plan is not asked: what each scene does is derived from §11.3 and §11.5 here), each
/// on the scenes of 0, 1 and 2 frames and the samples 1.0 and -1.0.
///
/// A chain `if~ d == 0 { .. } else if 100 / d > 3 { .. } else { .. }`: the second condition is evaluated only where the first is
/// false, so where `d` is 0 it is not, at `block` with no frame and at `init` also: nothing panics, for `k`, `ki` and `n`.
///
/// A `match~ k` whose first arm has the guard `g1` and whose second has the guard `100 / d > 3` (the last arm is `_`): the second
/// guard is evaluated where the first arm is not chosen. With `g1` = `x > 0.0` (decided per sample) it is evaluated per sample
/// where it is reached: at the second frame of -1.0, not at the first of 1.0, never in a call of no frame; with `g1` = `k > 1`
/// (decided at `block`) it is evaluated at `block` where `k` is 0 or 1, with `d` of `init` too (the later stage of the two).
pub fn fixed() -> Vec<(Option<u64>, Prog, BTreeSet<&'static str>)> {
    let chain = |d| {
        Node::If(vec![Cond::Eq0(d), Cond::Div(d)], [Leaf::State, Leaf::X, Leaf::Raw("0.5")].map(Node::Leaf).to_vec())
    };
    let guarded = |g1, d| {
        let arm = |pat, guard, body| Arm { pat, guard, body: Node::Leaf(body) };
        let second = Leaf::Raw("2.0 + F32.round_from(b0)");
        let arms = vec![
            arm(Pat::Wild, Some(g1), Leaf::State),
            arm(Pat::Bind, Some(Cond::Div(d)), second),
            arm(Pat::Wild, None, Leaf::Raw("3.0")),
        ];
        Node::Match(Scr::K, arms)
    };
    let (x, k) = (Cond::X("0.0"), Cond::Raw("k > 1"));
    // `match~ k { 0 => acc~(x), b0 => match~ b0 { 0 => x, b1 => scale~(x, F32.round_from(100 / b1)) } }`: where `k` is 0 the outer
    // arm `b0` is not taken, so it is 0 and the inner arm of `b1` is taken with 0 (the arms are chosen from the outside in): the
    // division is by 0 at `block`, in a call of no frame too. Where `k` is not 0, `b1` is `k`.
    let nested = {
        let arm = |pat, body| Arm { pat, guard: None, body: Node::Leaf(body) };
        let inner = Node::Match(Scr::B(0), vec![arm(Pat::Lit(0), Leaf::X), arm(Pat::Bind, Leaf::Block(D::B(1)))]);
        let outer = vec![arm(Pat::Lit(0), Leaf::State), Arm { pat: Pat::Bind, guard: None, body: inner }];
        Node::Match(Scr::K, outer)
    };
    let forms: [(Node, Hand); 8] = [
        (chain(D::K), |_| None),
        (chain(D::Ki), |_| None),
        (chain(D::N), |_| None),
        (guarded(x, D::Ki), |s| (s.ki == 0 && s.frames == Some(2)).then_some(PanicAt::Sample(1))),
        (guarded(x, D::N), |s| (s.n == 0 && s.frames == Some(2)).then_some(PanicAt::Sample(1))),
        (guarded(k, D::Ki), |s| (s.ki == 0 && s.k <= 1 && s.frames.is_some()).then_some(PanicAt::Block)),
        (guarded(k, D::N), |s| (s.n == 0 && s.k <= 1 && s.frames.is_some()).then_some(PanicAt::Block)),
        (nested, |s| (s.k == 0 && s.frames.is_some()).then_some(PanicAt::Block)),
    ];
    let hands = forms.into_iter().map(|(plan, hand)| Prog {
        plan,
        xs: "[1.0, -1.0]",
        scenes: scenes(&[0, 1, 2]),
        hand: Some(hand),
    });
    hands.map(|p| (None, p, BTreeSet::new())).collect()
}

/// The rank of the stage a panic is at (`Start`, the lengths of the columns, none of these programs have).
fn rank(at: PanicAt) -> u8 {
    match at {
        PanicAt::Init => 0,
        PanicAt::Block => 1,
        PanicAt::Sample(_) => 2,
        PanicAt::Start => 9,
    }
}

/// What is wrong with what a scene did (`at`: the panic, if any), by what the plan allows.
fn by_plan(plan: &Node, s: &Scene, at: Option<PanicAt>) -> (Option<String>, bool) {
    let (mut ds, live) = (Vec::new(), |d: D| s.frames.is_some() || d.rank() == 0);
    plan.divs(&mut ds);
    let possible = ds.iter().filter(|(d, _)| d.zero(s) && live(*d)).map(|(d, _)| d.rank()).min();
    let surely = (ds.iter())
        .filter(|(d, sure)| *sure && !matches!(d, D::B(_)) && d.zero(s) && live(*d))
        .map(|(d, _)| d.rank())
        .min();
    let bad = match (at.map(rank), possible, surely) {
        (None, _, Some(_)) => Some(format!("{MISSING_PANIC}: a division that is surely evaluated divides by zero")),
        (Some(_), None, _) => Some(format!("{UNEXPECTED_PANIC}: no division can divide by zero here")),
        (Some(r), Some(first), _) if r < first => {
            Some(format!("{OUT_OF_STAGES}: at {at:?}, no division is evaluated before rank {first}"))
        }
        (Some(r), _, Some(last)) if r > last => {
            Some(format!("{OUT_OF_STAGES}: at {at:?}, a division that is surely evaluated is by rank {last}"))
        }
        _ => None,
    };
    (bad, surely.is_some())
}

/// What a run of programs came to, summed: the scenes, those that panicked and those that did not, by the stage of the panic.
#[derive(Debug, Default)]
pub struct Stats {
    pub programs: usize,
    pub scenes: usize,
    pub panicked: usize,
    pub quiet: usize,
    pub by_stage: [usize; 3],
    pub compared: usize,
    /// The scenes where a division that is surely evaluated divides by zero (they have to panic).
    pub surely: usize,
}

/// What a program came to: the panic of each scene and what is wrong.
fn judge(p: &Prog, wrappers: &Wrappers) -> (Vec<Option<PanicAt>>, usize, Vec<String>) {
    let (path, src) = ("panic_stages.onsa", p.src());
    let input = PackageInput::single_file(path, &src);
    let run = match run_case_with(input.clone(), wrappers, Expect::Evaluator) {
        Ok(r) if r.tests.len() == p.scenes.len() => r,
        Ok(r) => {
            return (
                Vec::new(),
                0,
                vec![format!("not evaluated: {} tests for {} scenes", r.tests.len(), p.scenes.len())],
            );
        }
        Err(e) => return (Vec::new(), 0, vec![format!("not read: {e}")]),
    };
    let (mut seen, mut why, mut surely) = (Vec::new(), Vec::new(), 0);
    for (s, t) in p.scenes.iter().zip(&run.tests) {
        let at = match (&t.verdict, t.panic) {
            (Verdict::Ok, None) => None,
            (Verdict::Ok, Some(Panic::Call(at))) => Some(at),
            (v, _) => {
                why.push(format!("not evaluated: {}: {v:?} {:?}", s.name(), t.panic));
                continue;
            }
        };
        seen.push(at);
        let bad = match p.hand {
            Some(hand) if hand(s) != at => Some(format!(
                "{}: it is {at:?}, it has to be {:?}",
                [MISSING_PANIC, UNEXPECTED_PANIC][usize::from(at.is_some())],
                hand(s)
            )),
            Some(_) => None,
            None => {
                let (bad, sure) = by_plan(&p.plan, s, at);
                surely += usize::from(sure);
                bad
            }
        };
        why.extend(bad.map(|b| format!("scene {}: {b}", s.name())));
    }
    let c = compare_case(path, input, &run);
    let panicked = seen.iter().flatten().count();
    why.extend(c.failures);
    why.extend(
        (c.ran != seen.len() || c.panicked != panicked)
            .then(|| format!("not compared: {} of {} tests, {} of {panicked} panics", c.ran, seen.len(), c.panicked)),
    );
    (seen, surely, why)
}

impl Node {
    /// How much a plan is: its nodes, its conditions and guards that are not the simplest, its leaves that are not `x`. Each of
    /// the smaller plans is less, which is what ends a shrink.
    pub fn size(&self) -> usize {
        let cond = |c: &Cond| usize::from(*c != Cond::X("0.0"));
        match self {
            Node::Leaf(l) => 1 + usize::from(*l != Leaf::X),
            Node::If(conds, arms) => {
                1 + conds.iter().map(cond).sum::<usize>() + arms.iter().map(Node::size).sum::<usize>()
            }
            Node::Match(_, arms) => {
                1 + arms
                    .iter()
                    .map(|a| a.guard.iter().map(cond).sum::<usize>() + a.guard.is_some() as usize + a.body.size())
                    .sum::<usize>()
            }
        }
    }
}

/// The smaller plans: a leaf for the whole, or for a branch, an arm that is not the last dropped, a condition and a guard
/// made simple.
pub fn smaller_plans(n: &Node) -> Vec<Node> {
    let Node::Leaf(l) = n else { return smaller_inside(n) };
    [Leaf::X].into_iter().filter(|x| x != l).map(Node::Leaf).collect()
}

fn smaller_inside(n: &Node) -> Vec<Node> {
    let mut v = vec![Node::Leaf(Leaf::State)];
    match n {
        Node::If(conds, arms) => {
            v.extend(
                (0..conds.len()).filter(|_| arms.len() > 2).map(|i| Node::If(without(conds, i), without(arms, i))),
            );
            v.extend(
                (0..conds.len())
                    .filter(|&i| conds[i] != Cond::X("0.0"))
                    .map(|i| Node::If(with(conds, i, Cond::X("0.0")), arms.clone())),
            );
            v.extend((0..arms.len()).flat_map(|i| {
                smaller_plans(&arms[i]).into_iter().map(move |a| Node::If(conds.clone(), with(arms, i, a)))
            }));
        }
        Node::Match(s, arms) => {
            v.extend((0..arms.len() - 1).filter(|_| arms.len() > 2).map(|i| Node::Match(*s, without(arms, i))));
            for (i, arm) in arms.iter().enumerate() {
                v.extend(arm.guard.map(|_| Node::Match(*s, with(arms, i, Arm { guard: None, ..arm.clone() }))));
                v.extend(
                    smaller_plans(&arm.body)
                        .into_iter()
                        .map(|b| Node::Match(*s, with(arms, i, Arm { body: b, ..arm.clone() }))),
                );
            }
        }
        Node::Leaf(_) => {}
    }
    v
}

fn without<T: Clone>(xs: &[T], i: usize) -> Vec<T> {
    xs.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, x)| x.clone()).collect()
}

fn with<T: Clone>(xs: &[T], i: usize, x: T) -> Vec<T> {
    xs.iter().enumerate().map(|(j, y)| if j == i { x.clone() } else { y.clone() }).collect()
}

/// The programs run (a seed with each, or `None` for one written by hand): the numbers, and a message for each program with
/// anything wrong (the failing scene is kept alone first when the program is shrunk, then its plan made smaller).
pub fn run(progs: Vec<(Option<u64>, Prog, BTreeSet<&'static str>)>) -> (Stats, Vec<String>) {
    stack::run(move || {
        let (wrappers, mut s, mut bad) = (Wrappers::default(), Stats::default(), Vec::new());
        for (seed, p, tags) in progs {
            let (seen, surely, why) = judge(&p, &wrappers);
            let panicked = seen.iter().flatten().count();
            (s.programs, s.scenes, s.panicked, s.quiet) =
                (s.programs + 1, s.scenes + seen.len(), s.panicked + panicked, s.quiet + seen.len() - panicked);
            seen.iter().flatten().for_each(|a| s.by_stage[usize::from(rank(*a)).min(2)] += 1);
            (s.compared, s.surely) = (s.compared + seen.len(), s.surely + surely);
            if why.is_empty() {
                continue;
            }
            let class = class_of(&why[0]);
            // A scene alone, the one the failure names first (a failure of the whole program, a broken Core, names none: each is tried).
            let alone = |q: &Prog| -> Vec<Prog> {
                let mut all = q.scenes.clone();
                all.sort_by_key(|c| !why[0].contains(&format!("scene {}:", c.name())));
                let one = |c: Scene| Prog { scenes: vec![c], ..q.clone() };
                all.into_iter().filter(|_| q.scenes.len() > 1).map(one).collect()
            };
            let smaller = |q: &Prog| {
                let mut v = alone(q);
                v.extend(smaller_plans(&q.plan).into_iter().map(|plan| Prog { plan, ..q.clone() }));
                v
            };
            let kind = |q: &Prog| judge(q, &wrappers).2.first().map(|w| class_of(w));
            let small = (bad.len() < 3).then(|| shrink(p.clone(), class, LIMITS, smaller, kind));
            bad.push(report(
                "panic_stages",
                seed,
                &tags,
                class,
                &why,
                small.map(|(q, n)| (q.src(), n)).as_ref().map(|(s, n)| (s.as_str(), *n)),
            ));
        }
        (s, bad)
    })
}
