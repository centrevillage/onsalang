//! Flows made at random with `match~` and their twins (W7-20 U2a): `fa` writes a `match~` as it is, `fb` as §11.5 defines it
//! (the choice of the arm in a `let` first, the bindings of the arms that are not taken at `T.default()`, every body in a `let`,
//! then a plain `if` that selects), so that the two give the same outputs. The choice looks at the scrutinee, the patterns and
//! the guards from the top and stops at the first arm that fits (S-1094); a binding is at the clock of the scrutinee and of the
//! guards of the arms up to its own (S-1131). The helpers of `fb` are `rt fn`s: a plain `match` that is a value has no guard
//! in a flow (E0200). The forms that nest (U2b): an `if~`, a `match~` or a `par~` of `match~`es in an arm, a `match~` in a
//! branch of an `if~` (`twin.rs` asks for it), and a `par~` around the `match~`, whose index the scrutinee, the guards and the
//! bodies read (`IDX` is `i` in `fa` and its number in each copy of `fb`, as in `twin.rs`).

use std::collections::BTreeSet;

use super::twin::{HEADER, RANGES, Rng, WRAPS, chain_in, in_par, program, rename};
use Clk::*;

pub const EXTRA: &str = "pub flow gsum(x: F32 at sample, g: F32 at block) -> F32 at sample {
  let y = x * g + prev~(^y)
  y
}
pub rt fn bf(b: Bool) -> F32 { if b { 1.0 } else { 0.0 } }
enum Mode { Off, Gain(F32), Mix(F32, F32) }
pub struct Gt: Default { open: Bool, level: F32 = 0.5, tag: U32 }
struct Pt { a: U32, b: F32 }
struct Hd { a: U32, b: F32 }
impl Default for Hd { rt fn default() -> Hd { Hd { a: 3, b: 0.75 } } }
";

/// An arm of a template: the pattern (`{0}`, `{1}` are its bindings), the types of the bindings, whether it may (1) or has to
/// (2) have a guard, and whether it is irrefutable (what the arm that gives the default of a binding may leave out).
type A = (&'static str, &'static [&'static str], u8, bool);
/// The inputs that a helper of the choice may be given (a guard reads them), and their types.
const INS: [(&str, &str); 5] = [("k", "U32"), ("x", "F32"), ("n", "U32"), ("ki", "I32"), ("IDX", "U32")];
const NO: &[&str] = &[];
const U: &[&str] = &["U32"];
const F: &[&str] = &["F32"];
#[rustfmt::skip]
const T_U32: &[&[A]] = &[
    &[("0 | 1", NO, 1, false), ("{0}", U, 2, true), ("_", NO, 0, true)],
    &[("0", NO, 1, false), ("1", NO, 1, false), ("{0}", U, 2, true), ("_", NO, 0, true)],
    &[("{0}", U, 2, true), ("_", NO, 0, true)],
    &[("0", NO, 1, false), ("{0}", U, 2, true), ("{0}", U, 0, true)],
    &[("1", NO, 0, false), ("2", NO, 0, false), ("{0}", U, 0, true)],
];
#[rustfmt::skip]
const T_I32: &[&[A]] = &[
    &[("-1", NO, 1, false), ("0", NO, 1, false), ("{0}", &["I32"], 0, true)],
    &[("{0}", &["I32"], 2, true), ("_", NO, 0, true)],
];
#[rustfmt::skip]
const T_OPT: &[&[A]] = &[
    &[("Some(0) | Some(1)", NO, 1, false), ("Some({0})", U, 0, false), ("None", NO, 0, false)],
    &[("Some({0})", U, 1, false), ("_", NO, 0, true)],
    &[("Some({0})", U, 2, false), ("Some({0})", U, 0, false), ("None", NO, 0, false)],
];
#[rustfmt::skip]
const T_MODE: &[&[A]] = &[
    &[("Mode.Gain({0})", F, 0, false), ("Mode.Mix({0}, {1})", &["F32", "F32"], 0, false), ("Mode.Off", NO, 0, false)],
    &[("Mode.Mix({0}, _)", F, 1, false), ("_", NO, 0, true)],
];
#[rustfmt::skip]
const T_TUP: &[&[A]] = &[
    &[("(0, {0})", U, 1, false), ("({0}, 1)", U, 1, false), ("({0}, {1})", &["U32", "U32"], 0, true)],
    &[("({0}, {1})", &["U32", "U32"], 2, true), ("_", NO, 0, true)],
];
#[rustfmt::skip]
const T_PT: &[&[A]] = &[
    &[("Pt { a: 0, b: {0} }", F, 1, false), ("Pt { a: {0}, b: {1} }", &["U32", "F32"], 0, true)],
    &[("Pt { a: {0}, b: {1} }", &["U32", "F32"], 2, true), ("_", NO, 0, true)],
];
#[rustfmt::skip]
const T_ARR: &[&[A]] = &[&[("{0}", &["[U32; 2]"], 2, true), ("_", NO, 0, true)], &[("{0}", &["[U32; 2]"], 0, true)]];
#[rustfmt::skip]
const T_GT: &[&[A]] = &[
    &[("{0}", &["Gt"], 2, true), ("_", NO, 0, true)],
    &[("Gt { open: true, level: {0}, tag: {1} }", &["F32", "U32"], 1, false), ("{0}", &["Gt"], 0, true)],
];
#[rustfmt::skip]
const T_BOOL: &[&[A]] = &[
    &[("true", NO, 0, false), ("false", NO, 0, false)],
    &[("{0}", &["Bool"], 0, true)],
    &[("true", NO, 0, false), ("{0}", &["Bool"], 0, true)],
];
#[rustfmt::skip]
const T_WIDE: &[&[A]] = &[
    &[("(0, {0}, {1}, true)", &["I64", "F64"], 0, false), ("({0}, _, {1}, _)", &["U32", "F64"], 2, true), ("_", NO, 0, true)],
    &[("({0}, {1}, _, false)", &["U32", "I64"], 1, false), ("(_, _, {0}, {1})", &["F64", "Bool"], 0, true)],
];

/// The clock of a scrutinee, a guard or a binding (the faster is the greater).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Clk {
    Init,
    Block,
    Sample,
}

#[rustfmt::skip]
const T_HD: &[&[A]] = &[
    &[("{0}", &["Hd"], 2, true), ("_", NO, 0, true)], &[("Hd { a: 0, b: {0} }", F, 1, false), ("{0}", &["Hd"], 0, true)],
];

/// A scrutinee: its tags, its text, the `let`s before it (in both flows), its clock, its
/// type and its templates.
type S = (&'static str, &'static str, &'static [&'static str], Clk, &'static str, &'static [&'static [A]]);
const KU: &str = "let ku: U32 = if x > 0.5 { 2 } else if x > 0.0 { 1 } else { 0 }";
const SOME_K: &str = "let ok: Option[U32] = if k > 0 { Some(k) } else { None }";
const SOME_N: &str = "let on: Option[U32] = if n > 0 { Some(n) } else { None }";
const SOME_U: &str = "let ou: Option[U32] = if x > 0.25 { Some(ku) } else { None }";
const MODE: &str = "let md: Mode = if x > 0.5 { Mode.Gain(x) } else if x > 0.0 { Mode.Mix(x, 1.0) } else { Mode.Off }";
#[rustfmt::skip]
const SCRS: &[S] = &[
    ("int", "k", &[], Block, "U32", T_U32), ("int", "n", &[], Init, "U32", T_U32), ("int", "ku", &[KU], Sample, "U32", T_U32),
    ("i32", "ki", &[], Block, "I32", T_I32), ("arr", "[k, n]", &[], Block, "[U32; 2]", T_ARR), ("arr", "[ku, k]", &[KU], Sample, "[U32; 2]", T_ARR),
    ("gt", "(Gt { open: x > 0.0, level: x, tag: k })", &[], Sample, "Gt", T_GT),
    ("gt", "(Gt { open: k > 1, level: F32.round_from(n), tag: k })", &[], Block, "Gt", T_GT),
    ("bool", "(x > 0.25)", &[], Sample, "Bool", T_BOOL), ("bool", "(k > 1)", &[], Block, "Bool", T_BOOL), ("bool", "(n > 0)", &[], Init, "Bool", T_BOOL),
    ("wide", "(k, ki as I64, x as F64, x > 0.25)", &[], Sample, "(U32, I64, F64, Bool)", T_WIDE),
    ("wide", "(k, ki as I64, (n as F64), k > 1)", &[], Block, "(U32, I64, F64, Bool)", T_WIDE),
    ("state", "((if acc~(x) > 1.5 { 1 } else { 0 }) + k)", &[], Sample, "U32", T_U32),
    ("state", "((if prev~(x) > 0.0 { 1 } else { 0 }) + n)", &[], Sample, "U32", T_U32),
    ("opt state", "(if acc~(x) > 1.0 { Some(k) } else { None })", &[], Sample, "Option[U32]", T_OPT),
    ("opt", "ok", &[SOME_K], Block, "Option[U32]", T_OPT), ("opt", "on", &[SOME_N], Init, "Option[U32]", T_OPT),
    ("opt", "ou", &[KU, SOME_U], Sample, "Option[U32]", T_OPT), ("mode", "md", &[MODE], Sample, "Mode", T_MODE),
    ("tup", "(k, n)", &[], Block, "(U32, U32)", T_TUP), ("tup", "(k, ku)", &[KU], Sample, "(U32, U32)", T_TUP),
    ("hd", "(Hd { a: k, b: x })", &[], Sample, "Hd", T_HD), ("hd", "(Hd { a: k, b: F32.round_from(n) })", &[], Block, "Hd", T_HD),
    ("pt", "(Pt { a: k, b: F32.round_from(n) })", &[], Block, "Pt", T_PT), ("pt", "(Pt { a: k, b: x })", &[], Sample, "Pt", T_PT),
    ("idx int", "(k + IDX)", &[], Block, "U32", T_U32), ("idx int", "(n + IDX)", &[], Init, "U32", T_U32),
    ("idx int", "(if x > 0.25 { IDX + 1 } else { IDX })", &[], Sample, "U32", T_U32),
    ("idx bool", "(x > F32.round_from(IDX) * 0.5)", &[], Sample, "Bool", T_BOOL),
    ("idx opt", "(if x > F32.round_from(IDX) * 0.25 { Some(k + IDX) } else { None })", &[], Sample, "Option[U32]", T_OPT),
];

/// The bodies that read a binding in a stage before the sample (a state of an input of `init` or `block`), and those with a state.
const STAGED: [&str; 4] = ["prev_init", "delay_init", "gsum", "shift"];
const STATE_B: [&str; 8] = ["acc_b", "prev_b", "delay_b", "par_b", "prev_init", "delay_init", "gsum", "shift"];

/// The words of a text (a name is read in it when it is one of them).
fn words(t: &str) -> impl Iterator<Item = &str> {
    t.split(|c: char| !c.is_alphanumeric() && c != '_')
}

/// A binding as an `F32`, so that every type can be read in a body.
fn flt(b: &str, t: &str) -> String {
    match t {
        "F32" => b.into(),
        "Bool" => format!("bf({b})"),
        "[U32; 2]" => format!("F32.round_from({b}[0] + {b}[1] * 2)"),
        "Gt" => format!("({b}.level + F32.round_from({b}.tag))"),
        "Hd" => format!("({b}.b + F32.round_from({b}.a))"),
        _ => format!("F32.round_from({b})"),
    }
}

/// The default of a type (§6.4: what the binding of an arm that is not taken is), or the mutant's, which is not.
fn dflt(t: &str, mutant: bool) -> &'static str {
    match (t, mutant) {
        ("U32" | "I32" | "I64", false) => "0",
        ("U32" | "I32" | "I64", true) => "1",
        ("F32" | "F64", false) => "0.0",
        ("F32" | "F64", true) => "1.0",
        ("Bool", m) => ["false", "true"][m as usize],
        ("[U32; 2]", m) => ["[0; 2]", "[1; 2]"][m as usize],
        ("Hd", m) => ["Hd { a: 3, b: 0.75 }", "Hd { a: 4, b: 1.75 }"][m as usize],
        (_, m) => ["Gt { open: false, level: 0.5, tag: 0 }", "Gt { open: true, level: 1.5, tag: 1 }"][m as usize],
    }
}

/// The text of a pattern with the names of its bindings.
fn fill(raw: &str, names: &[&str]) -> String {
    names.iter().enumerate().fold(raw.to_string(), |p, (i, n)| p.replace(&format!("{{{i}}}"), n))
}

struct Arm {
    raw: &'static str,
    binds: Vec<(String, &'static str)>,
    /// The guard and its clock.
    guard: Option<(String, Clk)>,
    irref: bool,
    /// The clock of the bindings, and the ones the body reads.
    clk: Clk,
    used: Vec<String>,
    /// The kind of its body.
    kind: &'static str,
}

impl Arm {
    /// The pattern with the bindings that `keep` says, and the guard (what the helper of the choice has of the arm).
    fn text(&self, keep: impl Fn(&str) -> bool) -> String {
        let names: Vec<&str> = self.binds.iter().map(|(b, _)| if keep(b) { b.as_str() } else { "_" }).collect();
        let guard = self.guard.as_ref().map_or(String::new(), |g| format!(" if {}", g.0));
        fill(self.raw, &names) + &guard
    }

    fn reads_in_guard(&self, b: &str) -> bool {
        self.guard.as_ref().is_some_and(|g| words(&g.0).any(|w| w == b))
    }
}

pub struct Gen {
    rng: Rng,
    id: usize,
    helpers: Vec<String>,
    tags: BTreeSet<&'static str>,
    mutant: bool,
    /// Whether the `match~` is in a `par~`, and may read its index.
    pub idx: bool,
    /// The form that the bugs of the choice by stage hide in: a scrutinee before the sample, a guard on every arm that may
    /// have one, and a staged body after the first.
    force: bool,
    /// How many arms had a state that reads a binding (`parm_state` is of a `par~` whose arms have one).
    states: usize,
}

/// A body of an arm: as `fa` writes it, the `let`s of `fb` before its value, the value, and the bindings it reads.
struct Bd {
    fa: String,
    lets: Vec<String>,
    fb: String,
    used: Vec<String>,
    kind: &'static str,
}

/// A body that is one text in both flows, with the binding it reads.
fn flat(e: String, used: Option<String>, kind: &'static str) -> Bd {
    Bd { fb: e.clone(), fa: e, lets: Vec::new(), used: used.into_iter().collect(), kind }
}

impl Gen {
    pub fn new(seed: u64, mutant: bool, idx: bool) -> Gen {
        Gen {
            rng: Rng::new(seed),
            id: 0,
            helpers: Vec::new(),
            tags: BTreeSet::new(),
            mutant,
            idx,
            force: false,
            states: 0,
        }
    }

    /// The helpers (to put in the program) and the forms that the `match~`es made have.
    pub fn done(self) -> (String, BTreeSet<&'static str>) {
        (self.helpers.join(""), self.tags)
    }

    /// The scrutinees that may be made (one with a `let` before it only when `plain` is not asked for).
    fn scrs(&self, plain: bool) -> Vec<S> {
        (SCRS.iter()).filter(|s| (self.idx || !s.1.contains("IDX")) && (!plain || s.2.is_empty())).copied().collect()
    }

    /// A `match~` of the branch of an `if~`, which is as deep as the plan goes: as `fa` writes it, the `let`s of `fb` and the value.
    pub fn nested(&mut self) -> (String, Vec<String>, String) {
        let scrs = self.scrs(true);
        let s = *self.rng.pick_in(&scrs);
        self.matcher(s.1, &s, 1)
    }

    fn nm(&mut self, p: &str) -> String {
        self.id += 1;
        format!("{p}{}", self.id)
    }

    /// A guard for an arm of bindings `binds` (it has to, when `need`), and its clock: that of what it reads, with a binding at
    /// the clock `s` of the scrutinee.
    fn guard(&mut self, binds: &[(String, &'static str)], s: Clk, need: bool) -> Option<(String, Clk)> {
        if !need && !self.force && self.rng.chance(45) {
            return None;
        }
        let j = s.max(Block);
        let plain = [("k > 1", Block), ("n > 0", Init), ("x > 0.0", Sample), ("k == 2 || x > 0.5", Sample)];
        let mut o: Vec<(String, Clk, bool)> = plain.iter().map(|&(t, c)| (t.to_string(), c, false)).collect();
        let of_idx = [("x > F32.round_from(IDX) * 0.5", Sample), ("k > IDX", Block)];
        o.extend(of_idx.iter().filter(|_| self.idx).map(|&(t, c)| (t.to_string(), c, false)));
        for (b, t) in binds {
            let (i, f) = (*t == "I32", flt(b, t));
            let own = match *t {
                "U32" | "I32" => vec![
                    (format!("{b} > 1"), s),
                    (format!("{b} == 0"), s),
                    (format!("{b} < 2 && k > 0"), j),
                    (format!("{b} < {}", if i { "ki" } else { "k" }), j),
                    (format!("{b} + {} > 1", if i { "ki" } else { "n" }), if i { j } else { s }),
                    (format!("{f} + x > 0.5"), Sample),
                    (format!("{f} * F32.round_from(k) > 1.0"), j),
                ],
                "F32" | "F64" => vec![(format!("{b} > 0.5"), s)],
                "I64" => vec![(format!("{b} > 1"), s)],
                "[U32; 2]" => vec![(format!("{b}[0] > 1"), s), (format!("{b}[1] == 0 && k > 0"), j)],
                "Gt" => vec![(format!("{b}.open"), s), (format!("{b}.level > 0.6"), s)],
                "Hd" => vec![(format!("{b}.a > 1"), s), (format!("{b}.b > 0.6"), s)],
                _ => vec![(b.clone(), s), (format!("!{b} && k > 0"), j)],
            };
            o.extend(own.into_iter().map(|(t, c)| (t, c, true)));
        }
        // A guard no faster than the scrutinee more often: the bindings stay at `init` or `block` (what `prev~(x, b)` and
        // `shift~(x, b)` need, and `gsum~(x, b)`), also in an arm that follows a guard that may be false.
        o.retain(|g| g.1 <= s || self.rng.chance(if s == Init { 15 } else { 40 }));
        let (g, c, bound) = o[self.rng.below(o.len())].clone();
        self.tags.insert(["g_init", "g_block", "g_sample"][c as usize]);
        self.tags.extend(g.contains("IDX").then_some("g_idx"));
        self.tags.extend(bound.then_some("g_bind"));
        Some((g, c))
    }

    /// A body of an arm (with a state when `need`) that reads the bindings `env` (name, type, clock) in the forms of the table
    /// of the memo, and in an arm of a `match~` of depth 0 an `if~`, a `match~` of a binding or a `par~` of them.
    fn body(&mut self, env: &[(String, &'static str, Clk)], need: bool, after_guard: bool, depth: usize) -> Bd {
        let mut ks = vec!["acc_x", "twice"];
        ks.extend(["lit", "plain"].iter().filter(|_| !need));
        ks.extend(["acc_i", "acc_i"].iter().filter(|_| self.idx));
        let ints = |ts: &[&str]| env.iter().any(|e| ts.contains(&e.1));
        ks.extend(["nif", "nmatch", "nmatch"].iter().filter(|k| depth == 0 && (**k == "nif" || ints(&["U32", "I32"]))));
        ks.extend(["parm"; 3].iter().filter(|_| depth == 0 && ints(&["U32"])));
        if !env.is_empty() {
            ks.extend(["acc_b", "acc_b", "prev_b", "prev_b", "delay_b", "par_b"]);
            ks.extend(["mulx", "ifp", "ifk", "ifk"].iter().filter(|_| !need));
            let has = |f: fn(&(String, &str, Clk)) -> bool| env.iter().any(f);
            ks.extend(["prev_init", "delay_init", "prev_init", "delay_init"].iter().filter(|_| has(|e| e.2 == Init)));
            ks.extend(["gsum", "gsum"].iter().filter(|_| has(|e| e.2 < Sample)));
            ks.extend(["ifh"; 3].iter().filter(|_| !need && has(|e| e.2 < Sample)));
            ks.extend(["shift", "shift"].iter().filter(|_| has(|e| e.2 == Init && e.1 == "U32")));
        }
        if after_guard && (self.force || self.rng.chance(50)) && ks.iter().any(|k| STAGED.contains(k)) {
            ks.retain(|k| STAGED.contains(k));
        }
        let k = self.rng.pick(&ks);
        self.tags.insert(k);
        let lit = ["1.5", "-2.0", "0.25"][self.rng.below(3)];
        match k {
            "lit" => return flat(lit.into(), None, k),
            "acc_x" => return flat("acc~(x)".into(), None, k),
            "twice" => return flat("twice~(x + 1.0)".into(), None, k),
            "plain" => return flat("if k != 0 { x * 2.0 } else { 0.0 }".into(), None, k),
            "acc_i" => return flat("acc~(x * F32.round_from(IDX + 1))".into(), None, k),
            "nif" => {
                let floats = env.iter().map(|(b, t, _)| flt(b, t)).collect();
                let sfx = format!("_{}", self.nm("n"));
                let (fa, lets, fb, held) = chain_in(self.rng.below(1 << 30) as u64, self.idx, floats, &sfx);
                self.tags.extend(held);
                let used = env.iter().filter(|e| words(&fa).any(|w| w == e.0)).map(|e| e.0.clone()).collect();
                return Bd { fa, lets, fb, used, kind: k };
            }
            "nmatch" | "parm" => return self.nested_match(env, k, depth),
            _ => {}
        }
        let cands: Vec<_> = (env.iter())
            .filter(|e| match k {
                "prev_init" | "delay_init" => e.2 == Init,
                "gsum" | "ifh" => e.2 < Sample,
                "shift" => e.2 == Init && e.1 == "U32",
                _ => true,
            })
            .collect();
        let (b, t, c) = cands[self.rng.below(cands.len())].clone();
        let f = flt(&b, t);
        let v = self.rng.below(4);
        let e = match k {
            "acc_b" => format!("acc~(x * {f})"),
            "mulx" => format!("x * {f}"),
            "ifp" => format!("if {f} > 1.0 {{ x }} else {{ 0.5 }}"),
            "prev_b" if c == Sample => format!("prev~({f})"),
            "prev_b" => format!("prev~({f} + x)"),
            "delay_b" if c == Sample => format!("delay~({f}, 2)"),
            "delay_b" => format!("delay~({f} + x, 2)"),
            "par_b" => format!("sum2(par~ jj in 0 ..< 2 {{ prev~({f} + F32.round_from(jj) + x) }})"),
            "prev_init" => format!("prev~(x, {f})"),
            "delay_init" => format!("delay~(x, 2, {f})"),
            "gsum" => format!("gsum~(x, {f})"),
            "shift" => format!("shift~(x, {b})"),
            "ifk" => [
                format!("if {f} > 1.0 {{ x * F32.round_from(k + 1) }} else {{ x }}"),
                format!("if {f} > 0.5 {{ x * F32.round_from(n + 1) }} else {{ 0.25 }}"),
                format!("if k > 1 && {f} > 0.5 {{ x * F32.round_from(ki + 5) }} else {{ x }}"),
            ][v % 3]
                .clone(),
            "ifh" => [
                format!("if k > 0 {{ x * ({f} + F32.round_from(k)) }} else {{ x }}"),
                format!("if n > 0 {{ x * ({f} + F32.round_from(n)) }} else {{ 0.5 }}"),
                format!("if {f} > 0.5 {{ x * ({f} * F32.round_from(k + 1)) }} else {{ x }}"),
                format!("if k > 1 && n > 0 {{ x * F32.round_from(n + k) * {f} }} else {{ x }}"),
            ][v]
                .clone(),
            _ => panic!("a kind of body that is not known: {k}"),
        };
        flat(e, Some(b), k)
    }

    /// The body of an arm that is a `match~` of one of its bindings (`nmatch`), or a `par~` of two `match~`es of it and the index
    /// of the `par~` (`parm`, whose index is `jp` in `fa` and 0 and 1 in the copies of `fb`).
    fn nested_match(&mut self, env: &[(String, &'static str, Clk)], k: &'static str, depth: usize) -> Bd {
        let cands: Vec<_> = env.iter().filter(|e| e.1 == "U32" || (k == "nmatch" && e.1 == "I32")).collect();
        let (b, t, c) = (*self.rng.pick_in(&cands)).clone();
        let s: S = ("", "", &[], c, t, if t == "I32" { T_I32 } else { T_U32 });
        if k == "nmatch" {
            let (fa, lets, fb) = self.matcher(&b, &s, depth + 1);
            return Bd { fa, lets, fb, used: vec![b], kind: k };
        }
        let before = self.states;
        let (fa, lets, value) = self.matcher(&format!("({b} + JP)"), &s, depth + 1);
        self.tags.extend((self.states > before).then_some("parm_state"));
        let (mut all, mut names) = (Vec::new(), Vec::new());
        for j in 0..2 {
            let (ls, v) = rename(&lets, &value, &format!("_p{j}"));
            all.extend(ls.iter().map(|l| l.replace("JP", &j.to_string())));
            names.push(self.nm("t"));
            all.push(format!("let {} = {}", names[j], v.replace("JP", &j.to_string())));
        }
        let fa = format!("sum2(par~ jp in 0 ..< 2 {{ {} }})", fa.replace("JP", "jp"));
        Bd { fa, lets: all, fb: format!("sum2([{}])", names.join(", ")), used: vec![b], kind: k }
    }

    /// The `match~` of the scrutinee `scr` of `s` (as `fa` writes it), the `let`s of `fb` and the value it ends in. Its arms nest
    /// a form only at depth 0.
    fn matcher(
        &mut self,
        scr: &str,
        &(tags, _, _, sclk, sty, templates): &S,
        depth: usize,
    ) -> (String, Vec<String>, String) {
        let tmpl = self.rng.pick(templates);
        let n = tmpl.len();
        self.tags.extend(tags.split_whitespace());
        self.tags.insert(["scr_init", "scr_block", "scr_sample"][sclk as usize]);
        let (mut clk, mut arms) = (sclk, Vec::new());
        for &(raw, tys, may, irref) in tmpl {
            let binds: Vec<_> = tys.iter().map(|t| (self.nm("b"), *t)).collect();
            let guard = if may > 0 { self.guard(&binds, sclk, may == 2) } else { None };
            clk = clk.max(guard.as_ref().map_or(Init, |g| g.1));
            let bare = fill(raw, &["", ""]);
            self.tags.extend(raw.contains(" | ").then_some("or_pat"));
            self.tags.extend(raw.contains("{0}").then_some("bind_pat"));
            self.tags
                .extend((bare.contains(|c: char| c.is_ascii_digit()) || bare.contains("true")).then_some("lit_pat"));
            self.tags.extend(raw.starts_with('_').then_some("wild_pat"));
            arms.push(Arm { raw, binds, guard, irref, clk, used: Vec::new(), kind: "" });
        }
        let clocks: BTreeSet<_> = arms.iter().filter_map(|a| a.guard.as_ref().map(|g| g.1)).collect();
        self.tags.extend((clocks.len() > 1).then_some("g_mixed"));
        let with_state = self.rng.below(n);
        let (mut bodies, mut has_guard) = (Vec::new(), false);
        for (i, a) in arms.iter_mut().enumerate() {
            let env: Vec<_> = a.binds.iter().map(|(b, t)| (b.clone(), *t, a.clk)).collect();
            let mut bd = self.body(&env, i == with_state, has_guard, depth);
            has_guard |= a.guard.is_some();
            let ty = (a.binds.iter()).find(|(b, _)| bd.used.first() == Some(b)).map(|b| b.1);
            self.tags.extend((n > 1 && STATE_B.contains(&bd.kind)).then_some("bind_state"));
            self.states += (n > 1 && STATE_B.contains(&bd.kind)) as usize;
            self.tags.extend(
                (n > 1 && STATE_B.contains(&bd.kind) && ["Gt", "Hd"].contains(&ty.unwrap_or("")))
                    .then_some("struct_bind_state"),
            );
            a.kind = bd.kind;
            a.used.extend(bd.used.clone());
            // A binding that nothing reads (the body, or the guard) is read by the body, `0.0 *` it.
            let unread: Vec<_> =
                (a.binds.iter()).filter(|(b, _)| !a.used.contains(b) && !a.reads_in_guard(b)).cloned().collect();
            for (b, t) in unread {
                (bd.fa, bd.fb) =
                    (format!("({}) + 0.0 * {}", bd.fa, flt(&b, t)), format!("({}) + 0.0 * {}", bd.fb, flt(&b, t)));
                a.used.push(b);
            }
            bodies.push(bd);
        }
        // A staged body after an arm that may not be taken, and a binding after a guard faster than the scrutinee.
        let guards = |j: usize| arms[..j].iter().filter_map(|a| a.guard.as_ref());
        let staged_after = (0..n).any(|j| STAGED.contains(&arms[j].kind) && guards(j).next().is_some());
        self.tags.extend(staged_after.then_some("staged_guard_false"));
        let late = (0..n).any(|j| !arms[j].used.is_empty() && guards(j).any(|g| g.1 > sclk));
        self.tags.extend(late.then_some("late_clock"));
        let arm_text: Vec<_> =
            arms.iter().zip(&bodies).map(|(a, e)| format!("{} => {}", a.text(|_| true), e.fa)).collect();
        let fa = format!("match~ {scr} {{ {} }}", arm_text.join(", "));
        let s = self.nm("s");
        let mut lets = vec![format!("let {s} = {scr}")];
        // The choice: for each arm that is needed, a helper that matches the arms up to it and gives the number of the first.
        let mut sels = vec![String::new(); n];
        for i in (0..n).filter(|&i| i == n - 1 || !arms[i].used.is_empty()) {
            let inputs: BTreeSet<_> =
                (arms[..=i].iter().filter_map(|a| a.guard.as_ref())).flat_map(|g| words(&g.0)).collect();
            let ins: Vec<_> = INS.iter().filter(|q| inputs.contains(&q.0)).collect();
            let params: String = ins.iter().map(|q| format!(", {}: {}", q.0.to_lowercase(), q.1)).collect();
            let args: String = ins.iter().map(|q| format!(", {}", q.0)).collect();
            let parts: Vec<_> = (arms[..=i].iter().enumerate())
                .map(|(j, a)| format!("{} => {{ r = {j} }}", a.text(|b| a.reads_in_guard(b)).replace("IDX", "idx")))
                .collect();
            let (f, sel) = (self.nm("selfn"), self.nm("sel"));
            let tail = if i < n - 1 { ", _ => {}" } else { "" };
            self.helpers.push(format!(
                "rt fn {f}(v: {sty}{params}) -> U32 {{\n  var r: U32 = {n}\n  match v {{ {}{tail} }}\n  r\n}}\n",
                parts.join(", ")
            ));
            lets.push(format!("let {sel}: U32 = {f}({s}{args})"));
            sels[i] = sel;
        }
        // The bindings: what the arm that is taken has, and the default of the type for the arms that are not.
        for (i, a) in arms.iter().enumerate() {
            for (bi, (b, t)) in a.binds.iter().enumerate().filter(|(_, (b, _))| a.used.contains(b)) {
                let (d, f) = (dflt(t, self.mutant), self.nm("extfn"));
                let names: Vec<_> = (0..a.binds.len()).map(|k| if k == bi { b.as_str() } else { "_" }).collect();
                let tail = if a.irref { "" } else { ", _ => {}" };
                self.helpers.push(format!(
                    "rt fn {f}(v: {sty}) -> {t} {{\n  var r: {t} = {d}\n  match v {{ {} => {{ r = {b} }}{tail} }}\n  r\n}}\n",
                    fill(a.raw, &names)
                ));
                lets.push(format!("let {b} = if {} == {i} {{ {f}({s}) }} else {{ {d} }}", sels[i]));
            }
        }
        let mut names = Vec::new();
        for bd in &bodies {
            names.push(self.nm("t"));
            lets.extend(bd.lets.iter().cloned());
            lets.push(format!("let {} = {}", names[names.len() - 1], bd.fb));
        }
        let chain: String = (0..n - 1).map(|i| format!("if {} == {i} {{ {} }} else ", sels[n - 1], names[i])).collect();
        (fa, lets, format!("{chain}{{ {} }}", names[n - 1]))
    }
}

/// The program of a seed (with `mutant`, the one whose bindings of the arms not taken are not the defaults).
pub fn make(seed: u64, mutant: bool) -> (String, BTreeSet<&'static str>) {
    let mut g = Gen::new(seed, mutant, false);
    let (name, wrap) = g.rng.pick(WRAPS);
    let par = name == "wrap_par";
    (g.idx, g.force) = (par, g.rng.chance(15));
    let all = g.scrs(par);
    let init: Vec<S> = all.iter().filter(|s| s.3 == Init).copied().collect();
    let early: Vec<S> = all.iter().filter(|s| s.3 < Sample).copied().collect();
    let of_idx: Vec<S> = all.iter().filter(|s| s.1.contains("IDX")).copied().collect();
    let scr = if g.force {
        g.rng.pick(&early)
    } else if par && g.rng.chance(60) {
        g.rng.pick(&of_idx)
    } else if g.rng.chance(20) {
        g.rng.pick(&init)
    } else {
        g.rng.pick(&all)
    };
    let (a, lets, b) = g.matcher(scr.1, &scr, 0);
    g.tags.insert(name);
    let (fa, fb, out, elems) = if par {
        let (range, elems) = g.rng.pick(RANGES);
        let mut all = Vec::new();
        for (p, e) in elems.iter().enumerate() {
            let (ls, v) = rename(&lets, &b, &format!("_{e}"));
            all.extend(ls.iter().chain([&format!("let r{p} = {v}")]).map(|l| l.replace("IDX", &e.to_string())));
        }
        let names: Vec<_> = (0..elems.len()).map(|p| format!("r{p}")).collect();
        let fa = format!("par~ i in {range} {{ {} }}", a.replace("IDX", "i"));
        (
            fa,
            format!("{}\n  [{}]", all.join("\n  "), names.join(", ")),
            format!("[F32; {}]", elems.len()),
            Some(elems.len()),
        )
    } else {
        let pre = scr.2.join("\n  ");
        let fb = format!("{pre}\n  {}\n  {}", lets.join("\n  "), wrap.replace("{}", &b));
        (format!("{pre}\n  {}", wrap.replace("{}", &a)), fb, "F32".to_string(), None)
    };
    in_par(par, &mut g.tags);
    let head = format!("{HEADER}{EXTRA}{}", g.helpers.join(""));
    (program(&mut g.rng, &head, (&fa, &fb, &out), elems), g.tags)
}
