//! Flows made at random with `match~` and their twins (W7-20 U2a): `fa` writes a `match~` as it is, `fb` as §11.5 defines it
//! (the choice of the arm in a `let` first, the bindings of the arms that are not taken at `T.default()`, every body in a `let`,
//! then a plain `if` that selects), so that the two give the same outputs. The choice looks at the scrutinee, the patterns and
//! the guards from the top and stops at the first arm that fits (S-1094); a binding is at the clock of the scrutinee and of the
//! guards of the arms up to its own (S-1131). The helpers of `fb` are `rt fn`s: a plain `match` that is a value has no guard
//! in a flow (E0200). The forms that nest (an `if~` or a `match~` in an arm, a `par~` around) are of U2b.

use std::collections::BTreeSet;

use super::twin::{HEADER, Rng, SIGNATURE, WRAPS, tests};
use Clk::*;

const EXTRA: &str = "pub flow gsum(x: F32 at sample, g: F32 at block) -> F32 at sample {
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

struct Gen {
    rng: Rng,
    id: usize,
    helpers: Vec<String>,
    tags: BTreeSet<&'static str>,
    mutant: bool,
    /// The form that the bugs of the choice by stage hide in: a scrutinee before the sample, a guard on every arm that may
    /// have one, and a staged body after the first.
    force: bool,
}

impl Gen {
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
        self.tags.extend(bound.then_some("g_bind"));
        Some((g, c))
    }

    /// A body of an arm (with a state when `need`) that reads the bindings `env` (name, type, clock) in the forms of the table
    /// of the memo, and the binding it reads.
    fn body(
        &mut self,
        env: &[(String, &'static str, Clk)],
        need: bool,
        after_guard: bool,
    ) -> (String, Option<String>, &'static str) {
        let mut ks = vec!["acc_x", "twice"];
        ks.extend(["lit", "plain"].iter().filter(|_| !need));
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
            "lit" => return (lit.into(), None, k),
            "acc_x" => return ("acc~(x)".into(), None, k),
            "twice" => return ("twice~(x + 1.0)".into(), None, k),
            "plain" => return ("if k != 0 { x * 2.0 } else { 0.0 }".into(), None, k),
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
        (e, Some(b), k)
    }

    /// The `match~` of the scrutinee `s` (as `fa` writes it), the `let`s of `fb` and the value it ends in.
    fn matcher(&mut self, &(tags, scr, _, sclk, sty, templates): &S) -> (String, Vec<String>, String) {
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
            let (mut e, used, kind) = self.body(&env, i == with_state, has_guard);
            has_guard |= a.guard.is_some();
            let ty = (a.binds.iter()).find(|(b, _)| used.as_ref() == Some(b)).map(|b| b.1);
            self.tags.extend((n > 1 && STATE_B.contains(&kind)).then_some("bind_state"));
            self.tags.extend(
                (n > 1 && STATE_B.contains(&kind) && ["Gt", "Hd"].contains(&ty.unwrap_or("")))
                    .then_some("struct_bind_state"),
            );
            a.kind = kind;
            a.used.extend(used);
            // A binding that nothing reads (the body, or the guard) is read by the body, `0.0 *` it.
            let unread: Vec<_> =
                (a.binds.iter()).filter(|(b, _)| !a.used.contains(b) && !a.reads_in_guard(b)).cloned().collect();
            for (b, t) in unread {
                e = format!("({e}) + 0.0 * {}", flt(&b, t));
                a.used.push(b);
            }
            bodies.push(e);
        }
        // A staged body after an arm that may not be taken, and a binding after a guard faster than the scrutinee.
        let guards = |j: usize| arms[..j].iter().filter_map(|a| a.guard.as_ref());
        let staged_after = (0..n).any(|j| STAGED.contains(&arms[j].kind) && guards(j).next().is_some());
        self.tags.extend(staged_after.then_some("staged_guard_false"));
        let late = (0..n).any(|j| !arms[j].used.is_empty() && guards(j).any(|g| g.1 > sclk));
        self.tags.extend(late.then_some("late_clock"));
        let arm_text: Vec<_> = arms.iter().zip(&bodies).map(|(a, e)| format!("{} => {e}", a.text(|_| true))).collect();
        let fa = format!("match~ {scr} {{ {} }}", arm_text.join(", "));
        let s = self.nm("s");
        let mut lets = vec![format!("let {s} = {scr}")];
        // The choice: for each arm that is needed, a helper that matches the arms up to it and gives the number of the first.
        let mut sels = vec![String::new(); n];
        for i in (0..n).filter(|&i| i == n - 1 || !arms[i].used.is_empty()) {
            let inputs: BTreeSet<_> =
                (arms[..=i].iter().filter_map(|a| a.guard.as_ref())).flat_map(|g| words(&g.0)).collect();
            let ins: Vec<_> = ["k", "x", "n", "ki"].into_iter().filter(|q| inputs.contains(q)).collect();
            let ty =
                |q: &str| ["U32", "F32", "U32", "I32"][["k", "x", "n", "ki"].iter().position(|w| *w == q).unwrap()];
            let params: String = ins.iter().map(|q| format!(", {q}: {}", ty(q))).collect();
            let args: String = ins.iter().map(|q| format!(", {q}")).collect();
            let parts: Vec<_> = (arms[..=i].iter().enumerate())
                .map(|(j, a)| format!("{} => {{ r = {j} }}", a.text(|b| a.reads_in_guard(b))))
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
        let names: Vec<_> = bodies.iter().map(|e| (self.nm("t"), e)).collect();
        lets.extend(names.iter().map(|(t, e)| format!("let {t} = {e}")));
        let chain: String =
            (0..n - 1).map(|i| format!("if {} == {i} {{ {} }} else ", sels[n - 1], names[i].0)).collect();
        (fa, lets, format!("{chain}{{ {} }}", names[n - 1].0))
    }
}

/// The program of a seed (with `mutant`, the one whose bindings of the arms not taken are not the defaults).
pub fn make(seed: u64, mutant: bool) -> (String, BTreeSet<&'static str>) {
    let mut g = Gen { rng: Rng::new(seed), id: 0, helpers: Vec::new(), tags: BTreeSet::new(), mutant, force: false };
    let init: Vec<S> = SCRS.iter().filter(|s| s.3 == Init).copied().collect();
    let early: Vec<S> = SCRS.iter().filter(|s| s.3 < Sample).copied().collect();
    g.force = g.rng.chance(15);
    let scr = if g.force {
        g.rng.pick(&early)
    } else if g.rng.chance(20) {
        g.rng.pick(&init)
    } else {
        g.rng.pick(SCRS)
    };
    let (a, lets, b) = g.matcher(&scr);
    let wraps: Vec<_> = WRAPS.iter().filter(|w| w.0 != "wrap_par").collect();
    let (name, wrap) = *g.rng.pick(&wraps);
    g.tags.insert(name);
    let (pre, fa, fb) = (scr.2.join("\n  "), wrap.replace("{}", &a), wrap.replace("{}", &b));
    let flows = format!(
        "pub flow fa{SIGNATURE} -> F32 at sample {{\n  {pre}\n  {fa}\n}}\npub flow fb{SIGNATURE} -> F32 at sample {{\n  {pre}\n  {}\n  {fb}\n}}\n",
        lets.join("\n  ")
    );
    let tests = tests(&mut g.rng, None, ("fa", "fb"));
    (format!("{HEADER}{EXTRA}{}{flows}{tests}", g.helpers.join("")), g.tags)
}
