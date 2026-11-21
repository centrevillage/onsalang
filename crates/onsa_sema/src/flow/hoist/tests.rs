//! The choice of the hoisted subexpressions (§11.3, W7-05 U1, U2): the
//! largest slow Copy one, no name, `sample_rate()` or constant, the Copy
//! parts of one that is not Copy, guarded under conditions decided at `init`
//! or `block` (S-1157), of each replica in the body of a `par~` (S-1140),
//! the stages its parts are read at, the checked constants (S-888 (c′)),
//! and the numbers and the order of the fields (§11.6, §12.4).

use crate::Analysis;
use crate::clock::ClockStage;
use crate::flow::{FieldOf, FlowInfo, Kept, Owner};
use crate::tests::check;

const HEAD: &str = "pub fn make(v: F32) -> F32 { v * 2.0 }
pub rt fn half(v: F32) -> F32 { v * 0.5 }
";

/// The analysis of `HEAD` and `src`, with no diagnostic, and its text.
fn flow(src: &str) -> (Analysis, String) {
    let text = format!("{HEAD}{src}");
    let a = check(&text);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    (a, text)
}

fn info(a: &Analysis) -> &FlowInfo {
    let id = crate::DefId(a.defs.iter().position(|d| d.name == "f").expect("the flow") as u32);
    let f = &a.flows[&id];
    assert!(f.complete);
    f
}

/// Each hoisted field: its path, its stage and the text of its subexpression.
fn hoists(src: &str) -> Vec<(String, ClockStage, String)> {
    let (a, text) = flow(src);
    let f = info(&a);
    f.hoists.iter().map(|h| (h.path.clone(), h.stage, h.span.text_in(&text).to_string())).collect()
}

fn one(path: &str, stage: ClockStage, text: &str) -> (String, ClockStage, String) {
    (path.to_string(), stage, text.to_string())
}

const B: ClockStage = ClockStage::Block;
const I: ClockStage = ClockStage::Init;

#[test]
fn the_largest_slow_subexpression_is_hoisted_and_its_names_are_read_at_its_stage() {
    let src = "pub flow f(x: F32 at sample, level: F32 at block) -> F32 at sample {
  x * (half(level) * 2.0 + 1.0)
}";
    assert_eq!(hoists(src), [one("_out._hoist_0", B, "half(level) * 2.0 + 1.0")]);
    let (a, _) = flow(src);
    let f = info(&a);
    let level = f.inputs[1];
    assert_eq!(f.read_at[&level].iter().copied().collect::<Vec<_>>(), [B]);
    assert!(!f.stored(Kept::Local(level)), "read at `block` only, in the field");
}

#[test]
fn names_sample_rate_and_constants_are_not_hoisted() {
    let src = "const K: F32 = 3.0
pub flow f(x: F32 at sample, level: F32 at block, p: (F32, F32) at block) -> F32 at sample {
  x * level + x * (level) + x * sample_rate() + x * (2.0 * K) + (level at sample)
}";
    assert_eq!(hoists(src), []);
}

#[test]
fn a_part_that_is_not_copy_stays_and_its_copy_parts_are_hoisted() {
    // Static literals only, so no value needs `Alloc` (§11.5).
    let src = "pub rt fn pick(o: Option[Str], x: F32) -> F32 { match o { Some(_) => x, None => 0.0 } }
pub flow f(x: F32 at sample, a: F32 at init) -> F32 at sample {
  pick(if a + 1.0 > 0.0 { Some(\"on\") } else { None }, x)
}";
    assert_eq!(hoists(src), [one("_out._hoist_0", I, "a + 1.0 > 0.0")]);
}

#[test]
fn a_call_that_is_not_rt_is_hoisted_to_init_with_what_holds_it_at_block() {
    let src = "pub flow f(x: F32 at sample, a: F32 at init, level: F32 at block) -> F32 at sample {
  let h = level * make(a)
  x * h + x * (make(a) * level)
}";
    // The field of a `let` at `block` holds its part at `init`; the outer
    // and the inner start at one place, the outer first (S-1164).
    assert_eq!(
        hoists(src),
        [
            one("h._hoist_0", I, "make(a)"),
            one("_out._hoist_0", B, "make(a) * level"),
            one("_out._hoist_1", I, "make(a)")
        ]
    );
}

/// Each hoisted field: its path, its stage, whether it is guarded and the
/// text of its subexpression.
fn guarded(src: &str) -> Vec<(String, ClockStage, bool, String)> {
    let (a, text) = flow(src);
    let f = info(&a);
    f.hoists.iter().map(|h| (h.path.clone(), h.stage, h.guarded, h.span.text_in(&text).to_string())).collect()
}

fn g(path: &str, stage: ClockStage, guarded: bool, text: &str) -> (String, ClockStage, bool, String) {
    (path.to_string(), stage, guarded, text.to_string())
}

/// S-1157 (D′): under conditions decided at `init` or `block` (an `if`, the
/// left of `&&`, the scrutinee of a `match`), a slow part has a guarded
/// field at the later of its stage and theirs; the conditions are hoisted
/// unguarded. The body of a `par~` is no conditional position (S-1140).
#[test]
fn conditions_decided_at_init_or_block_guard_the_fields_under_them() {
    let src = "pub flow f(x: F32 at sample, a: F32 at init, level: F32 at block, n: I32 at block) -> F32 at sample {
  let p = if level > 0.5 { x * (level * 2.0) } else { x }
  let q = level > 0.5 && x > level * 2.0
  let r = match n { 0 => x * (level * 3.0), _ => x }
  let s = if a > 0.0 { x * (level + a) + x * (a * 2.0) } else { x }
  let t = if level > 0.5 { x * (a * 3.0) } else { x }
  let u = par i in 0 ..< 2 { x * (level * 4.0) }
  if q { p + r + s + t + u[0] } else { x }
}";
    assert_eq!(
        guarded(src),
        [
            g("p._hoist_0", B, false, "level > 0.5"),
            g("p._hoist_1", B, true, "level * 2.0"),
            g("q._hoist_0", B, false, "level > 0.5"),
            g("q._hoist_1", B, true, "level * 2.0"),
            g("r._hoist_0", B, true, "level * 3.0"),
            g("s._hoist_0", I, false, "a > 0.0"),
            g("s._hoist_1", B, true, "level + a"),
            g("s._hoist_2", I, true, "a * 2.0"),
            g("t._hoist_0", B, false, "level > 0.5"),
            g("t._hoist_1", B, true, "a * 3.0"),
            g("u.par_0._hoist_0", B, false, "level * 4.0"),
        ]
    );
}

/// A condition decided per sample (§11.3), or by a value that is not Copy
/// read at `sample` (S-1046 (a)), leaves what is under it where it is
/// reached; one in `at` is decided at the stage of its clock (S-1166).
#[test]
fn a_condition_decided_per_sample_leaves_its_branches_where_they_are_reached() {
    let src = "pub flow f(x: F32 at sample, a: I32 at init, level: F32 at block) -> F32 at sample {
  let c = level > 0.5
  let p = if x > 0.0 { if level > 0.5 { x * (level * 2.0) } else { x } } else { x }
  let q = match (if a > 0 { Some(\"on\") } else { None }) { Some(_) => x * (level * 3.0), None => x }
  let r = if (c at sample) { x * (level * 4.0) } else { x }
  p + q + r
}";
    let hoisted: Vec<String> = guarded(src).into_iter().map(|h| h.3).collect();
    assert_eq!(hoisted, ["a > 0"]);
}

/// The binding of an arm read in a guarded field is read at its stage, where
/// the arm binds it again; a condition that is a name is read there too.
#[test]
fn a_guarded_field_reads_its_conditions_and_the_bindings_of_its_arm_at_its_stage() {
    let src =
        "pub flow f(x: F32 at sample, o: Option[F32] at block, k: F32 at block, on: Bool at init) -> F32 at sample {
  let r = match o { Some(v) => v * k + x, None => x }
  r + (if on { x * (k * 2.0) } else { x })
}";
    assert_eq!(guarded(src), [g("r._hoist_0", B, true, "v * k"), g("_out._hoist_0", B, true, "k * 2.0")]);
    let (a, _) = flow(src);
    let f = info(&a);
    let on = f.inputs[3];
    assert!(f.read_at[&on].contains(&B), "`on` is read at `block` too");
    assert!(f.stored(Kept::Local(on)), "an input at `init` read at `block`");
    let v = f.read_at.iter().filter(|(l, _)| !f.inputs.contains(l) && f.clocks.locals[l] == crate::clock::Clock::Block);
    assert!(v.into_iter().any(|(_, s)| s.contains(&B)), "`v` is read at `block`");
}

/// S-888 (c′): a computed constant expression under conditions decided at
/// `init` or `block` is checked at their stage; under constants or a
/// condition per sample it is evaluated where it is reached. Each is
/// recorded with its conditions for W9-03.
#[test]
fn a_constant_expression_in_a_branch_is_checked_at_the_stage_of_its_conditions() {
    use crate::flow::Cond;
    let src = "const K: I32 = 2
const PAIR: (F32, F32) = (1.0, 2.0)
pub flow f(x: F32 at sample, n: I32 at block) -> F32 at sample {
  let p = if n == 0 { panic(\"bad n\") } else { x }
  let q = if K > 0 { x * (1.0 / 3.0) } else { x }
  let r = if x > 0.0 { x * (2.0 / 3.0) } else if n == 1 { 1.0 } else { (PAIR.1) }
  p + q + r
}";
    let (a, text) = flow(src);
    let f = info(&a);
    let ast = onsa_syntax::parse(onsa_diag::FileId(0), &text).ast;
    let mut found: Vec<(String, Option<ClockStage>, Cond)> =
        f.const_conds.iter().map(|(&e, &c)| (ast.expr(e).span.text_in(&text).to_string(), f.check_of(e), c)).collect();
    found.sort();
    // A branch `{ e }` of a constant is the largest constant expression;
    // one of a literal, a name or a field of one (`{ 1.0 }`, `{ (PAIR.1) }`)
    // is not computed.
    let want = [
        ("1.0 / 3.0".to_string(), None, Cond::Const),
        ("2.0 / 3.0".to_string(), None, Cond::Late),
        // The tail of the block of a value only (its body).
        ("panic(\"bad n\")".to_string(), Some(B), Cond::Block),
    ];
    assert_eq!(found, want);
}

#[test]
fn the_arguments_of_a_node_are_roots_of_their_let() {
    let src = "pub flow f(x: F32 at sample, level: F32 at block) -> F32 at sample {
  let k = prev~((level * 2.0) at sample)
  k + x
}";
    assert_eq!(hoists(src), [one("k._hoist_0", B, "level * 2.0")]);
}

/// §11.6: numbered per `let` in the order of the starts; §12.4: after the
/// nodes of the output, the `let`s in their order and the output last.
#[test]
fn the_fields_are_numbered_per_let_and_follow_the_nodes() {
    let src = "pub flow f(x: F32 at sample, level: F32 at block) -> F32 at sample {
  let a = x * (level + 1.0) + x * (level + 2.0)
  let _ = x * (level + 3.0)
  a + x * (level + 4.0) + prev~(x)
}";
    let paths: Vec<String> = hoists(src).into_iter().map(|h| h.0).collect();
    assert_eq!(paths, ["a._hoist_0", "a._hoist_1", "_0._hoist_0", "_out._hoist_0"]);
    let (a, _) = flow(src);
    let f = info(&a);
    let names: Vec<&str> = f.fields.iter().map(|x| x.name.as_str()).collect();
    assert_eq!(
        names,
        ["_out.prev_0", "a._hoist_0", "a._hoist_1", "_0._hoist_0", "_out._hoist_0", "_poisoned", "_initialized"]
    );
    assert!(f.fields.iter().all(|x| !matches!(x.of, FieldOf::Hoist(h) if f.hoist(h).guarded)));
    assert_eq!(f.hoist(f.hoist_of(f.hoists[3].expr).expect("its field")).owner, Owner::Output);
}

/// S-1140 (its provisional form): a field of the body of a `par~` is of
/// each replica: numbered in that body by itself in the order of the
/// starts, after the scope of the `par~` (of a nested one too, and of one
/// in the output), in an argument of a node of the body (read at `block`
/// by `lp~`, its part at `init`), guarded under the conditions in that
/// body; the replica
/// holds it after its nodes, also a replica with no node, and the `State`
/// does not. A `par~` whose body holds no node is named as one with no name,
/// the whole value of its `let` too (S-1175): `w.par_0`, `c.par_0`.
#[test]
fn the_fields_of_the_body_of_a_par_are_of_each_replica() {
    let src = "pub flow lp(x: F32 at sample, g: F32 at block) -> F32 at sample { x * g }
pub rt fn pair(xs: [F32; 2]) -> F32 { xs[0] + xs[1] }
pub flow f(x: F32 at sample, a: F32 at init, level: F32 at block, n: I32 at block) -> F32 at sample {
  let saws = par~ i in 0 ..< 2 { lp~(x, level * make(F32.round_from(i))) + x * (a * 2.0) }
  let m = x * (level + 1.0)
  let w = par i in 0 ..< 2 { pair(par j in 0 ..< 2 { x * make(F32.round_from(i + j)) }) }
  let c = par i in 0 ..< 2 { if n != 0 { x * F32.round_from(100 / n) } else { x } }
  saws[0] + m + w[1] + c[0] + pair(par k in 0 ..< 2 { x * (level * 3.0) })
}";
    assert_eq!(
        guarded(src),
        [
            g("m._hoist_0", B, false, "level + 1.0"),
            g("saws._hoist_0", I, false, "make(F32.round_from(i))"),
            g("saws._hoist_1", I, false, "a * 2.0"),
            g("w.par_0.par_0._hoist_0", I, false, "make(F32.round_from(i + j))"),
            g("c.par_0._hoist_0", B, false, "n != 0"),
            g("c.par_0._hoist_1", B, true, "F32.round_from(100 / n)"),
            g("_out.par_0._hoist_0", B, false, "level * 3.0"),
        ]
    );
    let (a, _) = flow(src);
    let f = info(&a);
    let names: Vec<&str> = f.fields.iter().map(|x| x.name.as_str()).collect();
    assert_eq!(names, ["saws", "w.par_0", "c.par_0", "_out.par_0", "m._hoist_0", "_poisoned", "_initialized"]);
    let replica = |path: &str| {
        let p = f.nodes.iter().find(|n| n.path == path).expect("the `par~`");
        let owner = Owner::Par(f.node_of[&p.expr]);
        let fields = f.fields_of(owner).iter().map(|x| x.name.as_str()).collect::<Vec<_>>();
        let owned = f.hoists.iter().filter(|h| h.owner == owner).count();
        (fields, owned)
    };
    assert_eq!(replica("saws"), (vec!["lp_0", "_hoist_0", "_hoist_1"], 2));
    assert_eq!(replica("w.par_0"), (vec!["par_0"], 0));
    assert_eq!(replica("w.par_0.par_0"), (vec!["_hoist_0"], 1));
    assert_eq!(replica("_out.par_0"), (vec!["_hoist_0"], 1));
    let h = f.hoist_of(f.hoists[1].expr).expect("its field");
    assert_eq!((f.field(FieldOf::Hoist(h)), f.field_at(FieldOf::Hoist(h))), (Some("_hoist_0"), Some(1)));
}

/// A block of a value only (`{ b2 * 2.0 }`, the body of a branch or an arm)
/// is made of its tail in place, as parentheses: its tail is chosen.
#[test]
fn a_block_of_a_value_only_has_its_tail_hoisted() {
    let src = "pub flow f(x: F32 at sample, b2: F32 at block, c: I32 at init) -> F32 at sample {
  let a = if c == 0 { x } else { b2 * 2.0 }
  a + x * ({ b2 + 1.0 })
}";
    assert_eq!(
        guarded(src),
        [
            g("a._hoist_0", I, false, "c == 0"),
            g("a._hoist_1", B, true, "b2 * 2.0"),
            g("_out._hoist_0", B, false, "b2 + 1.0")
        ]
    );
}

/// S-1094: a guard of `match~` chooses, under the scrutinee and the guards
/// before it, so its slow part is guarded; an arm body, evaluated on every
/// sample, is under no more than the `match~`.
#[test]
fn the_guards_of_a_match_tilde_are_guarded_and_its_arm_bodies_are_not() {
    let src = "pub flow f(x: F32 at sample, level: F32 at block, n: I32 at block) -> F32 at sample {
  let r = match~ n { 0 if level * 2.0 > 1.0 => prev~(x) * (level * 3.0), _ => prev~(x) }
  r
}";
    assert_eq!(guarded(src), [g("r._hoist_0", B, true, "level * 2.0 > 1.0"), g("r._hoist_1", B, false, "level * 3.0")]);
}

/// S-1158 (c): a computed part and a node with no name of a tick slower
/// than the stage that reads them have fields written at the tick, guarded
/// under a condition decided at `init`; a name of a tick has none of its
/// own. The fields at a tick and the `let` of a tick read at `sample` start
/// at `T.default()` (S-1186, R-92), not those at `block` or `init`.
#[test]
fn a_computed_part_and_a_node_of_a_slow_tick_have_fields_at_the_tick() {
    use crate::clock::Ratio;
    let (t4, t8) = (ClockStage::Tick(Ratio(-2)), ClockStage::Tick(Ratio(-3)));
    let src = "pub flow f(x: F32 at sample, p: F32 at block, k: I32 at init) -> F32 at sample {
  let a = prev~(p at (sample / 4))
  let y = x * ((a * 2.0) at sample) + (a at sample) + (prev~(p at (sample / 8)) at sample)
  let z = if k > 0 { (a + 1.0) at sample } else { (p * 2.0) at sample }
  y + z
}";
    assert_eq!(
        guarded(src),
        [
            g("y._hoist_0", t4, false, "a * 2.0"),
            g("y._hoist_1", t8, false, "prev~(p at (sample / 8))"),
            g("z._hoist_0", I, false, "k > 0"),
            g("z._hoist_1", t4, true, "a + 1.0"),
            g("z._hoist_2", B, true, "p * 2.0"),
        ]
    );
    let (a, _) = flow(src);
    let f = info(&a);
    let starts: Vec<bool> =
        (0..f.hoists.len()).map(|h| f.starts_default(FieldOf::Hoist(super::HoistId(h as u32)))).collect();
    assert_eq!(starts, [true, true, false, true, false]);
    let local = |n: &str| f.lets.iter().find(|l| l.name.as_deref() == Some(n)).expect("the let").locals[0];
    assert!(f.starts_default(FieldOf::Let(local("a"))), "read at `sample` from its field");
    assert!(!f.starts_default(FieldOf::Let(local("y"))) && !f.starts_default(FieldOf::Input(f.inputs[1])));
}
