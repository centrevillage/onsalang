//! The choice of the hoisted subexpressions (§11.3, W7-05 U1): the largest
//! slow Copy one, no name, `sample_rate()` or constant, the Copy parts of
//! one that is not Copy, none in a conditional position or the body of a
//! `par~` in this unit, the stages its parts are read at, and the numbers
//! and the order of the fields (§11.6, §12.4).

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

#[test]
fn a_conditional_position_and_the_body_of_a_par_have_no_field_in_this_unit() {
    let src = "pub flow f(x: F32 at sample, level: F32 at block, n: I32 at block) -> F32 at sample {
  let a = if level > 0.5 { x * (level * 2.0) } else { x }
  let b = level > 0.5 && x > level * 2.0
  let c = match n { 0 => x * (level * 3.0), _ => x }
  let d = par~ i in 0 ..< 2 { x * (level * 4.0) }
  if b { a + c + d[0] } else { x }
}";
    assert_eq!(hoists(src), [one("a._hoist_0", B, "level > 0.5"), one("b._hoist_0", B, "level > 0.5")]);
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
