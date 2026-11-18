//! What each stage reads of the plan (§11.3, §11.4, S-05): the `let`s of a
//! stage, the constants it defines and what it reads from the state.

use crate::Analysis;
use crate::body::LocalId;
use crate::clock::ClockStage;
use crate::flow::{FieldOf, FlowInfo, Kept};
use crate::tests::check;

const SRC: &str = "pub flow f(x: F32 at sample, k: F32 at block, t: F32 at init) -> F32 at sample {
  let c = 2.0
  let d = 3.0
  let w = k * c / sample_rate()
  let u = t * d
  let y = x * w * u * c
  y
}
";

fn flow(a: &Analysis) -> &FlowInfo {
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let f = a.flows.values().next().expect("the flow");
    assert!(f.complete);
    f
}

fn local(f: &FlowInfo, name: &str) -> LocalId {
    LocalId(f.body.locals.iter().position(|l| l.name == name).unwrap_or_else(|| panic!("no local {name}")) as u32)
}

fn names<'a>(ls: impl Iterator<Item = &'a crate::flow::FlowLet>) -> Vec<&'a str> {
    ls.map(|l| l.name.as_deref().unwrap_or("_")).collect()
}

/// The `let`s of each stage in their order, and the constants a stage
/// reads (`c` at `block` and `sample`, `d` at `init` alone).
#[test]
fn a_stage_has_its_lets_and_the_constants_it_reads() {
    let a = check(SRC);
    let f = flow(&a);
    assert_eq!(names(f.lets_at(ClockStage::Init)), ["u"]);
    assert_eq!(names(f.lets_at(ClockStage::Block)), ["w"]);
    assert_eq!(names(f.lets_at(ClockStage::SAMPLE)), ["y"]);
    assert_eq!(names(f.consts_at(ClockStage::Init)), ["d"]);
    assert_eq!(names(f.consts_at(ClockStage::Block)), ["c"]);
    assert_eq!(names(f.consts_at(ClockStage::SAMPLE)), ["c"]);
}

/// A stage reads from the state what the state keeps and is of another
/// stage: `w` and `u` at `sample`, not at their own; `sample_rate()` at all
/// but `init`; never what the state does not keep (`x`, `c`).
#[test]
fn a_stage_reads_from_the_state_what_another_stage_made() {
    let a = check(SRC);
    let f = flow(&a);
    let at = |n: &str, s: ClockStage| f.from_state(Kept::Local(local(f, n)), s);
    assert!(at("w", ClockStage::SAMPLE) && !at("w", ClockStage::Block));
    assert!(at("u", ClockStage::SAMPLE) && !at("u", ClockStage::Init));
    assert!(!at("x", ClockStage::SAMPLE) && !at("c", ClockStage::SAMPLE) && !at("k", ClockStage::SAMPLE));
    assert!(f.from_state(Kept::SampleRate, ClockStage::Block) && !f.from_state(Kept::SampleRate, ClockStage::Init));
    assert_eq!(f.kept_field(local(f, "w")), Some(FieldOf::Let(local(f, "w"))));
    assert_eq!(f.kept_field(local(f, "x")), None);
    assert_eq!(f.own_stage(local(f, "k")), Some(ClockStage::Block));
    assert_eq!(f.own_stage(local(f, "c")), None);
}
