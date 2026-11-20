//! The fields of the state the plan makes (S-05, S-06, §12.4): what the
//! state keeps ([`FlowInfo::stored`]), the order of the fields of the
//! `State` and of the replica of a `par~`, the `init` of a delay stored only
//! when it is an `Init`-rate expression, no field of a `par~` with no state,
//! and the names the lowering reads ([`FlowInfo::field`]).

use super::{FieldOf, Part};
use crate::Analysis;
use crate::body::LocalId;
use crate::flow::{FlowInfo, Kept, Owner, PlanKind};
use crate::tests::check;

fn flow<'a>(a: &'a Analysis, name: &str) -> &'a FlowInfo {
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let id = crate::DefId(a.defs.iter().position(|d| d.name == name).expect("the flow") as u32);
    let f = &a.flows[&id];
    assert!(f.complete);
    f
}

fn local(f: &FlowInfo, name: &str) -> LocalId {
    LocalId(f.body.locals.iter().position(|l| l.name == name).unwrap_or_else(|| panic!("no local {name}")) as u32)
}

/// What a field holds, in words that do not depend on the names of the
/// nodes: `in k`, `let w`, `prev`, `delay.Buf`, `par`.
fn what(f: &FlowInfo, of: FieldOf) -> String {
    let local = |l: LocalId| f.body.locals[l.0 as usize].name.clone();
    match of {
        FieldOf::SampleRate => "sample_rate".into(),
        FieldOf::Input(l) => format!("in {}", local(l)),
        FieldOf::Let(l) => format!("let {}", local(l)),
        FieldOf::Node(id, part) => {
            let kind = match &f.node(id).kind {
                PlanKind::Prev { .. } => "prev",
                PlanKind::Delay { .. } => "delay",
                PlanKind::Vdelay { .. } => "vdelay",
                PlanKind::Instance { .. } => "inst",
                PlanKind::Par { .. } => "par",
            };
            if part == Part::Own { kind.into() } else { format!("{kind}.{part:?}") }
        }
        FieldOf::Hoist(h) => format!("hoist {}", f.hoist(h).path),
        FieldOf::Poisoned => "poisoned".into(),
        FieldOf::Initialized => "initialized".into(),
    }
}

fn whats(f: &FlowInfo, owner: Owner) -> Vec<String> {
    f.fields_of(owner).iter().map(|x| what(f, x.of)).collect()
}

const ORDER: &str = "pub flow g(x: F32 at sample) -> F32 at sample {
  prev~(x)
}
pub flow f(x: F32 at sample, k: F32 at block, t: F32 at init, u: F32 at block) -> F32 at sample {
  let c = 2.0
  let w = (k + u) / sample_rate()
  let a = prev~(x, t)
  let b = g~(a) + delay~(x, 4)
  a + (b * w * k * c) + prev~(b)
}
";

/// The state keeps an input, a `let` or the sample rate read at a stage
/// that is not its own (S-05); a constant `let` is never kept.
#[test]
fn the_state_keeps_what_a_later_stage_reads() {
    let a = check(ORDER);
    let f = flow(&a, "f");
    let kept = |n: &str| f.stored(Kept::Local(local(f, n)));
    assert!(kept("k") && kept("w"));
    assert!(!kept("x") && !kept("t") && !kept("u") && !kept("a") && !kept("b") && !kept("c"));
    assert!(f.stored(Kept::SampleRate));
    let state: Vec<(&str, bool)> = f.lets.iter().map(|l| (l.name.as_deref().unwrap(), l.state)).collect();
    assert_eq!(state, vec![("c", false), ("w", true), ("a", false), ("b", false)]);
    let g = flow(&a, "g");
    assert!(!g.stored(Kept::SampleRate));
}

/// The fields of `State` in the order of §12.4: the sample rate, the kept
/// inputs, each `let`'s own field and its nodes, the nodes of the output,
/// `_poisoned` and `_initialized`.
#[test]
fn the_fields_of_the_state_are_in_the_order_of_12_4() {
    let a = check(ORDER);
    let f = flow(&a, "f");
    let want = [
        "sample_rate",
        "in k",
        "let w",
        "prev",
        "prev.Init",
        "inst",
        "delay.Buf",
        "delay.W",
        "prev",
        "poisoned",
        "initialized",
    ];
    assert_eq!(whats(f, Owner::Output), want);
    assert_eq!(whats(f, Owner::Let(0)), want);
    // The names of §11.6 the lowering reads (S-1138).
    let names: Vec<&str> = f.fields.iter().map(|x| x.name.as_str()).collect();
    let want = [
        "_sample_rate",
        "k",
        "w",
        "a",
        "a.init",
        "b.g_0",
        "b.delay_0.buf",
        "b.delay_0.w",
        "_out.prev_0",
        "_poisoned",
        "_initialized",
    ];
    assert_eq!(names, want);
    for x in &f.fields {
        assert_eq!(f.field(x.of), Some(x.name.as_str()));
    }
    assert_eq!(f.field(FieldOf::Input(local(f, "u"))), None);
}

/// A delay stores its `init` only when it is an `Init`-rate expression:
/// not when it is omitted or a constant (S-06, §11.4).
#[test]
fn a_delay_stores_an_init_of_the_stage_init_only() {
    let src = "const C: F32 = 0.25
pub flow f(x: F32 at sample, t: F32 at init) -> F32 at sample {
  prev~(x) + prev~(x, C) + prev~(x, t) + delay~(x, 2) + delay~(x, 2, 0.5) + vdelay~(x, 2.0, 4, t * 2.0)
}
";
    let a = check(src);
    let f = flow(&a, "f");
    let want = [
        "prev",
        "prev",
        "prev",
        "prev.Init",
        "delay.Buf",
        "delay.W",
        "delay.Buf",
        "delay.W",
        "vdelay.Buf",
        "vdelay.W",
        "vdelay.Init",
        "poisoned",
        "initialized",
    ];
    assert_eq!(whats(f, Owner::Output), want);
    let init = |k: usize| f.field(FieldOf::Node(f.roots(Owner::Output)[k], Part::Init)).is_some();
    assert_eq!((0..6).map(init).collect::<Vec<_>>(), vec![false, false, true, false, false, true]);
}

/// A `par~` with no node with state has no field (of its own or of a
/// replica); one with state has the fields of its body in its replica, an
/// inner `par~` its own.
#[test]
fn a_par_has_the_fields_of_its_body_and_none_with_no_state() {
    let src = "pub flow f(x: F32 at sample) -> F32 at sample {
  let v = (par i in 0..<2 { x * 2.0 })[0]
  let s = (par~ i in 0..<2 { prev~(x) + (par~ j in 0..<2 { delay~(x, 2) })[0] })[1]
  v + s
}
";
    let a = check(src);
    let f = flow(&a, "f");
    let par = |k: u32| f.roots(Owner::Let(k))[0];
    let (empty, outer) = (par(0), par(1));
    let PlanKind::Par { fields, .. } = &f.node(empty).kind else { panic!("not a par~") };
    assert!(fields.is_empty() && f.node(empty).field.is_none());
    assert_eq!(f.field(FieldOf::Node(empty, Part::Own)), None);
    assert_eq!(whats(f, Owner::Output), ["par", "poisoned", "initialized"]);
    assert_eq!(whats(f, Owner::Par(outer)), ["prev", "par"]);
    let inner = f.roots(Owner::Par(outer))[1];
    assert_eq!(whats(f, Owner::Par(inner)), ["delay.Buf", "delay.W"]);
    // A node in a `par~` is named in the replica that holds it.
    let delay = f.roots(Owner::Par(inner))[0];
    assert_eq!(f.field(FieldOf::Node(delay, Part::W)), Some("delay_0.w"));
    assert_eq!(f.node(delay).field, Some(0));
    assert_eq!(f.field(FieldOf::Node(delay, Part::Own)), None);
    assert_eq!(f.field(FieldOf::Node(outer, Part::Own)), Some("s.par_0"));
    assert_eq!(f.node(delay).path, "s.par_0.par_0.delay_0");
}

/// The place of a field (`FlowInfo::field_at`, R-498) is its index in the
/// struct that holds it, the `State` or a replica of a `par~`; none of what
/// the state does not keep.
#[test]
fn the_place_of_a_field_is_its_index_in_its_struct() {
    let src = "pub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample {
  let s = (par~ i in 0..<2 { prev~(x) + (par~ j in 0..<2 { delay~(x, 2) })[0] })[1]
  s + k + prev~(x)
}
";
    let a = check(src);
    let f = flow(&a, "f");
    let outer = f.roots(Owner::Let(0))[0];
    let inner = f.roots(Owner::Par(outer))[1];
    let mut seen = 0;
    for owner in [Owner::Output, Owner::Par(outer), Owner::Par(inner)] {
        for (k, x) in f.fields_of(owner).iter().enumerate() {
            assert_eq!(f.field_at(x.of), Some(k as u32), "{}", x.name);
            seen += 1;
        }
    }
    assert_eq!(seen, 5 + 2 + 2);
    assert_eq!(f.field_at(FieldOf::Input(local(f, "x"))), None);
    assert_eq!(f.field_at(FieldOf::Node(inner, Part::Init)), None);
}

/// Two fields of one name in a struct of the state are an internal error
/// at the later one (§11.6, S-1138: no name of the processor is a user's).
#[test]
fn two_fields_of_one_name_are_an_internal_error() {
    let a = check(ORDER);
    let f = flow(&a, "f");
    super::unique(f, &f.fields);
    let mut fields = f.fields.clone();
    let k = fields.iter().position(|x| matches!(x.of, FieldOf::Node(..))).expect("a field of a node");
    fields[k].name = "w".into();
    let payload = std::panic::catch_unwind(|| super::unique(f, &fields)).expect_err("two fields `w`");
    let bug = payload.downcast_ref::<onsa_diag::internal::InternalBug>().expect("an internal error");
    let FieldOf::Node(id, _) = fields[k].of else { unreachable!() };
    assert_eq!(bug.span, Some(f.node(id).span), "{bug:?}");
}

/// R-507, S-1175: the `let` of a `par~` whose body holds no node, kept for a
/// faster stage, has the field of its value beside the replicas, which are
/// named as a `par~` with no name; one whose body holds a node in a nested
/// `par~` keeps the name of the `let`.
#[test]
fn the_value_of_a_let_of_a_par_with_no_node_is_apart_from_its_replicas() {
    let src = "pub rt fn pick(xs: [F32; 2]) -> F32 { xs[0] }
pub flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {
  let v0: [F32; 3] = par i in 0 ..< 3 { p * F32.round_from(i) }
  let m = par~ i in 0 ..< 2 { pick(par~ j in 0 ..< 2 { prev~(x) }) }
  let a = if x > 0.5 { x } else { v0[1] }
  a + m[0]
}
";
    let a = check(src);
    let f = flow(&a, "f");
    let names: Vec<&str> = f.fields.iter().map(|x| x.name.as_str()).collect();
    assert_eq!(names, ["v0", "v0.par_0", "m", "_poisoned", "_initialized"]);
    assert_eq!(whats(f, Owner::Output), ["let v0", "par", "par", "poisoned", "initialized"]);
}
