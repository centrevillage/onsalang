use onsa_syntax::ast::ExprId;

use super::{NodeCall, NodeKind};
use crate::flow_names::Delay;
use crate::ty::TyId;

fn call(delay: Delay, args: &[u32], init: Option<u32>) -> NodeCall {
    let args = args.iter().map(|&i| ExprId(i)).collect();
    let kind = NodeKind::Delay(delay, Some(4));
    NodeCall { expr: ExprId(0), kind, args, init: None, init_expr: init.map(ExprId), ty: TyId(0) }
}

#[test]
fn delay_parts_are_the_first_argument_the_d_of_a_vdelay_and_the_written_init() {
    let (e, some) = (ExprId, |i| Some(ExprId(i)));
    // prev~(x), prev~(x, init)
    assert_eq!(call(Delay::Prev, &[1], None).delay_parts(), (e(1), None, None));
    assert_eq!(call(Delay::Prev, &[1, 2], Some(2)).delay_parts(), (e(1), None, some(2)));
    // delay~(x, N, init): the length is not a `d`
    assert_eq!(call(Delay::Fixed, &[1, 2, 3], Some(3)).delay_parts(), (e(1), None, some(3)));
    // vdelay~(x, d, MAX), vdelay~(x, d, MAX, init)
    assert_eq!(call(Delay::Variable, &[1, 2, 3], None).delay_parts(), (e(1), some(2), None));
    assert_eq!(call(Delay::Variable, &[1, 2, 3, 4], Some(4)).delay_parts(), (e(1), some(2), some(4)));
}

/// The diagnostics of `src` (one unit in error each) and whether the flow
/// `flow` has its tables (`complete`).
fn held(src: &str, flow: &str) -> (Vec<(onsa_diag::Code, onsa_diag::Stage)>, bool) {
    let a = crate::tests::check(src);
    let id = a.defs.iter().position(|d| d.name == flow).expect("the flow") as u32;
    let ds = a.diagnostics.iter().map(|d| (d.code, d.stage)).collect();
    (ds, a.flows[&crate::DefId(id)].complete)
}

const HEAD: &str = "pub flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {\n";

#[test]
fn a_held_flow_error_is_reported_by_position_with_the_walk_and_a_type_error_wins() {
    use onsa_diag::{Code, Stage};
    // R-495: the length (held) before a clock error of the walk.
    let src = format!("{HEAD}  let a = delay~(x, 1)\n  let b = prev~(p)\n  x\n}}\n");
    assert_eq!(held(&src, "f"), (vec![(Code::E0807, Stage::Flow)], false));
    // The other order: the walk's error is first.
    let src = format!("{HEAD}  let b = prev~(p)\n  let a = delay~(x, 0)\n  x\n}}\n");
    assert_eq!(held(&src, "f"), (vec![(Code::E0813, Stage::Flow)], false));
    // R-329: a type error after it is reported, and the held one is not.
    let src = format!("{HEAD}  let a = par i in 2 ..< 2 {{ x }}\n  let b: Bool = 1.0\n  x\n}}\n");
    assert_eq!(held(&src, "f"), (vec![(Code::E0401, Stage::Types)], false));
}

#[test]
fn a_held_flow_error_is_reported_when_the_types_stop_with_no_diagnostic() {
    use onsa_diag::{Code, Stage};
    // `K` is a name held as an error (its unit has the E0302): the check of
    // the types stops at it with no diagnostic of the flow (§18.1, S-692).
    let src = format!("const K: U32 = nowhere\n{HEAD}  let a = delay~(x, 1)\n  let b = delay~(x, K)\n  x\n}}\n");
    let (ds, complete) = held(&src, "f");
    assert!(!complete);
    assert!(ds.contains(&(Code::E0807, Stage::Flow)), "{ds:?}");
    // With no error held, nothing of the flow is reported.
    let src = format!("const K: U32 = nowhere\n{HEAD}  let b = delay~(x, K)\n  x\n}}\n");
    let (ds, _) = held(&src, "f");
    assert!(ds.iter().all(|&(c, _)| c != Code::E0807), "{ds:?}");
}
