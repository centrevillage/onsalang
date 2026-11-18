use onsa_syntax::ast::ExprId;

use super::{NodeCall, NodeKind};
use crate::flow_names::Delay;
use crate::ty::TyId;

fn call(delay: Delay, args: &[u32], init: Option<u32>) -> NodeCall {
    let args = args.iter().map(|&i| ExprId(i)).collect();
    let kind = NodeKind::Delay(delay, 4);
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
