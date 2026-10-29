//! The table of §5.4 ([`row`]), a row each (R-85 (2)).

use onsa_syntax::ast::Mode;

use super::{Bind, HeadRow, row};
use crate::names::body::BindingKind;

#[test]
fn the_rows_with_no_head() {
    let borrow = Bind::Borrow { no_drop: false };
    for k in [BindingKind::Param, BindingKind::SelfParam, BindingKind::ClosureParam] {
        assert_eq!(row(k(Mode::Borrow), None), borrow);
        assert_eq!(row(k(Mode::Inout), None), Bind::Inout);
        assert_eq!(row(k(Mode::Move), None), Bind::OwnedMut, "R-191");
    }
    assert_eq!(row(BindingKind::FlowInput, None), borrow);
    assert_eq!(row(BindingKind::Var, None), Bind::OwnedMut);
    assert_eq!(row(BindingKind::For { moved: true }, None), Bind::Owned);
    assert_eq!(row(BindingKind::ParVar, None), Bind::Owned);
}

#[test]
fn the_rows_of_a_head() {
    let owned = HeadRow::Owned;
    let static_ = HeadRow::Borrow { sources: Vec::new(), no_drop: true };
    let place = HeadRow::Borrow { sources: Vec::new(), no_drop: false };
    let heads = [BindingKind::Let, BindingKind::FlowLet, BindingKind::MatchBind, BindingKind::For { moved: false }];
    for k in heads {
        assert_eq!(row(k, None), Bind::Owned, "not settled");
        assert_eq!(row(k, Some(&owned)), Bind::Owned);
        assert_eq!(row(k, Some(&static_)), Bind::Borrow { no_drop: true });
        assert_eq!(row(k, Some(&place)), Bind::Borrow { no_drop: false });
    }
    // The head of `for x in move xs` is owned; the kind decides alone.
    assert_eq!(row(BindingKind::For { moved: true }, Some(&place)), Bind::Owned);
}
