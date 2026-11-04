//! Where an expression stands in the body (§3.1): what decides whether a
//! form a candidate puts in its place is written in parentheses, and
//! whether its value is used at all.

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::{Ast, BinOp, ExprId, ExprKind, Operand, OperandPlace, StmtKind};

/// The place of an expression under its parent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Slot {
    /// A whole expression (an argument, an element, a tail, the inside of
    /// parentheses, …).
    Free,
    /// An operand of its parent ([`ExprKind::operands`]).
    Operand(OperandPlace),
    /// An expression statement, whose value is dropped.
    Discarded,
}

/// The form at the top of the text a candidate writes in a slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// A chain whose root is this operator (`s.len() == 0`).
    Binary(BinOp),
}

/// Where an expression is: its own slot, and the slot and the parent (none
/// of the root) of the parentheses around it, or of itself without them.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Place {
    pub slot: Slot,
    pub outer: Slot,
    pub parent: Option<ExprId>,
}

/// The place of `e` under `root`, found from the root down with
/// [`Ast::sub_exprs`] (each expression once; linear in the body, which the
/// error stops, so once a body); `None` when `e` is not under `root`.
pub(crate) fn slot_of(ast: &Ast, root: ExprId, e: ExprId) -> Option<Place> {
    let mut todo = vec![(root, Slot::Free, (Slot::Free, None))];
    while let Some((x, slot, (outer, parent))) = todo.pop() {
        if x == e {
            return Some(Place { slot, outer, parent });
        }
        let kind = &ast.expr(x).kind;
        let operands = kind.operands();
        let dropped: HashSet<ExprId> = match kind {
            ExprKind::Block(b) => (b.stmts.iter())
                .filter_map(|&s| match ast.stmt(s).kind {
                    StmtKind::Expr(x) => Some(x),
                    _ => None,
                })
                .collect(),
            _ => HashSet::default(),
        };
        for c in ast.sub_exprs(x) {
            let place = operands.iter().flatten().find(|(o, _)| *o == c);
            let s = match place {
                Some(&(_, p)) => Slot::Operand(p),
                None if dropped.contains(&c) => Slot::Discarded,
                None => Slot::Free,
            };
            let around = match kind {
                ExprKind::Paren(_) => (outer, parent),
                _ => (s, Some(x)),
            };
            todo.push((c, s, around));
        }
    }
    None
}

impl Slot {
    /// Whether `form` is written in parentheses in this slot (§3.1).
    pub(crate) fn wraps(self, form: Form) -> bool {
        let Form::Binary(op2) = form;
        match self {
            Slot::Free | Slot::Discarded => false,
            Slot::Operand(OperandPlace::Binary(op, side)) => !op.bare(side, Operand::Binary(op2)),
            Slot::Operand(OperandPlace::AsAtLeft) => !Operand::Binary(op2).bare_before_as_at(),
            Slot::Operand(OperandPlace::Prefix | OperandPlace::Postfix) => true,
        }
    }
}
