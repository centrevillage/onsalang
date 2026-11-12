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
    /// An end of a range, which takes every operator (§3.1) but not a bare
    /// `as` or `at` (§3.3).
    RangeEnd,
}

/// The form at the top of the text a candidate writes in a slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// A name, a literal, a postfix chain, a bracket.
    Plain,
    /// `-x`, `!x`.
    Prefix,
    /// `x as T`, `e at k`.
    AsAt,
    /// A block-like expression ([`ExprKind::block_like`]).
    Block,
    /// A chain whose root is this operator (`s.len() == 0`).
    Binary(BinOp),
}

impl Form {
    /// The form of the expression `e`, as it is written.
    pub(crate) fn of(ast: &Ast, e: ExprId) -> Form {
        match ast.expr(e).kind {
            ExprKind::Binary { op, .. } => Form::Binary(op),
            ExprKind::Cast { .. } | ExprKind::At { .. } => Form::AsAt,
            ExprKind::Unary { .. } => Form::Prefix,
            ref kind if kind.block_like() => Form::Block,
            _ => Form::Plain,
        }
    }
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
        let ends = match kind {
            ExprKind::Range(r) | ExprKind::Par { range: r, .. } => [Some(r.lo), Some(r.hi)],
            _ => [None, None],
        };
        for c in ast.sub_exprs(x) {
            let place = operands.iter().flatten().find(|(o, _)| *o == c);
            let s = match place {
                Some(&(_, p)) => Slot::Operand(p),
                None if dropped.contains(&c) => Slot::Discarded,
                None if ends.contains(&Some(c)) => Slot::RangeEnd,
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
        let operand = match form {
            Form::Plain | Form::Prefix => Operand::Plain,
            Form::AsAt => Operand::AsAt,
            Form::Binary(op) => Operand::Binary(op),
            Form::Block => return matches!(self, Slot::Operand(_)),
        };
        match self {
            Slot::Free | Slot::Discarded => false,
            Slot::RangeEnd => form == Form::AsAt,
            Slot::Operand(OperandPlace::Binary(op, side)) => !op.bare(side, operand),
            Slot::Operand(OperandPlace::AsAtLeft) => !operand.bare_before_as_at(),
            Slot::Operand(OperandPlace::Prefix | OperandPlace::Postfix) => form != Form::Plain,
        }
    }
}

/// Whether the text of `e`, out of the parentheses of a call, has a `{`
/// that a header would read as its body (§3.1): a struct literal or a block
/// among the operands (each once, on a stack: chains may be long).
pub(crate) fn opens_a_brace(ast: &Ast, e: ExprId) -> bool {
    let mut todo = vec![e];
    while let Some(x) = todo.pop() {
        let kind = &ast.expr(x).kind;
        if matches!(kind, ExprKind::Struct { .. } | ExprKind::Block(_)) {
            return true;
        }
        todo.extend(kind.operands().into_iter().flatten().map(|(o, _)| o));
    }
    false
}
