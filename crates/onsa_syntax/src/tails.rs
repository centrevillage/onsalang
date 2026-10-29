//! The tails of a value (spec §5.2, §5.4, S-604): the expressions that give
//! its value through `if`, `match`, blocks and parentheses. The one walk of
//! them on the tree, for the rows of the heads of the bindings (§5.4) and
//! the checks of each tail of an owned one (W4-09).

use crate::ast::{Ast, Block, ExprId, ExprKind, StmtKind};

/// A tail of a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tail {
    /// An expression that is no `if`, `match`, block or parenthesis.
    Value(ExprId),
    /// A block that exits ([`Ast::block_exits`]): it gives no value.
    Exits,
    /// The `()` of a block with no tail that does not exit, or of an `if`
    /// with no `else` (the node of the block or the `if`).
    Unit(ExprId),
}

impl Ast {
    /// The tails of `e` (§5.2: the tail of a block, of each branch of an `if`
    /// and of each arm of a `match`), through parentheses, in source order.
    /// The depth of the walk is that of the nesting of `e` (§2.5).
    pub fn tails(&self, e: ExprId, out: &mut Vec<Tail>) {
        let e = self.without_parens(e);
        match &self.expr(e).kind {
            ExprKind::If { then, else_: Some(other), .. } => {
                self.tails(*then, out);
                self.tails(*other, out);
            }
            ExprKind::If { else_: None, .. } => out.push(Tail::Unit(e)),
            ExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.tails(arm.body, out);
                }
            }
            ExprKind::Block(b) => match b.tail {
                Some(t) => self.tails(t, out),
                None if self.block_exits(b) => out.push(Tail::Exits),
                None => out.push(Tail::Unit(e)),
            },
            _ => out.push(Tail::Value(e)),
        }
    }

    /// Whether the block `b` exits: it has no tail and its last statement is
    /// a `return`, a `break` or a `continue` (§7; it takes any type, §6.1).
    // `panic` and `while true` are W5-08.
    pub fn block_exits(&self, b: &Block) -> bool {
        b.tail.is_none()
            && b.stmts.last().is_some_and(|&s| {
                matches!(self.stmt(s).kind, StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue)
            })
    }
}
