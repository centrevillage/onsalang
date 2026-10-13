//! The height of a binary chain ([`Chain`]), read by the parser and the
//! levels the tests count.

/// The height of a binary chain read as the tree of §3.1 (spec §2.5), one
/// level per operator: the one reading of a chain ([`crate::ast::Chain`]),
/// with heights for its nodes.
pub(crate) struct Chain(crate::ast::Chain<u32, crate::ast::OpGroup>);

fn tighter(op: crate::ast::OpGroup, waiting: crate::ast::OpGroup) -> bool {
    op.stronger(waiting)
}

fn join(left: u32, _: crate::ast::OpGroup, right: u32) -> u32 {
    left.max(right) + 1
}

impl Chain {
    pub(crate) fn new(first: u32) -> Chain {
        Chain(crate::ast::Chain::new(first))
    }

    /// An operator of `group` after the last operand. Returns how many
    /// operators wait then, this one included, and the height of its left
    /// operand.
    pub(crate) fn operator(&mut self, group: crate::ast::OpGroup) -> (u32, u32) {
        let (waiting, left) = self.0.operator(group, tighter, join);
        (waiting as u32, left)
    }

    pub(crate) fn operand(&mut self, height: u32) {
        self.0.operand(height);
    }

    /// The height of the whole chain.
    pub(crate) fn height(self) -> u32 {
        self.0.finish(join)
    }
}
