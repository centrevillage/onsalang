//! The height of a binary chain ([`ChainHeight`]), read by the parser and
//! the levels the tests count.

use crate::ast::{Chain, OpGroup};

/// The height of a binary chain read as the tree of §3.1 (spec §2.5), one
/// level per operator: the one reading of a chain ([`Chain`]) with the
/// strengths of [`OpGroup::stronger`], with heights for its nodes.
pub(crate) struct ChainHeight(Chain<u32, OpGroup>);

fn join(left: u32, _: OpGroup, right: u32) -> u32 {
    left.max(right) + 1
}

impl ChainHeight {
    pub(crate) fn new(first: u32) -> ChainHeight {
        ChainHeight(Chain::new(first))
    }

    /// An operator of `group` after the last operand. Returns how many
    /// operators wait then, this one included, and the height of its left
    /// operand.
    pub(crate) fn operator(&mut self, group: OpGroup) -> (u32, u32) {
        let (waiting, left) = self.0.operator(group, OpGroup::stronger, join);
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
