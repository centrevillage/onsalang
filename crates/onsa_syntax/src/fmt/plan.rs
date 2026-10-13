//! The plan of `onsa fmt`: the decisions about single tokens that the
//! printer (`fmt/print.rs`) reads as it walks (W3-11).
//!
//! The plan is made once, before the walk. It says which code tokens the
//! printer leaves out and which get another text. From W3-11 unit U3b on it
//! holds the tokens §3.2 and §3.3 of `docs/onsa-tools.md` drop, add or
//! respell; in unit U3a it is empty, and the printer writes every token as it
//! is in the source.

use crate::cst::{Cst, TokenIdx};

pub(super) struct Plan {}

impl Plan {
    pub(super) fn new(_cst: &Cst) -> Plan {
        Plan {}
    }

    /// Whether the printer writes the code token `t` (a token left out is
    /// passed over like trivia).
    pub(super) fn kept(&self, _t: TokenIdx) -> bool {
        true
    }

    /// The text the printer writes for the code token `t`, when it is not
    /// the text of the source.
    pub(super) fn text(&self, _t: TokenIdx) -> Option<&str> {
        None
    }
}
