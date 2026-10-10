//! What the expression before a postfix opener is, as a callee (§6.1, S-191,
//! S-256): the one reading of a postfix chain, for the parser's openers (`(`,
//! `[`, the marks `!` and `~`, `::[`) and the table of the forms of other
//! languages ([`crate::foreign`]). A chain is read link by link
//! ([`Callee::start`], [`Callee::then`]) from the kinds of its links
//! ([`Link`]); a later stage that reads a callee from the AST (the calls
//! decided by name, W4-12) reads it through the same links.
//!
//! Two questions are asked of it, and they are kept apart: whether a call's
//! callee is written by name ([`Callee::by_name`]: the `(` and the `[`), and
//! whether the last link names a path ([`Link::names_a_path`]: `::[`, the
//! marks, the type arguments of other languages). Whether the two are to be
//! one is W4-12's and W4-13's to decide. The table's reading of a callee in
//! parentheses from its tokens (`foreign/calls.rs`, `is_postfix_chain`) reads
//! the same links in the text.

use crate::cst::NodeKind;

/// A link of a postfix chain: what the expression that ends there is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Link {
    /// A path of names (`f`, `a.b` as one path, `Self`).
    Name,
    /// A field or a method (`x.f`).
    Field,
    /// A tuple index (`t.0`).
    TupleIndex,
    /// Type arguments (`f::[T]`).
    TypeArgs,
    /// An index (`xs[i]`, or the type arguments of a method of other
    /// languages, which the type stage tells apart).
    Index,
    /// A value that is no path (`(e)`, `g(x)`, `x?`).
    Value,
    /// Anything else (a literal, a block, an operator).
    Other,
}

impl Link {
    /// The link of an expression node of `kind`.
    pub(crate) fn of(kind: NodeKind) -> Link {
        match kind {
            NodeKind::PathExpr => Link::Name,
            NodeKind::FieldExpr => Link::Field,
            NodeKind::TupleIndexExpr => Link::TupleIndex,
            NodeKind::TypeArgsExpr => Link::TypeArgs,
            NodeKind::IndexExpr => Link::Index,
            NodeKind::ParenExpr | NodeKind::CallExpr | NodeKind::TryExpr => Link::Value,
            _ => Link::Other,
        }
    }

    /// Whether the link names a path (a path of names, a method, a tuple
    /// index): what a `::[…]` may follow, and the callees whose type
    /// arguments of another language become `::[…]`.
    pub(crate) fn names_a_path(self) -> bool {
        matches!(self, Link::Name | Link::Field | Link::TupleIndex)
    }

    /// Whether a mark `!` or `~` before a `(` may follow the link: a link
    /// that names a path, or `::[…]` after one.
    pub(crate) fn takes_a_mark(self) -> bool {
        self.names_a_path() || self == Link::TypeArgs
    }

    /// Whether the link is a value and no path (`(e)`, `g(x)`, `xs[i]`,
    /// `x?`): no `::[` can be written after it, and it is called with `.(`.
    pub(crate) fn is_value(self) -> bool {
        matches!(self, Link::Value | Link::Index)
    }
}

/// How a postfix chain has been read so far: a path of names (§2.4: names
/// and the fields, tuple indexes and `::[…]` after them), that path with
/// `[…]`s after it, a field of anything else (a method, `g(x).m`), one `[…]`
/// after such a field (`g(x).m[I32]`), or anything else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Chain {
    Names,
    Indexed,
    Member,
    MemberIndexed,
    Value,
}

/// A postfix chain read so far, and its last link.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Callee {
    chain: Chain,
    last: Link,
}

impl Callee {
    /// The chain that starts with an operand of `kind`.
    pub(crate) fn start(kind: NodeKind) -> Callee {
        let last = Link::of(kind);
        Callee { chain: if last == Link::Name { Chain::Names } else { Chain::Value }, last }
    }

    /// The chain after its next link, a node of `kind`, closed. A field keeps
    /// a path of names (`ops[i].m[T](x)` is a method's, of the type stage,
    /// S-256); after anything else it is a member, and one `[…]` after it is
    /// a method's type arguments or an index of a field, which the type stage
    /// tells apart (`g(x).m[I32](y)`, §4.5); a tuple index ends a path of
    /// names only after names.
    pub(crate) fn then(self, kind: NodeKind) -> Callee {
        use Chain::*;
        let last = Link::of(kind);
        let chain = match (self.chain, last) {
            (c @ (Names | Indexed), Link::Field | Link::TypeArgs) => c,
            (_, Link::Field) => Member,
            (Names, Link::TupleIndex) => Names,
            (Names | Indexed, Link::Index) => Indexed,
            (Member, Link::Index) => MemberIndexed,
            _ => Value,
        };
        Callee { chain, last }
    }

    /// The last link of the chain.
    pub(crate) fn last(self) -> Link {
        self.last
    }

    /// Whether a call of the chain is written by name, so that a later stage
    /// decides the call (§6.1, S-191, S-256): a path of names (`f`, `s.f`;
    /// `t.0`, S-342), a method (`x.f`, `g(x).f`), `::[…]` after one
    /// (`f::[T]`), a path of names with `[…]` after it (`ops[i]`), or a field
    /// of anything else with one `[…]` after it (`g(x).m[I32]`, §4.5). Any
    /// other callee (`(s.f)`, `pick(true)`, `ts[0].0`, `mk2().0`) is no item:
    /// the parser fails at the `(` (`Want::Callee`), and the row
    /// `callee_expression` gives `.(`.
    pub(crate) fn by_name(self) -> bool {
        match self.last {
            Link::Name | Link::Field | Link::TypeArgs => true,
            Link::TupleIndex => self.chain == Chain::Names,
            Link::Index => matches!(self.chain, Chain::Indexed | Chain::MemberIndexed),
            Link::Value | Link::Other => false,
        }
    }
}
