//! The lists and the enclosures of `onsa fmt`, and the form of a list
//! (`spec/tools.md` §3.2, the third item).
//!
//! [`shape`] says whether a CST node is a list (its elements separated by
//! `,` between an opening and a closing bracket), a container (a block or a
//! body of items: statements or items between line breaks), another
//! enclosure (brackets round something that is no list: a group, an index)
//! or neither; the table [`TABLE`] has the brackets of each. [`brackets`] finds
//! the two tokens in a node ([`pairs`] each pair of a node with nested
//! pairs), [`elements`] the elements of a list and [`forms`] the form the
//! writer gave each pair.
//!
//! The form (§3.2) is read from the line breaks of the source:
//! - **block:** a line break right after the opening bracket (a comment at
//!   the end of that line may come before it);
//! - **continuation:** otherwise, a line break between two elements (after
//!   one element and its `,`, before the next);
//! - **one line:** otherwise. Line breaks only inside the elements keep the
//!   list on one line (`two(a +` newline `1, b)`). So does a list without
//!   elements (`()`, `{}`; a comment in it is §3.4's).
//!
//! An enclosure has the form of a list of one element (S-522): the block form
//! or one line. So has each pair inside the outermost of a node with nested
//! pairs (`-(` newline `(2))`).
//!
//! Every list keeps the writer's form: none is folded onto one line (S-510,
//! S-328).
//!
//! The indentation reads a base line from the brackets (§3.2, S-498, S-518):
//! the line of the opening bracket for a `(`, a `[`, an effect row and a
//! `use` list, and for any other `{` the line where the form that holds it
//! starts ([`Base`], [`holder`]).

use std::ops::Range;

use crate::cst::{Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// What a node with brackets is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape {
    /// A list (§3.2): written in one of the three forms.
    List,
    /// A block or a body of items: statements or items between line breaks.
    Container,
    /// Other brackets round something that is no list.
    Enclosure,
}

/// The line the content of the brackets is one level deeper than (§3.2, S-498).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Base {
    /// The line of the opening bracket: `(`, `[`, an effect row and a `use` list (S-518).
    Open,
    /// The line where the node starts (a struct pattern `P {`).
    Node,
    /// The line where the parent starts: the form the `{` is part of (the
    /// declaration of a `FieldList`, the `match` of its arms).
    Parent,
    /// A block: the parent's line when the block is the body of a form of
    /// [`BLOCK_HOLDERS`] (`fn f() {`, `if c {`, `} else {`), and its own
    /// line when it is a block expression, a form of its own.
    Body,
}

/// The form of a list (§3.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    OneLine,
    Block,
    Continuation,
}

/// The kinds of node with brackets: the shape and the opening and closing
/// tokens, and how many pairs of them a node of the kind holds.
pub(crate) struct Brackets {
    pub(crate) node: NodeKind,
    pub(crate) shape: Shape,
    pub(crate) open: TokenKind,
    pub(crate) close: TokenKind,
    pub(crate) pairs: Pairs,
    pub(crate) base: Base,
}

/// How many pairs of brackets a node holds among its own tokens.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Pairs {
    One,
    /// None or more, one inside the other (`-1`, `-(1)`, `-((1))`): [`brackets`] gives the outermost,
    /// [`pairs`] each.
    Nested,
}

use NodeKind as N;
use TokenKind as T;

const fn list(node: NodeKind, open: TokenKind, close: TokenKind) -> Brackets {
    Brackets { node, shape: Shape::List, open, close, pairs: Pairs::One, base: Base::Open }
}

const fn enclosure(node: NodeKind, open: TokenKind, close: TokenKind) -> Brackets {
    Brackets { node, shape: Shape::Enclosure, open, close, pairs: Pairs::One, base: Base::Open }
}

/// A node in braces, with its base line.
const fn braces(node: NodeKind, shape: Shape, base: Base) -> Brackets {
    Brackets { node, shape, open: T::LBrace, close: T::RBrace, pairs: Pairs::One, base }
}

/// The table: every kind of node with brackets.
pub(crate) const TABLE: &[Brackets] = &[
    // The lists of §3.2.
    list(N::ArgList, T::LParen, T::RParen), // arguments (of a call, a flow call, a handler)
    list(N::ParamList, T::LParen, T::RParen), // parameters, and the inputs of a flow
    list(N::ArrayExpr, T::LBracket, T::RBracket),
    list(N::TupleExpr, T::LParen, T::RParen),
    braces(N::StructLitFields, Shape::List, Base::Parent),
    braces(N::FieldList, Shape::List, Base::Parent),
    braces(N::VariantList, Shape::List, Base::Parent),
    braces(N::MatchArms, Shape::List, Base::Parent),
    braces(N::UseNames, Shape::List, Base::Open),
    list(N::TuplePat, T::LParen, T::RParen),
    list(N::TupleStructPat, T::LParen, T::RParen),
    braces(N::StructPat, Shape::List, Base::Node),
    // The lists of the places of types, of the effects and of the attributes: the same three forms (S-510,
    // S-328).
    list(N::TypeArgs, T::LBracket, T::RBracket),
    list(N::GenericParams, T::LBracket, T::RBracket),
    list(N::VariantFields, T::LParen, T::RParen),
    list(N::TupleType, T::LParen, T::RParen),
    list(N::FnTypeParams, T::LParen, T::RParen),
    braces(N::EffectRow, Shape::List, Base::Open),
    list(N::AttrArgs, T::LParen, T::RParen),
    // The containers (and `SourceFile`, which has no brackets: [`holds_statements`]).
    braces(N::Block, Shape::Container, Base::Body),
    braces(N::ItemList, Shape::Container, Base::Parent),
    // The other enclosures.
    enclosure(N::ParenExpr, T::LParen, T::RParen),
    enclosure(N::ParenPat, T::LParen, T::RParen),
    enclosure(N::ParenType, T::LParen, T::RParen),
    enclosure(N::UnitType, T::LParen, T::RParen),
    enclosure(N::RepeatExpr, T::LBracket, T::RBracket),
    enclosure(N::ArrayType, T::LBracket, T::RBracket),
    enclosure(N::IndexExpr, T::LBracket, T::RBracket),
    Brackets { pairs: Pairs::Nested, ..enclosure(N::NegLitPat, T::LParen, T::RParen) }, // `-(1)`
];

/// The row of [`TABLE`] of a kind of node; `None` for a node without brackets.
pub(crate) fn shape(kind: NodeKind) -> Option<&'static Brackets> {
    TABLE.iter().find(|b| b.node == kind)
}

/// The opening and the closing bracket of `n` (children of `n`), of the
/// outermost pair; `None` for a node without brackets.
pub(crate) fn brackets(cst: &Cst, n: NodeId) -> Option<(TokenIdx, TokenIdx)> {
    pairs(cst, n).first().copied()
}

/// The pairs of brackets of `n` (children of `n`), the outermost first: one,
/// or for a row of [`Pairs::Nested`] each with the next inside it. Empty for
/// a node without brackets.
pub(crate) fn pairs(cst: &Cst, n: NodeId) -> Vec<(TokenIdx, TokenIdx)> {
    let Some(b) = shape(cst.kind(n)) else { return Vec::new() };
    let of = |kind: TokenKind| cst.child_tokens(n).filter(move |&t| cst.token(t).kind == kind);
    match b.pairs {
        Pairs::One => of(b.open).next().zip(of(b.close).last()).into_iter().collect(),
        Pairs::Nested => of(b.open).zip(of(b.close).collect::<Vec<_>>().into_iter().rev()).collect(),
    }
}

/// A part of a list between its brackets and its `,`: the range of its code
/// tokens, and whether it is the `..` of a struct pattern.
struct Part {
    tokens: Range<TokenIdx>,
    rest: bool,
}

/// The parts of the list `n` (empty for a node that is no list).
fn parts(cst: &Cst, n: NodeId) -> Vec<Part> {
    let (Some(Brackets { shape: Shape::List, .. }), Some((open, close))) = (shape(cst.kind(n)), brackets(cst, n))
    else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut part: Option<Part> = None;
    for e in cst.children(n) {
        let (first, last, rest) = match *e {
            Elem::Token(t) if t <= open || cst.token(t).kind.is_trivia() => continue,
            Elem::Token(t) if t >= close || cst.token(t).kind == TokenKind::Comma => {
                out.extend(part.take());
                continue;
            }
            Elem::Token(t) => (t, t, false),
            Elem::Node(c) if cst.token_range(c).start <= open.index() => continue,
            Elem::Node(c) => match cst.significant_tokens(c) {
                Some((first, last)) => (first, last, cst.kind(c) == N::StructPatRest),
                None => continue,
            },
        };
        let start = part.take().map_or(first, |p| p.tokens.start);
        part = Some(Part { tokens: start..TokenIdx(last.0 + 1), rest });
    }
    out.extend(part);
    out
}

/// The elements of the list `n`, each as the range of its code tokens (from
/// the first to the last that is no trivia, the `,` after it not included).
/// Empty for a node that is no list. The `..` of a struct pattern is no
/// element (S-500: no `,` goes after it, also in the block form; [`rest`]);
/// a line break before it still makes the form ([`form`]).
pub(crate) fn elements(cst: &Cst, n: NodeId) -> Vec<Range<TokenIdx>> {
    parts(cst, n).into_iter().filter(|p| !p.rest).map(|p| p.tokens).collect()
}

/// The `..` of the struct pattern `n`, if it has one.
pub(crate) fn rest(cst: &Cst, n: NodeId) -> Option<Range<TokenIdx>> {
    parts(cst, n).into_iter().find(|p| p.rest).map(|p| p.tokens)
}

/// The first code token of each part of the list `n`, in order: its
/// elements and the `..` of a struct pattern ([`elements`], [`rest`]), read
/// once. Empty for a node that is no list.
pub(crate) fn part_starts(cst: &Cst, n: NodeId) -> Vec<TokenIdx> {
    parts(cst, n).into_iter().map(|p| p.tokens.start).collect()
}

/// A line break among the tokens from `from` to before `to`.
fn breaks(cst: &Cst, from: TokenIdx, to: TokenIdx) -> bool {
    cst.tokens()[from.index()..to.index()].iter().any(|t| t.kind == TokenKind::Newline)
}

/// The form the writer gave the list `n` (the module documentation), or the
/// enclosure `n`: as a list of one element (S-522), in the block form or on
/// one line. Each pair of [`pairs`] with its form; empty for a container and
/// a node without brackets.
pub(crate) fn forms(cst: &Cst, n: NodeId) -> Vec<((TokenIdx, TokenIdx), Form)> {
    if shape(cst.kind(n)).is_none_or(|b| b.shape == Shape::Container) {
        return Vec::new();
    }
    let parts = parts(cst, n);
    let form = |(open, close): (TokenIdx, TokenIdx)| {
        if cst.tokens()[open.index() + 1..close.index()].iter().all(|t| t.kind.is_trivia()) {
            return Form::OneLine;
        }
        let mut after_open =
            cst.tokens()[open.index() + 1..].iter().filter(|t| t.kind != T::Whitespace && !t.kind.is_comment());
        if after_open.next().is_some_and(|t| t.kind == T::Newline) {
            return Form::Block;
        }
        let between = parts.windows(2).any(|w| breaks(cst, w[0].tokens.end, w[1].tokens.start));
        if between { Form::Continuation } else { Form::OneLine }
    };
    pairs(cst, n).into_iter().map(|pair| (pair, form(pair))).collect()
}

/// The form of the outermost pair of `n` ([`forms`]).
#[cfg(test)]
pub(crate) fn form(cst: &Cst, n: NodeId) -> Option<Form> {
    forms(cst, n).first().map(|&(_, form)| form)
}

/// The kinds whose `Block` is a body that the head of the form leads to
/// (`fn f() {`, `if c {`, `} else {`): its `{` is part of that form. Any
/// other `Block` is a block expression, a form of its own (the self-test of
/// the tables names the kinds that hold those).
pub(crate) const BLOCK_HOLDERS: &[NodeKind] = &[
    N::Fn,
    N::Flow,
    N::Test,
    N::IfExpr,
    N::ForStmt,
    N::WhileStmt,
    N::ClosureExpr,
    N::HandleExpr,
    N::UnsafeExpr,
    N::ParExpr,
];

/// The node whose first line is the base line of the brackets of the node
/// `n` ([`Base`]); `None` when the base line is the line of the opening
/// bracket, or for a node without brackets.
pub(crate) fn holder(cst: &Cst, n: NodeId) -> Option<NodeId> {
    let parent = || cst.parent(n).expect("a node with brackets has a parent");
    match shape(cst.kind(n))?.base {
        Base::Open => None,
        Base::Node => Some(n),
        Base::Parent => Some(parent()),
        Base::Body if BLOCK_HOLDERS.contains(&cst.kind(parent())) => Some(parent()),
        Base::Body => Some(n),
    }
}

/// Whether the nodes of `kind` hold statements or items, with the line
/// breaks between them: the file and the containers.
pub(crate) fn holds_statements(kind: NodeKind) -> bool {
    kind == N::SourceFile || shape(kind).is_some_and(|b| b.shape == Shape::Container)
}
