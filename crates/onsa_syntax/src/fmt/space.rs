//! The spaces of `onsa fmt` between two tokens on one line
//! (`spec/tools.md` §3.2, the second item; spec §2.5, §2.6).
//!
//! [`space`] says whether two code tokens that the printer puts on one line
//! touch or have one space between them. It reads the two tokens and the
//! nodes that hold them, nothing else: the line breaks, the indentation and
//! the columns of the alignment (the `=` of a run of `let`, `fmt/align.rs`)
//! are decided elsewhere.
//!
//! The decision is the closed table [`ROWS`]. A row names the token on the
//! left, the token on the right (either may be any token) and the space
//! between them. **The pair touches when one row that matches it says none,
//! and has one space otherwise.** So only the rows that say none decide; the
//! rows that say one are there as the record of what §3.2 names, and the
//! self-test checks that no such row meets a row that says none where it
//! should not (`fmt/table_tests.rs`). A row that says none needs no order
//! against the others, and a decision of the spec changes one row.
//!
//! [`space`] reads the rows that say none through an index by the kind of
//! the left token, which it makes from [`ROWS`] once ([`by_left`]): the rows
//! whose left side may be a token of that kind (a row of any token on the
//! left is under every kind). It is no second table: a row changed in
//! [`ROWS`] changes it too, and the self-tests check it against every row.
//!
//! **A pair no row names has one space.** This is the general rule of §3.2
//! (S-496): one space before and after a keyword and a contextual word, and
//! every other pair of tokens on a line that §3.2 does not name. Its
//! exceptions are rows that say none: inside an opening bracket, after a
//! member `.`, the `(`, `[` and `~` that §2.5 and §2.6 write right after a
//! keyword (`fn(`, `impl[`, `if~`, `match~`), and the symbols next to a value
//! word (`self.x`, `!true`).

use std::sync::OnceLock;

use crate::cst::{Cst, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// The space between two tokens on one line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Space {
    None,
    One,
}

/// The tokens one side of a row is about.
#[derive(Clone, Copy)]
enum Tok {
    Any,
    Kinds(&'static [TokenKind]),
    /// A token of a binary operator ([`TokenKind::binop`]).
    BinOp,
}

/// One side of a row: the tokens, and the nodes that hold them (empty: any).
#[derive(Clone, Copy)]
struct Side {
    tok: Tok,
    within: &'static [NodeKind],
}

struct Row {
    left: Side,
    right: Side,
    space: Space,
}

const ANY: Side = Side { tok: Tok::Any, within: &[] };

const fn k(kinds: &'static [TokenKind]) -> Side {
    Side { tok: Tok::Kinds(kinds), within: &[] }
}

const fn k_in(kinds: &'static [TokenKind], within: &'static [NodeKind]) -> Side {
    Side { tok: Tok::Kinds(kinds), within }
}

const fn row(left: Side, right: Side, space: Space) -> Row {
    Row { left, right, space }
}

use NodeKind as N;
use Space::{None as NO, One as ONE};
use TokenKind as T;

/// The symbols with one space on each side (§3.2): `=`, `->`, `=>`, the range symbols (and `as`
/// and `at`, in their nodes: `at` may be the name of a method, `x.at(i)`).
const SPACED: &[TokenKind] = &[T::Eq, T::Arrow, T::FatArrow, T::DotDotLt, T::DotDotEq];
/// The `(` that opens a list right after the token before it (§2.5): a call, a
/// declaration, a closure and a function type, a variant, a pattern `Some(x)`, an attribute.
pub(super) const ATTACHED_PAREN: &[NodeKind] =
    &[N::ArgList, N::ParamList, N::FnTypeParams, N::VariantFields, N::TupleStructPat, N::AttrArgs];
/// The `[` that opens right after the token before it (§2.5): an index, type arguments, type parameters.
pub(super) const ATTACHED_SQUARE: &[NodeKind] = &[N::IndexExpr, N::TypeArgs, N::GenericParams];
/// The braces with one space inside on one line and before them (§3.2): blocks, the bodies of
/// declarations and of `match`, struct literals and patterns.
pub(super) const SPACED_BRACES: &[NodeKind] =
    &[N::Block, N::ItemList, N::FieldList, N::VariantList, N::MatchArms, N::StructLitFields, N::StructPat];
/// The braces with no space inside (§3.2): an effect row and a `use` list.
pub(super) const TIGHT_BRACES: &[NodeKind] = &[N::EffectRow, N::UseNames];

/// The table. Each row has where the rule comes from.
const ROWS: &[Row] = &[
    // §3.2: one space on each side of a binary operator, `=`, `->`, `=>`, `as`, `at`, `..<`, `..=`.
    row(Side { tok: Tok::BinOp, within: &[N::BinaryExpr] }, ANY, ONE),
    row(ANY, Side { tok: Tok::BinOp, within: &[N::BinaryExpr] }, ONE),
    row(k(SPACED), ANY, ONE),
    row(ANY, k(SPACED), ONE),
    row(k_in(&[T::KwAs], &[N::CastExpr]), ANY, ONE),
    row(ANY, k_in(&[T::KwAs], &[N::CastExpr]), ONE),
    row(k_in(&[T::KwAt], &[N::Clock]), ANY, ONE),
    row(ANY, k_in(&[T::KwAt], &[N::Clock]), ONE),
    // §3.2: one on each side of the `|` of a pattern and the `+` of bounds.
    row(k_in(&[T::Pipe], &[N::OrPat]), ANY, ONE),
    row(ANY, k_in(&[T::Pipe], &[N::OrPat]), ONE),
    row(k_in(&[T::Plus], &[N::TypeParam, N::Derives]), ANY, ONE),
    row(ANY, k_in(&[T::Plus], &[N::TypeParam, N::Derives]), ONE),
    // §3.2, §2.5: none after a prefix symbol (`-x`, `!x`, `-1` in a pattern, `^y`, `?Sized`, `@repr`).
    row(k_in(&[T::Minus, T::Bang], &[N::PrefixExpr]), ANY, NO),
    row(k_in(&[T::Minus], &[N::NegLitPat]), ANY, NO),
    row(k_in(&[T::Caret], &[N::FeedbackExpr]), ANY, NO),
    row(k_in(&[T::Question], &[N::Bound]), ANY, NO),
    row(k_in(&[T::At], &[N::Attr]), ANY, NO),
    // §3.2, §2.5, §2.6: none before the marks of a name (`f~(x)`, `f!(x)`) and the `~` of `if~` and
    // `match~` (after a mark of a name, the `(` of the arguments has none before it, below).
    row(ANY, k_in(&[T::Tilde, T::Bang], &[N::CallExpr]), NO),
    row(ANY, k_in(&[T::Tilde], &[N::IfExpr, N::MatchExpr]), NO),
    // §3.2, §2.5: none round a member `.` (`a.b`, `v.(x)`, `use a.{x}`) and `::` (`f::[T](x)`), before `?`.
    row(ANY, k(&[T::Dot, T::ColonColon]), NO),
    row(k(&[T::Dot, T::ColonColon]), ANY, NO),
    row(ANY, k_in(&[T::Question], &[N::TryExpr]), NO),
    // §2.5: none before the `(` and the `[` that open a list after a name, a keyword or a mark.
    row(ANY, k_in(&[T::LParen], ATTACHED_PAREN), NO),
    row(ANY, k_in(&[T::LBracket], ATTACHED_SQUARE), NO),
    // §3.2: none inside round and square brackets.
    row(k(&[T::LParen, T::LBracket]), ANY, NO),
    row(ANY, k(&[T::RParen, T::RBracket]), NO),
    // §3.2: one after `,`, `:` and `;` (`[e; N]`), none before.
    row(ANY, k(&[T::Comma, T::Colon, T::Semi]), NO),
    row(k(&[T::Comma, T::Colon, T::Semi]), ANY, ONE),
    // §3.2: one before a `{` (`fn f() {`, `Point { x: 1.0 }`, `uses {Alloc}`), and one inside the
    // braces on one line (`{ a }`, `Point { x: 1.0 }`, `match v { _ => 0 }`) but not inside those of
    // an effect row and of a `use` list (`uses {Alloc}`, `use a.{x, y}`), nor in an empty `{}`.
    row(ANY, k_in(&[T::LBrace], SPACED_BRACES), ONE),
    row(ANY, k_in(&[T::LBrace], &[N::EffectRow]), ONE),
    row(k_in(&[T::LBrace], SPACED_BRACES), ANY, ONE),
    row(ANY, k_in(&[T::RBrace], SPACED_BRACES), ONE),
    row(k_in(&[T::LBrace], TIGHT_BRACES), ANY, NO),
    row(ANY, k_in(&[T::RBrace], TIGHT_BRACES), NO),
    row(k(&[T::LBrace]), k(&[T::RBrace]), NO),
];

impl Tok {
    /// Whether a token of `kind` is one of these.
    fn admits(self, kind: TokenKind) -> bool {
        match self {
            Tok::Any => true,
            Tok::Kinds(kinds) => kinds.contains(&kind),
            Tok::BinOp => kind.binop().is_some(),
        }
    }
}

impl Side {
    fn matches(&self, cst: &Cst, t: TokenIdx) -> bool {
        self.tok.admits(cst.token(t).kind)
            && (self.within.is_empty() || self.within.contains(&cst.kind(cst.token_parent(t))))
    }
}

impl Row {
    fn matches(&self, cst: &Cst, left: TokenIdx, right: TokenIdx) -> bool {
        self.left.matches(cst, left) && self.right.matches(cst, right)
    }
}

/// The rows of [`ROWS`] that match the pair, as `(index, space)` (for the self-test).
#[cfg(test)]
pub(super) fn rows(cst: &Cst, left: TokenIdx, right: TokenIdx) -> impl Iterator<Item = (usize, Space)> + '_ {
    let all = ROWS.iter().enumerate();
    all.filter(move |(_, r)| r.matches(cst, left, right)).map(|(i, r)| (i, r.space))
}

/// The number of rows of [`ROWS`] (for the self-test that every row is met).
#[cfg(test)]
pub(super) const ROW_COUNT: usize = ROWS.len();

/// The rows of [`ROWS`] that say none, by the kind of the left token (its
/// discriminant, the index of the kind in [`TokenKind::ALL`]): those whose
/// left side admits a token of the kind (their indices in [`ROWS`]). Made
/// from [`ROWS`] at the first call.
fn by_left() -> &'static [Vec<usize>] {
    static INDEX: OnceLock<Vec<Vec<usize>>> = OnceLock::new();
    INDEX.get_or_init(|| {
        let none = || ROWS.iter().enumerate().filter(|(_, r)| r.space == NO);
        let of = |kind| none().filter(|(_, r)| r.left.tok.admits(kind)).map(|(i, _)| i).collect();
        TokenKind::ALL.iter().map(|&kind| of(kind)).collect()
    })
}

/// The space between the code tokens `left` and `right`, printed on one
/// line with `left` first: none when a row of [`ROWS`] that matches says
/// none, one otherwise (the module documentation).
pub(crate) fn space(cst: &Cst, left: TokenIdx, right: TokenIdx) -> Space {
    let rows = &by_left()[cst.token(left).kind as usize];
    if rows.iter().any(|&r| ROWS[r].matches(cst, left, right)) { NO } else { ONE }
}

#[cfg(test)]
mod tests {
    use super::{NO, ROWS, Tok, TokenKind, by_left};

    /// RF-14: the index of [`by_left`] holds, under each kind of token, the
    /// rows that say none and whose left side may be a token of that kind
    /// (any token, one of the kinds named, a binary operator), and no other.
    /// `fmt/table_tests.rs` checks its answers against every row.
    #[test]
    fn the_index_by_the_left_token_holds_the_rows_that_say_none_and_may_match_it() {
        let index = by_left();
        assert_eq!(index.len(), TokenKind::ALL.len());
        let (mut binops, mut named) = (0, 0);
        for (i, &kind) in TokenKind::ALL.iter().enumerate() {
            assert_eq!(kind as usize, i, "{kind:?}");
            let got = &index[i];
            let want: Vec<usize> = (0..ROWS.len())
                .filter(|&r| ROWS[r].space == NO)
                .filter(|&r| match ROWS[r].left.tok {
                    Tok::Any => true,
                    Tok::Kinds(kinds) => kinds.contains(&kind),
                    Tok::BinOp => kind.binop().is_some(),
                })
                .collect();
            assert_eq!(*got, want, "{kind:?}");
            binops += usize::from(kind.binop().is_some());
            named += usize::from(want.iter().any(|&r| matches!(ROWS[r].left.tok, Tok::Kinds(_))));
        }
        assert!(binops > 10 && named > 5, "{binops} binary operators, {named} kinds named on the left");
    }
}
