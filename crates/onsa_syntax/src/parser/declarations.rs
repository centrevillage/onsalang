//! The declarations ([`DECLARATIONS`]): their keywords, their nodes, how
//! each is parsed and where it may be written (§18.1).

use super::*;

/// A token that starts the head of a declaration (§18.1): a visibility, an
/// attribute (`@`, and `#[` of other languages, S-321) or a keyword of a
/// declaration ([`DECLARATIONS`]). The one list (the recovery's item starts
/// add the doc comments, `file::is_item_start`).
pub(super) fn starts_heading(kind: TokenKind) -> bool {
    is_declaration_keyword(kind)
        || matches!(kind, TokenKind::KwPub | TokenKind::KwPriv | TokenKind::At | TokenKind::Hash)
}

/// How a declaration is parsed after its attributes and visibility.
type DeclParser = fn(&mut Parser<'_>, ItemCtx) -> PResult<()>;

/// Where a declaration may be written: the top level of a module, and the
/// lists of declarations it is a member of (§18.1, [`Parser::not_a_member`]).
const TOP: &[ItemCtx] = &[ItemCtx::Top];
const FUNCTION_PLACES: &[ItemCtx] = &[
    ItemCtx::Top,
    ItemCtx::Trait,
    ItemCtx::Impl,
    ItemCtx::Effect,
    ItemCtx::Handler,
    ItemCtx::Extern,
    ItemCtx::InlineHandler,
];
const CONST_PLACES: &[ItemCtx] = &[ItemCtx::Top, ItemCtx::Trait, ItemCtx::Impl];
const TYPE_PLACES: &[ItemCtx] = &[ItemCtx::Top, ItemCtx::Extern];

/// A declaration: its keyword, its node, how it is parsed after its
/// attributes and visibility, and where it may be written.
pub(super) struct Declaration {
    pub(super) keyword: TokenKind,
    pub(super) node: NodeKind,
    pub(super) parse: DeclParser,
    pub(super) places: &'static [ItemCtx],
}

/// The keywords that start a declaration, with the node of the declaration,
/// how to parse it and where it may be written: the one list. `parse_item`
/// dispatches on it and refuses a declaration out of its places, and the
/// recovery's item starts (`file::is_item_start`) are these keywords and
/// what may come before them.
pub(super) const DECLARATIONS: &[Declaration] = &[
    Declaration { keyword: TokenKind::KwFn, node: NodeKind::Fn, parse: |p, c| p.parse_fn(c), places: FUNCTION_PLACES },
    Declaration { keyword: TokenKind::KwRt, node: NodeKind::Fn, parse: |p, c| p.parse_fn(c), places: FUNCTION_PLACES },
    Declaration { keyword: TokenKind::KwFlow, node: NodeKind::Flow, parse: |p, c| p.parse_flow(c), places: TOP },
    Declaration { keyword: TokenKind::KwStruct, node: NodeKind::Struct, parse: |p, c| p.parse_struct(c), places: TOP },
    Declaration { keyword: TokenKind::KwEnum, node: NodeKind::Enum, parse: |p, c| p.parse_enum(c), places: TOP },
    Declaration {
        keyword: TokenKind::KwType,
        node: NodeKind::TypeAlias,
        parse: |p, c| p.parse_type_item(c),
        places: TYPE_PLACES,
    },
    Declaration { keyword: TokenKind::KwTrait, node: NodeKind::Trait, parse: |p, c| p.parse_trait(c), places: TOP },
    Declaration { keyword: TokenKind::KwImpl, node: NodeKind::Impl, parse: |p, c| p.parse_impl(c), places: TOP },
    Declaration { keyword: TokenKind::KwEffect, node: NodeKind::Effect, parse: |p, c| p.parse_effect(c), places: TOP },
    Declaration {
        keyword: TokenKind::KwBlocking,
        node: NodeKind::Effect,
        parse: |p, c| p.parse_effect(c),
        places: TOP,
    },
    Declaration {
        keyword: TokenKind::KwHandler,
        node: NodeKind::Handler,
        parse: |p, c| p.parse_handler(c),
        places: TOP,
    },
    Declaration {
        keyword: TokenKind::KwConst,
        node: NodeKind::Const,
        parse: |p, c| p.parse_const(c),
        places: CONST_PLACES,
    },
    Declaration { keyword: TokenKind::KwUse, node: NodeKind::Use, parse: |p, c| p.parse_use(c), places: TOP },
    Declaration { keyword: TokenKind::KwExtern, node: NodeKind::Extern, parse: |p, c| p.parse_extern(c), places: TOP },
    Declaration { keyword: TokenKind::KwTarget, node: NodeKind::Target, parse: |p, c| p.parse_target(c), places: TOP },
    Declaration { keyword: TokenKind::KwTest, node: NodeKind::Test, parse: |p, c| p.parse_test(c), places: TOP },
];

/// The declaration whose keyword is `kind`, if one is ([`DECLARATIONS`]).
pub(super) fn declaration(kind: TokenKind) -> Option<&'static Declaration> {
    DECLARATIONS.iter().find(|d| d.keyword == kind)
}

/// The node of the declaration whose keyword is `kind` ([`DECLARATIONS`]).
pub(crate) fn declaration_node(kind: TokenKind) -> Option<NodeKind> {
    declaration(kind).map(|d| d.node)
}

/// Whether `kind` is the keyword of a declaration ([`DECLARATIONS`]).
pub(super) fn is_declaration_keyword(kind: TokenKind) -> bool {
    declaration(kind).is_some()
}
